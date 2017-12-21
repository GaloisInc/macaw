{-# Language GADTs, RankNTypes, DataKinds, TypeOperators #-}
module Data.Macaw.X86.Semantics.AVX (all_instructions) where

import Data.Word(Word8)
import Data.Int(Int8)
import Control.Monad(forM_)

import Data.Parameterized.NatRepr

import Flexdis86.Register (ymmReg)
import qualified Flexdis86 as F

import Data.Macaw.CFG.Core(Value,bvValue)
import Data.Macaw.Types(BVType,typeWidth,n0,n1,n32,n256)

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Monad((.=), ymm, reg_high128)
import Data.Macaw.X86.Getters(SomeBV(..),getSomeBVValue,getSomeBVLocation)
import Data.Macaw.X86.Generator(X86Generator, Expr(..),inAVX,evalArchFn,eval)
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.ArchTypes(X86_64,X86PrimFn(..),
                                  AVXOp1(..),AVXOp2(..),AVXPointWiseOp2(..))

maxReg :: Word8
maxReg = 15 -- or 7 in 32-bit mode

avxMov :: String -> InstructionDef
avxMov m = defBinary m def
  where
  def :: unused -> F.Value -> F.Value -> X86Generator st ids ()
  def _ v1 v2 = inAVX $
    do SomeBV l <- getSomeBVLocation v1
       SomeBV v <- getSomeBVValue v2
       let lw = typeWidth l
           lv = typeWidth v
       case testEquality lw lv of
         Just Refl -> l .= v
         Nothing -> fail $ "Widths aren't equal: " ++ show lw ++ " and "
                                                   ++ show lv


avx3 :: String ->
        (forall st ids.  F.Value -> F.Value -> F.Value ->
                                                  X86Generator st ids ()) ->
        InstructionDef
avx3 m k = defInstruction m $ \ii ->
    case F.iiArgs ii of
      [(v1,_), (v2,_), (v3,_)] -> inAVX (k v1 v2 v3)
      n -> fail $ "[avx3] " ++ m ++ " needs 3 arguments, but has " ++
                                                               show (length n)

avx4 :: String ->
        (forall st ids.
            F.Value -> F.Value -> F.Value -> Int8 -> X86Generator st ids ()) ->
        InstructionDef
avx4 m k = defInstruction m $ \ii ->
    case F.iiArgs ii of
      [(v1,_), (v2,_), (v3,_), (F.ByteImm v4, _) ]  -> inAVX (k v1 v2 v3 v4)
      [_,_,_,_] -> fail $ "[avx4]: " ++ m ++ " expected operand 4 to be a byte"
      n -> fail $ "[avx4] " ++ m ++ " needs 4 arguments but has " ++
                                                               show (length n)

(<~) :: F.Value -> X86PrimFn (Value X86_64 ids) (BVType n) ->
                                                    X86Generator st ids ()
loc <~ f =
  do SomeBV lc <- getSomeBVLocation loc
     r         <- evalArchFn f
     case testEquality (typeWidth lc) (typeWidth r) of
       Just Refl -> lc .= r
       Nothing   -> fail "Value and result sizes are different"


avxOp1I :: String -> (Word8 -> AVXOp1) -> InstructionDef
avxOp1I mnem op = avx3 mnem $ \arg1 arg2 arg3 ->
  do SomeBV vec <- getSomeBVValue arg2
     let vw = typeWidth vec
     case arg3 of
       F.ByteImm amt ->
          do v <- eval vec
             arg1 <~ VOp1 vw (op (fromIntegral amt)) v
       _ -> fail ("[" ++ mnem ++ "]: Expected argument 3 to be immediate.")

avxOp2I :: String -> (Word8 -> AVXOp2) -> InstructionDef
avxOp2I mnem op =
  avx4 mnem $ \dst src1 src2 amt ->
    do SomeBV e1 <- getSomeBVValue src1
       SomeBV e2 <- getSomeBVValue src2
       let e1w = typeWidth e1
           e2w = typeWidth e2
       case testEquality e1w e2w of
         Just Refl ->
            do v1 <- eval e1
               v2 <- eval e2
               dst <~ VOp2 e1w (op (fromIntegral amt)) v1 v2
         _ -> fail ("[" ++ mnem ++ "]: Arguements of different widths")





avxOp2 :: String -> AVXOp2 -> InstructionDef
avxOp2 mnem op =
  avx3 mnem $ \arg1 arg2 arg3 ->
    do SomeBV vec1 <- getSomeBVValue arg2
       SomeBV vec2 <- getSomeBVValue arg3
       let v1w = typeWidth vec1
           v2w = typeWidth vec2
       case testEquality v1w v2w of
         Just Refl ->
           do v1 <- eval vec1
              v2 <- eval vec2
              arg1 <~ VOp2 v1w op v1 v2
         _ -> fail ("[" ++ mnem ++ "] Invalid arguments")

avxPointwise2 :: (1 <= n) => String -> AVXPointWiseOp2 -> NatRepr n ->
                                                              InstructionDef
avxPointwise2 mnem op sz =
  avx3 mnem $ \arg1 arg2 arg3 ->
    do SomeBV vec1 <- getSomeBVValue arg2
       SomeBV vec2 <- getSomeBVValue arg3
       let v1w = typeWidth vec1
           v2w = typeWidth vec2
       withDivModNat v1w sz $ \elN remi ->
         case (testEquality v1w v2w, testEquality remi n0, testLeq n1 elN) of
           (Just Refl, Just Refl, Just LeqProof) ->
              do v1 <- eval vec1
                 v2 <- eval vec2
                 arg1 <~ Pointwise2 elN sz op v1 v2
           _ -> fail ("[" ++ mnem ++ "] Invalid arguments")



all_instructions :: [InstructionDef]
all_instructions =
  [

    defNullary "vzeroall" $
      inAVX $
      forM_ [ 0 .. maxReg ] $ \r ->
        ymm (ymmReg r) .= ValueExpr (bvValue 0)

  , defNullary "vzeroupper" $
      inAVX $
      forM_ [ 0 .. maxReg ] $ \r ->
        reg_high128 (YMM (ymmReg r)) .= ValueExpr (bvValue 0)

  , avxMov "vmovaps"
  , avxMov "vmovups"
  , avxMov "vmovdqa"
  , avxMov "vmovdqu"

  , avx3 "vpslld" $ \arg1 arg2 arg3 ->
      do SomeBV vec <- getSomeBVValue arg2
         SomeBV amt <- getSomeBVValue arg3
         let vw   = typeWidth vec
             amtw = typeWidth amt
         withDivModNat vw n32 $ \elN remi ->
           case (testEquality remi n0, testLeq n1 elN) of
             (Just Refl, Just LeqProof) ->
               do v <- eval vec
                  a <- eval amt
                  arg1 <~ PointwiseShiftL elN n32 amtw v a
             _ -> fail "[vpslld]: invalid arguments"

  , avxOp1I "vpslldq" VShiftL
  , avxOp1I "vpshufd" VShufD

  , avxPointwise2 "vpaddd" PtAdd n32
  , avxPointwise2 "vpsubd" PtAdd n32

  , avxOp2 "vpand" VPAnd
  , avxOp2 "vpor" VPOr
  , avxOp2 "vpxor" VPXor
  , avxOp2 "vpshufb" VPShufB

  , avxOp2I "vpalignr" VPAlignR

  , avxOp2 "vaesenc" VAESEnc
  , avxOp2 "vaesenclast" VAESEncLast

  , avx3 "vextractf128" $ \arg1 arg2 arg ->
      do SomeBV vec <- getSomeBVValue arg2
         case (testEquality (typeWidth vec) n256, arg) of
           (Just Refl, F.ByteImm i) ->
              do v <- eval vec
                 arg1 <~ VExtractF128 v (fromIntegral i)
           _ -> fail "[vextractf128] Unexpected operands"

  , avxOp2I "vpclmulqdq" VPCLMULQDQ
  ]


