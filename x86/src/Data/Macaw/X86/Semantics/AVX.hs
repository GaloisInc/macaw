{-# Language GADTs,PatternGuards, RankNTypes #-}
module Data.Macaw.X86.Semantics.AVX (all_instructions) where

import Data.Word(Word8)
import Data.Int(Int8)
import Control.Monad(forM_)

import Data.Parameterized.NatRepr

import Flexdis86.Register (ymmReg)
import qualified Flexdis86 as F

import Data.Macaw.CFG.Core(bvValue)
import Data.Macaw.Types(typeWidth)

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Monad((.=), ymm, reg_high128)
import Data.Macaw.X86.Getters(SomeBV(..),getSomeBVValue,getSomeBVLocation)
import Data.Macaw.X86.Generator(X86Generator, Expr(..),inAVX,evalArchFn,eval)
import Data.Macaw.X86.X86Reg
import Data.Macaw.X86.ArchTypes(X86PrimFn(..))

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

avx4 :: String ->
        (forall st ids.
            F.Value -> F.Value -> F.Value -> Int8 -> X86Generator st ids ()) ->
        InstructionDef
avx4 m k = defInstruction m $ \ii ->
    case F.iiArgs ii of
      [(v1,_), (v2,_), (v3,_), (F.ByteImm v4, _) ]  -> k v1 v2 v3 v4
      [_,_,_,_] -> fail $ "[avx4]: " ++ m ++ " expected operand 4 to be a byte"
      n -> fail $ "[avx4]: " ++ m ++ ": expecting 4 arguments, got " ++
                                                               show (length n)


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

  , avx4 "vpalignr" $ \dst src1 src2 amt ->
      do SomeBV l  <- getSomeBVLocation dst
         SomeBV e1 <- getSomeBVValue src1
         SomeBV e2 <- getSomeBVValue src2
         let lw  = typeWidth l
             e1w = typeWidth e1
             e2w = typeWidth e2
         case (testEquality lw e1w, testEquality e1w e2w) of
           (Just Refl, Just Refl) ->
              do v1 <- eval e1
                 v2 <- eval e2
                 r <- evalArchFn (VPAlignr lw v1 v2 (fromIntegral amt))
                 l .= r
           _ -> fail "[vpalignr]: Arguements of different widths"

  ]


