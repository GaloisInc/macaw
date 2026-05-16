{-# LANGUAGE TypeApplications #-}

module AbsDomain.SolveDiophantineTests
  ( tests
  ) where

import qualified Hedgehog as H
import qualified Hedgehog.Gen as H.Gen
import qualified Hedgehog.Range as H.Range
import qualified Test.Tasty as TT
import qualified Test.Tasty.Hedgehog as TTH

import           Data.Macaw.AbsDomain.StridedInterval.Internal

-- ---------------------------------------------------------------------------
-- Generators

-- | Positive 'Integer' biased toward small values, with exponential reach
-- toward 2^32.  Most samples are small so common cases dominate, but large
-- values are still exercised.
genPos :: H.Gen Integer
genPos = H.Gen.integral (H.Range.exponential 1 (2 ^ (32 :: Int)))

-- | Nonzero 'Integer' (positive or negative), exponentially biased.
genNonZero :: H.Gen Integer
genNonZero = H.Gen.choice
  [ H.Gen.integral (H.Range.exponential 1 (2 ^ (32 :: Int)))
  , H.Gen.integral (H.Range.exponentialFrom (-1) (- (2 ^ (32 :: Int))) (-1))
  ]

-- | Small positive 'Integer' (at most 64).  Used where a property iterates
-- @[0 .. n]@ for brute-force checks.
genSmallPos :: H.Gen Integer
genSmallPos = H.Gen.integral (H.Range.linear 1 64)

-- ---------------------------------------------------------------------------
-- eGCD properties

prop_eGCD_bezout :: H.Property
prop_eGCD_bezout = H.property $ do
  a <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  b <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  let (g, n, m) = eGCD a b
  n * a + m * b H.=== g

prop_eGCD_nonNegative :: H.Property
prop_eGCD_nonNegative = H.property $ do
  a <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  b <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  let (g, _, _) = eGCD a b
  H.assert (g >= 0)

prop_eGCD_divides :: H.Property
prop_eGCD_divides = H.property $ do
  a <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  b <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  let (g, _, _) = eGCD a b
  if g == 0
    then do
      a H.=== 0
      b H.=== 0
    else do
      a `mod` g H.=== 0
      b `mod` g H.=== 0

prop_eGCD_matches_gcd :: H.Property
prop_eGCD_matches_gcd = H.property $ do
  a <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  b <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-256) 256))
  let (g, _, _) = eGCD a b
  g H.=== gcd a b

-- ---------------------------------------------------------------------------
-- ceil_quot / floor_quot properties

prop_ceil_quot_bounds :: H.Property
prop_ceil_quot_bounds = H.property $ do
  x <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-1024) 1024))
  y <- H.forAll genPos
  let q = ceil_quot x y
  -- q is the least integer with q * y >= x
  H.assert (q * y >= x)
  H.assert ((q - 1) * y < x)

prop_floor_quot_bounds :: H.Property
prop_floor_quot_bounds = H.property $ do
  x <- H.forAll (H.Gen.integral (H.Range.linearFrom 0 (-1024) 1024))
  y <- H.forAll genPos
  let q = floor_quot x y
  -- q is the greatest integer with q * y <= x
  H.assert (q * y <= x)
  H.assert ((q + 1) * y > x)

-- ---------------------------------------------------------------------------
-- solveLinearDiophantine properties

-- | Soundness: every returned @(x, y)@ must satisfy the equation and the
-- nonnegativity / range bounds.  We construct the input from a known
-- solution so the solver is guaranteed to succeed.
prop_sld_sound :: H.Property
prop_sld_sound = H.property $ do
  a    <- H.forAll genPos
  b    <- H.forAll genPos
  aMax <- H.forAll genPos
  bMax <- H.forAll genPos
  x0   <- H.forAll (H.Gen.integral (H.Range.linear 0 aMax))
  y0   <- H.forAll (H.Gen.integral (H.Range.linear 0 bMax))
  let c = a * x0 - b * y0
  if c == 0
    then H.discard  -- the function's contract requires c /= 0
    else case solveLinearDiophantine a b c aMax bMax of
           Nothing     -> H.failure
           Just (x, y) -> do
             H.assert (0 <= x && x <= aMax)
             H.assert (0 <= y && y <= bMax)
             a * x - b * y H.=== c

-- | Completeness, brute-forced on small inputs: if any nonnegative
-- @(x, y)@ in range solves the equation, 'solveLinearDiophantine' must
-- return /something/ (not necessarily the same pair).
prop_sld_complete :: H.Property
prop_sld_complete = H.property $ do
  a    <- H.forAll genSmallPos
  b    <- H.forAll genSmallPos
  c    <- H.forAll genNonZero
  aMax <- H.forAll genSmallPos
  bMax <- H.forAll genSmallPos
  let exists = or [ a * x - b * y == c
                  | x <- [0 .. aMax], y <- [0 .. bMax]
                  ]
  case (exists, solveLinearDiophantine a b c aMax bMax) of
    (True,  Nothing) -> H.failure
    (False, Just _ ) -> H.failure
    _                -> H.success

prop_sld_endpoint_intersection :: H.Property
prop_sld_endpoint_intersection = H.property $ do
  -- a * k - 1 * 0 = a * k for any k <= aMax means y=0, x=k is a solution.
  a    <- H.forAll genPos
  k    <- H.forAll genPos
  let aMax = k
      bMax = 1
      c    = a * k
  case solveLinearDiophantine a 1 c aMax bMax of
    Just _  -> H.success
    Nothing -> H.failure

-- ---------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "StridedInterval.Internal"
  [ TT.testGroup "eGCD"
    [ TTH.testProperty "Bezout identity"            prop_eGCD_bezout
    , TTH.testProperty "g is nonnegative"           prop_eGCD_nonNegative
    , TTH.testProperty "g divides both inputs"      prop_eGCD_divides
    , TTH.testProperty "matches Prelude.gcd"        prop_eGCD_matches_gcd
    ]
  , TT.testGroup "ceil_quot / floor_quot"
    [ TTH.testProperty "ceil_quot bounds"  prop_ceil_quot_bounds
    , TTH.testProperty "floor_quot bounds" prop_floor_quot_bounds
    ]
  , TT.testGroup "solveLinearDiophantine"
    [ TTH.testProperty "sound"                       prop_sld_sound
    , TTH.testProperty "complete (brute-force)"      prop_sld_complete
    , TTH.testProperty "finds endpoint intersection" prop_sld_endpoint_intersection
    ]
  ]
