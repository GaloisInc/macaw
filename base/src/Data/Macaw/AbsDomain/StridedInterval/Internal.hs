{-|
Copyright        : (c) Galois, Inc 2015-2026

Internal helpers for "Data.Macaw.AbsDomain.StridedInterval".  Exposed only so
that the test suite can exercise them directly; not part of the public API.
-}
module Data.Macaw.AbsDomain.StridedInterval.Internal
  ( solveLinearDiophantine
  , eGCD
  , ceil_quot
  , floor_quot
  ) where

-- solves ax - by = c, (NOTE - sign) for x and y with 0 <= x, y <=
-- a_max, b_max resp.  Assumes a > 0, b > 0, c /= 0.
--
-- In this restricted case, we have
--
-- a * n - b * m = gcd (a, -b) (> 0)
--
-- so we want least t s.t.
--
-- ceiling (max (n * c / - a, m * c / - b)) <= t
-- and
-- t <= floor (min ((a_max * gcd - n * c) / b, b_max * gcd - m * c) / a)

solveLinearDiophantine :: Integer -> Integer -> Integer
                          -> Integer -> Integer
                          -> Maybe (Integer, Integer)
solveLinearDiophantine a b c a_max b_max
  | c `rem` g /= 0 = Nothing
  | t <= t_upper = Just ( n * (c `quot` g) + (b `quot` g) * t
                        , m * (c `quot` g) + (a `quot` g) * t )
  | otherwise  = Nothing
  where
    (g, n, m) = eGCD a (-b)

    t = max (ceil_quot (n * c) (- a)) (ceil_quot (m * c) (- b))
    t_upper = min (floor_quot (a_max * g - n * c) b)
                  (floor_quot (b_max * g - m * c) a)

-- calculates ceil(x/y)
ceil_quot :: Integral a => a -> a -> a
ceil_quot x y = x `quot` y + (if x `rem` y == 0 then 0 else 1)

floor_quot :: Integral a => a -> a -> a
floor_quot _ 0 = error "floor_quot div by 0"
floor_quot x y = x `div` y

-- prop_sld :: Positive Integer -> Positive Integer
--             -> NonZero Integer -> Positive Integer -> Positive Integer
--             -> Property
-- prop_sld a b c d e = not (isNothing v) ==> p
--   where
--     p = case v of
--          Just (x, y) -> x >= 0 && y >= 0
--                         && x <= getPositive d
--                         && y <= getPositive e
--                         && (getPositive a) * x - (getPositive b) * y == (getNonZero c)
--          _ -> True
--     v = solveLinearDiophantine (getPositive a) (getPositive b) (getNonZero c)
--                                (getPositive d) (getPositive e)


-- | Returns the gcd, and n and m s.t. n * a + m * b = g
-- clagged, fixed, from
--    http://en.wikibooks.org/wiki/Algorithm_Implementation/Mathematics/Extended_Euclidean_algorithm
-- this is presumably going to be slower than the gmp version :(
eGCD :: Integral a => a -> a -> (a,a,a)
eGCD a0 b0 = let (g, m, n) = go a0 b0
           in if g < 0 then (-g, -m, -n) else (g, m, n)
  where
    go a 0 = (a, 1, 0)
    go a b = let (g, x, y) = go b $ rem a b
             in (g, y, x - (a `quot` b) * y)

-- prop_eGCD :: Integer -> Integer -> Bool
-- prop_eGCD x y = let (g, a, b) = eGCD x y in x * a + y * b == g
