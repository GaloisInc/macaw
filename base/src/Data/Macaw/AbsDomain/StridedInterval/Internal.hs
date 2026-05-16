{-|
Copyright        : (c) Galois, Inc 2015-2026

Internal helpers for "Data.Macaw.AbsDomain.StridedInterval".  Exposed so the
test suite can exercise them directly; not part of the public API.
-}
module Data.Macaw.AbsDomain.StridedInterval.Internal
  ( solveLinearDiophantine
  , eGCD
  , ceilDivPos
  , floorDivPos
  ) where

-- | @solveLinearDiophantine a b c a_max b_max@ finds nonnegative integers @x,
-- y@ with @0 <= x <= a_max@, @0 <= y <= b_max@ such that
--
-- > a * x - b * y = c
--
-- Assumes @a > 0@, @b > 0@, and @c /= 0@.  Returns 'Nothing' when no such pair
-- exists; when one does, returns the lex-least solution.
--
-- == Proof of correctness
--
-- We must show two things: (1) the function returns 'Nothing' exactly when no
-- solution in the 2D box @0 <= x <= a_max@, @0 <= y <= b_max@ exists, and (2)
-- when a solution in the box exists, the returned pair is the lex-least one.
-- We prove both by reducing the search over the two-dimensional set
--
-- > S = { (x, y) ∈ Z^2 : a*x - b*y = c, 0 <= x <= a_max, 0 <= y <= b_max }
--
-- to a search over a one-dimensional integer interval @[t_lower, t_upper]@, via
-- a bijection @t \<-\> (x(t), y(t))@ that is increasing in both coordinates.
-- Three lemmas do the work; the function then simply checks whether the
-- @t@-interval is nonempty and, if so, evaluates @(x, y)@ at its left endpoint.
--
-- The construction follows the standard Bézout / extended-Euclidean recipe for
-- linear Diophantine equations, restricted to the box.
--
-- === Setup
--
-- Let @g = gcd(a, b)@; since @a, b > 0@, @g > 0@.  'eGCD', called with @-b@,
-- returns @(g, n, m)@ satisfying
--
-- > n * a - m * b = g                                                (*)
--
-- Define @aq = a \/ g@ and @bq = b \/ g@; both are positive integers.  By the
-- general identity @gcd(k*x, k*y) = k * gcd(x, y)@ for @k > 0@, applied to
-- @a = g*aq@ and @b = g*bq@, we get @g = gcd(a, b) = g * gcd(aq, bq)@, hence
--
-- > gcd(aq, bq) = 1                                                  (coprime)
--
-- === Lemma 1 (Divisibility is necessary)
--
-- If @a*x - b*y = c@ has any integer solution, then @g | c@.  Proof: the left
-- side is an integer combination of @a@ and @b@, hence a multiple of @g@.  So
-- if @g@ does not divide @c@, even the unbounded equation has no solutions and
-- @S@ is empty.  The code checks this as @c \`rem\` g /= 0@.
--
-- === Lemma 2 (Bézout parameterization)
--
-- Assume @g | c@ and let @cq = c \/ g@.  Then the set of /all/ integer
-- solutions to @a*x - b*y = c@ is exactly
--
-- > P = { (n*cq + bq*t, m*cq + aq*t) : t ∈ Z }                       (**)
--
-- We need both inclusions.
--
-- /(P ⊆ solutions.)/  For any @t ∈ Z@, direct substitution gives
--
-- > a*(n*cq + bq*t) - b*(m*cq + aq*t)
-- >   = (n*a - m*b)*cq + (a*bq - b*aq)*t      { distribute, regroup by cq and t }
-- >   = g*cq + (a*bq - b*aq)*t                { by (*) }
-- >   = g*cq + (a*(b\/g) - b*(a\/g))*t        { unfold aq = a\/g, bq = b\/g }
-- >   = g*cq + 0                              { a*b\/g - b*a\/g = 0 }
-- >   = g*(c\/g)                              { unfold cq = c\/g }
-- >   = c                                     { simplify }
--
-- /(solutions ⊆ P.)/  This direction is what justifies enumerating by @t@ at
-- all: it ensures we are not missing solutions outside @P@.  Let @(x, y)@ be
-- any solution.  Then
--
-- > a*(x - n*cq) - b*(y - m*cq)
-- >   = (a*x - b*y) - (a*(n*cq) - b*(m*cq))   { distribute }
-- >   = c - (n*a - m*b)*cq                    { (x,y) solves the equation; regroup }
-- >   = c - g*cq                              { by (*) }
-- >   = c - g*(c\/g)                          { unfold cq = c\/g }
-- >   = 0                                     { g | c, so g*(c\/g) = c }
--
-- so @a*(x - n*cq) = b*(y - m*cq)@; dividing by @g > 0@,
--
-- > aq*(x - n*cq) = bq*(y - m*cq)
--
-- This shows @bq | aq*(x - n*cq)@.  By Euclid's lemma — if @gcd(p, q) = 1@ and
-- @p | q*r@, then @p | r@ — together with (coprime), we conclude @bq | (x -
-- n*cq)@.  Let @t = (x - n*cq) \/ bq@; then @x = n*cq + bq*t@, and substituting
-- into the displayed equation gives @aq*bq*t = bq*(y - m*cq)@, so @y = m*cq
-- + aq*t@ (since @bq > 0@). Hence @(x, y) ∈ P@ with this @t@, which is unique
-- because @aq, bq@ are nonzero.
--
-- === Lemma 3 (Box constraints reduce to a @t@-interval)
--
-- Under the bijection @t \<-\> (x(t), y(t))@ from (**), the four box
-- constraints are equivalent to a single integer interval on @t@. Substituting
-- into @0 <= x <= a_max@ and @0 <= y <= b_max@ gives
--
-- > -n*cq <= bq*t <= a_max - n*cq        -m*cq <= aq*t <= b_max - m*cq
--
-- Multiplying through by @g > 0@ and using @g*bq = b@, @g*cq = c@ (and
-- analogously for @a@) preserves the inequalities and clears the divisions:
--
-- > -n*c <= b*t <= a_max*g - n*c          -m*c <= a*t <= b_max*g - m*c
--
-- Since @a, b > 0@, dividing by the coefficient of @t@ preserves the
-- direction; rounding inward (because @t@ is an integer) is exact.  So the
-- four constraints are equivalent to @t_lower <= t <= t_upper@ where
--
-- > t_lower = max (ceiling(-n*c \/ b)) (ceiling(-m*c \/ a))
-- > t_upper = min (floor((a_max*g - n*c) \/ b)) (floor((b_max*g - m*c) \/ a))
--
-- === Putting it together
--
-- Combining Lemmas 1--3, @S@ is nonempty iff @g | c@ /and/ @t_lower <=
-- t_upper@; and when it is, @S = { (x(t), y(t)) : t_lower <= t <= t_upper
-- }@.  Since @aq, bq > 0@, both coordinates of (**) are strictly increasing
-- in @t@, so @t = t_lower@ simultaneously minimizes @x@ and @y@ and yields the
-- lex-least element of @S@.
--
-- The code mirrors this exactly: it returns 'Nothing' when @cr /= 0@ (Lemma
-- 1) or @t_upper < t@ (Lemma 3), and otherwise @Just (x(t_lower), y(t_lower))@
-- (Lemma 2).
solveLinearDiophantine :: Integer -> Integer -> Integer
                       -> Integer -> Integer
                       -> Maybe (Integer, Integer)
solveLinearDiophantine a b c a_max b_max
  | cr /= 0      = Nothing  -- Lemma 1
  | t_upper < t  = Nothing  -- Lemma 3
  | otherwise    = Just (n * cq + bq * t, m * cq + aq * t)  -- Lemma 2
  where
    (g, n, m) = eGCD a (-b)
    (cq, cr)  = c `quotRem` g
    aq        = a `quot` g
    bq        = b `quot` g
    nc        = n * c
    mc        = m * c
    t         = max (ceilDivPos (-nc) b) (ceilDivPos (-mc) a)
    t_upper   = min (floorDivPos (a_max * g - nc) b)
                    (floorDivPos (b_max * g - mc) a)

-- | Extended Euclidean algorithm.  @eGCD a b@ returns @(g, n, m)@ such that
-- @n * a + m * b = g@ and @g >= 0@.  When @a@ and @b@ are both nonzero, @g@
-- is @gcd a b@.
--
-- Adapted from the Wikibooks reference implementation:
-- <http://en.wikibooks.org/wiki/Algorithm_Implementation/Mathematics/Extended_Euclidean_algorithm>
eGCD :: Integer -> Integer -> (Integer, Integer, Integer)
eGCD a0 b0 =
  case go a0 b0 of
    (g, n, m)
      | g < 0     -> (-g, -n, -m)
      | otherwise -> (g, n, m)
  where
    go a 0 = (a, 1, 0)
    go a b =
      case go b (rem a b) of
        (g, x, y) -> (g, y, x - (a `quot` b) * y)

-- | @ceilDivPos x y@ is @ceiling(x \/ y)@ as integers.  Requires @y > 0@.
ceilDivPos :: Integer -> Integer -> Integer
ceilDivPos x y = negate (negate x `div` y)
{-# INLINE ceilDivPos #-}

-- | @floorDivPos x y@ is @floor(x \/ y)@ as integers.  Requires @y > 0@.
floorDivPos :: Integer -> Integer -> Integer
floorDivPos x y = x `div` y
{-# INLINE floorDivPos #-}
