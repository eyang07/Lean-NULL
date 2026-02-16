import NULL.Basic
import Mathlib
open Equiv

-- An Almost Perfect Number satisfies: σ(n) = 2n -1
-- This is equivalent to: s(n) = n - 1
-- In Nat, 0 - 1 = 0, so we require n to be positive to avoid
-- zero satisfying the criterion
def AlmostPerfectNumber (n : ℕ) : Prop :=
  n > 0 ∧ n.properDivisors.sum id = n - 1

def IsPowerOfTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ k

-- The Non-Power-Of-2 Almost Perfect Numbers Conjecture asks if there is an
-- Almost perfect number that is not a power of 2
theorem NonPowOfTwoAlmostPerfectNumbersConjecture :
  ∃ n : ℕ, AlmostPerfectNumber n ∧ ¬IsPowerOfTwo n := by
  sorry
