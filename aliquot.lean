import NULL.Basic
import Mathlib
open Equiv

def ali (k : ℕ) : ℕ → ℕ
  | 0 => k
  | n + 1 => (Nat.properDivisors (ali k n)).sum id
