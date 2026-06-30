import Mathlib.NumberTheory.LucasLehmer
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

-- ============================================================================
-- 𝔽_p with p = 2¹²⁷ − 1: Octra's arithmetic field
-- ============================================================================
--
-- Octra HFHE does arithmetic "on a 127-bit prime field".  That prime is the
-- Mersenne prime p = 2¹²⁷ − 1 (Lucas 1876).  This file establishes p is prime
-- (via the Lucas–Lehmer test, already in Mathlib) and packages 𝔽_p = ZMod p as
-- a field, ready to be the plaintext / ciphertext-coefficient carrier in Phase 3.

namespace Octra.Field127

-- Octra's modulus: the Mersenne prime `p = 2¹²⁷ − 1`.
abbrev p : ℕ := 2 ^ 127 - 1

-- `p` is literally `mersenne 127`.
theorem p_eq_mersenne : p = mersenne 127 := rfl

-- Its 39-digit decimal value.
theorem p_value : p = 170141183460469231731687303715884105727 := by norm_num

-- `p` is prime, certified by the Lucas-Lehmer test.
theorem p_prime : Nat.Prime p :=
  lucas_lehmer_sufficiency _ (by simp) (by norm_num)

instance : Fact (Nat.Prime p) := ⟨p_prime⟩
instance : NeZero p := ⟨p_prime.ne_zero⟩

-- The 127-bit prime field `𝔽_p` (plaintext space).
abbrev F : Type := ZMod p

-- Since `p` is prime, `𝔽_p` is a finite field with exactly `p` elements.
example : Field F := inferInstance
example : Fintype.card F = p := ZMod.card p

end Octra.Field127
