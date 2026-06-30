import Octra.HFHE.Defs
import Mathlib.Tactic

-- ============================================================================
-- Examples: the shared 𝔽₇ test rig  (small enough to `native_decide`)
-- ============================================================================
--
-- The real scheme lives in 𝔽_p, p = 2^127-1 (`Crypto/Field127.lean`); for runnable
-- examples we shrink to 𝔽₇ so every number is checkable by `decide`/`native_decide`.
-- This file fixes the common setup the HFHE example files share: a public carrier
-- base `g`, a SECRET per-layer `Mask R`, and two plaintext slot-vectors; so the
-- engine (`Examples/Homomorphism.lean`), the public ciphertext (`Examples/Cipher.lean`),
-- and the full scheme (`Examples/Octra.lean`) all run on one consistent rig.
--
-- Useful inverses in 𝔽₇:  3⁻¹ = 5,  2⁻¹ = 4,  4⁻¹ = 2.

namespace Examples.Field7

open Octra.HFHE

notation "𝔽₇" => ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Public carrier base. -/
def g : 𝔽₇ := 3

/-- A secret mask, made layer-MULTIPLICATIVE so it also supports `homMul`: layer `l`
    has mask `⟨2,4⟩^(l+1)`, so layer 0 is `⟨2,4⟩` and a PROD layer `prod a b = a+b+1`
    gets `⟨2,4⟩^(a+b+2) = (layer a)·(layer b)`: exactly `Mask.prod_eq`. -/
def R : Mask 2 𝔽₇ where
  toFun l j := (![2, 4] j) ^ (l + 1)
  nonzero := by intro _ j; fin_cases j <;> exact pow_ne_zero _ (by decide)
  prod a b := a + b + 1
  prod_eq := by
    intro a b j
    show (![2, 4] j) ^ (a + b + 1 + 1) = (![2, 4] j) ^ (a + 1) * (![2, 4] j) ^ (b + 1)
    rw [← pow_add]; congr 1; omega

/-- A plaintext slot-vector. -/
def v  : Fin 2 → 𝔽₇ := ![5, 4]
/-- A second plaintext. -/
def v₂ : Fin 2 → 𝔽₇ := ![1, 2]

end Examples.Field7
