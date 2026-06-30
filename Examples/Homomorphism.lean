import Octra.HFHE.Gates
import Octra.HFHE.Noise
import Examples.Field7
import Mathlib.Tactic

-- ============================================================================
-- Examples: homomorphism over encrypt / decrypt  (the engine, keystones #2–3)
-- ============================================================================
--
-- Run the bare engine (`Encoding`/`Term`/`decrypt`/`homAdd`…/`homMul`) on real
-- numbers in 𝔽₇ (the shared rig `Examples/Field7.lean`).  This is the hypergraph-FREE
-- value path: carrier positions + secret mask, nothing else.  Decryption is an EXACT
-- identity over the field: the mask cancels `R·R⁻¹ = 1`, no rounding, no noise budget.
--
-- ENCRYPT `v = ⟨5,4⟩` as one masked edge at carrier position `idx = 1` (`encrypt1`).
-- The edge stores `w j = v j · (g^idx)⁻¹ · R 0 j`, so the wire carries ⟨1,3⟩, NOT the
-- plaintext.  DECRYPT divides the mask back out and re-applies the carrier, recovering
-- `v` exactly.  The homomorphisms then say: computing on ciphertexts computes on
-- plaintexts: `Dec(Enc a ⊞ Enc b) = a + b`, and likewise for −, ·, and the gates.
--
-- Each `native_decide` literally runs the scheme; each generic `example` shows the
-- numbers are no accident, falling straight out of `encrypt1_correct` + `decrypt_hom*`.

namespace Examples.Homomorphism

open Octra.HFHE Examples.Field7

/-- The ciphertext of `v`: a single masked edge at carrier position `1`. -/
def ct : Encoding 2 𝔽₇ := encrypt1 g R 1 v

-- ----------------------------------------------------------------------------
-- (1) ENCRYPT → DECRYPT round-trips EXACTLY  (`encrypt1_correct`, run)
-- ----------------------------------------------------------------------------

example : ∀ j, decrypt g R ct j = v j := by native_decide

-- What actually travels on the wire is the MASKED weight ⟨1,3⟩; the plaintext
-- ⟨5,4⟩ is nowhere stored (confidentiality rests on `R` being pseudorandom).
example : ct.edges.map (fun e => (e.w 0, e.w 1)) = [(1, 3)] := by native_decide

-- ----------------------------------------------------------------------------
-- (2) ADD: `Dec(Enc a ⊞ Enc b) = a + b`, slot-wise
-- ----------------------------------------------------------------------------
--   ⟨5,4⟩ + ⟨1,2⟩ = ⟨6,6⟩; the summands sit at DIFFERENT carrier positions (1, 3),
--   which `homAdd` (it just concatenates edge lists) does not care about.

example :
    ∀ j, decrypt g R (homAdd (encrypt1 g R 1 v) (encrypt1 g R 3 v₂)) j = ![6, 6] j := by
  native_decide

-- …and that is NO numerical accident: for ANY carrier positions it falls out of the
-- two keystones: `decrypt_homAdd` (homomorphism) then `encrypt1_correct` (round-trip).
example (i₁ i₂ : ℕ) :
    ∀ j, decrypt g R (homAdd (encrypt1 g R i₁ v) (encrypt1 g R i₂ v₂)) j = v j + v₂ j := by
  intro j
  rw [decrypt_homAdd, encrypt1_correct g R i₁ v j (by decide),
      encrypt1_correct g R i₂ v₂ j (by decide)]

-- ----------------------------------------------------------------------------
-- (3) SUBTRACT: `Dec(A ⊟ B) = a − b`:  ⟨5,4⟩ − ⟨1,2⟩ = ⟨4,2⟩
-- ----------------------------------------------------------------------------

example : ∀ j, decrypt g R (homSub (encrypt1 g R 1 v) (encrypt1 g R 3 v₂)) j = ![4, 2] j := by
  native_decide

example (i₁ i₂ : ℕ) :
    ∀ j, decrypt g R (homSub (encrypt1 g R i₁ v) (encrypt1 g R i₂ v₂)) j = v j - v₂ j := by
  intro j
  rw [decrypt_homSub, encrypt1_correct g R i₁ v j (by decide),
      encrypt1_correct g R i₂ v₂ j (by decide)]

-- ----------------------------------------------------------------------------
-- (4) MULTIPLY: `Dec(A ⊠ B) = a · b`:  ⟨5,4⟩ · ⟨1,2⟩ = ⟨5,1⟩
-- ----------------------------------------------------------------------------
--   The `gA·gB` cross term builds a PROD layer whose mask is the product of the
--   parents'; decryption cancels it exactly via `Mask.prod_eq`.

example : ∀ j, decrypt g R (homMul R.toLayerAlg (encrypt1 g R 1 v) (encrypt1 g R 2 v₂)) j = ![5, 1] j := by
  native_decide

example (i₁ i₂ : ℕ) :
    ∀ j, decrypt g R (homMul R.toLayerAlg (encrypt1 g R i₁ v) (encrypt1 g R i₂ v₂)) j = v j * v₂ j := by
  intro j
  rw [decrypt_homMul, encrypt1_correct g R i₁ v j (by decide),
      encrypt1_correct g R i₂ v₂ j (by decide)]

-- ----------------------------------------------------------------------------
-- (5) The full K-edge encryption also runs  (`encrypt`/`balance`)
-- ----------------------------------------------------------------------------
--   Two freely-chosen signal edges plus one SOLVED balancing edge (SPEC §3's "last
--   coeff solved"), telescoping to `v` with NO hypothesis.

def free : List (Signal 2 𝔽₇) :=
  [ { idx := 0, sign := true,  coef := ![1, 1] },
    { idx := 2, sign := false, coef := ![2, 3] } ]

example : ∀ j, decrypt g R (encrypt R (balance g free 1 v)) j = v j := by native_decide

example (i : ℕ) : ∀ j, decrypt g R (encrypt R (balance g free i v)) j = v j :=
  fun j => encrypt_balanced_correct g R free i v j (by decide)

-- ----------------------------------------------------------------------------
-- (6) GATES: boolean logic on ciphertexts (Phase 4, a corollary of #3)
-- ----------------------------------------------------------------------------
--   Bits are `0/1 ∈ 𝔽`; each gate is a polynomial computed by the homomorphisms.
--   Build a TRUE and a FALSE ciphertext and watch the truth tables come out.

def ctT : Encoding 2 𝔽₇ := encrypt1 g R 0 (fun _ => 1)   -- decrypts to bit `true`
def ctF : Encoding 2 𝔽₇ := encrypt1 g R 0 (fun _ => 0)   -- decrypts to bit `false`

example : ∀ j, decrypt g R (gAnd R.toLayerAlg ctT ctF) j = 0 := by native_decide   -- T ∧ F = F
example : ∀ j, decrypt g R (gOr  R.toLayerAlg ctT ctF) j = 1 := by native_decide   -- T ∨ F = T
example : ∀ j, decrypt g R (gXor R.toLayerAlg ctT ctF) j = 1 := by native_decide   -- T ⊕ F = T
example : ∀ j, decrypt g R (gNot             ctT)     j = 0 := by native_decide   -- ¬T   = F
example : ∀ j, decrypt g R (gNand R.toLayerAlg ctT ctT) j = 0 := by native_decide  -- T ↑ T = F

-- the generic boolean-correctness lemma, with the bit hypotheses spelled out.
example {ba bb : Bool} (a b : Encoding 2 𝔽₇)
    (ha : ∀ j, decrypt g R a j = bit ba) (hb : ∀ j, decrypt g R b j = bit bb) :
    ∀ j, decrypt g R (gAnd R.toLayerAlg a b) j = bit (ba && bb) :=
  fun j => gAnd_bit g R a b j (ha j) (hb j)

-- ----------------------------------------------------------------------------
-- (7) SIZE growth: the edge-count budget (`Noise.lean`), not a noise budget
-- ----------------------------------------------------------------------------
--   Decryption is exact, so nothing CORRECTNESS-related grows.  What grows is the
--   ciphertext SIZE: multiply is ~quadratic, `|a|·|b| + |a| + |b|`.

example (a b : Encoding 2 𝔽₇) (k : ℕ) (ha : numEdges a = k) (hb : numEdges b = k) :
    numEdges (homMul R.toLayerAlg a b) = k ^ 2 + 2 * k := by
  rw [numEdges_homMul, ha, hb]; ring

-- run it: `ct` has one edge, so squaring it gives 1·1 + 1 + 1 = 3 edges.
example : numEdges (homMul R.toLayerAlg ct ct) = 3 := by native_decide

end Examples.Homomorphism
