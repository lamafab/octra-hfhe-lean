import Octra.HFHE.Homomorphism
import Mathlib.Tactic

-- ============================================================================
-- HFHE: boolean logic gates on encrypted data  (Phase 4)
-- ============================================================================
--
-- Gates on ciphertexts, as a DIRECT corollary of keystone #3.  Bits live as
-- `0`/`1 ∈ 𝔽`, and every gate is a POLYNOMIAL in its inputs: exactly what the
-- homomorphic operations compute:
--     NOT a = 1 − a         AND a b = a·b
--     OR  a b = a+b − a·b   XOR a b = a+b − 2·a·b
--
-- So each gate is a fixed composition of `homAdd`/`homSub`/`homScale`/`homMul`,
-- and correctness comes in two tiers:
--   * ARITHMETIC (unconditional): `decrypt (gate …) = <polynomial of decrypts>`,
--     straight from the `decrypt_hom*` lemmas;
--   * BOOLEAN (inputs are bits): combine the arithmetic tier with a 0/1 field
--     identity (`bit_*`, a 4-case truth table) to get the actual gate on `Bool`.
--
-- Everything is EXACT (no noise): Phase 4 is bookkeeping on top of keystone #3.
--
-- [!!] Cost: every NONLINEAR gate (AND/OR/XOR/NAND) contains a `homMul`, so it
-- incurs the ~quadratic edge growth of `Size.lean`; gate DEPTH is what drives
-- the `edge_budget`/`recrypt` story. `NOT` is linear (cheap).

namespace Octra.HFHE

-- `S` = slots, `F` = the field.
variable {S : ℕ} {F : Type*} [Field F]

/-- Encode a bit as a field element: `true ↦ 1`, `false ↦ 0`. -/
def bit (b : Bool) : F := if b then 1 else 0

/-- The trivial ciphertext of a constant `k` (no edges): decrypts to `k`.  Used to
    inject the constant `1` that `NOT` needs. -/
def encConst (k : Fin S → F) : Encoding S F where
  edges := []
  c0    := k

@[simp] theorem decrypt_encConst (g : F) (R : Mask S F) (k : Fin S → F) (j : Fin S) :
    decrypt g R (encConst k) j = k j := by
  simp [decrypt, encConst]

-- ----------------------------------------------------------------------------
-- The gates (as compositions of the homomorphic operations)
-- ----------------------------------------------------------------------------

/-- `AND a b` = `a·b`.  Like every nonlinear gate it consumes only the PUBLIC `LayerAlg`
    (via `homMul`), never the secret mask: see the `Mask`/`LayerAlg` split in `Defs.lean`. -/
def gAnd (alg : LayerAlg) (a b : Encoding S F) : Encoding S F := homMul alg a b

/-- `NOT a` = `1 − a` (subtract from the constant-`1` ciphertext).  Linear, no `homMul`,
    so it needs no `LayerAlg` at all. -/
def gNot (a : Encoding S F) : Encoding S F := homSub (encConst (fun _ => 1)) a

/-- `OR a b` = `a + b − a·b`. -/
def gOr (alg : LayerAlg) (a b : Encoding S F) : Encoding S F :=
  homSub (homAdd a b) (homMul alg a b)

/-- `XOR a b` = `a + b − 2·a·b`. -/
def gXor (alg : LayerAlg) (a b : Encoding S F) : Encoding S F :=
  homSub (homAdd a b) (homScale (fun _ => 2) (homMul alg a b))

/-- `NAND a b` = `NOT (AND a b)`: functionally complete on its own. -/
def gNand (alg : LayerAlg) (a b : Encoding S F) : Encoding S F := gNot (gAnd alg a b)

-- ----------------------------------------------------------------------------
-- Tier 1: arithmetic correctness (unconditional; from the homomorphism)
-- ----------------------------------------------------------------------------

theorem decrypt_gAnd (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (gAnd R.toLayerAlg a b) j = decrypt g R a j * decrypt g R b j :=
  decrypt_homMul g R a b j

theorem decrypt_gNot (g : F) (R : Mask S F) (a : Encoding S F) (j : Fin S) :
    decrypt g R (gNot a) j = 1 - decrypt g R a j := by
  simp only [gNot, decrypt_homSub, decrypt_encConst]

theorem decrypt_gOr (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (gOr R.toLayerAlg a b) j
      = decrypt g R a j + decrypt g R b j - decrypt g R a j * decrypt g R b j := by
  simp only [gOr, decrypt_homSub, decrypt_homAdd, decrypt_homMul]

theorem decrypt_gXor (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (gXor R.toLayerAlg a b) j
      = decrypt g R a j + decrypt g R b j - 2 * (decrypt g R a j * decrypt g R b j) := by
  simp only [gXor, decrypt_homSub, decrypt_homAdd, decrypt_homScale, decrypt_homMul]

theorem decrypt_gNand (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (gNand R.toLayerAlg a b) j = 1 - decrypt g R a j * decrypt g R b j := by
  rw [gNand, decrypt_gNot, decrypt_gAnd]

-- ----------------------------------------------------------------------------
-- The 0/1 field identities (a 4-case truth table)
-- ----------------------------------------------------------------------------

theorem bit_and (a b : Bool) : bit a * bit b = (bit (a && b) : F) := by
  cases a <;> cases b <;> simp [bit]

theorem bit_not (a : Bool) : 1 - bit a = (bit (!a) : F) := by
  cases a <;> simp [bit]

theorem bit_or (a b : Bool) : bit a + bit b - bit a * bit b = (bit (a || b) : F) := by
  cases a <;> cases b <;> simp [bit]

theorem bit_xor (a b : Bool) :
    bit a + bit b - 2 * (bit a * bit b) = (bit (xor a b) : F) := by
  cases a <;> cases b <;> simp [bit]
  ring

-- ----------------------------------------------------------------------------
-- Tier 2: boolean correctness (when the inputs decrypt to bits)
-- ----------------------------------------------------------------------------

theorem gAnd_bit (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) {ba bb : Bool}
    (ha : decrypt g R a j = bit ba) (hb : decrypt g R b j = bit bb) :
    decrypt g R (gAnd R.toLayerAlg a b) j = bit (ba && bb) := by
  rw [decrypt_gAnd, ha, hb, bit_and]

theorem gNot_bit (g : F) (R : Mask S F) (a : Encoding S F) (j : Fin S) {ba : Bool}
    (ha : decrypt g R a j = bit ba) :
    decrypt g R (gNot a) j = bit (!ba) := by
  rw [decrypt_gNot, ha, bit_not]

theorem gOr_bit (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) {ba bb : Bool}
    (ha : decrypt g R a j = bit ba) (hb : decrypt g R b j = bit bb) :
    decrypt g R (gOr R.toLayerAlg a b) j = bit (ba || bb) := by
  rw [decrypt_gOr, ha, hb, bit_or]

theorem gXor_bit (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) {ba bb : Bool}
    (ha : decrypt g R a j = bit ba) (hb : decrypt g R b j = bit bb) :
    decrypt g R (gXor R.toLayerAlg a b) j = bit (xor ba bb) := by
  rw [decrypt_gXor, ha, hb, bit_xor]

theorem gNand_bit (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) {ba bb : Bool}
    (ha : decrypt g R a j = bit ba) (hb : decrypt g R b j = bit bb) :
    decrypt g R (gNand R.toLayerAlg a b) j = bit (!(ba && bb)) := by
  rw [gNand, gNot_bit g R _ j (gAnd_bit g R a b j ha hb)]

-- `gNand` is functionally complete, so every boolean function is (in principle) an
-- encrypted circuit built from it.  Formalizing "evaluate an arbitrary boolean
-- circuit homomorphically, `decrypt (eval C cts) = C (cts.map decrypt)`" by
-- induction on a circuit datatype is the natural Phase-4 capstone (a follow-on).

end Octra.HFHE
