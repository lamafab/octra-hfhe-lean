import Octra.HFHE.Octra
import Examples.Field7
import Mathlib.Tactic

-- ============================================================================
-- Examples: homomorphism over the public `Cipher`  (the C++-faithful object)
-- ============================================================================
--
-- `Examples/Homomorphism.lean` runs the bare ENGINE (`Encoding`).  This file lifts
-- everything to the full PUBLIC ciphertext the C++ ships (`Octra.lean`):
--
--     Cipher = Encoding (the decryptable core) + Layer[] provenance + one decoy/edge
--
-- with the invariant `aligned : #decoys = #edges`.  An adversary sees ALL of this; the
-- secret `Mask` is NOT part of it.  The Cipher-level ops (`taggedAdd`/`taggedScale`/
-- `taggedNeg`/`taggedSub`) mirror the engine ops while carrying the decoys/layers along
-- and re-establishing `aligned`; the σ-density and `recrypt` machinery live here too.
--
-- We fix the decoy index `ι = Fin 3` and build concrete ciphertexts over the shared 𝔽₇
-- rig.  The theme: the VALUE path is unchanged (decrypt of `.enc` still gives the
-- engine answer), while the decoys/density are the extra public structure that rides
-- along, permutation-invariant, and refreshable by recrypt without touching the value.

namespace Examples.Cipher

open Octra.HFHE Examples.Field7

-- ----------------------------------------------------------------------------
-- Two concrete public ciphertexts over `ι = Fin 3`
-- ----------------------------------------------------------------------------
--   `encrypt1` gives a one-edge encoding, so each Cipher carries exactly one decoy.

/-- Public ciphertext of `v = ⟨5,4⟩`: one masked edge, one BASE layer, one decoy. -/
def Cv : Cipher 2 (Fin 3) 𝔽₇ where
  enc     := encrypt1 g R 1 v
  layers  := [Layer.base 0]
  decoys  := [![1, 0, 1]]        -- a syndrome with count 2
  aligned := by native_decide

/-- Public ciphertext of `v₂ = ⟨1,2⟩`. -/
def Cw : Cipher 2 (Fin 3) 𝔽₇ where
  enc     := encrypt1 g R 3 v₂
  layers  := [Layer.base 0]
  decoys  := [![0, 1, 1]]
  aligned := by native_decide

-- ----------------------------------------------------------------------------
-- (1) The value path is unchanged: decrypt reads ONLY `.enc`
-- ----------------------------------------------------------------------------

example : ∀ j, decrypt g R Cv.enc j = v j := by native_decide

-- ----------------------------------------------------------------------------
-- (2) Cipher-level ADD: `taggedAdd` (C++ `ct_add`): concatenate encs AND decoys
-- ----------------------------------------------------------------------------
--   The value side sums (⟨5,4⟩ + ⟨1,2⟩ = ⟨6,6⟩); the decoys concatenate, and the
--   alignment invariant is preserved by construction.

example : ∀ j, decrypt g R (taggedAdd Cv Cw).enc j = ![6, 6] j := by native_decide
example : (taggedAdd Cv Cw).decoys = [![1, 0, 1], ![0, 1, 1]] := by native_decide
example : (taggedAdd Cv Cw).decoys.length = (taggedAdd Cv Cw).enc.edges.length :=
  (taggedAdd Cv Cw).aligned

-- ----------------------------------------------------------------------------
-- (3) Cipher-level SCALE / NEG / SUB: edge COUNT unchanged, decoys ride along
-- ----------------------------------------------------------------------------
--   `taggedScale` maps over edges, so the decoys/layers are untouched (`aligned`
--   is literally `c.aligned`).  Scale `v` by ⟨2,2⟩: ⟨5,4⟩·⟨2,2⟩ = ⟨10,8⟩ = ⟨3,1⟩.

example : ∀ j, decrypt g R (taggedScale (fun _ => 2) Cv).enc j = ![3, 1] j := by native_decide
example : (taggedScale (fun _ => 2) Cv).decoys = Cv.decoys := rfl

-- subtract: ⟨5,4⟩ − ⟨1,2⟩ = ⟨4,2⟩, decoys of `−Cw` are still `Cw`'s (scale by −1).
example : ∀ j, decrypt g R (taggedSub Cv Cw).enc j = ![4, 2] j := by native_decide

-- ----------------------------------------------------------------------------
-- (4) σ-density and the `ubk` permutation: a hardness/hiding statistic
-- ----------------------------------------------------------------------------
--   σ-density = (Σ count of decoys) / (#edges · |ι|).  `Cv` has one decoy ⟨1,0,1⟩
--   of count 2 over |ι| = 3, with one edge → 2/3.

example : sigmaDensity Cv = 2 / 3 := by native_decide

-- permuting the decoys by any `σ` (the public `ubk` step) preserves σ-density;
-- a permutation preserves each decoy's count and the edge count.
example (σ : Equiv.Perm (Fin 3)) : sigmaDensity (ubkApply σ Cv) = sigmaDensity Cv :=
  sigmaDensity_ubkApply σ Cv

-- ----------------------------------------------------------------------------
-- (5) Recrypt preserves the plaintext: for ANY schedule
-- ----------------------------------------------------------------------------
--   A refresh round injects a zero-encryption and permutes the decoys; both are
--   plaintext-neutral.  Build a zero ciphertext (encrypts ⟨0,0⟩) and inject it.

/-- A zero-encryption as a public ciphertext (its `.enc` decrypts to ⟨0,0⟩). -/
def Czero : Cipher 2 (Fin 3) 𝔽₇ where
  enc     := encrypt1 g R 0 (fun _ => 0)
  layers  := [Layer.base 0]
  decoys  := [![0, 0, 0]]
  aligned := by native_decide

-- one refresh round leaves the message untouched (`decrypt_recryptStep`).
example (σ : Equiv.Perm (Fin 3)) :
    ∀ j, decrypt g R (recryptStep σ Czero Cv).enc j = decrypt g R Cv.enc j :=
  fun j => decrypt_recryptStep g R σ Czero Cv j (by native_decide)

-- the full refresh loop, ANY pool of zero-encryptions, preserves the plaintext.
example (σ : Equiv.Perm (Fin 3)) :
    ∀ j, decrypt g R (recryptLoop σ [Czero, Czero] Cv).enc j = decrypt g R Cv.enc j := by
  have hz0 : ∀ j, decrypt g R Czero.enc j = 0 := by native_decide
  refine decrypt_recryptLoop g R σ [Czero, Czero] Cv ?_
  intro z hz j
  -- every pool member is `Czero`, which decrypts to 0
  have : z = Czero := by
    rcases List.mem_cons.1 hz with h | h
    · exact h
    · exact List.mem_singleton.1 h
  subst this; exact hz0 j

end Examples.Cipher
