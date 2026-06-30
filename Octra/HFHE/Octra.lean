import Octra.HFHE.Cipher
import Octra.HFHE.Repack
import Octra.HFHE.Recrypt
import Octra.HFHE.Merge
import Mathlib.Tactic

-- ============================================================================
-- Octra, the facade: the public/secret boundary, and the pipeline end to end
-- ============================================================================
--
-- This module wraps the engine and the Cipher-level components into a `Scheme` and
-- tells the whole story in one place.  It re-exports every component, so a downstream
-- file just `import`s this one.
--
-- THE PIPELINE, end to end (file each step lives in):
--
--   plaintext v
--     │  encrypt  : balance v into signals, mask with R     (engine: Correctness.lean)
--     │            attach one `H`-syndrome decoy per edge    (HyperDecoy.lean: withDecoys)
--     ▼
--   Cipher  = enc (masked value) + layers (DAG provenance) + decoys   (Cipher.lean)
--     │  homomorphic compute on the PUBLIC ciphertext:
--     │    taggedAdd / taggedScale / taggedSub      linear, decoys ride along   (Cipher.lean)
--     │    taggedMul                                fold + repack, fresh decoys (Repack.lean)
--     │  maintenance (decode-neutral):
--     │    recryptLoop   inject Enc(0) + ubk-permute, refresh σ-density → ½      (Recrypt.lean)
--     │    merge/prune   collapse edges; the ONE decoy READ (ghost survival)    (Merge.lean)
--     ▼
--   decrypt  = c0 + Σ ±w·g^idx·R(layer)⁻¹   : EXACT field identity, reads only `enc`
--
-- The split that runs through it all: the VALUE channel is key-gated (mask `R`,
-- reproducible, the secret key); the DECOY channel is public + one-way (built at encrypt,
-- never decoded).  `decrypt` reads only the value; everything decoy is decode-neutral.
--
-- C++: mirrors `pvac_hfhe_cpp` (`core/types.hpp`, `ops/arithmetic.hpp`, `ops/recrypt.hpp`).

namespace Octra.HFHE

variable {S : ℕ} {ι : Type*} [Fintype ι] {F : Type*} [Field F]

-- ----------------------------------------------------------------------------
-- The public / secret boundary
-- ----------------------------------------------------------------------------

/-- Public key / parameters: the carrier base `g` and the public re-randomizing permutation
    `ubk` of the decoy index (used by `recrypt`).  The hypergraph `H`, the other public datum,
    enters only in `HyperDecoy.lean`, where the decoy index is fixed to `H.EdgeIdx` (it
    cannot be named here, where `ι` is an abstract `Fintype`).

    C++: `pk` (`g`, `ubk`). -/
structure PubKey (ι : Type*) (F : Type*) where
  /-- carrier base `g`; the positional constants are `g ^ idx` -/
  g : F
  /-- public permutation of the decoy index, applied during refresh (`ubkApply`) -/
  ubk : Equiv.Perm ι

/-- Secret key: the per-layer `Mask` (the LPN/PRF-derived blinding; abstract here).

    C++: `sk`. -/
structure SecKey (S : ℕ) (F : Type*) [Field F] where
  mask : Mask S F

/-- A full instance with the public/secret boundary EXPLICIT: an adversary sees `pk` and the
    public ciphertext `ct`; only the holder of `sk` can decrypt.  The structure the IND-CPA
    reduction (keystone #4) will be stated over. -/
structure Scheme (S : ℕ) (ι : Type*) (F : Type*) [Field F] where
  pk : PubKey ι F         -- public
  ct : Cipher S ι F       -- public
  sk : SecKey S F         -- SECRET

/-- Decryption of an instance: strip the secret mask off the public ciphertext. -/
def Scheme.plaintext (s : Scheme S ι F) (j : Fin S) : F :=
  decrypt s.pk.g s.sk.mask s.ct.enc j

/-- Refresh the public ciphertext using the public permutation `pk.ubk` and a pool `zs` of
    zero-encryptions; the keys are untouched. -/
def Scheme.recrypt (s : Scheme S ι F) (zs : List (Cipher S ι F)) : Scheme S ι F :=
  { s with ct := recryptLoop s.pk.ubk zs s.ct }

/-- Recrypt preserves the plaintext at the `Scheme` level: a corollary of
    `decrypt_recryptLoop`: as long as the pool really is zero-encryptions under this instance's
    own key, refreshing changes nothing the holder of `sk` sees. -/
theorem Scheme.plaintext_recrypt (s : Scheme S ι F) (zs : List (Cipher S ι F))
    (hz : ∀ z ∈ zs, ∀ j, decrypt s.pk.g s.sk.mask z.enc j = 0) (j : Fin S)
  :
    (s.recrypt zs).plaintext j = s.plaintext j := by
  simp only [Scheme.recrypt, Scheme.plaintext]
  exact decrypt_recryptLoop s.pk.g s.sk.mask s.pk.ubk zs s.ct hz j

end Octra.HFHE
