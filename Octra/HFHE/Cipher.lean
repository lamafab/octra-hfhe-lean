import Octra.HFHE.Homomorphism
import Octra.HFHE.Decoy
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- Octra: the public ciphertext  (the C++ vocabulary base)
-- ============================================================================
--
-- The engine (`Defs`/`Correctness`/`Homomorphism`) speaks NEUTRALLY (`Encoding`,
-- `Term`, `decrypt`, `homAdd`/`homMul`) and proves the homomorphic properties there.
-- This module introduces the C++'s vocabulary and shape on top of it: the `Layer`
-- DAG-provenance, `Edge`, and the public `Cipher = Encoding + Layer[] + one decoy per
-- edge`, plus the LINEAR Cipher ops (`taggedAdd`/`taggedScale`/`taggedNeg`/`taggedSub`)
-- and `sigmaDensity`.
--
-- `Cipher` is the HINGE every Cipher-level module imports: the multiply lives in
-- `Repack.lean`, refresh in `Recrypt.lean`, compaction in `Merge.lean`, the hypergraph
-- decoys in `HyperDecoy.lean`, and `Octra.lean` is the facade that wraps them into a
-- `Scheme`.  Keeping `Cipher` here (not in `Octra.lean`) is what lets those components
-- each own their mechanism end-to-end without import cycles.
--
-- C++: `core/types.hpp` (`Cipher`, `Layer`, `Edge`); `ct_add`/`ct_scale`/`ct_neg`/`ct_sub`.

namespace Octra.HFHE

variable {S : ℕ} {ι : Type*} [Fintype ι] {F : Type*} [Field F]

-- ----------------------------------------------------------------------------
-- C++ vocabulary: views of the neutral engine types
-- ----------------------------------------------------------------------------

/-- A DAG-node tag, BASE or PROD: pure provenance the public `Cipher` carries and the
    commitment binds.  Decryption never reads it (it works off each edge's `layer : ℕ` index
    + the `Mask`), so it lives here, not in the engine `Encoding`.

    C++: `Layer` (the `L[]` array). -/
inductive Layer
  | base (seed : ℕ)
  /-- PROD node of two parents.  The engine never emits these (its layer→mask map is
      `Mask.prod`/`prod_eq` keyed by each edge's `layer : ℕ`); they are built only at the
      Cipher level by `taggedMul`, one per parent-layer pair, for the public DAG. -/
  | prod (pa pb : ℕ)
deriving Repr, DecidableEq

/-- An edge `±w·g^idx`, the engine's `Term`.  (The C++ edge also carries the decoy `s`; we
    keep that as a parallel list on `Cipher`, since decryption never reads it.)

    C++: `Edge`. -/
abbrev Edge (S : ℕ) (F : Type*) := Term S F

-- ----------------------------------------------------------------------------
-- The public ciphertext: a bare encoding + provenance + one decoy per edge
-- ----------------------------------------------------------------------------

/-- The public ciphertext an adversary sees: the decryptable core `enc`, the `Layer[]`
    provenance `layers`, and one decoy per edge.  The secret `Mask` is NOT here (see `Scheme`);
    decryption reads only `enc`, so `layers`/`decoys` are provenance and hardness the commitment
    binds but `decrypt` ignores.

    DECOY-AGNOSTIC invariant: every Cipher operation (here and in `Repack`/`Recrypt`/`Merge`)
    carries `decoys` as an OPAQUE, positionally-aligned (`aligned`) ride-along: concat
    (`taggedAdd`), pass-through (`taggedScale`), replace-with-fresh (`taggedMul` discards operand
    decoys for `pd`), or permute (`ubkApply`).  NONE decodes a decoy or tells real from ghost;
    that clean structure is known only to the producer at fresh encryption (`sigma_from_H`) and
    is never assumed to persist.  The sole content-reads anywhere are `sigmaDensity`'s aggregate
    popcount and `Merge`'s `nz` survival test.  To reason about VALUES alone (no decoys, no `ι`),
    drop to the engine layer: `homAdd`/`homMul` on `Encoding` (`Homomorphism.lean`); the
    `tagged*` ops are that algebra plus public-decoy transport.

    C++: `Cipher = {L, E, c0, …}`. -/
structure Cipher (S : ℕ) (ι : Type*) (F : Type*) where
  enc     : Encoding S F
  layers  : List Layer
  decoys  : List (Decoy ι)
  -- one decoy per edge
  aligned : decoys.length = enc.edges.length

/-- σ-density: the fraction of set bits across all edge decoys; `recrypt` keeps it in
    `[0.495, 0.505]`.

    C++: `sigma_density` (`Σ popcnt / (numEdges · |ι|)`). -/
def sigmaDensity (c : Cipher S ι F) : ℚ :=
  ((c.decoys.map decoyWeight).sum : ℚ) / ((c.decoys.length * Fintype.card ι : ℕ) : ℚ)

-- ----------------------------------------------------------------------------
-- The linear Cipher operations: lift the engine ops, carry `layers`/`decoys`,
-- re-establish `aligned`.  (The nonlinear multiply lives in `Repack.lean`.)
-- ----------------------------------------------------------------------------

/-- Cipher-level addition: append both encodings, layers, and decoys (alignment kept).  Used to
    inject a zero-encryption during refresh.

    C++: `ct_add`. -/
def taggedAdd (a b : Cipher S ι F) : Cipher S ι F where
  enc     := homAdd a.enc b.enc
  layers  := a.layers ++ b.layers
  decoys  := a.decoys ++ b.decoys
  aligned := by simp only [homAdd, List.length_append, a.aligned, b.aligned]

/-- Cipher-level scalar multiply: scale the encoding by `s`.  The edge count is unchanged, so
    decoys and layers ride along untouched and `aligned` is inherited.

    C++: `ct_scale`. -/
def taggedScale (s : Fin S → F) (c : Cipher S ι F) : Cipher S ι F where
  enc     := homScale s c.enc
  layers  := c.layers
  decoys  := c.decoys
  aligned := by simp only [homScale, scaleEdges, List.length_map]; exact c.aligned

/-- Cipher-level negation: the `s = −1` case of `taggedScale`.

    C++: `ct_neg`. -/
def taggedNeg (c : Cipher S ι F) : Cipher S ι F := taggedScale (fun _ => -1) c

/-- Cipher-level subtraction: `taggedAdd a (taggedNeg b)`.

    C++: `ct_sub`. -/
def taggedSub (a b : Cipher S ι F) : Cipher S ι F := taggedAdd a (taggedNeg b)

end Octra.HFHE
