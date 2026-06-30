import Octra.Hypergraph.Incidence
import Octra.Coding.LinearCode
import Mathlib.Tactic

-- ============================================================================
-- The hypergraph syndrome map = a linear code  (Phase 2)
-- ============================================================================
--
-- This file is the hinge of the HARDNESS track: it says the combinatorial
-- syndrome map of a hypergraph (Hypergraphs/Incidence.lean) is LITERALLY the
-- parity-check syndrome of a linear code (Coding/LinearCode.lean).  So
-- "decode this hypergraph syndrome" = "solve a syndrome-decoding instance",
-- and the LPN hardness assumption (Coding/LPN.lean) applies verbatim.

namespace Octra.Coding

open Hypergraph

variable {V : Type*} [DecidableEq V] (H : Hypergraph V) (R : Type*) [Semiring R]

/-- The hypergraph syndrome map is exactly the linear-code syndrome of the
    incidence matrix used as a parity-check matrix.  (Keystone #1, in coding
    language.) -/
theorem hypergraph_syndrome_eq (x : H.VertIdx → R) :
    H.syndrome R x = Coding.syndrome (H.incidence R) x := rfl

/-- The hypergraph-decoding problem: recover a low-weight `e` on the vertices
    explaining an observed edge-syndrome `σ`.  This is the concrete instance
    whose hardness the random k-uniform hypergraph (Phase 1) is chosen to
    guarantee: k-uniformity makes the parity check `k`-regular
    (`row_weight_uniform`), the regime the MIPT-threshold hardness results
    target.  The weight bound `w` is the sparse-error rate (`lpnNoise`, τ = 1/8,
    `Coding/LPN.lean`). -/
def IsHypergraphDecodingSolution [DecidableEq R]
    (σ : H.EdgeIdx → R) (w : ℕ) (e : H.VertIdx → R) : Prop :=
  IsSyndromeDecodingSolution (H.incidence R) σ w e

/-- **Hypergraph decoding is well-posed within radius `t`.**  If the incidence
    code has minimum distance `≥ 2t+1`, any two weight-`≤ t` selections
    explaining the same edge-syndrome `σ` coincide.  This is
    `eq_of_syndrome_eq_of_weight_le` specialized to the incidence parity-check:
    the uniqueness that makes "the selection behind `σ`" a well-defined target
    (the geometry half of the hardness story; cf. `Coding/LPN.lean`). -/
theorem hypergraph_decoding_unique {S : Type*} [Field S] [DecidableEq S]
    (H : Hypergraph V) {t : ℕ} {σ : H.EdgeIdx → S}
    (hmin : ∀ c ∈ code (H.incidence S), c ≠ 0 → 2 * t + 1 ≤ hammingWeight c)
    {e₁ e₂ : H.VertIdx → S}
    (h₁ : IsHypergraphDecodingSolution H S σ t e₁)
    (h₂ : IsHypergraphDecodingSolution H S σ t e₂)
  :
    e₁ = e₂
  :=
    eq_of_syndrome_eq_of_weight_le (H.incidence S) hmin (h₁.1.trans h₂.1.symm)
      h₁.2 h₂.2

end Octra.Coding
