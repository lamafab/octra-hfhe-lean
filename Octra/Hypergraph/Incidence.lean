import Octra.Hypergraph.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

-- ============================================================================
-- The incidence matrix: the bridge from hypergraphs to linear codes
-- ============================================================================
--
-- PURPOSE.  This file is KEYSTONE #1 of the Octra roadmap (see octra.md): it turns a
-- combinatorial `Hypergraph` into linear algebra over a ring R, so the rest of the
-- stack (coding/LPN, the decoy syndromes) can treat a hypergraph as a PARITY-CHECK
-- MATRIX.  It defines that matrix (`incidence`), the SYNDROME map it induces
-- (`syndrome`, `x ↦ M·x`), and proves the two structural facts the crypto layer
-- relies on: the syndrome map is LINEAR, and a k-uniform hypergraph gives a constant
-- row weight k (a k-regular parity-check). The matrix M has one row per hyperedge,
-- one column per vertex; the entry `M e v` is 1 when vertex v lies in edge
-- e, and 0 otherwise.
--
--   For the worked hypergraph of V = {0,1,2,3}, edges e₁ = {0,1,2}, e₂ = {1,3}, and
--   e₃ = {0,3}: that is the 3-edge-row × 4-vertex-col table:
--
--           v₀ v₁ v₂ v₃
--     e₁ [  1  1  1  0 ]    -- 0,1,2 ∈ e₁, 3 ∉ e₁
--     e₂ [  0  1  0  1 ]    -- 1,3 ∈ e₂
--     e₃ [  1  0  0  1 ]    -- 0,3 ∈ e₃
--
-- Read over 𝔽₂, `x ↦ M.mulVec x` sums the columns selected by `x` (mod 2): this is
-- the SYNDROME the coding/LPN layer builds on, and the map Octra pushes its decoys
-- through (`HyperDecoy.decoyOf`).
--
-- The two facts that make this the right bridge:
--   * the syndrome map is LINEAR (`syndrome_add`, `syndrome_smul`);
--   * a k-uniform hypergraph gives a CONSTANT row weight k  (`row_weight_uniform`)
--     i.e. a k-regular parity-check, exactly the "k-uniform" code Octra wants.

namespace Hypergraph

open Matrix

variable {V : Type*} [DecidableEq V] (H : Hypergraph V)

-- The index types: the edges and vertices of H as Fintypes (they are Finsets,
-- so their subtypes are finite).

/-- Rows of the incidence matrix: the hyperedges of `H`. -/
abbrev EdgeIdx := {e // e ∈ H.edges}

/-- Columns of the incidence matrix: the vertices of `H`. -/
abbrev VertIdx := {v // v ∈ H.vertices}

/-- The incidence matrix of `H` over `R`: the entry `M e v` is `1` when vertex `v`
    lies in edge `e`, and `0` otherwise (rows = edges, columns = vertices). -/
def incidence (R : Type*) [Zero R] [One R] :
    Matrix H.EdgeIdx H.VertIdx R :=
  fun e v => if (v : V) ∈ (e : Finset V) then 1 else 0

@[simp] theorem incidence_apply (R : Type*) [Zero R] [One R]
    (e : H.EdgeIdx) (v : H.VertIdx) :
    H.incidence R e v = if (v : V) ∈ (e : Finset V) then 1 else 0 := rfl

-- ============================================================================
-- The syndrome map and its linearity (KEYSTONE #1)
-- ============================================================================

/-- The syndrome map `x ↦ M·x` of the incidence/parity-check matrix. -/
def syndrome (R : Type*) [Semiring R] (x : H.VertIdx → R) : H.EdgeIdx → R :=
  (H.incidence R).mulVec x

/-- The syndrome `M·x`, written as a linear combination of the columns of `M`: what
    "multiply the matrix by the vector" means concretely. Scale each column of `M` by
    the matching coordinate of `x`, then add the scaled columns:

        M·x  =  Σ_v  x_v · (column v of M).

    Over 𝔽₂ every coordinate `x_v` is 0 or 1, so this keeps exactly the columns where
    `x_v = 1` and drops the rest: the syndrome is just the sum of the columns `x`
    selects. -/
theorem syndrome_eq_sum_cols (R : Type*) [CommSemiring R] (x : H.VertIdx → R) :
    H.syndrome R x = ∑ v, x v • (fun e => H.incidence R e v) := by
  ext e
  simp only [syndrome, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun v _ => mul_comm _ _

/-- The syndrome map is additive: the defining property of a parity check. -/
theorem syndrome_add (R : Type*) [Semiring R] (x y : H.VertIdx → R) :
    H.syndrome R (x + y) = H.syndrome R x + H.syndrome R y := by
  simp only [syndrome, Matrix.mulVec_add]

/-- The syndrome map commutes with scaling (over a commutative ring). -/
theorem syndrome_smul (R : Type*) [CommSemiring R] (c : R) (x : H.VertIdx → R) :
    H.syndrome R (c • x) = c • H.syndrome R x := by
  ext e
  simp only [syndrome, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

-- ============================================================================
-- Row weight = edge size; k-uniform ⇒ constant row weight k
-- ============================================================================

/-- The weight of row `e` (number of incident vertices) is `|e|`. -/
theorem row_weight (e : H.EdgeIdx) :
    ∑ v : H.VertIdx, H.incidence ℕ e v = (e : Finset V).card := by
  have he : (e : Finset V) ⊆ H.vertices := H.mem_vertices _ e.2
  simp only [incidence_apply]
  rw [Finset.sum_coe_sort H.vertices (fun v => if v ∈ (e : Finset V) then (1 : ℕ) else 0),
    Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr he]

/-- For a k-uniform hypergraph every row of the incidence matrix has weight `k`:
    the parity-check is `k`-regular.  This constant row weight is the hardness-relevant
    structure: average-case syndrome decoding (`IsHypergraphDecodingSolution`) is
    conjectured hard precisely for RANDOM k-uniform hypergraphs at the MIPT density
    threshold (Shabanov, Raigorodskii et al.; see the `HyperDecoy.lean` header). -/
theorem row_weight_uniform {k : ℕ} (hk : H.IsUniform k) (e : H.EdgeIdx) :
    ∑ v : H.VertIdx, H.incidence ℕ e v = k := by
  rw [H.row_weight e, hk _ e.2]

end Hypergraph
