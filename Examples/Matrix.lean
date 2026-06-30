import Octra.Hypergraph.Incidence
import Mathlib.Tactic

-- ============================================================================
-- Examples: the incidence MATRIX  (hypergraph → linear algebra, keystone #1)
-- ============================================================================
--
-- This is the bridge that turns the combinatorial `Hypergraph` into a matrix the
-- coding/LPN layer can treat as a PARITY CHECK (`Hypergraphs/Incidence.lean`).
-- The incidence matrix `M` of the worked `H` has one row per edge, one column
-- per vertex, with `M e v = 1 ⇔ v ∈ e`.
--
--   For the worked hypergraph of V = {0,1,2,3}, edges e₁ = {0,1,2}, e₂ = {1,3},
--   and e₃ = {0,3}:
--
--           v₀ v₁ v₂ v₃
--     e₁ [  1  1  1  0 ]
--     e₂ [  0  1  0  1 ]
--     e₃ [  1  0  0  1 ]
--
-- Read over 𝔽₂, the SYNDROME map `x ↦ M·x` sums the columns `x` selects (mod 2).
-- Below: the matrix entries, a concrete matrix–vector product run on real numbers,
-- the row-weight = edge-size fact, and the LINEARITY of the syndrome map (the two
-- structural properties that make this a legitimate parity check).
--
-- The same matrix, written abstractly as a linear code, is `Examples/LinearCoding.lean`.

namespace Examples.Matrix

open Hypergraph Matrix

/-- The shared worked hypergraph; we study its incidence matrix. -/
abbrev H : Hypergraph (Fin 4) := Hypergraph.example1

-- ----------------------------------------------------------------------------
-- (1) Matrix entries: `M e v = 1 ⇔ v ∈ e`
-- ----------------------------------------------------------------------------
--   Rows/columns are the subtypes `H.EdgeIdx`/`H.VertIdx`; we name two concrete
--   ones by exhibiting their membership proofs, then read entries off `M` over 𝔽₂.

-- Edges e₁, e₂, and e₃ as a row index.
def e₁ : H.EdgeIdx := ⟨{0, 1, 2}, by decide⟩
def e₂ : H.EdgeIdx := ⟨{1, 3}, by decide⟩
def e₃ : H.EdgeIdx := ⟨{0, 3}, by decide⟩

-- Vertex `v₂ = 2` and `v₃ = 3` as column indices.
def v₂ : H.VertIdx := ⟨2, by decide⟩
def v₃ : H.VertIdx := ⟨3, by decide⟩

-- TODO: The ring size does technically not effect the values -- it's always 0 or 1
example : H.incidence (ZMod 2) e₁ v₂ = 1 := by decide    -- 2 ∈ e₁
example : H.incidence (ZMod 2) e₁ v₃ = 0 := by decide    -- 3 ∉ e₁

-- ----------------------------------------------------------------------------
-- (2) The matrix–vector product `M·x`: run it on numbers
-- ----------------------------------------------------------------------------
--   Pick the column selection x = {v₀, v₁}. Summing the selected columns mod 2:
--     e₁: 1+1 = 0,  e₂: 0+1 = 1,  e₃: 1+0 = 1  →  syndrome ⟨0,1,1⟩, count 2.

/-- Select vertices `v₀` and `v₁` (a 0/1 column-selection vector over 𝔽₂). -/
def xsel : H.VertIdx → ZMod 2 :=
  fun w => if (w : Fin 4) = 0 ∨ (w : Fin 4) = 1 then 1 else 0

-- the syndrome map IS the matrix product `mulVec` (definitional, keystone #1).
example : H.syndrome (ZMod 2) xsel = (H.incidence (ZMod 2)).mulVec xsel := rfl

-- evaluate the syndrome edge-by-edge on the rows e₁, e₂, and e₃.
example : H.syndrome (ZMod 2) xsel e₁ = 0 := by native_decide
example : H.syndrome (ZMod 2) xsel e₂ = 1 := by native_decide
example : H.syndrome (ZMod 2) xsel e₃ = 1 := by native_decide

-- ----------------------------------------------------------------------------
-- (3) Row weight = edge size; k-uniform ⇒ constant row weight
-- ----------------------------------------------------------------------------
--   The number of 1s in row `e` is exactly `|e|`, so the parity check inherits the
--   hypergraph's geometry (a k-uniform hypergraph gives a k-regular check).

example (e : H.EdgeIdx) : ∑ v : H.VertIdx, H.incidence ℕ e v = (e : Finset (Fin 4)).card :=
  H.row_weight e

example : ∑ v : H.VertIdx, H.incidence ℕ e₁ v = 3 := by native_decide   -- |e₁| = 3

-- ----------------------------------------------------------------------------
-- (4) Linearity of the syndrome map: the defining parity-check property
-- ----------------------------------------------------------------------------
--   `M·(x+y) = M·x + M·y`  and  `M·(c•x) = c•(M·x)`: this is exactly what makes
--   the kernel a LINEAR code (the substrate for syndrome decoding / LPN).

example (x y : H.VertIdx → ZMod 2) :
    H.syndrome (ZMod 2) (x + y) = H.syndrome (ZMod 2) x + H.syndrome (ZMod 2) y :=
  H.syndrome_add (ZMod 2) x y

example (c : ZMod 2) (x : H.VertIdx → ZMod 2) :
    H.syndrome (ZMod 2) (c • x) = c • H.syndrome (ZMod 2) x :=
  H.syndrome_smul (ZMod 2) c x

end Examples.Matrix
