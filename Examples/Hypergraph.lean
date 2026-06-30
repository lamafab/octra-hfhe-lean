import Octra.Hypergraph.Basic
import Mathlib.Tactic

-- ============================================================================
-- Examples: Hypergraphs  (the combinatorial foundation)
-- ============================================================================
--
-- A hypergraph `H = (V, E)` generalises a graph: a hyperedge may join ANY number
-- of vertices, not just two.  This file exercises the `Hypergraph` structure of
-- `Hypergraphs/Basic.lean` on one small, fully concrete instance: the worked
-- example `Hypergraph.example1`:
--
--     V = {0, 1, 2, 3}    e₁ = {0,1,2}   e₂ = {1,3}   e₃ = {0,3}
--
-- Every claim below is closed by `decide`, so the file doubles as an executable
-- sanity check on the combinatorial measures (order, size, degree, adjacency,
-- neighbourhoods, rank, uniformity) and the one structural operation (`addEdge`).
-- This is layer-0 of the Octra stack; the incidence MATRIX of this same `H` is the
-- bridge to coding theory (see `Examples/Matrix.lean`).

namespace Examples.Hypergraphs

open Hypergraph

/-- The shared worked hypergraph (from `Hypergraphs/Basic.lean`). -/
abbrev H : Hypergraph (Fin 4) := Hypergraph.example1

def v₀ : Fin 4 := 0
def v₁ : Fin 4 := 1
def v₂ : Fin 4 := 2
def v₃ : Fin 4 := 3

-- ----------------------------------------------------------------------------
-- (1) Order and size: |V| and |E|
-- ----------------------------------------------------------------------------

example : H.order = 4 := by decide    -- four vertices
example : H.size = 3 := by decide     -- three hyperedges

-- ----------------------------------------------------------------------------
-- (2) Degree: how many edges each vertex sits in
-- ----------------------------------------------------------------------------
--   vertex 0 ∈ e₁,e₃; vertex 1 ∈ e₁,e₂; vertex 2 ∈ e₁; vertex 3 ∈ e₂,e₃

example : H.degree v₀ = 2 := by decide
example : H.degree v₁ = 2 := by decide
example : H.degree v₂ = 1 := by decide
example : H.degree v₃ = 2 := by decide

-- ----------------------------------------------------------------------------
-- (3) Adjacency and neighbourhoods
-- ----------------------------------------------------------------------------
--   Two vertices are adjacent when a SINGLE edge holds both.

example : H.Adjacent v₀ v₂ := by decide      -- both in e₁ = {0,1,2}
example : ¬ H.Adjacent v₂ v₃ := by decide    -- no edge contains both 2 and 3
example : H.neighbors v₀ = {v₁, v₂, v₃} := by decide   -- (e₁ ∪ e₃) \ {0}

-- ----------------------------------------------------------------------------
-- (4) Rank and uniformity: the "is it a graph?" question
-- ----------------------------------------------------------------------------
--   `rank` is the largest edge size; `IsUniform k` means EVERY edge has size k.
--   Here the sizes are 3, 2, 2, so rank 3, and NOT 2-uniform (i.e. not a graph).

example : H.rank = 3 := by decide
example : ¬ H.IsUniform 2 := by decide   -- e₁ has size 3, so it is not a graph

-- A genuinely 2-uniform hypergraph IS an ordinary graph: a single edge {0,1}.
def graphLike : Hypergraph (Fin 4) where
  vertices     := {0, 1}
  edges        := {{0, 1}}
  mem_vertices := by decide

example : graphLike.IsUniform 2 := by decide

-- ----------------------------------------------------------------------------
-- (5) An operation: `addEdge` respects the invariant E ⊆ 𝒫(V)
-- ----------------------------------------------------------------------------
--   Adding {2,3} (a subset of V) yields a 4-edge hypergraph; the proof obligation
--   `{2,3} ⊆ H.vertices` is discharged once, at the call site.

def Hplus : Hypergraph (Fin 4) := H.addEdge {2, 3} (by decide)

example : Hplus.size = 4 := by decide
example : Hplus.Adjacent 2 3 := by decide    -- the new edge makes 2,3 adjacent

end Examples.Hypergraphs
