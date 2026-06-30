import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

-- ============================================================================
-- Hypergraphs
-- ============================================================================
--
-- An ordinary graph connects vertices in *pairs*: every edge is a set of
-- exactly two vertices. A hypergraph drops that restriction: an edge (now
-- called a *hyperedge*) may join any number of vertices at once.
--
-- Formally a (finite) hypergraph is a pair
--
--     H = (V, E)    with   E ⊆ 𝒫(V)
--
-- where V is a finite set of *vertices* and E is a family of *hyperedges*,
-- each hyperedge being a subset of V. An ordinary graph is exactly the
-- special case where every edge has size 2.
--
-- This file fixes a simple structure and defines the basic operations:
-- incidence, degree, adjacency, neighbourhoods, rank, and uniformity.

-- ============================================================================
-- Section 1: The structure
-- ============================================================================

-- A finite hypergraph on a vertex type `V`: a finite set of vertices
-- together with a finite family of hyperedges, each contained in the vertex
-- set.
structure Hypergraph (V : Type*) [DecidableEq V] where
  vertices     : Finset V
  edges        : Finset (Finset V)
  -- Define the condition `E ⊆ 𝒫(V)`.
  mem_vertices : ∀ e ∈ edges, e ⊆ vertices

namespace Hypergraph

variable {V : Type*} [DecidableEq V] (H : Hypergraph V)

-- ============================================================================
-- Section 2: Basic measures
-- ============================================================================

-- The *order* of a hypergraph is its number of vertices, |V|.
def order : ℕ := H.vertices.card

-- The *size* of a hypergraph is its number of hyperedges, |E|.
def size : ℕ := H.edges.card

-- ============================================================================
-- Section 3: Incidence and degree
-- ============================================================================
--
-- A vertex v is *incident* to an edge e when v ∈ e. The whole combinatorial
-- content of a hypergraph is captured by this incidence relation, which is
-- often written as a 0/1 *incidence matrix* M with rows indexed by vertices,
-- columns by edges, and M[v, e] = 1 ⇔ v ∈ e.
-- TODO: Clarify this; or remove it.

-- `v` is *incident* to `e` when `e` is an edge of `H` containing `v`.
def Incident (v : V) (e : Finset V) : Prop := e ∈ H.edges ∧ v ∈ e

-- The *degree* of a vertex is the number of edges incident to it.
def degree (v : V) : ℕ := (H.edges.filter (fun e => v ∈ e)).card

-- ============================================================================
-- Section 4: Active and inactive vertices
-- ============================================================================
--
-- Read a hyperedge `e` as the set of vertices it *activates*: vertex `v` is
-- ACTIVE in `e` when `v ∈ e`. Relative to `H`, the INACTIVE vertices are the
-- vertices of `H` that `e` omits: the complement `H.vertices \ e`. This
-- inactive set is the bar `\overline{·}` used by the gates in LogicGates.lean.
-- (Activity needs no `H`; inactivity does, since "not in `e`" is only
-- meaningful relative to a fixed vertex set.)

-- `v` is *active* in `e` when it belongs to `e`.
def Active (e : Finset V) (v : V) : Prop := v ∈ e

-- The hyperedge of vertices of `H` active in `e`: those of `H.vertices` lying in `e`.
def active (e : Finset V) : Finset V := H.vertices ∩ e

@[simp] theorem mem_active {e : Finset V} {v : V} :
    v ∈ H.active e ↔ v ∈ H.vertices ∧ Active e v := by
  simp only [active, Active, Finset.mem_inter]

-- The active set is always a hyperedge of H (a subset of its vertices).
theorem active_subset (e : Finset V) : H.active e ⊆ H.vertices :=
  Finset.inter_subset_left

-- `v` is *inactive* in `e` (relative to `H`): a vertex of `H` not in `e`.
def Inactive (e : Finset V) (v : V) : Prop := v ∈ H.vertices ∧ v ∉ e

-- The hyperedge of vertices of `H` inactive in `e`: the complement H.vertices \ e.
def inactive (e : Finset V) : Finset V := H.vertices \ e

@[simp] theorem mem_inactive {e : Finset V} {v : V} :
    v ∈ H.inactive e ↔ H.Inactive e v := by
  simp only [inactive, Inactive, Finset.mem_sdiff]

-- The inactive set is always a hyperedge of H (a subset of its vertices).
theorem inactive_subset (e : Finset V) : H.inactive e ⊆ H.vertices :=
  Finset.sdiff_subset

-- ============================================================================
-- Section 5: Adjacency and neighbourhoods
-- ============================================================================

-- Two vertices are *adjacent* when some single edge contains them both.
-- (`abbrev`, so it stays reducible and `decide` can see the underlying `∃`.)
abbrev Adjacent (u v : V) : Prop := ∃ e ∈ H.edges, u ∈ e ∧ v ∈ e

-- The *neighbourhood* of `v`: all vertices sharing an edge with `v`,
-- excluding `v` itself.
def neighbors (v : V) : Finset V :=
  (H.edges.filter (fun e => v ∈ e)).biUnion id \ {v}

-- ============================================================================
-- Section 6: Rank and uniformity
-- ============================================================================
--
-- A graph is the case "every edge has size 2". The natural generalisation is
-- a *k-uniform* hypergraph, in which every edge has size k. The *rank* is the
-- size of the largest edge.

-- The *rank* of a hypergraph: the size of its largest edge (0 if empty).
def rank : ℕ := H.edges.sup Finset.card

-- `H` is *k-uniform* when every edge has exactly `k` vertices. A `2`-uniform
-- hypergraph is precisely an ordinary (loopless) graph. (`abbrev`, so it stays
-- reducible and `decide` can see the underlying `∀`.)
abbrev IsUniform (k : ℕ) : Prop := ∀ e ∈ H.edges, e.card = k

-- ============================================================================
-- Section 7: An operation: adding an edge
-- ============================================================================
--
-- Operations on hypergraphs must respect the defining invariant E ⊆ 𝒫(V).
-- Adding a hyperedge is only allowed if the new edge lies inside the vertex
-- set; the proof obligation is discharged once, here, rather than at every
-- use site.

-- Insert a new hyperedge `e` (which must lie inside the vertex set).
def addEdge (e : Finset V) (he : e ⊆ H.vertices) : Hypergraph V where
  vertices     := H.vertices
  edges        := insert e H.edges
  mem_vertices := by
    intro f hf
    rcases Finset.mem_insert.1 hf with h | h
    · subst h; exact he
    · exact H.mem_vertices f h

-- TODO: This should not be here
-- ============================================================================
-- Section 8: A worked example
-- ============================================================================
--
-- Take V = {0, 1, 2, 3} with three hyperedges:
--
--     e₁ = {0, 1, 2}    (a "triangle" hyperedge of size 3)
--     e₂ = {1, 3}       (an ordinary graph-like edge of size 2)
--     e₃ = {0, 3}       (another edge of size 2)
--
-- Note e₁ shows why this is a hypergraph and not a graph: it joins three
-- vertices at once.

def example1 : Hypergraph (Fin 4) where
  vertices     := {0, 1, 2, 3}
  edges        := {{0, 1, 2}, {1, 3}, {0, 3}}
  mem_vertices := by decide

-- Order and size
example : example1.order = 4 := by decide
example : example1.size = 3 := by decide

-- Degrees: vertex 0 lies in e₁ and e₃, vertex 2 only in e₁
example : example1.degree 0 = 2 := by decide
example : example1.degree 1 = 2 := by decide
example : example1.degree 2 = 1 := by decide
example : example1.degree 3 = 2 := by decide

-- Adjacency: 0 and 2 share e₁; but 2 and 3 share no edge
example : example1.Adjacent 0 2 := by decide
example : ¬ example1.Adjacent 2 3 := by decide

-- Neighbourhood of 0: vertices from e₁ ∪ e₃ minus 0 itself = {1, 2, 3}
example : example1.neighbors 0 = {1, 2, 3} := by decide

-- Rank is the largest edge size, here |e₁| = 3
example : example1.rank = 3 := by decide

-- It is not uniform (edges have sizes 3, 2, 2)
example : ¬ example1.IsUniform 2 := by decide

-- ============================================================================
-- Section 9: The dual (in words)
-- ============================================================================
--
-- Every hypergraph H = (V, E) has a *dual* H* obtained by swapping the roles
-- of vertices and edges: the vertices of H* are the edges of H, and for each
-- vertex v of H there is an edge of H* collecting all original edges incident
-- to v (the *star* of v). Transposing the incidence matrix turns H into H*,
-- and (H*)* recovers H. Duality exchanges "degree" and "edge size", which is
-- the hypergraph analogue of point/line duality in projective geometry.

end Hypergraph
