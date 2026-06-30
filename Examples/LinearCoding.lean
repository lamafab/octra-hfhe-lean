import Octra.Coding.Syndrome
import Mathlib.Tactic

-- ============================================================================
-- Examples: linear codes, syndromes, syndrome decoding  (the hardness substrate)
-- ============================================================================
--
-- A linear code is the kernel of a parity-check matrix `H`; the SYNDROME of a word
-- `x` is `σ = H·x`, and `x` is a codeword iff `σ = 0`.  The hard problem Octra leans
-- on is SYNDROME DECODING: given `H` and `σ`, find a LOW-WEIGHT `e` with `H·e = σ`.
--
-- TODO: Clarify that "the gap is literally "any preimage (easy linear algebra) vs the
-- sparse one (NP-hard)."
--
-- We run the abstract layer (`Coding/LinearCode.lean`) on the SAME 3×4 matrix as the
-- hypergraph incidence example. Its whole point is the decoding GAP: a ONE-WAY map with
-- no trapdoor. Over 𝔽₂:
--
--   FORWARD:  σ = H·x  (easy):  x keeps the columns where xⱼ = 1, then XORs them per row.
--
--               x₀ x₁ x₂ x₃         x = (1,1,0,0) keeps x₀, x₁
--         c₀ [  1  1  1  0 ]        1 ⊕ 1 = 0   ┐
--     H = c₁ [  0  1  0  1 ]        0 ⊕ 1 = 1   ├►  σ = (0,1,1)
--         c₂ [  1  0  0  1 ]        1 ⊕ 0 = 1   ┘
--
--   BACKWARD:  σ ↦ x  (hard):  the SAME σ has TWO preimages, so "invert" is ill-posed:
--
--         x = (1,1,0,0)   weight 2  ─┐  both solve  H·? = σ
--         e = (0,0,0,1)   weight 1  ─┘  ◄ the sparsest  (column 3 of H is σ itself)
--
--   Finding that sparsest preimage is the search: trivial at 3×4, ~2ⁿ at scale; no
--   factoring, no discrete log, just sparse-preimage search.  THAT one-way gap is the
--   hardness Octra leans on.
--
-- Same problem, HYPERGRAPH view: each matrix row cᵢ is just edge eᵢ written
-- out as a 0/1 row (so row c₀ = (1,1,1,0) IS e₁ = {0,1,2}). Reading that row
-- against x then counts (mod 2) how many of the SELECTED vertices {v₀, v₁} land
-- in eᵢ: that count is σᵢ.
--
--                      v₀ v₁   count hits
--   e₁ = {0, 1, 2}     ✓  ✓    2 (mod 2) = 0   ┐
--   e₂ = {1, 3}        ·  ✓    1 (mod 2) = 1   ├►  σ = (0, 1, 1)
--   e₃ = {0, 3}        ✓  ·    1 (mod 2) = 1   ┘
--
-- So decoding = "recover x from the per-edge parities", and `Hypergraph.syndrome` IS
-- `Coding.syndrome` of the incidence matrix: combinatorics ↔ coding theory.

namespace Examples.LinearCoding

open Octra.Coding Matrix

/-- The parity check, written out as an honest matrix over 𝔽₂. -/
def Hmat : Matrix (Fin 3) (Fin 4) (ZMod 2) :=
  !![
    1, 1, 1, 0;
    0, 1, 0, 1;
    1, 0, 0, 1
  ]

/-- The column selection x = {x₀, x₁}. -/
def x : Fin 4 → ZMod 2 := ![1, 1, 0, 0]
/-- Its syndrome σ = H·x = (0,1,1). -/
def σ : Fin 3 → ZMod 2 := ![0, 1, 1]
/-- The SPARSE decoding e = {x₃}: column 3 of H is itself (0,1,1) = σ. -/
def e : Fin 4 → ZMod 2 := ![0, 0, 0, 1]

-- ----------------------------------------------------------------------------
-- (1) The syndrome: apply the check, mod 2
-- ----------------------------------------------------------------------------

-- The weight-2 `x` AND the weight-1 `e` hit the SAME σ:
example : syndrome Hmat x = σ := by decide
example : syndrome Hmat e = σ := by decide

-- x is NOT a codeword (its syndrome is nonzero); the zero word IS (syndrome 0).
example : syndrome Hmat x ≠ 0 := by decide
example : syndrome Hmat (0 : Fin 4 → ZMod 2) = 0 := by decide

-- ----------------------------------------------------------------------------
-- (2) Hamming weight: count the set coordinates
-- ----------------------------------------------------------------------------

example : hammingWeight x = 2 := by decide    -- bits x₀,x₁ set
example : hammingWeight σ = 2 := by decide    -- checks c₁,c₂ fire
example : hammingWeight e = 1 := by decide    -- the sparse decoding: one bit

-- TODO: Change this section, it feels out out place in its current form.
-- ----------------------------------------------------------------------------
-- (2½) Codewords: the kernel, and why σ has two preimages
-- ----------------------------------------------------------------------------
--   Codewords are the words H kills (syndrome 0): the CODE itself (`code Hmat`).  The
--   abstract layer's `syndrome_eq_iff_sub_mem_code` says two words share a syndrome IFF
--   they differ by a codeword, so σ's preimages form a COSET = (one solution) + (any
--   codeword).  That coset structure IS the decoding gap; here we make it fully concrete.

-- x and e differ by exactly the (only) nonzero codeword of this H:
example : x + e = ![1, 1, 0, 1] := by decide
example : syndrome Hmat (x + e) = 0 := by decide    -- ...which is a codeword (syndrome 0)

-- The CODE is exactly {0000, 1101}: H has rank 3 over 4 columns, so by `finrank_code` the
-- kernel is `4 − 3 = 1`-dimensional, i.e. 2¹ = 2 codewords.  Both facts, checked:
example : ∀ y : Fin 4 → ZMod 2, syndrome Hmat y = 0 ↔ y = 0 ∨ y = ![1, 1, 0, 1] := by decide
example : Fintype.card {y : Fin 4 → ZMod 2 // syndrome Hmat y = 0} = 2 := by decide

-- The nonzero codeword's weight is the code's MINIMUM DISTANCE, d = 3.  Equivalently:
-- EVERY nonzero codeword has weight ≥ 3 (the hypothesis the error-correction bound needs).
example : ∀ c : Fin 4 → ZMod 2, syndrome Hmat c = 0 → c ≠ 0 → 3 ≤ hammingWeight c := by decide

-- d = 3 ≥ 2·1+1, so the abstract `eq_of_syndrome_eq_of_weight_le` (the t = ⌊(d−1)/2⌋ = 1
-- bound) fires: ANY two weight-≤1 words with the same syndrome are equal.  So `e` (weight 1)
-- is THE UNIQUE sparsest preimage of σ: the decoder's answer is well-defined.
example {e₁ e₂ : Fin 4 → ZMod 2} (h : syndrome Hmat e₁ = syndrome Hmat e₂)
    (h₁ : hammingWeight e₁ ≤ 1) (h₂ : hammingWeight e₂ ≤ 1) : e₁ = e₂ := by
  have hw : ∀ c : Fin 4 → ZMod 2, syndrome Hmat c = 0 → c ≠ 0 → 2 * 1 + 1 ≤ hammingWeight c :=
    by decide
  exact eq_of_syndrome_eq_of_weight_le (t := 1) Hmat
    (fun c hc hne => hw c ((mem_code_iff Hmat c).mp hc) hne) h h₁ h₂

-- ----------------------------------------------------------------------------
-- (3) Syndrome decoding, and the SPARSITY gap
-- ----------------------------------------------------------------------------
--   Both x and e decode σ, but only e meets the weight-1 budget. Decoding asks
--   for the SPARSEST explanation, so the weight-1 instance is the "right" answer.

-- The sparse `e` solves the weight-1 instance...
example : IsSyndromeDecodingSolution Hmat σ 1 e := by
  unfold IsSyndromeDecodingSolution; decide

-- ...but the heavier `x` does NOT (weight 2 > 1)...
example : ¬ IsSyndromeDecodingSolution Hmat σ 1 x := by
  unfold IsSyndromeDecodingSolution; decide

-- ...though `x` is fine once the budget is loosened to 2.
example : IsSyndromeDecodingSolution Hmat σ 2 x := by
  unfold IsSyndromeDecodingSolution; decide

-- ----------------------------------------------------------------------------
-- (4) Back to the hypergraph: its syndrome map IS a linear code (keystone #1)
-- ----------------------------------------------------------------------------
--   `Coding/Syndrome.lean`: the combinatorial hypergraph syndrome is LITERALLY the
--   parity-check syndrome of the incidence matrix, so syndrome-decoding a hypergraph
--   is a syndrome-decoding instance verbatim.

open Hypergraph

example (x : (Hypergraph.example1).VertIdx → ZMod 2) :
    (Hypergraph.example1).syndrome (ZMod 2) x
      = syndrome ((Hypergraph.example1).incidence (ZMod 2)) x :=
  hypergraph_syndrome_eq Hypergraph.example1 (ZMod 2) x

-- the hypergraph-decoding problem unfolds to a plain syndrome-decoding instance.
example (σ : (Hypergraph.example1).EdgeIdx → ZMod 2) (w : ℕ)
    (e : (Hypergraph.example1).VertIdx → ZMod 2) :
    IsHypergraphDecodingSolution Hypergraph.example1 (ZMod 2) σ w e
      = IsSyndromeDecodingSolution ((Hypergraph.example1).incidence (ZMod 2)) σ w e :=
  rfl

end Examples.LinearCoding
