import Octra.HFHE.Homomorphism
import Mathlib.Tactic

-- TODO: This file is outdated => update!
-- ============================================================================
-- HFHE: evaluation growth: the edge-count budget  (Phase 3)
-- ============================================================================
--
-- NOT a decryption-noise budget.  Decryption here is EXACT (Correctness.lean) and
-- the scheme's "noise" tuples cancel identically, so, unlike LWE/BGV, there is no
-- β bound that correctness depends on.  What DOES grow under homomorphic
-- evaluation is the ciphertext SIZE: the C++ caps it with `edge_budget` and reins
-- it in with `guard_budget` / `compact` / `recrypt` (SPEC §6–7).
--
-- This file makes that growth precise.  `numEdges` counts edges; the laws below
-- are exact (`=`, no hypotheses) and quantify the costs:
--   * add / sub   : edges ADD;
--   * scale / neg : edges UNCHANGED (a per-edge `map`);
--   * mul         : in the VALUE model (`homMul`, used by the gates) the pairwise
--                   `gA·gB` expansion grows ~QUADRATICALLY, `|a|·|b| + |a| + |b|`.
--                   The DEPLOYED multiply no longer does this: it FOLDS + RE-PACKS, so a
--                   product is a fixed `width` edges per layer-pair, not `|a|·|b|`; see
--                   `Octra.numEdges_taggedMul` (`Octra.lean`).  That repack is exactly the
--                   C++ fix for the quadratic blow-up.
--
-- The OTHER half of SPEC's budget, σ-density (the decoy-selector density that
-- `recrypt` refreshes toward ½, SPEC §7), lives on each edge's decoy `s`, which
-- the decryption-relevant `Term` model deliberately omits.  Modelling it would
-- mean re-introducing the decoy and wiring in the hypergraph `H`; deferred.

namespace Octra.HFHE

variable {S : ℕ} {F : Type*} [Field F]

/-- The size measure homomorphic evaluation grows: the edge count. -/
def numEdges (c : Encoding S F) : ℕ := c.edges.length

/-- **Add** concatenates edge lists, so counts add. -/
@[simp] theorem numEdges_homAdd (a b : Encoding S F) :
    numEdges (homAdd a b) = numEdges a + numEdges b := by
  simp only [numEdges, homAdd, List.length_append]

/-- **Scale** is a per-edge `map`, so the count is unchanged (free, size-wise). -/
@[simp] theorem numEdges_homScale (s : Fin S → F) (c : Encoding S F) :
    numEdges (homScale s c) = numEdges c := by
  simp only [numEdges, homScale, scaleEdges, List.length_map]

/-- **Negation** = scale by `−1`: count unchanged. -/
@[simp] theorem numEdges_homNeg (c : Encoding S F) :
    numEdges (homNeg c) = numEdges c := by
  rw [homNeg, numEdges_homScale]

/-- **Subtraction** = `add ∘ neg`: counts add. -/
@[simp] theorem numEdges_homSub (a b : Encoding S F) :
    numEdges (homSub a b) = numEdges a + numEdges b := by
  rw [homSub, numEdges_homAdd, numEdges_homNeg]

/-- **Multiply (VALUE model)** is the quadratic one: the two scaled cross terms contribute
    `|a| + |b|` edges and the pairwise `gA·gB` term contributes `|a|·|b|`.  The DEPLOYED
    multiply repacks to a fixed `width` instead (`Octra.numEdges_taggedMul`). -/
@[simp] theorem numEdges_homMul (alg : LayerAlg) (a b : Encoding S F) :
    numEdges (homMul alg a b) = numEdges a + numEdges b + numEdges a * numEdges b := by
  simp only [numEdges, homMul, List.length_append, scaleEdges, List.length_map,
             List.length_flatMap, List.map_const', List.sum_const_nat]

end Octra.HFHE
