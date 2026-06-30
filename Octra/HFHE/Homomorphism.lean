import Octra.HFHE.Correctness
import Mathlib.Tactic

-- ============================================================================
-- HFHE: additive & multiplicative homomorphism
-- ============================================================================
--
-- Operating on ciphertexts operates on plaintexts: every operation here
-- preserves `decrypt` as an EXACT identity in 𝔽 (no noise budget).  ADD /
-- SCALE / NEG / SUB are linear and immediate; MUL is the deep one, where
-- PROD-layer masks cancel via `Mask.prod_eq`.
--
-- Runnable demos over 𝔽₇ live in `Examples/`.
--
-- C++: the `ct_add`/`ct_scale`/`ct_neg`/`ct_sub`/`ct_mul` family (`ops/arithmetic.hpp`).

namespace Octra.HFHE

-- `S` = slots, `F` = the field.
variable {S : ℕ} {F : Type*} [Field F]

/-- Homomorphic addition: concatenate the edge lists and add the constants `c0`.

    C++: `ct_add`. -/
def homAdd (a b : Encoding S F) : Encoding S F where
  edges := a.edges ++ b.edges
  c0    := fun j => a.c0 j + b.c0 j

/-- **Additive homomorphism**  Decrypting a sum of ciphertexts gives
    the sum of the plaintexts (exact, no hypotheses).

    C++: correctness of `ct_add`. -/
theorem decrypt_homAdd (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (homAdd a b) j = decrypt g R a j + decrypt g R b j := by
  simp only [decrypt, homAdd, List.map_append, List.sum_append]
  ring

-- ============================================================================
-- SCALE / NEG / SUB: the linear ops (exact, no hypotheses)
-- ============================================================================

/-- Scale every edge's weight per-slot by `s`.  Shared by `homScale` and (with
    `s` = the other factor's constant `c0`) by `homMul`. -/
def scaleEdges (s : Fin S → F) (es : List (Term S F)) : List (Term S F) :=
  es.map fun e => { e with w := fun j => s j * e.w j }

/-- Homomorphic scalar multiply: scale every edge weight and the constant `c0`
    by `s`. Decrypts to `s · v` (`decrypt_homScale`).

    C++: `ct_scale`. -/
def homScale (s : Fin S → F) (c : Encoding S F) : Encoding S F where
  edges := scaleEdges s c.edges
  c0    := fun j => s j * c.c0 j

/-- **Scalar homomorphism.**  Decrypting a per-slot scaling gives the scaled
    plaintext: `Dec(s · C) = s · Dec C`. -/
theorem decrypt_homScale (g : F) (R : Mask S F) (s : Fin S → F) (c : Encoding S F) (j : Fin S) :
    decrypt g R (homScale s c) j = s j * decrypt g R c j := by
  simp only [decrypt, homScale, scaleEdges, List.map_map, Function.comp_def, mul_add]
  congr 1
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro e _
  ring

/-- Homomorphic negation: the `s = −1` case of `homScale`.

    C++: `ct_neg`. -/
def homNeg (c : Encoding S F) : Encoding S F := homScale (fun _ => -1) c

/-- **Negation homomorphism**: `Dec(−C) = −Dec C`, the `s = −1` case of
    `decrypt_homScale`. -/
theorem decrypt_homNeg (g : F) (R : Mask S F) (c : Encoding S F) (j : Fin S) :
    decrypt g R (homNeg c) j = - decrypt g R c j := by
  simp only [homNeg, decrypt_homScale, neg_one_mul]

/-- Homomorphic subtraction: `homAdd a (homNeg b)`.

    C++: `ct_sub`. -/
def homSub (a b : Encoding S F) : Encoding S F := homAdd a (homNeg b)

/-- **Subtractive homomorphism**: `Dec(A − B) = Dec A − Dec B`, inherited from
    `homAdd`/`homNeg`. -/
theorem decrypt_homSub (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (homSub a b) j = decrypt g R a j - decrypt g R b j := by
  rw [homSub, decrypt_homAdd, decrypt_homNeg]
  ring

-- ============================================================================
-- MUL: the masked edge-sum `esum`, and the PROD-layer product expansion
-- ============================================================================
--
-- `decrypt = c0 + esum edges`, where `esum` is the masked edge-sum.  The lemmas
-- below give it the algebra MUL needs: additive over `++` (`esum_append`),
-- scales over `scaleEdges` (`esum_scaleEdges`), distributes over `flatMap`
-- (`esum_flatMap`), and turns the pairwise product-edge list into the PRODUCT
-- of the two edge-sums (`esum_prod`).

/-- The masked edge-sum: the non-`c0` part of `decrypt`, `Σ_e ±w·g^idx·(R layer)⁻¹`. -/
def esum (g : F) (R : Mask S F) (j : Fin S) (es : List (Term S F)) : F :=
  (es.map fun e => sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹).sum

/-- `decrypt` split into its constant and edge-sum parts. -/
theorem decrypt_eq (g : F) (R : Mask S F) (c : Encoding S F) (j : Fin S) :
    decrypt g R c j = c.c0 j + esum g R j c.edges := rfl

/-- `esum` is additive over edge-list concatenation. -/
@[simp] theorem esum_append (g : F) (R : Mask S F) (j : Fin S) (l₁ l₂ : List (Term S F)) :
    esum g R j (l₁ ++ l₂) = esum g R j l₁ + esum g R j l₂ := by
  simp only [esum, List.map_append, List.sum_append]

/-- `esum` pulls a per-slot scaling straight out. -/
@[simp] theorem esum_scaleEdges
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (s : Fin S → F)
    (es : List (Term S F))
  :
    esum g R j (scaleEdges s es) = s j * esum g R j es
  := by
    simp only [esum, scaleEdges, List.map_map, Function.comp_def]
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e _
    ring

-- TODO: Delete this?
/-- `esum` distributes over `flatMap` as a sum of per-element `esum`s. -/
@[simp] theorem esum_flatMap {α : Type*}
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (l : List α)
    (f : α → List (Term S F))
  :
    esum g R j (l.flatMap f) = (l.map fun x => esum g R j (f x)).sum
  := by
    induction l with
    | nil => simp [esum]
    | cons x xs ih => rw [List.flatMap_cons, esum_append, List.map_cons,
      List.sum_cons, ih]

-- ----------------------------------------------------------------------------
-- `wire`/`gsum` and the single-layer fold: substrate of the repack multiply
-- ----------------------------------------------------------------------------

/-- The on-the-wire value an edge contributes at slot `j`: `±w·g^idx`. This is
    the decrypt term WITHOUT the `(R layer)⁻¹` divisor, so it still carries the
    forward mask (`w = coef·R`).

    C++: the per-edge term `fold_edges`/`gsum_accumulator` sum, per layer. -/
def wire (g : F) (j : Fin S) (e : Term S F) : F := sgn e.sign * e.w j * g ^ e.idx

/-- `esum` rewritten through `wire`: `Σ_e wire·(R layer)⁻¹`. -/
theorem esum_eq_wire
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (es : List (Term S F))
  :
    esum g R j es = (es.map fun e => wire g j e * (R e.layer j)⁻¹).sum
  := by
    simp only [esum, wire]

/-- The masked wire-sum of an edge list. For a single layer `L` it is `R L · value`,
    still carrying the forward mask; decrypt strips it via `(R L)⁻¹` (`esum_single_layer`).

    C++: a layer's folded value `gA[L]` (before the mask-inverse). -/
def gsum (g : F) (j : Fin S) (es : List (Term S F)) : F := (es.map (wire g j)).sum

/-- A single-layer edge list folds to that layer's mask-inverse times its
    wire-sum: `esum = (R L)⁻¹ · gsum`.

    C++: the per-layer collapse `fold_edges` performs before a multiply. -/
theorem esum_single_layer
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (L : ℕ)
    (es : List (Term S F))
    (h : ∀ e ∈ es, e.layer = L)
  :
    esum g R j es = (R L j)⁻¹ * gsum g j es
  := by
    rw [esum_eq_wire, gsum, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro e he
    rw [h e he, mul_comm]

/-- A product of two list-sums as one flattened sum over all pairs (no `Finset`). -/
private theorem sum_mul_sum_flatMap {ι : Type*} (L₁ L₂ : List ι) (f h : ι → F) :
    (L₁.map f).sum * (L₂.map h).sum
      = (L₁.flatMap fun x => L₂.map fun y => f x * h y).sum := by
  induction L₁ with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons, List.sum_cons, add_mul, ih, List.flatMap_cons, List.sum_append,
        List.sum_map_mul_left]

/-- The product edge for a pair `(e, f)`: the signed weight product `w_e·w_f` at
    carrier `idx_e + idx_f` on the PROD layer `prod e.layer f.layer`
    (mask `R e.layer · R f.layer`). -/
private def prodEdge (alg : LayerAlg) (e f : Term S F) : Term S F where
  layer := alg.prod e.layer f.layer
  idx   := e.idx + f.idx
  sign  := true
  w     := fun j => (sgn e.sign * e.w j) * (sgn f.sign * f.w j)

/-- One product edge's decrypt term factors into its two parents' terms, via
    `(R_e·R_f)⁻¹ = R_e⁻¹·R_f⁻¹` and `g^(idx_e+idx_f) = g^idx_e·g^idx_f`. -/
private theorem prodEdge_term (g : F) (R : Mask S F) (j : Fin S) (e f : Term S F) :
    sgn (prodEdge R.toLayerAlg e f).sign * (prodEdge R.toLayerAlg e f).w j
        * g ^ (prodEdge R.toLayerAlg e f).idx * (R (prodEdge R.toLayerAlg e f).layer j)⁻¹
      = (sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹)
        * (sgn f.sign * f.w j * g ^ f.idx * (R f.layer j)⁻¹) := by
  have hp : R (R.prod e.layer f.layer) j = R e.layer j * R f.layer j :=
    R.prod_eq e.layer f.layer j
  simp only [prodEdge, sgn]
  rw [hp, pow_add, mul_inv_rev]
  ring

/-- The pairwise product-edge list decrypts to the PRODUCT of the two edge-sums. -/
@[simp] theorem esum_prod (g : F) (R : Mask S F) (j : Fin S) (A B : List (Term S F)) :
    esum g R j (A.flatMap fun e => B.map fun f => prodEdge R.toLayerAlg e f)
      = esum g R j A * esum g R j B := by
  rw [esum, List.map_flatMap]
  simp only [List.map_map, Function.comp_def, prodEdge_term]
  rw [esum, esum, sum_mul_sum_flatMap]

-- TODO: Revisit this.
-- NOTE: `homMul` is the layout-free VALUE model (decrypt is layout-independent), the clean
-- vehicle for the boolean gates (`Gates.lean`).  The DEPLOYED multiply (the C++ fold+repack
-- layout and its fixed-`width` (non-quadratic) edge count) is `Octra.taggedMul` (`Octra.lean`)
-- on the `Repack` abstraction; both decrypt identically since `R.prod_eq` (`R(prod a b) = R a ·
-- R b`, the C++ `layer_R_cached` PROD case) cancels the PROD-layer mask either way.  See
-- `docs/SPEC.md` §6 / `docs/basic.md` for the fold+repack details.

/-- Homomorphic multiply (the VALUE model): expand `(a0 + gA)(b0 + gB)`, resp.
    `c0 = a0·b0`, the cross terms `a0·gB`/`b0·gA` scale the other's edges, and
    the `gA·gB` term is one `prodEdge` per edge pair. Decrypts to the product
    (`decrypt_homMul`).

    C++: `ct_mul`, but the deployed fold+repack EDGE LAYOUT lives in
    `Octra.taggedMul`; here the layout is the simpler pairwise product
    (decrypt-equivalent). See the NOTE above. -/
def homMul (alg : LayerAlg) (a b : Encoding S F) : Encoding S F where
  edges := scaleEdges b.c0 a.edges ++ scaleEdges a.c0 b.edges
              ++ a.edges.flatMap fun e => b.edges.map fun f => prodEdge alg e f
  c0    := fun j => a.c0 j * b.c0 j

/-- **Multiplicative homomorphism (the other half of keystone #3).**  Decrypting a product of
    ciphertexts gives the product of the plaintexts, exact, no hypotheses: the
    `(a0 + gA)(b0 + gB)` expansion with the `gA·gB` term collapsing via `esum_prod` (the PROD
    masks cancel by the algebra of `R.prod_eq`, not by invertibility). -/
theorem decrypt_homMul (g : F) (R : Mask S F) (a b : Encoding S F) (j : Fin S) :
    decrypt g R (homMul R.toLayerAlg a b) j = decrypt g R a j * decrypt g R b j := by
  simp only [decrypt_eq, homMul, esum_append, esum_scaleEdges, esum_prod]
  ring

end Octra.HFHE
