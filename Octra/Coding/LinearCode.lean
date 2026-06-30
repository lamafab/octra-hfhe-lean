import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

-- ============================================================================
-- Linear codes, parity-check matrices, syndromes  (Phase 1b)
-- ============================================================================
--
-- A linear code is the kernel of a parity-check matrix `H`; the SYNDROME of a
-- word `x` is `σ = H·x`, and codewords are exactly the words of syndrome `0`.
-- The hardness Octra relies on is SYNDROME DECODING: given `H` and `σ`, recover
-- a low-Hamming-weight `e` with `H·e = σ`. Here `H` is the hypergraph
-- incidence matrix (`Coding/Syndrome.lean`); this file is the abstract layer.

namespace Octra.Coding

open Matrix

variable {m n : Type*} [Fintype n]

/-- The syndrome of `x` under parity-check matrix `H`: `σ = H·x`. -/
def syndrome {R : Type*} [Semiring R] (H : Matrix m n R) (x : n → R) : m → R :=
  H.mulVec x

/-- Hamming weight: the number of nonzero coordinates of `x`. -/
def hammingWeight {R : Type*} [Zero R] [DecidableEq R] (x : n → R) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ 0).card

/-- Hamming weight is SUBADDITIVE: the support of a sum sits inside the union of
    supports. This is the triangle inequality the decoding-radius bound needs. -/
theorem hammingWeight_add_le {R : Type*} [AddMonoid R] [DecidableEq R] [DecidableEq n]
    (x y : n → R)
  :
    hammingWeight (x + y) ≤ hammingWeight x + hammingWeight y
  := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.add_apply] at hi ⊢
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hi (by rw [h.1, h.2, add_zero])

theorem hammingWeight_neg {R : Type*} [AddGroup R] [DecidableEq R] (x : n → R) :
    hammingWeight (-x) = hammingWeight x
  := by
    unfold hammingWeight; congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply,
    neg_ne_zero]

theorem hammingWeight_sub_le {R : Type*} [AddGroup R] [DecidableEq R] [DecidableEq n]
    (x y : n → R)
  :
    hammingWeight (x - y) ≤ hammingWeight x + hammingWeight y
  := by
    rw [sub_eq_add_neg]
    exact le_trans (hammingWeight_add_le x (-y)) (by rw [hammingWeight_neg])

/-- `e` solves the syndrome-decoding instance `(H, σ, w)` when it has the right
    syndrome and weight at most `w`. Finding such `e` is the hard problem. Octra
    instantiates this on the hypergraph incidence matrix (`IsHypergraphDecodingSolution`,
    `Coding/Syndrome.lean`); the weight bound `w` is the decoy's sparse-selection weight
    (`xColWt`, `HFHE/HyperDecoy.lean`). -/
def IsSyndromeDecodingSolution {R : Type*} [Semiring R] [DecidableEq R]
    (H : Matrix m n R) (σ : m → R) (w : ℕ) (e : n → R) : Prop
  :=
    syndrome H e = σ ∧ hammingWeight e ≤ w

-- ============================================================================
-- The code itself: kernel, cosets, dimension, and the decoding radius
-- ============================================================================
--
-- The CODE `code H = ker (x ↦ H·x)` is the words `H` kills. Decoding follows
-- from one fact: two words share a syndrome iff they differ by a codeword, so
-- the preimages of a fixed `σ` form a COSET `e + code H`: the ambiguity a
-- decoder must resolve. The MINIMUM DISTANCE `d` bounds it: if every nonzero
-- codeword has weight `≥ 2t+1`, a low-weight preimage is unique (decoding radius
-- `t = ⌊(d−1)/2⌋`). Octra picks `H` so the unique low-weight preimage EXISTS
-- (geometry, proven here) yet is infeasible to FIND (cited axiom).

section Code

variable {R : Type*} [Field R] (H : Matrix m n R)

/-- The CODE of `H`: the kernel of the parity-check map `x ↦ H·x`, exactly the words of
    syndrome `0` (`mem_code_iff`).  A `Submodule`, so it carries a dimension. -/
def code : Submodule R (n → R) := LinearMap.ker H.mulVecLin

theorem mem_code_iff (x : n → R) : x ∈ code H ↔ syndrome H x = 0 := by
  simp only [code, LinearMap.mem_ker, Matrix.mulVecLin_apply, syndrome]

/-- **The coset structure of decoding.**  Two words have the SAME syndrome iff
    they differ by a codeword; so the preimages of any σ are a coset `e + code H`.
    This is the source of decoding ambiguity: every nonzero codeword gives a
    second preimage of every σ. -/
theorem syndrome_eq_iff_sub_mem_code (a b : n → R) :
    syndrome H a = syndrome H b ↔ a - b ∈ code H
  := by
    rw [mem_code_iff, syndrome, syndrome, syndrome, Matrix.mulVec_sub,
    sub_eq_zero]

/-- **Unique decoding within radius `t` (the `t = ⌊(d−1)/2⌋` bound).**  If every
    nonzero codeword has weight `≥ 2t+1`, two weight-`≤ t` words with the same
    syndrome are equal: their difference is a codeword of weight `≤ 2t`, hence
    zero. -/
theorem eq_of_syndrome_eq_of_weight_le [DecidableEq R] [DecidableEq n] {t : ℕ}
    {e₁ e₂ : n → R}
    (hmin : ∀ c ∈ code H, c ≠ 0 → 2 * t + 1 ≤ hammingWeight c)
    (hsyn : syndrome H e₁ = syndrome H e₂)
    (h₁ : hammingWeight e₁ ≤ t)
    (h₂ : hammingWeight e₂ ≤ t)
  :
    e₁ = e₂
  := by
    have hc : e₁ - e₂ ∈ code H := (syndrome_eq_iff_sub_mem_code H e₁ e₂).mp hsyn
    by_contra hne
    have hsub : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr hne
    have hle : hammingWeight (e₁ - e₂) ≤ 2 * t :=
      le_trans (hammingWeight_sub_le e₁ e₂) (by omega)
    have := hmin _ hc hsub
    omega

end Code

end Octra.Coding
