import Octra.HFHE.Cipher
import Mathlib.Tactic

-- ============================================================================
-- HFHE: edge compaction (`reduction::merge`): the ONE place the decoy is read
-- ============================================================================
--
-- Homomorphic operations just concatenate edge lists, so a ciphertext's edge
-- count keeps growing. Compaction (the C++ `reduction::merge`) reins it in: it
-- collapses edges that sit at the same position `(layer, idx, sign)`, adding
-- their weights, then drops the edges that have become "empty". This is the
-- one place in the scheme where the decoy is read.
--
-- The subtlety is what counts as "empty". A collapsed edge is kept iff its
-- weight is nonzero in some slot, OR its decoy still has a set bit (decoys are
-- combined by XOR (addition over 𝔽₂) as edges merge). So an edge whose value
-- has cancelled to zero can still survive, on the strength of its decoy alone:
-- a "ghost" edge (`w = 0`, hence invisible to decryption).
--
-- That is the decoy's real job. Without it, compaction would keep exactly the
-- nonzero-value positions, leaking which positions the plaintext actually uses
-- (its support). With it (and a decoy density near ½) a pseudorandom half of
-- the cancelled positions survive too, hiding the value-driven ones among them.
-- Telling the two apart is itself syndrome decoding.
--
-- This file models the decoy-critical core: the survival test and the additive
-- collapse, on tagged edges (an engine `Term` paired with its `Decoy`), and
-- proves:
--
--   (a) compaction never changes the decrypted value (every dropped edge has
--       zero weight); and
--   (b) the surviving set genuinely depends on the decoys (a zero-value edge
--       survives iff its decoy is nonzero).
--
-- The surrounding array bookkeeping (grouping edges by position) is
-- decryption-trivial and is not formalized here.
--
-- C++: `reduction::merge` (`ops/encrypt.hpp`), on the hot path of
-- `synth`/`recrypt`/`guard_budget`.

namespace Octra.HFHE

variable {S : ℕ} {ι : Type*} {F : Type*} [Field F]

/-- The decoy-aware survival test of `reduction::merge` (C++ `nz(w, s)`): a
    (collapsed) edge is KEPT iff its weight is nonzero in some slot, OR its
    decoy has a set bit.  Equivalently it is DROPPED only when BOTH the weight
    and the decoy are zero. -/
def Survives (e : Term S F) (d : Decoy ι) : Prop :=
  (∃ j, e.w j ≠ 0) ∨ d ≠ 0

instance [Fintype ι] [DecidableEq F] (e : Term S F) (d : Decoy ι)
  :
    Decidable (Survives e d)
  := by
    unfold Survives; infer_instance

/-- **The decoy controls survival of a ghost edge.**  For an edge whose value is
    zero in every slot, survival is decided *entirely* by the decoy: it is kept
    iff the decoy is nonzero.  This is the formal "the surviving set depends on
    the decoys": flip the decoy from `0` to nonzero and a zero-value position
    appears/disappears. -/
theorem survives_zeroWeight (e : Term S F) (hw : ∀ j, e.w j = 0) (d : Decoy ι)
  :
    Survives e d ↔ d ≠ 0
  := by
    unfold Survives
    constructor
    · rintro (⟨j, hj⟩ | hd)
      · exact absurd (hw j) hj
      · exact hd
    · intro hd; exact Or.inr hd

-- ----------------------------------------------------------------------------
-- The collapse step: sum weights, XOR (add) decoys (decode-faithful)
-- ----------------------------------------------------------------------------

/-- One decrypt summand for edge `e`: the body of `decrypt`'s sum,
    `±w·g^idx·R(layer)⁻¹`. -/
def eterm (g : F) (R : Mask S F) (j : Fin S) (e : Term S F) : F :=
  sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹

theorem decrypt_eq_sum_eterm
    (g : F)
    (R : Mask S F)
    (c : Encoding S F)
    (j : Fin S)
  :
    decrypt g R c j = c.c0 j + (c.edges.map (eterm g R j)).sum
  := rfl

/-- Collapse two tagged edges sharing a position into one: ADD the weights, XOR
    (equals add over 𝔽₂) the decoys: the inner step of `reduction::merge`. -/
def combine (p1 p2 : Term S F × Decoy ι) : Term S F × Decoy ι :=
  ({ p1.1 with w := fun j => p1.1.w j + p2.1.w j }, p1.2 + p2.2)

/-- **The collapse is decode-faithful**: when two edges share `(layer, idx,
    sign)`, the summed-weight edge contributes exactly what the two did, so
    merging never changes the decrypted value (and the decoy XOR rides along,
    invisible to decrypt). -/
theorem eterm_combine
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (p1 p2 : Term S F × Decoy ι)
    (hl : p1.1.layer = p2.1.layer)
    (hi : p1.1.idx = p2.1.idx)
    (hs : p1.1.sign = p2.1.sign)
  :
    eterm g R j (combine p1 p2).1 = eterm g R j p1.1 + eterm g R j p2.1
  := by
    simp only [combine, eterm, hl.symm, hi.symm, hs.symm]
    ring

-- ----------------------------------------------------------------------------
-- The prune step: keep only the survivors; preserves the decrypted value
-- ----------------------------------------------------------------------------

/-- Compaction's prune (the `nz` filter of `reduction::merge`): drop the tagged edges
    that fail the survival test (zero weight AND zero decoy). -/
def prune [Fintype ι] [DecidableEq F] (L : List (Term S F × Decoy ι)) :
    List (Term S F × Decoy ι) :=
  L.filter fun p => decide (Survives p.1 p.2)

private theorem sum_filter_drop {α : Type*} (L : List α) (p : α → Bool) (f : α → F)
    (h : ∀ a ∈ L, p a = false → f a = 0) :
    ((L.filter p).map f).sum = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have iht : ∀ b ∈ t, p b = false → f b = 0 := fun b hb => h b (List.mem_cons_of_mem a hb)
    by_cases hpa : p a = true
    · simp only [List.filter_cons, hpa, if_true, List.map_cons, List.sum_cons, ih iht]
    · rw [Bool.not_eq_true] at hpa
      simp only [List.filter_cons, hpa, Bool.false_eq_true, if_false, List.map_cons,
        List.sum_cons, h a List.mem_cons_self hpa, zero_add]
      exact ih iht

/-- **Compaction preserves the decrypted value.**  Pruning the dead/ghost edges does
    not change `decrypt`: every dropped edge has zero weight, so it contributes `0`
    to the decrypt sum: exactly the "ghost edges add 0" fact.  The decoys (which
    decide *which* edges are dropped) never enter the decrypted value. -/
theorem decrypt_prune [Fintype ι] [DecidableEq F] (g : F) (R : Mask S F)
    (L : List (Term S F × Decoy ι)) (c0 : Fin S → F) (j : Fin S) :
    decrypt g R ⟨(prune L).map Prod.fst, c0⟩ j = decrypt g R ⟨L.map Prod.fst, c0⟩ j := by
  rw [decrypt_eq_sum_eterm, decrypt_eq_sum_eterm]
  congr 1
  simp only [List.map_map]
  apply sum_filter_drop
  intro pr _ hfalse
  have hns : ¬ Survives pr.1 pr.2 := of_decide_eq_false hfalse
  simp only [Survives, not_or, not_exists, ne_eq, not_not] at hns
  simp only [Function.comp_apply, eterm, hns.1 j, mul_zero, zero_mul]

/-- **(b) made concrete.**  The same zero-weight edge is KEPT with a nonzero decoy and
    DROPPED with the zero decoy, so the post-compaction edge set is not a function of
    the weights alone; the decoys move positions in and out. -/
example (e : Term S F) (hw : ∀ j, e.w j = 0) (d : Decoy ι) (hd : d ≠ 0) :
    Survives e d ∧ ¬ Survives e (0 : Decoy ι) := by
  refine ⟨(survives_zeroWeight e hw d).mpr hd, ?_⟩
  rw [survives_zeroWeight e hw (0 : Decoy ι)]
  simp

end Octra.HFHE
