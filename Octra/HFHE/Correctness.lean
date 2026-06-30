import Octra.HFHE.Defs
import Mathlib.Tactic

-- ============================================================================
-- HFHE: decryption correctness  (Phase 3, KEYSTONE #2)
-- ============================================================================
--
-- This file proves decryption is correct, and that it is EXACT: `decrypt (encrypt v) = v`
-- as an equality in the field 𝔽, with no noise term and no modular congruence (unlike
-- Paillier or LWE/BGV, where correctness holds only up to noise or a hard-to-invert kernel).
--
-- The proof is built in layers:
--   * `decrypt_strip` is the core algebra: every edge's weight is its intended coefficient
--     times its layer's secret mask (`w = coef · R`), so decryption, which divides by `R`,
--     cancels the mask edge by edge. It needs only that the mask is nonzero.
--   * `encrypt_correct` applies that to the real K-edge signal split: once the masks cancel,
--     correctness reduces to the signal contributions telescoping to `v` (the hypothesis
--     `Σ contrib = v`), a transparent condition on the chosen signals.
--   * `encrypt_balanced_correct` discharges even that hypothesis: appending one solved
--     balancing edge makes the telescoping hold by construction, so correctness is
--     unconditional (only `g ≠ 0`; mask invertibility is carried by the `Mask` type itself).
--   * `encrypt1_correct` is the K=1 corollary.

namespace Octra.HFHE

-- Throughout: `S` = number of SIMD slots (a plaintext / slot-vector is `Fin S → F`);
-- `F` = the field 𝔽 (intended 𝔽_p, p = 2^127-1; see Crypto/Field127.lean).
variable {S : ℕ} {F : Type*} [Field F]

/-- Mask cancellation through the edge sum.  If every edge's weight is the
    intended coefficient times its layer's mask, and every mask is nonzero, then
    decryption strips the masks exactly. -/
theorem decrypt_strip
    (g : F)                         -- carrier base; edge `e` weighs `g ^ e.idx`
    (R : Mask S F)                  -- secret mask: `R l j` = mask of layer `l` at slot `j`
    (c : Encoding S F)              -- the ciphertext (DAG of layers + edges + `c0`)
    (j : Fin S)                     -- the slot being decrypted
    (coef : Term S F → (Fin S → F)) -- intended unmasked coefficient: `coef e j`
    (hw : ∀ e ∈ c.edges, e.w j = coef e j * R e.layer j)  -- every weight = coefficient · mask
  :
    decrypt g R c j
      = c.c0 j + (c.edges.map fun e => sgn e.sign * coef e j * g ^ e.idx).sum
  := by
    unfold decrypt
    have hmap :
        (c.edges.map fun e => sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹)
          = (c.edges.map fun e => sgn e.sign * coef e j * g ^ e.idx) := by
      apply List.map_congr_left
      intro e he
      have hne : R e.layer j ≠ 0 := R.nonzero e.layer j -- the mask's bundled invariant
      rw [hw e he]
      field_simp
    rw [hmap]

-- ============================================================================
-- Encryption correctness: the engine, applied (no deferred kernel)
-- ============================================================================

/-- **Exact decryption correctness**: the K-edge signal split decrypts
    to `v` exactly when the (unmasked) signal contributions telescope to `v`:
    `decrypt_strip` cancels every layer mask (each edge carries `w = coef·R 0`),
    leaving `Σ ±coef·g^idx`, and `hsum` supplies the telescoping, a transparent
    hypothesis on the chosen signals. -/
theorem encrypt_correct
    (R : Mask S F)             -- secret mask (one BASE layer ⇒ only `R 0` is used)
    (g : F)                    -- carrier base; signal `s` contributes `±coef·g^idx`
    (sigs : List (Signal S F)) -- the signal edges (signal split + noise tuples)
    (v : Fin S → F)            -- the plaintext expected back
    (j : Fin S)                -- the slot being decrypted
    (hsum : (sigs.map fun s => s.contrib g j).sum = v j)  -- contributions telescope to `v`
  :
    decrypt g R (encrypt R sigs) j = v j
  := by
    -- recover each intended coefficient as `w · R⁻¹`; `decrypt_strip` then
    -- cancels the mask (invertibility comes straight from `R.nonzero`, no `hR`
    -- hypothesis needed)
    have hw : ∀ e ∈ (encrypt R sigs).edges,
        e.w j = e.w j * (R e.layer j)⁻¹ * R e.layer j :=
      fun e _ => (inv_mul_cancel_right₀ (R.nonzero e.layer j) (e.w j)).symm
    rw [decrypt_strip g R (encrypt R sigs) j (fun e j' => e.w j' * (R e.layer j')⁻¹) hw]
    -- masks gone; reduce the edge sum to `Σ contrib` and apply the telescoping `hsum`
    simp only [encrypt, List.map_map, Function.comp_def, zero_add]
    rw [← hsum]
    apply congrArg List.sum
    apply List.map_congr_left
    intro s _
    have hne : R 0 j ≠ 0 := R.nonzero 0 j
    simp only [Signal.contrib]
    field_simp

/-- **Last coeff solved**: with one balancing edge appended, the signals
    telescope to `v` for ANY freely-chosen `free` edges. Needs only `g ≠ 0`, so
    the carrier `g^idx` is invertible. -/
theorem balance_telescopes
    (g : F)                     -- carrier base; needs `g ≠ 0`
    (free : List (Signal S F))  -- freely-chosen signal/noise edges
    (idx : ℕ)                   -- position of the balancing edge
    (v : Fin S → F)             -- the plaintext to hit
    (j : Fin S)                 -- the slot
    (hg : g ≠ 0)                -- ⇒ `g^idx` invertible, so the residual can be placed
  :
    ((balance g free idx v).map fun s => s.contrib g j).sum = v j
  := by
    have hgi : (g ^ idx) ≠ 0 := pow_ne_zero _ hg
    simp only [balance, List.map_append, List.sum_append, List.map_cons,
              List.map_nil, List.sum_cons, List.sum_nil, add_zero, Signal.contrib,
              sgn]
    field_simp
    ring

/-- **Fully closed**: the balanced K-edge encryption decrypts to `v`
    unconditionally; the only hypothesis is `g ≠ 0`. Mask invertibility
    (`R 0 j ≠ 0`) is automatic, bundled into the `Mask` type as `R.nonzero`. -/
theorem encrypt_balanced_correct
    (g : F)                     -- carrier base
    (R : Mask S F)              -- secret mask
    (free : List (Signal S F))  -- freely-chosen signal/noise edges
    (idx : ℕ)                   -- position of the solved balancing edge
    (v : Fin S → F)             -- the plaintext
    (j : Fin S)                 -- the slot being decrypted
    (hg : g ≠ 0)                -- carrier nonzero (`g^idx` is invertible)
  :
    decrypt g R (encrypt R (balance g free idx v)) j = v j
  :=
    encrypt_correct R g (balance g free idx v) v j
      (balance_telescopes g free idx v j hg)

/-- `encrypt1` is *definitionally* the K=1, no-free-edges instance of the balanced
    construction (it's now an alias); recorded here for readability. -/
theorem encrypt1_eq (g : F) (R : Mask S F) (idx : ℕ) (v : Fin S → F) :
    encrypt1 g R idx v = encrypt R (balance g [] idx v) := rfl

/-- The K=1 noise-free encryption decrypts exactly: now a corollary of the
    unconditional `encrypt_balanced_correct`. -/
theorem encrypt1_correct
    (g : F)                -- carrier base
    (R : Mask S F)         -- secret mask (only layer 0 is used by `encrypt1`)
    (idx : ℕ)              -- carrier position the single signal edge is placed at
    (v : Fin S → F)        -- the plaintext
    (j : Fin S)            -- the slot being decrypted
    (hg : g ≠ 0)           -- carrier nonzero ⇒ `g ^ idx` invertible
  :
    decrypt g R (encrypt1 g R idx v) j = v j
  := by
    rw [encrypt1_eq g R idx v]
    exact encrypt_balanced_correct g R [] idx v j hg

end Octra.HFHE
