import Octra.HFHE.Cipher
import Mathlib.Tactic

-- ============================================================================
-- Octra: recrypt: refresh σ-density, preserve the plaintext  (end to end)
-- ============================================================================
--
-- In a noisy FHE scheme, recrypt ("bootstrapping") resets the accumulated noise so that
-- evaluation can continue. Octra has no decryption noise (decryption is exact,
-- see `Correctness.lean`), so recrypt has a different job: refresh the decoy layer that hides
-- the ciphertext, without disturbing the encrypted value. One round does three things:
--
--   (1) add a fresh encryption of zero (re-randomize the ciphertext);
--   (2) permute every decoy by the public permutation `ubk`;
--   (3) compact the edge list (`Merge.lean`).
--
-- Only (1) could affect the plaintext, and since a zero-encryption adds zero, it does not;
-- (2) and (3) never touch the decrypted value. This file proves exactly that recrypt
-- preserves the plaintext, at two levels: the engine `recrypt` (`decrypt_recrypt`) and the
-- full ciphertext loop `recryptLoop` (`decrypt_recryptLoop`), for any zero-encryptions and
-- any number of rounds.
--
-- What it does NOT prove is recrypt's statistical goal: driving the decoy density back
-- toward ½. That is a runtime heuristic (the density band and round cap below), never
-- something correctness depends on.
--
-- C++: `ct_recrypt` (`ops/recrypt.hpp`); the σ-density band, `ubk_apply`.

namespace Octra.HFHE

variable {S : ℕ} {ι : Type*} [Fintype ι] {F : Type*} [Field F]

-- ----------------------------------------------------------------------------
-- Engine level: the zero-injection preserves the plaintext
-- ----------------------------------------------------------------------------

/-- Recrypt's plaintext-relevant action: fold a list of zero-encryptions into
    `c`. The decoy permutation and compaction are plaintext-neutral, layered on
    separately (`ubkApply` below, `Merge.lean`). -/
def recrypt (zs : List (Encoding S F)) (c : Encoding S F) : Encoding S F :=
  zs.foldl homAdd c

/-- **Recrypt preserves the plaintext.**  Adding ciphertexts that each decrypt to
    `0` leaves the message untouched: the exact analogue of "bootstrapping
    preserves the plaintext", here a clean consequence of additive homomorphism. -/
theorem decrypt_recrypt (g : F) (R : Mask S F) :
    ∀ (zs : List (Encoding S F)) (c : Encoding S F),
      (∀ z ∈ zs, ∀ j, decrypt g R z j = 0) →
      ∀ j, decrypt g R (recrypt zs c) j = decrypt g R c j := by
  intro zs
  induction zs with
  | nil => intro c _ j; rfl
  | cons z zs ih =>
    intro c h j
    -- `recrypt (z :: zs) c = recrypt zs (homAdd c z)` definitionally (foldl_cons)
    show decrypt g R (recrypt zs (homAdd c z)) j = decrypt g R c j
    rw [ih (homAdd c z) (fun z' hz' => h z' (List.mem_cons_of_mem z hz')) j,
        decrypt_homAdd, h z List.mem_cons_self j, add_zero]

/-- The randomness, abstracted the same way as `Mask`: a supply of ciphertexts that all decrypt to
    `0`, bundling the `decrypts-to-0` invariant (the CSPRNG just picks which to add). -/
structure ZeroPool (g : F) (R : Mask S F) where
  /-- the precomputed zero-encryptions -/
  members : List (Encoding S F)
  /-- every member decrypts to the zero plaintext -/
  isZero  : ∀ z ∈ members, ∀ j, decrypt g R z j = 0

/-- Recrypting with any selection drawn from a `ZeroPool` preserves the plaintext. -/
theorem decrypt_recrypt_pool {g : F} {R : Mask S F} (pool : ZeroPool g R)
    (zs : List (Encoding S F)) (hsub : ∀ z ∈ zs, z ∈ pool.members) (c : Encoding S F)
    (j : Fin S) :
    decrypt g R (recrypt zs c) j = decrypt g R c j :=
  decrypt_recrypt g R zs c (fun z hz => pool.isZero z (hsub z hz)) j

-- ----------------------------------------------------------------------------
-- The `ubk` permute step: re-randomizes decoys, preserves σ-density
-- ----------------------------------------------------------------------------

/-- The public permutation step of refresh: permute every decoy by `σ`, leaving the encoding
    untouched (so plaintext and alignment are kept).

    C++: `ubk_apply`. -/
def ubkApply (σ : Equiv.Perm ι) (c : Cipher S ι F) : Cipher S ι F where
  enc     := c.enc
  layers  := c.layers
  decoys  := c.decoys.map fun d => fun i => d (σ i)
  aligned := by rw [List.length_map]; exact c.aligned

omit [Field F] in
/-- `ubkApply` preserves σ-density: a permutation preserves each decoy's weight
    (`decoyWeight_perm`) and the edge count, so the ratio is unchanged; density moves only via
    zero-pool injections / compaction, never the permute. -/
theorem sigmaDensity_ubkApply (σ : Equiv.Perm ι) (c : Cipher S ι F) :
    sigmaDensity (ubkApply σ c) = sigmaDensity c := by
  simp only [sigmaDensity, ubkApply, List.length_map, List.map_map, Function.comp_def]
  rw [List.map_congr_left fun d _ => decoyWeight_perm σ d]

-- ----------------------------------------------------------------------------
-- The recrypt loop: refresh σ-density toward ½  (constants on record)
-- ----------------------------------------------------------------------------

/-- The σ-density band the refresh targets.  C++: hardcoded `0.495` / `0.505`. -/
def σLo : ℚ := 495 / 1000
def σHi : ℚ := 505 / 1000
/-- Maximum refresh rounds.  C++: hardcoded `8`. -/
def recryptRounds : ℕ := 8

/-- Is the decoy density outside the target band? -/
def sigmaNeedsBalance (c : Cipher S ι F) : Prop :=
  sigmaDensity c < σLo ∨ σHi < sigmaDensity c

instance (c : Cipher S ι F) : Decidable (sigmaNeedsBalance c) := by
  unfold sigmaNeedsBalance; infer_instance

/-- One refresh round: inject the zero-encryption `z`, then permute the decoys. -/
def recryptStep (σ : Equiv.Perm ι) (z c : Cipher S ι F) : Cipher S ι F :=
  ubkApply σ (taggedAdd c z)

/-- The refresh loop: while off-band, inject the next zero-encryption from `zs` and permute
    (caller supplies `≤ recryptRounds`).  Best-effort: if the pool runs out it returns
    as-is, possibly still off-band: a hiding concern only, never correctness.

    C++: the `ct_recrypt` loop body. -/
def recryptLoop (σ : Equiv.Perm ι) :
    List (Cipher S ι F) → Cipher S ι F → Cipher S ι F
  | [],      c => c
  | z :: zs, c => if sigmaNeedsBalance c then recryptLoop σ zs (recryptStep σ z c) else c

omit [Fintype ι] in
/-- One refresh round preserves the plaintext: a zero-injection (`decrypt_homAdd`) plus a decoy
    permutation, which decryption never reads. -/
theorem decrypt_recryptStep (g : F) (R : Mask S F) (σ : Equiv.Perm ι)
    (z c : Cipher S ι F) (j : Fin S) (hz : ∀ j, decrypt g R z.enc j = 0) :
    decrypt g R (recryptStep σ z c).enc j = decrypt g R c.enc j := by
  simp only [recryptStep, ubkApply, taggedAdd]
  rw [decrypt_homAdd, hz j, add_zero]

/-- The full refresh loop preserves the plaintext, for any round schedule and any density band,
    since every round is plaintext-neutral.  The public-object capstone of `decrypt_recrypt`. -/
theorem decrypt_recryptLoop (g : F) (R : Mask S F) (σ : Equiv.Perm ι) :
    ∀ (zs : List (Cipher S ι F)) (c : Cipher S ι F),
      (∀ z ∈ zs, ∀ j, decrypt g R z.enc j = 0) →
      ∀ j, decrypt g R (recryptLoop σ zs c).enc j = decrypt g R c.enc j := by
  intro zs
  induction zs with
  | nil => intro c _ j; rfl
  | cons z zs ih =>
    intro c hz j
    simp only [recryptLoop]
    split
    · rw [ih (recryptStep σ z c) (fun z' hz' => hz z' (List.mem_cons_of_mem z hz')) j]
      exact decrypt_recryptStep g R σ z c j (hz z List.mem_cons_self)
    · rfl

end Octra.HFHE
