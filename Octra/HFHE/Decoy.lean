import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

-- ============================================================================
-- The decoy: a syndrome vector in 𝔽₂^ι, and its Hamming weight
-- ============================================================================
--
-- Every Octra ciphertext edge carries a decoy: a bit-vector over 𝔽₂ that
-- decryption never reads. Its job is to plant a hard problem inside the
-- published ciphertext, where recovering the data behind a decoy is an instance of
-- syndrome decoding, and the scheme's security rests on that being intractable
-- (built and stated in `HyperDecoy.lean`, hardness cited in `Coding/`).
--
-- Concretely a decoy is a syndrome: a value `H·x + e` for the public
-- parity-check matrix `H`, a hidden selection `x`, and sparse noise `e`. As a
-- type it is just a function from a bit-position index to 𝔽₂. We keep that
-- index an arbitrary finite type `ι` (rather than `Fin m`) so it can later be
-- specialized to `H`'s edge type directly (`HyperDecoy.lean`).
--
-- This file is the pure-𝔽₂ core: the decoy type and its Hamming weight (the
-- number of set bits), plus the one fact the rest of the scheme needs: that a
-- permutation preserves Hamming weight. That is what lets the `ubk`
-- decoy-shuffle during recrypt leave the decoy density unchanged. The
-- ciphertext-level overlay (decoys attached to an encoding, the density measure,
-- the recrypt loop) is built on top in `Cipher.lean` and `Octra.lean`.

namespace Octra.HFHE

variable {ι : Type*} [Fintype ι]

/-- A decoy: a syndrome vector in 𝔽₂^ι (the row space of the parity-check `H`),
    indexed by a finite bit-position type `ι`. Its preimage problem is syndrome
    decoding: the keystone-#5 hardness. -/
abbrev Decoy (ι : Type*) := ι → ZMod 2

/-- Hamming weight of a decoy: the number of set bits (C++ `popcnt`). -/
def decoyWeight (d : Decoy ι) : ℕ := (Finset.univ.filter fun i => d i ≠ 0).card

/-- A permutation preserves Hamming weight: the key fact behind σ-density being
    invariant under the `ubk` permutation step (reindexing a sum by a bijection).
    -/
theorem decoyWeight_perm (σ : Equiv.Perm ι) (d : Decoy ι)
  :
    decoyWeight (fun i => d (σ i)) = decoyWeight d
  := by
    simp only [decoyWeight, Finset.card_filter]
    exact Equiv.sum_comp σ (fun i => if d i ≠ 0 then 1 else 0)

end Octra.HFHE
