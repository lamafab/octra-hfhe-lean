import Mathlib.Tactic

-- ============================================================================
-- Learning Parity with Noise (LPN): the hardness assumption  (Phase 2)
-- ============================================================================
--
-- LPN: given many samples (aᵢ, ⟨aᵢ, s⟩ ⊕ eᵢ) with secret s and sparse Bernoulli
-- noise eᵢ, recovering s is conjectured HARD (the dual of random syndrome decoding).
-- This is the post-quantum assumption replacing factoring: what makes Octra's
-- scheme more than Paillier. We NEVER prove it; it is the trust root.
--
-- "Hard" = "no efficient adversary recovers s", which needs a complexity / PPT-
-- adversary model Mathlib does not have and we deliberately do not build.  So the
-- body of `LPNHard` stays opaque.  The ONE thing we can state precisely is the
-- REGIME: LPN hardness is parametric in the secret length `n`, the sample count `m`,
-- and the noise weight `w` (that triple is what fixes the security level), so we
-- make the axiom parametric in it and pin it to the values Octra ships, rather than
-- postulating a single bare `Prop`.

namespace Octra.Coding

/-- **The LPN hardness assumption**, at secret length `n`, `m` samples, noise weight
    `w`: recovering the secret of a random instance is intractable.  Opaque body
    (no complexity model in Mathlib); parametric so the scheme names the exact regime
    it depends on. -/
axiom LPNHard (n m w : ℕ) : Prop

/-- LPN secret length `lpn_n` (C++ `types.hpp`). -/
def lpnSecretBits : ℕ := 4096
/-- LPN sample count `lpn_t` (C++ `types.hpp`). -/
def lpnSamples    : ℕ := 16384
/-- LPN noise weight `lpn_t · τ`, `τ = 1/8` (C++ `lpn_tau`): the same quantity as the
    weight bound `w` of a syndrome-decoding instance (`IsSyndromeDecodingSolution`,
    `Coding/LinearCode.lean`). -/
def lpnNoise      : ℕ := lpnSamples / 8   -- 2048

/-- We postulate LPN is hard at exactly those parameters: the single
    computational assumption the scheme's confidentiality rests on, never
    proved. -/
axiom lpn_hard : LPNHard lpnSecretBits lpnSamples lpnNoise

end Octra.Coding
