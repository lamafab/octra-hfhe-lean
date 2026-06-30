import Octra.Coding.LPN
import Mathlib.Tactic

-- ============================================================================
-- HFHE: the confidentiality assumption (NOT a security proof)
-- ============================================================================
--
-- This file records WHICH computational assumption Octra's confidentiality rests on,
-- and discharges it from the LPN axiom.  It is deliberately NOT an IND-CPA reduction:
-- a real reduction ("an adversary distinguishing ciphertexts solves LPN") needs a
-- PPT-adversary / advantage / negligibility model, and Mathlib has none; we are not
-- inventing a security-game framework here.  So we DO NOT prove "LPN-hard ⇒ scheme
-- secure"; we only NAME the trust root, pin it to the concrete LPN instance Octra
-- ships, and confirm it is exactly the postulated `Coding.lpn_hard`.
--
-- The decoy track (HyperDecoy.lean) builds the same shape over a random hypergraph;
-- its average-case hardness is a separate CITED assumption (not formalized).

namespace Octra.HFHE

/-- The single computational assumption Octra's confidentiality rests on: search-LPN
    is intractable at the shipped parameters (`lpn_n = 4096` secret bits,
    `lpn_t = 16384` samples, Bernoulli noise rate `τ = 1/8`).  Expressed through the
    precise `Coding.LPNHard` predicate, not an opaque `Prop`. -/
def confidentialityAssumption : Prop :=
  Coding.LPNHard Coding.lpnSecretBits Coding.lpnSamples Coding.lpnNoise

/-- The assumption is exactly Octra's trust root: it holds by `Coding.lpn_hard` (which
    is POSTULATED, never proved).  This is the use site that pins the scheme's
    confidentiality to the LPN axiom: not a reduction, just the named dependency. -/
theorem confidentiality_trusted : confidentialityAssumption :=
  Coding.lpn_hard

end Octra.HFHE
