import Octra.Field127
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic

-- ============================================================================
-- HFHE: ciphertext core, decryption, encryption
-- ============================================================================
--
-- Octra is an EXACT homomorphic encryption scheme over a field 𝔽 (intended 𝔽ₚ with
-- p = 2^127 − 1; see Field127.lean). Unlike noisy LWE/LPN schemes, decryption is an
-- exact identity: the "noise" cancels exactly, so there is no decryption noise budget.
--
-- A ciphertext's decryptable core is an `Encoding`: a list of edges plus a constant
-- `c0`. Each edge contributes `±w · g^idx` and names a layer whose secret mask `R` is
-- divided back out at decryption. The layer graph recording how a ciphertext was built
-- is provenance carried by the full `Cipher` (in `Octra.lean`); decryption never reads it.
--
-- The algebra here holds over any field. The secret mask `R` is its own type `Mask`,
-- which bundles the one invariant decryption needs: every mask entry is nonzero, so it
-- can be divided out. How `R` is actually derived is a separate layer; any value of
-- type `Mask` is correctness-valid.

namespace Octra.HFHE

variable {S : ℕ} {F : Type*} [Field F]

/-- Carrier sign: `true ↦ +1`, `false ↦ −1`. -/
def sgn : Bool → F
  | true  => 1
  | false => -1

/-- A single term of the decrypt sum: contributes `±w · g^idx`, attributed to layer
    `layer`. (In the full scheme each edge also carries a decoy bit-selector that
    decryption never reads; it is modeled separately on the `Cipher` in `Octra.lean`.) -/
structure Term (S : ℕ) (F : Type*) where
  layer : ℕ
  idx   : ℕ
  sign  : Bool
  w     : Fin S → F

/-- The decryptable core of a ciphertext: a list of `edges` and a constant `c0`, over
    `S` slots. Decryption uses only these and the per-layer mask `R`; the layer-graph
    provenance rides on the full `Cipher` in `Octra.lean`. -/
structure Encoding (S : ℕ) (F : Type*) where
  edges : List (Term S F)
  c0    : Fin S → F

/-- The public layer-index algebra: the rule forming a product (PROD) layer's index
    from its two parents. It carries no secret, so the homomorphic multiply depends
    only on this, never on the mask values. The secret `Mask` extends it with the
    actual mask values and a compatibility law. -/
structure LayerAlg where
  /-- index of the PROD layer built from parents `a` and `b` -/
  prod : ℕ → (ℕ → ℕ)

/-- The secret mask as an object rather than a bare function: `R l j` is the mask of
    layer `l` at slot `j`, and it is always invertible (`nonzero`). Invertibility is
    the single fact decryption needs to strip it (`R · R⁻¹ = 1`); bundling it into the
    type keeps `R l j ≠ 0` off every correctness theorem.

    `Mask` extends the public `LayerAlg`, adding the mask values (`toFun`/`nonzero`)
    and `prod_eq`, the law tying the inherited public `prod` to those values
    (`R (prod a b) = R a · R b`) that a homomorphic multiply's correctness relies on. -/
structure Mask (S : ℕ) (F : Type*) [Field F] extends LayerAlg where
  /-- the underlying per-layer, per-slot mask values -/
  toFun   : ℕ → (Fin S → F)
  /-- masks are nonzero, so decryption can divide them out -/
  nonzero : ∀ l j, toFun l j ≠ 0
  /-- a PROD layer's mask is the product of its parents' masks (drives `homMul`) -/
  prod_eq : ∀ a b j, toFun (prod a b) j = toFun a j * toFun b j

/-- Use a `Mask` as the function `R l j` it wraps, so call sites read unchanged. -/
instance : CoeFun (Mask S F) (fun _ => ℕ → Fin S → F) := ⟨Mask.toFun⟩

/-- Decryption under carrier `g` and a per-layer mask `R`:
      `v[j] = c0[j] + Σ_e sign(e)·w[j]·g^idx·R(layer)⁻¹`.
    `R l j` is the mask of layer `l` at slot `j` (nonzero by `R.nonzero`). -/
def decrypt (g : F) (R : Mask S F) (c : Encoding S F) (j : Fin S) : F :=
  c.c0 j + (c.edges.map fun e => sgn e.sign * e.w j * g ^ e.idx * (R e.layer j)⁻¹).sum

-- (The homomorphic operations `homAdd`/`homScale`/`homNeg`/`homSub`/`homMul` and
-- their exactness proofs live together in `Homomorphism.lean`.)

-- ============================================================================
-- Encryption: the signal split that makes the telescoping provable
-- ============================================================================
--
-- Encryption spreads the message across `K` signal edges `±coef·g^idx` that sum to it,
-- plus noise tuples that cancel in pairs. We model this directly: a `Signal` is one
-- unmasked edge; `encrypt` masks each by the layer-0 mask `R 0` and drops them into one
-- BASE layer, and the recovered message is exactly `Σ contrib`. `balance` solves the
-- final coefficient so that sum equals `v` by construction.

/-- A signal edge before masking: contributes `±coef·g^idx` (sign `sign`, carrier
    position `idx`) to the message. The masked ciphertext edge carries `w = coef·R`. -/
structure Signal (S : ℕ) (F : Type*) where
  idx  : ℕ
  sign : Bool
  coef : Fin S → F

/-- The unmasked contribution of a signal to slot `j`: `±coef·g^idx`.  Decryption
    strips the mask, so it recovers exactly `c0 + Σ contrib`. -/
def Signal.contrib (g : F) (s : Signal S F) (j : Fin S) : F :=
  sgn s.sign * s.coef j * g ^ s.idx

/-- Multi-edge, noise-free encryption: one BASE layer, one masked edge per signal
    (`w = coef · R 0`), `c0 = 0`. Noise tuples are just extra signals whose
    contributions cancel. Whether it decrypts to `v` is governed entirely by
    `Σ contrib = v` (`encrypt_correct`); `balance` makes that hold by construction. -/
def encrypt (R : Mask S F) (sigs : List (Signal S F)) : Encoding S F where
  edges := sigs.map fun s => { layer := 0, idx := s.idx, sign := s.sign,
                               w := fun j => s.coef j * R 0 j }
  c0    := fun _ => 0

/-- Append one balancing signal at position `idx` carrying the residual
    `(v − Σ free.contrib)·(g^idx)⁻¹`, so its own contribution is exactly
    `v − Σ free.contrib` (needs `g ≠ 0`). The whole list then telescopes to `v` for
    any freely-chosen `free` edges (`balance_telescopes`). -/
def balance (g : F) (free : List (Signal S F)) (idx : ℕ) (v : Fin S → F) : List (Signal S F) :=
  free ++ [{
    idx := idx,
    sign := true,
    coef := fun j => (v j - (free.map fun s => s.contrib g j).sum) * (g ^ idx)⁻¹
  }]

/-- The `K=1`, no-`free`-edges instance of `encrypt`/`balance`: a single signal edge
    at carrier position `idx` carrying all of `v` (so `encrypt1_eq` is `rfl`).

    Warning: this is NOT secure encryption. It hides nothing, an adversary sees one
    edge bearing the whole message. Real encryption spreads `v` across K signal edges
    plus canceling noise tuples so the edge set looks random (`encrypt`/`balance`).
    `encrypt1` exists only to exhibit exact correctness end to end (`encrypt1_correct`)
    and as a convenient zero-encryption builder in examples. Never use it to hide `v`. -/
def encrypt1 (g : F) (R : Mask S F) (idx : ℕ) (v : Fin S → F) : Encoding S F :=
  encrypt R (balance g [] idx v)

end Octra.HFHE
