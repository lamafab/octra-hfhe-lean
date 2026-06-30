import Octra.HFHE.Cipher
import Octra.HFHE.Size
import Mathlib.Tactic

-- ============================================================================
-- Octra: the Cipher-level multiply  (fold + repack)
-- ============================================================================
--
-- This is the multiply on full ciphertexts, and the one operation with real
-- depth.
--
-- The naive way to multiply two ciphertexts forms all `|a|·|b|` pairwise
-- products of their edges, so repeated multiplication blows the edge count up
-- quadratically. The deployed C++ `ct_mul` avoids that: it folds each layer
-- down to a single masked value (its wire-sum `gsum`), multiplies those folds,
-- and re-packs each product into a fresh edge set of fixed width on a new
-- product layer (each edge getting a fresh decoy). A product is then `width`
-- edges, independent of how big `a` and `b` were.
--
-- `Repack` captures the re-pack as an abstract recipe plus the one invariant
-- correctness needs (the new edges' wire-sum telescopes back to the value being
-- packed), and defers the actual sampling (as with `Mask`/`ZeroPool`). `taggedMul`
-- then runs fold → multiply → repack, taking the fresh per-edge decoys as input
-- data `pd`.
--
-- Two multiply models coexist; they agree under `decrypt` but differ in edge
-- layout. The engine `homMul` (`Homomorphism.lean`) is the simple value model
-- (the `prodEdge` outer product, `|a|·|b|` edges) used by the boolean gates.
-- `taggedMul` here is the deployed model: fixed `width` edges, faithful to the
-- wire.
--
-- C++: `ct_mul` = `build_product_cipher` + `emit_repack_edges`
-- (`ops/arithmetic.hpp`).

namespace Octra.HFHE

variable {S : ℕ} {ι : Type*} [Fintype ι] {F : Type*} [Field F]

/-- An abstract edge repacker: re-encode a `target` wire value into `width`
    fresh edges on a PROD layer, bundling the one invariant correctness needs:
    the edges' wire-sum `gsum` telescopes back to `target`. Sampling is
    deferred (as with `Mask`/`ZeroPool`); the per-edge decoys are NOT here (they
    are `H`-syndromes, passed to `taggedMul` as data `pd`).

    C++: `emit_repack_edges` (the `H`-free value path). -/
structure Repack (S : ℕ) (F : Type*) [Field F] where
  width      : ℕ
  -- layer → target → resulting edges
  edges      : ℕ → ((Fin S → F) → List (Term S F))
  card_edges : ∀ L t, (edges L t).length = width
  onLayer    : ∀ L t, ∀ e ∈ edges L t, e.layer = L
  telescopes : ∀ (g : F) L t j, gsum g j (edges L t) = t j

/-- A repacked layer decrypts to `(R L)⁻¹ · target`: single-layer fold
    (`esum_single_layer`) plus the `telescopes` invariant. -/
theorem esum_repack
    (rp : Repack S F)
    (g : F)
    (R : Mask S F)
    (j : Fin S)
    (L : ℕ)
    (t : Fin S → F)
  :
    esum g R j (rp.edges L t) = (R L j)⁻¹ * t j
  := by
    rw [esum_single_layer g R j L (rp.edges L t) (rp.onLayer L t),
    rp.telescopes]

/-- Cipher-level multiply: fold each operand's layer to its wire-sum (`gsum`),
    form `target = gsum a · gsum b`, and repack it (via `rp`) into `width` fresh
    edges on the PROD layer `prod la lb`; the fresh per-edge decoys arrive as
    data `pd`.  Edge count is `width`, not `|a|·|b|`.

    Scope (as in `encrypt`): single-layer operands (`a` on `la`, `b` on `lb`)
    with `c0 = 0`, the fresh case; the general multi-layer multiply folds every
    layer-pair (`esum_flatMap`), same per-pair algebra.

    C++: `ct_mul` (`HyperDecoy.taggedMulH` supplies `pd` via `sigma_from_H`). -/
def taggedMul
    (rp : Repack S F)
    (alg : LayerAlg)
    (g : F)
    (la lb : ℕ)
    (a b : Cipher S ι F)
    (pd : List (Decoy ι))
    (hpd : pd.length = rp.width)
  :
    Cipher S ι F where
    enc     := {
      edges := rp.edges (alg.prod la lb)
        (fun j => gsum g j a.enc.edges * gsum g j b.enc.edges)
      c0    := fun _ => 0
    }
    layers  := a.layers ++ b.layers ++ [Layer.prod la lb]
    decoys  := pd
    aligned := by rw [hpd, rp.card_edges]

omit [Fintype ι] in
/-- Cipher-level multiply decrypts to the product: for single-layer, `c0 = 0`
    operands the repacked product's mask `R(prod la lb) = R la · R lb` cancels
    both folds, giving `((R la)⁻¹·gsum a)·((R lb)⁻¹·gsum b) = decrypt a · decrypt b`.
    -/
theorem decrypt_taggedMul
    (rp : Repack S F)
    (g : F)
    (R : Mask S F)
    (la lb : ℕ)
    (a b : Cipher S ι F)
    (pd : List (Decoy ι))
    (hpd : pd.length = rp.width)
    (ha : ∀ e ∈ a.enc.edges, e.layer = la)
    (hb : ∀ e ∈ b.enc.edges, e.layer = lb)
    (hca : a.enc.c0 = fun _ => 0)
    (hcb : b.enc.c0 = fun _ => 0)
    (j : Fin S)
  :
    decrypt g R (taggedMul rp R.toLayerAlg g la lb a b pd hpd).enc j
      = decrypt g R a.enc j * decrypt g R b.enc j
  := by
    have hA : decrypt g R a.enc j = (R la j)⁻¹ * gsum g j a.enc.edges := by
      rw [decrypt_eq, esum_single_layer g R j la a.enc.edges ha, hca]; simp
    have hB : decrypt g R b.enc j = (R lb j)⁻¹ * gsum g j b.enc.edges := by
      rw [decrypt_eq, esum_single_layer g R j lb b.enc.edges hb, hcb]; simp
    rw [hA, hB, decrypt_eq]
    show (0 : F) + esum g R j (rp.edges (R.prod la lb)
          (fun j => gsum g j a.enc.edges * gsum g j b.enc.edges))
        = (R la j)⁻¹ * gsum g j a.enc.edges * ((R lb j)⁻¹ * gsum g j b.enc.edges)
    rw [esum_repack, R.prod_eq la lb j, mul_inv_rev]
    ring

omit [Fintype ι] in
/-- Edge count after a multiply is the fixed repack `width`, not `|a|·|b|` (the
    repack fix). -/
@[simp] theorem numEdges_taggedMul
    (rp : Repack S F)
    (alg : LayerAlg)
    (g : F)
    (la lb : ℕ)
    (a b : Cipher S ι F)
    (pd : List (Decoy ι))
    (hpd : pd.length = rp.width)
  :
    numEdges (taggedMul rp alg g la lb a b pd hpd).enc = rp.width
  := by
    show (rp.edges (alg.prod la lb) _).length = rp.width
    rw [rp.card_edges]

/-- Cipher-level square: the `b = a` case of `taggedMul`.

    C++: `ct_square`. -/
def taggedSquare
    (rp : Repack S F)
    (alg : LayerAlg)
    (g : F)
    (la : ℕ)
    (a : Cipher S ι F)
    (pd : List (Decoy ι))
    (hpd : pd.length = rp.width)
  :
    Cipher S ι F
  :=
    taggedMul rp alg g la la a a pd hpd

omit [Fintype ι] in
/-- Square decrypts to the square of the plaintext: the `b = a` case of
    `decrypt_taggedMul`. -/
theorem decrypt_taggedSquare (rp : Repack S F) (g : F) (R : Mask S F) (la : ℕ)
    (a : Cipher S ι F) (pd : List (Decoy ι)) (hpd : pd.length = rp.width)
    (ha : ∀ e ∈ a.enc.edges, e.layer = la) (hca : a.enc.c0 = fun _ => 0) (j : Fin S)
  :
    decrypt g R (taggedSquare rp R.toLayerAlg g la a pd hpd).enc j
      = decrypt g R a.enc j * decrypt g R a.enc j :=
  decrypt_taggedMul rp g R la la a a pd hpd ha ha hca hca j

end Octra.HFHE
