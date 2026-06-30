import Octra.HFHE.Octra
import Octra.Hypergraph.Incidence
import Octra.Coding.Syndrome
import Mathlib.Tactic

-- ============================================================================
-- HFHE: the decoy as a hypergraph syndrome  (the value ↔ hypergraph bridge)
-- ============================================================================
--
-- The value side of an Octra ciphertext (`Encoding`/`Term`/`encrypt`) knows
-- nothing about the hypergraph; it is just carrier positions and a mask. The
-- hypergraph enters through the decoy: each edge's decoy is a syndrome over the
-- public parity-check matrix `H`, of the form `H·x + e`. So a decoy is an
-- element of `H`'s syndrome space, and the hypergraph syndrome map
-- (`Incidence.lean`) is literally how it is built.
--
-- This file is the bridge between the two sides. It defines
-- decoys-as-syndromes, pairs a value `Encoding` with one decoy per edge to form
-- the public `Cipher`, gives the unified encryption and multiply over `H`, and
-- assembles the full `Scheme`.
--
-- Recovering the selection `x` behind a decoy is an instance of syndrome
-- decoding over `H`. We build that instance and prove it really is one (the
-- solution exists and is unique). The assumption that it is HARD on average,
-- for random k-uniform hypergraphs at the relevant density (Shabanov,
-- Raigorodskii et al.; the same regime as LPN, see `Coding/LPN.lean`), is
-- cited, never proved here.
--
-- C++: `sigma_from_H` (per-edge decoy emission), `synth` (fresh encryption),
-- `ct_mul`.

namespace Octra.HFHE

open Hypergraph Octra.Coding

variable {V : Type*} [DecidableEq V] (H : Hypergraph V) {S : ℕ} {F : Type*} [Field F]

/-- A decoy over `H`: an element of `H`'s syndrome space `Decoy H.EdgeIdx`, the same
    space `H.syndrome` lands in. -/
abbrev HDecoy := Decoy H.EdgeIdx

/-- A decoy as the syndrome of a column selection `x` over `H`, plus a sparse error
    `e`. `H.syndrome` is the "⊕ selected columns" parity-check map.

    C++: `sigma_from_H`. -/
def decoyOf (x : H.VertIdx → ZMod 2) (e : HDecoy H) : HDecoy H :=
  H.syndrome (ZMod 2) x + e

/-- The decoy as an explicit matrix–vector product: incidence matrix `H.incidence`
    applied to `x`, plus `e`. Makes the "hypergraph as parity-check" step
    literal at the use site. -/
theorem decoyOf_eq_mulVec (x : H.VertIdx → ZMod 2) (e : HDecoy H) :
    decoyOf H x e = (H.incidence (ZMod 2)).mulVec x + e := rfl

/-- Recovering the weight-`≤ w` selection `x` behind a decoy `σ` is a syndrome-decoding
    instance over `H`'s parity check: the hard problem the decoy's secrecy rests
    on. -/
def DecoyIsHardInstance (σ : HDecoy H) (w : ℕ) (x : H.VertIdx → ZMod 2) : Prop :=
  IsHypergraphDecodingSolution H (ZMod 2) σ w x

/-- A noiseless decoy `decoyOf x 0` is solved by its own selection `x` (within any
    weight bound `x` meets): `σ = H.syndrome x`, so `x` is a decoding solution. -/
theorem decoyOf_zero_solves
    (x : H.VertIdx → ZMod 2)
    (w : ℕ)
    (hw : hammingWeight x ≤ w)
  :
    DecoyIsHardInstance H (decoyOf H x 0) w x
  := by
    refine ⟨?_, hw⟩
    simp only [decoyOf, add_zero, hypergraph_syndrome_eq]

/-- **A decoy pins down its selection** (within decoding radius `t`): given the incidence
    code's minimum-distance hypothesis, any two weight-`≤ t` selections behind the same
    decoy `σ` coincide. -/
theorem decoy_selection_unique {t : ℕ} {σ : HDecoy H} {x₁ x₂ : H.VertIdx → ZMod 2}
    (hmin : ∀ c ∈ code (H.incidence (ZMod 2)), c ≠ 0 → 2 * t + 1 ≤ hammingWeight c)
    (h₁ : DecoyIsHardInstance H σ t x₁)
    (h₂ : DecoyIsHardInstance H σ t x₂)
  :
    x₁ = x₂
  :=
    hypergraph_decoding_unique H hmin h₁ h₂

/-- **The selection behind a noiseless decoy is unique.**  Existence (`decoyOf_zero_solves`)
    plus uniqueness (`decoy_selection_unique`): under the minimum-distance hypothesis, `x` is
    the ONE weight-`≤ t` selection explaining `decoyOf x 0`, so recovering it is a
    well-defined problem, the one whose average-case hardness the scheme rests on. -/
theorem decoyOf_zero_selection_unique {t : ℕ} {x₁ x₂ : H.VertIdx → ZMod 2}
    (hmin : ∀ c ∈ code (H.incidence (ZMod 2)), c ≠ 0 → 2 * t + 1 ≤ hammingWeight c)
    (hx : hammingWeight x₁ ≤ t)
    (hsol : DecoyIsHardInstance H (decoyOf H x₁ 0) t x₂)
  :
    x₂ = x₁
  :=
    decoy_selection_unique H hmin hsol (decoyOf_zero_solves H x₁ t hx)

-- ----------------------------------------------------------------------------
-- Octra's shipped decoy/syndrome parameters (C++ `types.hpp`)
-- ----------------------------------------------------------------------------
--
-- These describe the decoy's syndrome-decoding instance over `H`. They are a separate
-- parameter family from the LPN PRF (`Coding/LPN.lean`), which derives the value-channel
-- mask, not the decoy.

/-- Parity-check rows (C++ `m_bits`). -/
def mBits  : ℕ := 8192
/-- Parity-check columns (C++ `n_bits`). -/
def nBits  : ℕ := 16384
/-- Column weight of `H` (C++ `h_col_wt`). -/
def hColWt : ℕ := 192
/-- Selection weight: each decoy selects this many columns (C++ `x_col_wt`). This is the
    sparsity bound on the selection `x` in the decoy's syndrome-decoding instance. -/
def xColWt : ℕ := 128
/-- Error weight: each decoy flips this many output bits (C++ `err_wt`); the noise `e` in
    `σ = H·x + e`. Enters the noisy decoding question, not the noiseless lemma below. -/
def errWt  : ℕ := 128

/-- **The noiseless decoy's selection is unique** at the shipped selection weight
    weight `xColWt`: if the incidence code has minimum distance `d ≥ 2·xColWt + 1`,
    the `≤ xColWt`-sparse `x` behind `decoyOf x 0` is the only one.

    TODO: this is the noiseless case `e = 0`; the real decoy `σ = H·x + e`
    (error weight `errWt`) needs `d ≥ 2·(xColWt + errWt) + 1`, and hardness
    of finding `x` is unformalized. And `xColWt` is a decoy parameter, not the
    LPN PRF's `lpnNoise`. -/
theorem decoyOf_shipped_selection_unique {x₁ x₂ : H.VertIdx → ZMod 2}
    (hmin : ∀ c ∈ code (H.incidence (ZMod 2)), c ≠ 0 →
      2 * xColWt + 1 ≤ hammingWeight c)
    (hx : hammingWeight x₁ ≤ xColWt)
    (hsol : DecoyIsHardInstance H (decoyOf H x₁ 0) xColWt x₂)
  :
    x₂ = x₁
  :=
    decoyOf_zero_selection_unique H hmin hx hsol

-- ----------------------------------------------------------------------------
-- The unification layer: an `Encoding` + per-edge `H`-syndromes ⇒ a public `Cipher`
-- ----------------------------------------------------------------------------
--   The decoy side is pure parity-check data, indexed by edge POSITION and independent
--   of the value an edge carries.  `hDecoys` emits one syndrome per edge; `withDecoys`
--   pairs any value `Encoding` with them to form the public `Cipher`, leaving `.enc`
--   untouched, so the value and decoy worlds never entangle (`decrypt` reads only `.enc`).

/-- `n` per-edge syndrome decoys, edge `i` carrying `decoyOf H (sel i) (err i)`.  The
    decoy-emission primitive, shared by fresh encryption (`withDecoys`) and products
    (`taggedMulH`).  Each decoy depends only on the edge POSITION, never the payload:
    that independence is what keeps the value side decode-irrelevant.

    C++: `sigma_from_H`, batched per edge. -/
def hDecoys (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H) (n : ℕ) : List (HDecoy H) :=
  (List.range n).map fun i => decoyOf H (sel i) (err i)

@[simp] theorem length_hDecoys (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H) (n : ℕ) :
    (hDecoys H sel err n).length = n := by
  rw [hDecoys, List.length_map, List.length_range]

/-- **The unification layer**: pair a value `Encoding` `e` with one `H`-syndrome decoy
    per edge to form the public `Cipher`. `.enc = e` unchanged (by definition), so
    decryption reads exactly `e`: value and decoy worlds meet here without entangling.
    Sits on one BASE layer; alignment is free, as `hDecoys` emits one decoy per edge.

    C++: `synth` (fresh encryption). -/
def withDecoys (e : Encoding S F) (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H) :
  Cipher S H.EdgeIdx F where
  enc     := e
  layers  := [Layer.base 0]
  decoys  := hDecoys H sel err e.edges.length
  aligned := by rw [length_hDecoys]

-- ----------------------------------------------------------------------------
-- Unified encryption: value (hypergraph-free) + decoys (over `H`)
-- ----------------------------------------------------------------------------

/-- **Unified encryption**, value + decoys in one pipeline:
    1.  VALUE (hypergraph-free): balance `v` into signals (`balance g free idx v`) and
        mask with `encrypt R`, exactly as in `Correctness.lean`.
    2.  DECOY (the hypergraph enters here): `withDecoys` attaches one syndrome
        `decoyOf H (sel i) (err i)` per edge.

    The two sides never touch: encryption is just `withDecoys` of the value `Encoding`.
    C++: `synth`. -/
def encryptH
    (g : F)
    (R : Mask S F)
    (free : List (Signal S F))
    (idx : ℕ)
    (v : Fin S → F)
    (sel : ℕ → H.VertIdx → ZMod 2)
    (err : ℕ → HDecoy H)
  :
    Cipher S H.EdgeIdx F
  :=
    withDecoys H (encrypt R (balance g free idx v)) sel err

/-- The unified ciphertext still decrypts to `v`: decoys are decode-irrelevant, so this
    is exactly `encrypt_balanced_correct`. -/
theorem encryptH_plaintext
    (g : F)
    (R : Mask S F)
    (free : List (Signal S F))
    (idx : ℕ)
    (v : Fin S → F)
    (sel : ℕ → H.VertIdx → ZMod 2)
    (err : ℕ → HDecoy H)
    (j : Fin S) (hg : g ≠ 0)
  :
    decrypt g R (encryptH H g R free idx v sel err).enc j = v j
  :=
    encrypt_balanced_correct g R free idx v j hg

/-- Edge `i`'s attached decoy IS the parity-check syndrome of that edge's selection:
    the formal statement that "Octra uses `H` as a parity-check matrix" (`rfl`-deep). -/
theorem encryptH_decoy
    (g : F)
    (R : Mask S F)
    (free : List (Signal S F))
    (idx : ℕ)
    (v : Fin S → F)
    (sel : ℕ → H.VertIdx → ZMod 2)
    (err : ℕ → HDecoy H)
    (i : ℕ)
    (hi : i < (encryptH H g R free idx v sel err).enc.edges.length)
  :
    (encryptH H g R free idx v sel err).decoys[i]'(by
      rw [(encryptH H g R free idx v sel err).aligned]; exact hi) =
      decoyOf H (sel i) (err i) := by
  simp only [encryptH, withDecoys, hDecoys, List.getElem_map, List.getElem_range]

/-- Inverting a noiseless attached decoy (`err i = 0`) is the syndrome-decoding instance
    solved by `sel i`, so the decoys Octra emits are bona-fide instances of the problem
    whose average-case hardness is the cited assumption (see the file header). -/
theorem encryptH_decoy_solvable (sel : ℕ → H.VertIdx → ZMod 2) (i : ℕ) (w : ℕ)
    (hw : hammingWeight (sel i) ≤ w) :
    DecoyIsHardInstance H (decoyOf H (sel i) 0) w (sel i) :=
  decoyOf_zero_solves H (sel i) w hw

-- ----------------------------------------------------------------------------
-- Cipher-level multiply over `H`: supply the fresh repacked-edge decoys
-- ----------------------------------------------------------------------------
--
-- `Octra.taggedMul` is hypergraph-FREE: it repacks the product into `rp.width`
-- fresh edges and takes their decoys as data.  Here we build them with
-- `hDecoys` (the same emission primitive `withDecoys` uses), giving each
-- repacked edge a fresh `H`-syndrome.  Correctness rides for free on
-- `decrypt_taggedMul`, as decoys are decode-irrelevant.

/-- Cipher-level multiply over `H`: `Octra.taggedMul` with the `rp.width` repacked-edge
    decoys from `hDecoys` (same per-edge syndrome emission as `withDecoys`/`encryptH`).
    C++: `ct_mul`. -/
def taggedMulH
    (rp : Repack S F)
    (alg : LayerAlg)
    (g : F)
    (la lb : ℕ)
    (a b : Cipher S H.EdgeIdx F)
    (sel : ℕ → H.VertIdx → ZMod 2)
    (err : ℕ → HDecoy H)
  :
    Cipher S H.EdgeIdx F
  :=
    taggedMul rp alg g la lb a b
      (hDecoys H sel err rp.width)
      (length_hDecoys H sel err rp.width)

/-- The unified product still decrypts to the product of plaintexts: decoys are
    decode-irrelevant, so this is exactly `decrypt_taggedMul` (cf. `encryptH_plaintext`). -/
theorem decrypt_taggedMulH (rp : Repack S F) (g : F) (R : Mask S F) (la lb : ℕ)
    (a b : Cipher S H.EdgeIdx F)
    (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H)
    (ha : ∀ e ∈ a.enc.edges, e.layer = la) (hb : ∀ e ∈ b.enc.edges, e.layer = lb)
    (hca : a.enc.c0 = fun _ => 0) (hcb : b.enc.c0 = fun _ => 0) (j : Fin S) :
    decrypt g R (taggedMulH H rp R.toLayerAlg g la lb a b sel err).enc j
      = decrypt g R a.enc j * decrypt g R b.enc j :=
  decrypt_taggedMul rp g R la lb a b _ _ ha hb hca hcb j

-- ----------------------------------------------------------------------------
-- The assembled instance: where the hypergraph `H` enters the public key
-- ----------------------------------------------------------------------------

/-- **A full `Scheme` over the hypergraph `H`**: where the generic `Octra.Scheme`
    (abstract decoy index `ι`) gets `ι := H.EdgeIdx`: public key `g`+`ubk`, public
    ciphertext `encryptH` (value + `H`-syndrome decoys), secret key the mask `R`.  `H`
    is the public parity-check the decoys are syndromes of. -/
def schemeOf (g : F) (R : Mask S F) (free : List (Signal S F)) (idx : ℕ)
    (v : Fin S → F) (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H)
    (ubk : Equiv.Perm H.EdgeIdx) : Scheme S H.EdgeIdx F where
  pk := { g := g, ubk := ubk }
  ct := encryptH H g R free idx v sel err
  sk := { mask := R }

/-- The assembled instance decrypts to `v`: keys + hypergraph decoys + value in one
    statement; the holder of `sk` recovers exactly `v` (still `encrypt_balanced_correct`). -/
theorem schemeOf_plaintext (g : F) (R : Mask S F) (free : List (Signal S F)) (idx : ℕ)
    (v : Fin S → F) (sel : ℕ → H.VertIdx → ZMod 2) (err : ℕ → HDecoy H)
    (ubk : Equiv.Perm H.EdgeIdx) (j : Fin S) (hg : g ≠ 0) :
    (schemeOf H g R free idx v sel err ubk).plaintext j = v j := by
  simp only [schemeOf, Scheme.plaintext]
  exact encryptH_plaintext H g R free idx v sel err j hg

end Octra.HFHE
