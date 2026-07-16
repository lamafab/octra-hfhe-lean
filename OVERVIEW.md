# Octra HFHE: Formalization Overview

> A map of the Lean development: the one big idea, the two channels it splits into,
> the five keystone results, and where every module sits. Theorem and definition
> names link to source. This is a reading guide, not a spec.

---

## 0. Orientation

### The one idea

Octra is an exact homomorphic encryption scheme over a finite field 𝔽ₚ (`p =
2¹²⁷ − 1`, the Mersenne prime, [`Field127.lean`](Octra/Field127.lean)). Unlike
LWE/BGV‑style FHE, **there is no decryption noise**: decryption is an identity
over 𝔽ₚ, and the scheme's "noise" tuples cancel exactly. Consequently there is
no noise budget that correctness depends on: the only quantity that grows under
evaluation is ciphertext size (edge count).

### The two channels

The whole system is organized around a split that
[`Octra.lean`](Octra/HFHE/Octra.lean) states outright:

| | **Value channel** | **Decoy channel** |
|---|---|---|
| role | correctness | security / hardness |
| visibility | key‑gated (needs secret mask `R`) | public, one‑way |
| behavior | exact, reproducible | never decoded |
| lifecycle | `balance → encrypt → decrypt → homAdd/Mul → recrypt` | `decoy = H‑syndrome → merge → recrypt(permute)` |

`decrypt` reads **only** the value channel; everything on the decoy side is
decode‑neutral. The novelty lives in the decoy channel; the value channel alone is "just"
an exact homomorphic encoding.

### The five keystones

The development is tagged with five significant results. The rest of this document is
their context.

| # | Claim | Headline theorem | Module |
|---|---|---|---|
| **#1** | a hypergraph syndrome **is** a linear‑code parity check | `hypergraph_syndrome_eq`, `syndrome_add` | [`Hypergraph/Incidence.lean`](Octra/Hypergraph/Incidence.lean), [`Coding/Syndrome.lean`](Octra/Coding/Syndrome.lean) |
| **#2** | decryption is **exact** | `encrypt_balanced_correct` | [`HFHE/Correctness.lean`](Octra/HFHE/Correctness.lean) |
| **#3** | add & multiply are **homomorphic** | `decrypt_homAdd`, `decrypt_homMul` | [`HFHE/Homomorphism.lean`](Octra/HFHE/Homomorphism.lean) |
| **#4** | confidentiality **reduces to LPN** (named dependency, *not* a proved reduction) | `confidentiality_trusted` | [`HFHE/Security.lean`](Octra/HFHE/Security.lean) |
| **#5** | inverting a decoy is **hard syndrome decoding** | `IsHypergraphDecodingSolution`, `decoyOf_zero_selection_unique` | [`HFHE/HyperDecoy.lean`](Octra/HFHE/HyperDecoy.lean) |

A discipline runs through all of it: **prove correctness exactly, axiomatize hardness.**
Keystones #2/#3 are unconditional theorems; #4/#5 bottom out in a cited LPN assumption.

---

## 1. The value channel (correctness)

### 1a. Encoding: edges and balancing

A decryptable ciphertext core is an
[`Encoding`](Octra/HFHE/Defs.lean): a list of [`Term`](Octra/HFHE/Defs.lean)s (the
C++ `Edge`) plus a constant `c0`. Each term contributes `±w · gⁱᵈˣ` and names a `layer`
whose secret mask is divided out at decrypt time.

To encode a value `v`, it is **balanced** into a set of signals that telescope back to `v`:
[`balance`](Octra/HFHE/Defs.lean). The key invariant is

- **`balance_telescopes`**: the balanced signal split sums back to the original value.
  - `sum of contributions(balance(v)) = v`

This is what makes the K‑edge spread decryptable without loss.

### 1b. Encryption / decryption: KEYSTONE #2

[`encrypt`](Octra/HFHE/Defs.lean) masks each signal with the secret
[`Mask`](Octra/HFHE/Defs.lean) `R` (the one invariant decryption needs: every entry is
nonzero, hence invertible). [`decrypt`](Octra/HFHE/Defs.lean) strips the mask back off.

Supporting lemmas → headline:

- **`decrypt_strip`**: decrypt divides the mask out cleanly.
  - `Dec(c) = c0 + sum of (±coef · g^idx)` (the masks cancel)
- **`encrypt_correct`**: a single masked signal round‑trips.
  - `if sum of contributions = v, then Dec(Enc(signals)) = v`
- **`encrypt_balanced_correct`**: the balanced K‑edge encryption decrypts
  to exactly `v`. Exact, over any field, no hypotheses.
  - `Dec(Enc(v)) = v`

### 1c. Homomorphism: KEYSTONE #3

Operating on ciphertexts operates on plaintexts, as an exact identity in 𝔽ₚ:

- **`decrypt_homAdd`**: addition (concatenate edge lists).
  - `Dec(A + B) = Dec(A) + Dec(B)`
- **`decrypt_homScale`**, **`decrypt_homNeg`**, **`decrypt_homSub`**: the linear ops.
  - `Dec(s · A) = s · Dec(A)`
  - `Dec(−A) = −Dec(A)`
  - `Dec(A − B) = Dec(A) − Dec(B)`
- **`decrypt_homMul`**: the product‑layer masks cancel algebraically
  (`R.prod_eq`), not by invertibility.
  - `Dec(A · B) = Dec(A) · Dec(B)`

Boolean gates ([`Gates.lean`](Octra/HFHE/Gates.lean)) are a direct corollary: `gAnd`,
`gOr`, `gNot`, `gXor`, `gNand`, all exact. On bit‑valued ciphertexts a gate decrypts to the
boolean gate of the bits:

- **`gAnd_bit`**: `Dec(AND(A, B)) = Dec(A) AND Dec(B)`
- **`gXor_bit`**: `Dec(XOR(A, B)) = Dec(A) XOR Dec(B)` (and likewise `gOr`, `gNot`, `gNand`)

### 1d. The deployed multiply: fold + repack

`homMul` above is the clean **value model** (the `prodEdge` outer product, `|a|·|b|` edges),
decrypt‑correct but quadratic. The **deployed** multiply
([`Repack.lean`](Octra/HFHE/Repack.lean)) avoids the blow‑up: it *folds* each layer to a
single wire value, multiplies the folds, and *re‑packs* each product into a **fixed‑width**
fresh edge set on a new PROD layer.

- **`decrypt_taggedMul`**: the deployed multiply decrypts identically to the value model.
  - `Dec(taggedMul(A, B)) = Dec(A) · Dec(B)`
- **`numEdges_taggedMul`**: a product is `width` edges per layer‑pair, not `|a|·|b|`.
  - `edges(taggedMul(A, B)) = width`

`Repack` bundles the re‑pack as an abstract recipe + a `telescopes` invariant (deferring the
sampling, as with `Mask`). The fresh per‑edge decoys are carried as data `pd`.

### 1e. Size growth (not noise)

[`Size.lean`](Octra/HFHE/Size.lean) tracks the *edge‑count* budget: the real cost axis,
since there is no decryption noise. The `numEdges_*` laws:

- add / sub: `edges(A + B) = edges(A) + edges(B)` (grows)
- scale / neg: `edges(s · A) = edges(A)` (flat)
- value‑model multiply: `≈ |a| · |b|` (quadratic)
- deployed multiply: `edges(taggedMul(A, B)) = width` (fixed)

**This is the same concern repack (§1d) and merge (§2c) exist to manage**; keep it in mind as
the through‑line connecting them.

---

## 2. The decoy channel (security)

### 2a. The decoy is a hypergraph syndrome: KEYSTONE #1

A [`Decoy ι := ι → ZMod 2`](Octra/HFHE/Decoy.lean) is a syndrome vector over 𝔽₂. Each
Octra edge carries one. [`decoyOf H x e`](Octra/HFHE/HyperDecoy.lean) builds it as
`H.syndrome x + e`: the public hypergraph `H` used as a **parity‑check matrix**.

Keystone #1 is the bridge that makes this rigorous: the combinatorial hypergraph syndrome
map *is* the linear‑code syndrome of the incidence matrix.

- **`hypergraph_syndrome_eq`**: the hypergraph syndrome is the incidence matrix applied as a
  parity check.
  - `Syndrome_H(x) = Incidence(H) · x`
- **`syndrome_add`**, **`syndrome_smul`**: the map is linear (a genuine parity check).
  - `Syndrome(x + y) = Syndrome(x) + Syndrome(y)`
  - `Syndrome(c · x) = c · Syndrome(x)`
- **`row_weight_uniform`**: a k‑uniform hypergraph gives a k‑regular parity check; this
  constant row weight is the hardness‑relevant structure.
  - `every row of Incidence(H) has exactly k ones`

### 2b. Why inverting a decoy is hard: KEYSTONE #5

Recovering the sparse selection `x` behind a decoy `σ` is a **syndrome‑decoding** instance:

- **`IsHypergraphDecodingSolution`** ([`Coding/Syndrome.lean`](Octra/Coding/Syndrome.lean)):
  the decoding predicate, a specialization of the abstract `IsSyndromeDecodingSolution`
  ([`Coding/LinearCode.lean`](Octra/Coding/LinearCode.lean)).
  - `x solves (H, σ, w)  ⟺  H · x = σ  and  weight(x) ≤ w`
- **`decoyOf_zero_solves`**: the planted `x` solves its own noiseless instance (existence).
  - `decoy = H · x  ⟹  x solves (H, decoy, w)` (when `weight(x) ≤ w`)
- **`decoyOf_zero_selection_unique`**: under a minimum‑distance hypothesis, `x` is the
  *unique* such solution (well‑posedness; from `eq_of_syndrome_eq_of_weight_le`, the
  classical `t = ⌊(d−1)/2⌋` unique‑decoding bound).
  - `H · x = H · x'  and both sparse  ⟹  x = x'`
- **`decoyOf_shipped_selection_unique`**: at Octra's shipped selection weight `xColWt` (= 128),
  the `≤ xColWt`-sparse selection behind a noiseless decoy is unique, given `d ≥ 2·xColWt + 1`.
  `xColWt` is a decoy/syndrome parameter, *not* the LPN PRF's `lpnNoise`.
  - `H · x = H · x'  and  weight(x), weight(x') ≤ xColWt  ⟹  x = x'`

> TODO: the uniqueness above is for the **noiseless** decoy (`e = 0`); the real
> `σ = H · x + e` (error weight `errWt` = 128) needs `d ≥ 2·(xColWt + errWt) + 1`, and its
> search/distinguishing hardness is unformalized. And the decoy's average‑case hardness
> (random k‑uniform syndrome decoding at the MIPT threshold) is a **cited assumption**, distinct
> from the LPN PRF axiom `lpn_hard` ([`Coding/LPN.lean`](Octra/Coding/LPN.lean)), which masks the
> value channel, not the decoy. Existence + uniqueness are geometry (proved here); both hardness
> questions are assumed.

### 2c. Merge: the one place the decoy is read

In isolation the decoy looks inert (decryption ignores it). [`Merge.lean`](Octra/HFHE/Merge.lean),
the C++ `reduction::merge` compaction, is where it becomes load‑bearing. Compaction
collapses edges sharing a position `(layer, idx, sign)` by summing weights and **XOR‑ing
decoys**, then keeps a slot iff *some weight is nonzero OR the decoy bit is set*.

- **`survives_zeroWeight`**: a value‑cancelled edge (`w = 0`, decryption‑neutral) **survives
  iff its decoy is nonzero**: a "ghost" edge.
  - `weight(e) = 0  ⟹  (e survives  ⟺  decoy(e) ≠ 0)`
- **`decrypt_prune`**: compaction preserves the decrypted value (dead/ghost edges add 0).
  - `Dec(prune(c)) = Dec(c)`
- **`eterm_combine`**: the additive collapse is decode‑faithful.
  - `contribution(merge(e1, e2)) = contribution(e1) + contribution(e2)`

The consequence: without the decoy, compaction would prune to exactly the nonzero‑value
positions, **leaking the value's support**. With it (σ‑density ≈ ½) a pseudorandom half of
cancelled positions survive too, masking which positions are value‑driven. Separating the
two would itself be syndrome decoding.
([`sigmaDensity`](Octra/HFHE/Cipher.lean) measures the decoy‑selector density.)

### 2d. Confidentiality dependency: KEYSTONE #4

[`Security.lean`](Octra/HFHE/Security.lean) names the single computational assumption:

- **`confidentialityAssumption`**: search‑LPN at Octra's parameters.
  - `the statement "LPN is hard at Octra's parameters"`
- **`confidentiality_trusted`**: it holds by `Coding.lpn_hard`.
  - `confidentialityAssumption  ⟸  lpn_hard` (discharged from the axiom)

> TODO: this names only the **LPN PRF** assumption (the value‑channel mask). The decoy's
> syndrome‑decoding hardness (§2b) is a *separate* cited assumption that `Security.lean` does
> not yet name, and there is no IND‑CPA reduction. Both are open items for the whitepaper.

---

## 3. Assembly

### 3a. The public ciphertext and the scheme facade

[`Cipher.lean`](Octra/HFHE/Cipher.lean) introduces the C++ vocabulary on top of the
neutral engine: the `Layer` DAG‑provenance, `Edge`, and the public
[`Cipher`](Octra/HFHE/Cipher.lean) `= Encoding + Layer[] + one decoy per edge`, plus the
linear Cipher ops (`taggedAdd`/`taggedScale`/`taggedNeg`/`taggedSub`). `Cipher` is the hinge
every Cipher‑level module imports.

[`Octra.lean`](Octra/HFHE/Octra.lean) is the facade. It defines the public/secret
boundary: [`PubKey`](Octra/HFHE/Octra.lean) (`g`, `ubk`), [`SecKey`](Octra/HFHE/Octra.lean)
(`mask`), [`Scheme`](Octra/HFHE/Octra.lean), generic over an abstract decoy index `ι`.
[`HyperDecoy.lean`](Octra/HFHE/HyperDecoy.lean) instantiates `ι := H.EdgeIdx` via
`schemeOf`, the step where the hypergraph enters the public key. **`schemeOf_plaintext`**
confirms the assembled instance still decrypts to `v`:

- `Dec(scheme) = v`

> Note `ubk : Equiv.Perm ι` (the public re‑randomizing permutation) is **always abstract**:
> every theorem holds for *all* permutations; the concrete shuffle is a keygen artifact.

### 3b. Recrypt = inject + permute + compact

[`Recrypt.lean`](Octra/HFHE/Recrypt.lean) is the scheme's "bootstrap", but since
decryption is exact there is no noise to refresh. Up to a capped number of rounds while the
decoy σ‑density is off ½, it:

1. **injects** a fresh `Enc(0)` from a zero‑pool: the *only* plaintext‑relevant step;
2. **permutes** every edge's decoy by `ubk`: decode‑neutral (decryption never reads decoys);
3. **compacts**: i.e. **merge** (§2c), the size axis.

So **merge enters recrypt as step 3**, and **repack does not enter recrypt at all**: repack
is the multiply (§1d). Both are size‑control, but at different operations.

- **`decrypt_recrypt`** (engine level): each injected `Enc(0)` adds 0, so the plaintext is
  preserved.
  - `if each z decrypts to 0, then Dec(recrypt(zs, c)) = Dec(c)`
- **`decrypt_recryptLoop`** (cipher level): the full inject+permute loop preserves the
  plaintext for **any** schedule.
  - `Dec(recryptLoop(zs, c)) = Dec(c)`

> The density‑→½ effect is an **unproven statistical assumption** (the band/cap are runtime
> heuristics); correctness never depends on it.

---

## Appendix: module dependency sketch

```
Field127 ─┐
          │   Hypergraph/Basic ── Incidence (#1) ─┐
          │                                        ├─ Coding/Syndrome ─┐
          │   Coding/LinearCode ── Coding/LPN ─────┘                   │
          │                                                            │
HFHE/Defs ─ Correctness (#2) ─ Homomorphism (#3) ─ Gates               │
   │                                                                   │
   └─ Cipher ─┬─ Repack (mul)                                          │
              ├─ Merge (compaction + decoy)                            │
              ├─ Recrypt (refresh)                                     │
              ├─ Decoy ── HyperDecoy (#5, decoy = H‑syndrome) ─────────┘
              └─ Octra (Scheme facade) ─ Security (#4)
```

Read order for a newcomer: **0 → §1 (value, intuitive, self‑contained) → §2 (decoy, the
security half) → §3 (assembly)**. The hardness substrate (Hypergraph/Coding/LPN) is best
read *when §2 motivates it*, not first.
