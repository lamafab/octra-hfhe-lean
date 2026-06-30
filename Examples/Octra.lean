import Octra.HFHE.HyperDecoy
import Examples.Field7
import Mathlib.Tactic

-- ============================================================================
-- Examples: encrypting with Octra  (Signals + decoys, end to end)
-- ============================================================================
--
-- One story: build a real ciphertext FROM SCRATCH and recover the plaintext.
-- Two worlds meet here without entangling, and we walk each one by hand:
--   * VALUE side (hypergraph-free): honest `Signal`s → `balance` → `encrypt` →
--     `decrypt`.  This is what actually hides `v`: carrier positions + secret mask.
--   * DECOY side (the hypergraph enters HERE): a column selection `xsel` over `H`,
--     turned into a per-edge syndrome `decoyOf H xsel = H.incidence · xsel` (SPEC §4).
--
-- Then `encryptH` glues the two into the public ciphertext.  The punchline: gluing
-- changes NOTHING the secret-key holder sees: decrypt still returns `v`, and the
-- attached decoy is exactly the hypergraph syndrome.  Decryption never reads a decoy,
-- so the value correctness and the hardness wiring stay completely separate.
--
-- (The cipher-level homomorphisms live in `Examples/Cipher.lean`; the abstract
-- decoy ↔ syndrome-decoding bridge is `Examples/LinearCoding.lean`.)

namespace Examples.Octra

open Octra.HFHE Examples.Field7 Hypergraph Octra.Coding

/-- The shared worked hypergraph, used here as the public parity-check. -/
abbrev H : Hypergraph (Fin 4) := Hypergraph.example1

-- ----------------------------------------------------------------------------
-- (1) VALUE SIDE: a real multi-edge ciphertext, built from honest `Signal`s
-- ----------------------------------------------------------------------------
--   A `Signal` is one unmasked edge contributing `±coef·gⁱᵈˣ`.  We pick ONE free
--   signal, then `balance` APPENDS a second whose coefficient is solved so the pair
--   telescopes to `v` BY CONSTRUCTION (SPEC §3, "last coeff solved").  `encrypt`
--   then masks every signal by `R 0`.  Nothing here knows about the hypergraph.

/-- One freely-chosen signal edge: `+⟨2,1⟩` at carrier position `0`. -/
def free : Signal 2 𝔽₇ := { idx := 0, sign := true, coef := ![2, 1] }

/-- The masked value ciphertext of `v = ⟨5,4⟩`: `balance` solves the final
    coefficient at position `1`, `encrypt` masks each signal by `R 0`.  Two edges,
    `c0 = 0`, a genuine multi-edge encryption, not the transparent `encrypt1`. -/
def Cval : Encoding 2 𝔽₇ := encrypt R (balance g [free] 1 v)

-- it really has TWO edges: the free one plus the solved balancing one.
example : Cval.edges.length = 2 := by native_decide

-- what travels on the wire is the MASKED weight `coef · R 0`, NEVER the plaintext
-- ⟨5,4⟩; neither edge on its own reveals anything.
example : Cval.edges.map (fun e => (e.w 0, e.w 1)) = [(4, 4), (2, 4)] := by native_decide

-- DECRYPT strips the mask and re-applies the carrier, recovering `v` EXACTLY,
-- and it's no accident: this is `encrypt_balanced_correct` (the telescoping lemma).
example : ∀ j, decrypt g R Cval j = v j :=
  fun j => encrypt_balanced_correct g R [free] 1 v j (by decide)

-- ----------------------------------------------------------------------------
-- (2) DECOY SIDE: the hypergraph enters as a parity check
-- ----------------------------------------------------------------------------
--   `xsel` selects columns {v₀, v₁}; its decoy is the syndrome `H·xsel`: sum the
--   selected columns mod 2:  e₁: 1+1 = 0,  e₂: 0+1 = 1,  e₃: 1+0 = 1  →  ⟨0,1,1⟩.

/-- The column-selection `x = {v₀, v₁}` over `H` (a 0/1 vector over 𝔽₂). -/
def xsel : H.VertIdx → ZMod 2 :=
  fun w => if (w : Fin 4) = 0 ∨ (w : Fin 4) = 1 then 1 else 0

-- the decoy IS the incidence matrix applied to `xsel` (+ 0 error): "convert the
-- hypergraph to a matrix, then multiply" made literal (`rfl`-deep, keystone #1).
example : decoyOf H xsel 0 = (H.incidence (ZMod 2)).mulVec xsel + 0 :=
  decoyOf_eq_mulVec H xsel 0

-- …and that syndrome has popcount 2, computed on the real incidence matrix.
example : decoyWeight (decoyOf H xsel 0) = 2 := by native_decide

-- ----------------------------------------------------------------------------
-- (3) ASSEMBLE: `encryptH` glues the value side to a per-edge decoy
-- ----------------------------------------------------------------------------
--   Same `Signal`s as (1) (`free := [free]`), every edge decoyed by `xsel`'s
--   syndrome.  The two sides never touch: `decrypt` reads only `.enc`.

/-- The unified PUBLIC ciphertext: value `⟨5,4⟩` from real Signals, with every edge
    decoyed by the `H`-syndrome of `xsel`. -/
def C : Cipher 2 H.EdgeIdx 𝔽₇ :=
  encryptH H g R [free] 1 v (fun _ => xsel) (fun _ => 0)

-- the VALUE side still decrypts EXACTLY to `v`; the decoys ride along untouched.
example : ∀ j, decrypt g R C.enc j = v j :=
  fun j => encryptH_plaintext H g R [free] 1 v _ _ j (by decide)

-- the DECOY attached to edge 0 IS that hypergraph syndrome, by construction.
example (h : 0 < C.enc.edges.length) :
    C.decoys[0]'(by rw [C.aligned]; exact h) = decoyOf H xsel 0 :=
  encryptH_decoy H g R [free] 1 v (fun _ => xsel) (fun _ => 0) 0 h

end Examples.Octra
