/-
# Octra: PVAC-HFHE, formalized in Lean 4

Root module: importing this builds the entire library.
-/

-- Field 𝔽ₚ, p = 2^127 − 1
import Octra.Field127

-- Hypergraphs ↔ parity-check incidence
import Octra.Hypergraph.Basic
import Octra.Hypergraph.Incidence
import Octra.Hypergraph.LogicGates

-- Coding: linear codes, syndromes, LPN
import Octra.Coding.LinearCode
import Octra.Coding.Syndrome
import Octra.Coding.LPN

-- HFHE engine: defs, exact decryption, homomorphism, gates, size growth
import Octra.HFHE.Defs
import Octra.HFHE.Correctness
import Octra.HFHE.Homomorphism
import Octra.HFHE.Size
import Octra.HFHE.Recrypt
import Octra.HFHE.Gates

-- HFHE: full cipher, decoys/ghosts, compaction, hardness assumptions
import Octra.HFHE.Decoy
import Octra.HFHE.Cipher
import Octra.HFHE.Repack
import Octra.HFHE.Octra
import Octra.HFHE.HyperDecoy
import Octra.HFHE.Merge
import Octra.HFHE.Security
