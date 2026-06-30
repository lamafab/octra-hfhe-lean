import Octra.Hypergraph.Basic
import Mathlib.Tactic

-- ============================================================================
-- Logic Gates on Hyperedges
-- ============================================================================
--
-- Fix a hypergraph H = (V, E). A hyperedge is the set of vertices it
-- "activates" (v active ⇔ v ∈ e; see `Active`/`Inactive` in Basic.lean). The
-- Octra gates combine hyperedges vertex-by-vertex. Intersection and union need
-- no extra data, but the bar \overline{·} (inactivity) is exactly H's set of
-- inactive vertices:
--
--     \overline{e} = H.inactive e = H.vertices \ e     (vertices OF H not in e)
--
-- So the complement's universe is H.vertices, not the whole type. Consequently
-- every gate lands back inside H.vertices, i.e. produces a genuine hyperedge of
-- H (Section 0).

namespace Hypergraph.Gate

variable {V : Type*} [DecidableEq V]

-- Logic Gates implemented according to https://docs.octra.org/tech-docs/hfhe

-- AND: the intersection of two hyperedges, creating a new hyperedge that is
-- active only when both original hyperedges are active.
--     e_{and}(H) = e₁(H) ∩ e₂(H)
def and (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.active (e₁ ∩ e₂)

-- OR: a union of hyperedges, where a new hyperedge is active if at least one
-- of the original hyperedges is active.
--     e_{or}(H) = e₁(H) ∪ e₂(H)
def or (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.active (e₁ ∪ e₂)

-- NOT: inverting a hyperedge: a new hyperedge becomes active when the original
-- one is inactive.
--     e_{not}(H) = \overline{e(H)}
def not  (H : Hypergraph V) (e : Finset V) : Finset V := H.inactive e

-- NAND: a mix of _and_ and _not_ operations, with the nand hyperedge active
-- when the and hyperedge is inactive.
--     e_{nand}(H) = \overline{e₁(H) ∩ e₂(H)}
def nand (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.inactive (e₁ ∩ e₂)

-- NOR: the union of _or_ and _not_ activates the _nor_ hyperedge when the _or_
-- hyperedge is inactive.
--     e_{nor}(H) = \overline{e₁(H) ∪ e₂(H)}
def nor  (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V := H.inactive (e₁ ∪ e₂)

-- XOR: the combination of two hyperedges, `and` and `or`, is activated only
-- when only one of the original hyperedges is active.
--     e_{xor}(H) = (e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}
def xor  (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V :=
  (e₁ ∪ e₂) ∩ H.inactive (e₁ ∩ e₂)

-- XNOR: integration of `xor` and `not` operations, where the `xnor` hyperedge
-- is active when the `xor` hyperedge becomes inactive.
--     e_{xnor}(H) = \overline{(e₁(H) ∪ e₂(H)) ∩ \overline{(e₁(H) ∩ e₂(H))}}
def xnor (H : Hypergraph V) (e₁ e₂ : Finset V) : Finset V :=
  H.inactive ((e₁ ∪ e₂) ∩ H.inactive (e₁ ∩ e₂))

variable (H : Hypergraph V)

-- ============================================================================
-- Section 0: Every gate yields a hyperedge of H (a subset of H.vertices)
-- ============================================================================
--
-- This is what "explicit for H" buys us: the gates are closed on H's edges.
-- (AND/OR need the inputs to be edges of H; the complement-based ones land in
-- H.vertices unconditionally.)

theorem and_subset  (e₁ e₂ : Finset V) : and H e₁ e₂  ⊆ H.vertices := H.active_subset _
theorem or_subset   (e₁ e₂ : Finset V) : or H e₁ e₂   ⊆ H.vertices := H.active_subset _
theorem not_subset  (e : Finset V)     : not  H e     ⊆ H.vertices := H.inactive_subset _
theorem nand_subset (e₁ e₂ : Finset V) : nand H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem nor_subset  (e₁ e₂ : Finset V) : nor  H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem xnor_subset (e₁ e₂ : Finset V) : xnor H e₁ e₂ ⊆ H.vertices := H.inactive_subset _
theorem xor_subset  (e₁ e₂ : Finset V) : xor  H e₁ e₂ ⊆ H.vertices :=
  Finset.inter_subset_right.trans (H.inactive_subset _)

-- ============================================================================
-- Section 1: The "N" gates are the negations of their bases (by definition)
-- ============================================================================

theorem nand_eq_not_and (e₁ e₂ : Finset V) : nand H e₁ e₂ = not H (and H e₁ e₂) := by
  ext v; simp only [nand, not, and, active, inactive, Finset.mem_sdiff, Finset.mem_inter]; tauto
theorem nor_eq_not_or   (e₁ e₂ : Finset V) : nor  H e₁ e₂ = not H (or  H e₁ e₂) := by
  ext v; simp only [nor, not, or, active, inactive, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto
theorem xnor_eq_not_xor (e₁ e₂ : Finset V) : xnor H e₁ e₂ = not H (xor H e₁ e₂) := rfl

-- ============================================================================
-- Section 2: De Morgan: NAND is an OR of NOTs, NOR is an AND of NOTs
-- ============================================================================

theorem nand_eq_or_not (e₁ e₂ : Finset V) : nand H e₁ e₂ = or H (not H e₁) (not H e₂) := by
  ext v; simp only [nand, or, not, active, inactive, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto

theorem nor_eq_and_not (e₁ e₂ : Finset V) : nor H e₁ e₂ = and H (not H e₁) (not H e₂) := by
  ext v; simp only [nor, and, not, active, inactive, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]; tauto

-- NOT is an involution, but only for genuine hyperedges of H (e ⊆ H.vertices);
-- this is exactly where the complement's universe matters.
theorem not_not (e : Finset V) (he : e ⊆ H.vertices) : not H (not H e) = e := by
  ext v
  simp only [not, inactive, Finset.mem_sdiff]
  refine ⟨fun h => ?_, fun hv => ⟨he hv, fun h => h.2 hv⟩⟩
  by_contra hv
  exact h.2 ⟨h.1, hv⟩

-- ============================================================================
-- Section 3: Truth-table semantics: which vertices each gate activates
-- ============================================================================
--
-- Note the explicit `v ∈ H.vertices`: a vertex outside H is never activated by
-- a complement-based gate, since the complement only ranges over H.vertices.

theorem mem_xor (e₁ e₂ : Finset V) (v : V) :
    v ∈ xor H e₁ e₂ ↔
      v ∈ H.vertices ∧ ((Active e₁ v ∧ ¬ Active e₂ v) ∨ (¬ Active e₁ v ∧ Active e₂ v)) := by
  simp only [xor, inactive, Active, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]; tauto

theorem mem_xnor (e₁ e₂ : Finset V) (v : V) :
    v ∈ xnor H e₁ e₂ ↔ v ∈ H.vertices ∧ (Active e₁ v ↔ Active e₂ v) := by
  simp only [xnor, inactive, Active, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]; tauto

-- ============================================================================
-- Section 4: A worked example over a hypergraph whose vertices are a PROPER
-- subset of the type, so "within H" is visible
-- ============================================================================
--
-- H has vertices {0, 1, 2} (NOT vertex 3) and edges e₁ = {0, 1}, e₂ = {1, 2}.
-- Complements are taken within {0, 1, 2}, so vertex 3 never appears, unlike a
-- whole-type complement, which would also drag in 3.

-- First, see that the TYPE `Fin 4` has four inhabitants: its `univ` is {0,1,2,3}.
-- So a *whole-type* complement (`ᶜ`, taken over `univ`) of {0,1} keeps vertex 3:
-- this is the spurious 3 we want to avoid:
example : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
example : ({0, 1} : Finset (Fin 4))ᶜ     = {2, 3}       := by decide  -- drags in 3

-- The hypergraph below fixes its universe to {0,1,2}, so `not exampleH {0,1}` is
-- {2}, not {2,3}: vertex 3 is outside H and simply never enters the picture.

def exampleH : Hypergraph (Fin 4) where
  vertices     := {0, 1, 2}
  edges        := {{0, 1}, {1, 2}}
  mem_vertices := by decide

example : and  exampleH {0, 1} {1, 2} = {1}                        := by decide
example : or   exampleH {0, 1} {1, 2} = {0, 1, 2}                  := by decide
example : not  exampleH {0, 1}        = ({2}     : Finset (Fin 4)) := by decide  -- not {2,3}!
example : nand exampleH {0, 1} {1, 2} = ({0, 2}  : Finset (Fin 4)) := by decide
example : nor  exampleH {0, 1} {1, 2} = (∅       : Finset (Fin 4)) := by decide
example : xor  exampleH {0, 1} {1, 2} = ({0, 2}  : Finset (Fin 4)) := by decide
example : xnor exampleH {0, 1} {1, 2} = ({1}     : Finset (Fin 4)) := by decide

end Hypergraph.Gate

-- TODO: Create file on "modular arithmetic over hypergraphs in HFHE"

-- ## modular arithmetic operations

-- addition:
--   (a + b) mod n
-- where a and b are integers, and n is the modulus.


-- remainder calculation:
--   x mod n
-- where x is an integer, and n is the modulus.

-- ## homomorphic addition of encrypted numbers

-- encrypted addition:
--   (c1, c2, n) = (c1 * c2) mod (n * n)
-- where c1 and c2 are encrypted numbers, and n is the modulus.

-- ## encryption and decryption operations

-- encryption:
--   (m, (n, g)) = (g^m * r^n) mod (n * n)
-- where m is the message, (n, g) is the public key, and r is a
-- random value.

-- decryption:
--   (c, (n, _), (λ, µ)) = ((c^{λ} - 1)/n) * µ mod n
-- where c is the encrypted message, (n, _) is the public key,
-- and (λ, μ) is the private key.

-- ## type analysis for hyperedge operation (OCaml)

-- > this is useful for ensuring the correctness of operations
-- > on hypergraphs and preventing type-related errors in the code.

-- determine the type of a hyperedge operation, which can be int,
-- uint or func based on the analysis performed.

/-
```
open Octra.Z

module Variable = struct
  type t = string
  module Map = struct
    include Map.Make(String)
    let of_list bindings =
        List.fold_left (fun acc (k,v) -> add k v acc) empty bindings
  end
end

module TypeExpr = struct
  type t = IntType | UnitType | ArrType of t * t

  let rec eq t1 t2 =
    match t1, t2 with
    | UnitType, UnitType -> true
    | IntType, IntType -> true
    | ArrType(l1, r1), ArrType(l2, r2) -> eq l1 l2 && eq r1 r2
    | _ -> false
end

module Expression = struct
  type t =
    | VarExpr of Variable.t
    | AbsExpr of Variable.t * t
    | AppExpr of t * t
    | AnnExpr of t * TypeExpr.t
    | IntExpr of int
    | UnitExpr

  let rec synthesize expression ~env =
    match expression with
    | UnitExpr -> Some(TypeExpr.UnitType)
    | IntExpr _ -> Some(TypeExpr.IntType)
    | VarExpr var -> Variable.Map.find_opt var env
    | AnnExpr(e, ty) ->
        let env' = Variable.Map.empty in
        check e ~env:env' ~against:ty
    | AppExpr(e1, e2) ->
        (match synthesize e1 ~env with
        | Some TypeExpr.ArrType(a, b) ->
            (match check e2 ~env ~against:a with
            | Some _ -> Some b
            | _ -> None)
        | _ -> None)
    | AbsExpr(x, e) ->
        let env' = Variable.Map.add x (TypeExpr.UnitType) env in
        (match synthesize e ~env:env' with
        | Some ty -> Some (TypeExpr.ArrType(TypeExpr.UnitType, ty))
        | _  -> None)

  and check expression ~env ~against =
    match expression, against with
    | e, ty ->
        (match synthesize e ~env with
        | Some ty' when TypeExpr.eq ty' against -> Some ty
        | _ -> None)
end

type vertex = int
type hyperedge = { vertices: vertex list; weight: Z.t }
type hypergraph = hyperedge list

let encrypt m (n, g) =
  let lower = Z.one in
  let upper = Z.pred n in
  let diff = Z.sub upper lower in
  let r = Z.add lower (Z.rem (Z.of_int (Random.State.bits (Random.get_state ()))) diff) in
  let gm = Z.powm g m (Z.mul n n) in
  let rn = Z.powm r n (Z.mul n n) in
  Z.rem (Z.mul gm rn) (Z.mul n n)

let decrypt c (n, _) (lambda, mu) =
  let cl = Z.powm c lambda (Z.mul n n) in
  let l x = Z.div (Z.sub x Z.one) n in
  Z.rem (Z.mul (l cl) mu) n

let encrypted_add c1 c2 n =
  Z.rem (Z.mul c1 c2) (Z.mul n n)

let generate_keys () =
  let p = Z.of_int 61 in
  let q = Z.of_int 53 in
  let n = Z.mul p q in
  let lambda = Z.lcm (Z.pred p) (Z.pred q) in
  let g = Z.succ n in
  let mu = Z.invert lambda n in
  ((n, g), (lambda, mu))

let create_hyperedge m public_key =
  [encrypt m public_key]

let add_hyperedges he1 he2 public_key =
  if List.length he1 <> 1 || List.length he2 <> 1 then
    failwith "Hyperedges must contain only one encrypted number each"
  else
    let c1 = List.hd he1 in
    let c2 = List.hd he2 in
    let n = fst public_key in
    [encrypted_add c1 c2 n]

let analyze_hypergraph_operation a_hyperedge b_hyperedge =
  let open Expression in
  let env = Variable.Map.of_list [("encrypted_add", TypeExpr.ArrType(TypeExpr.IntType, TypeExpr.ArrType(TypeExpr.IntType, TypeExpr.IntType)))] in
  let add_expr = VarExpr "encrypted_add" in
  let a_expr = IntExpr 0 in
  let b_expr = IntExpr 1 in
  let operation_expr = AppExpr(AppExpr(add_expr, a_expr), b_expr) in
  match synthesize operation_expr ~env with
  | Some ty -> Printf.printf "Type of hyperedge operation: %s\n" (match ty with
                                                                  | TypeExpr.IntType -> "Integer"
                                                                  | TypeExpr.UnitType -> "Unit"
                                                                  | TypeExpr.ArrType(_, _) -> "Function")
  | None -> Printf.printf "Type of hyperedge operation could not be determined\n"

let () =
  Random.self_init ();
  let public_key, private_key = generate_keys () in
  let a = Z.of_int 111 in
  let b = Z.of_int 222 in

  let a_hyperedge = create_hyperedge a public_key in
  let b_hyperedge = create_hyperedge b public_key in

  let sum_hyperedge = add_hyperedges a_hyperedge b_hyperedge public_key in
  let decrypted_sum_hyperedge = List.map (fun c -> decrypt c public_key private_key) sum_hyperedge in

  Printf.printf "Encrypted Hyperedge A: %s\n" (Z.to_string (List.hd a_hyperedge));
  Printf.printf "Encrypted Hyperedge B: %s\n" (Z.to_string (List.hd b_hyperedge));
  Printf.printf "Encrypted Sum Hyperedge: %s\n" (Z.to_string (List.hd sum_hyperedge));
  Printf.printf "Decrypted Sum Hyperedge: %s\n" (Z.to_string (List.hd decrypted_sum_hyperedge));

  analyze_hypergraph_operation [List.hd a_hyperedge] [List.hd b_hyperedge];
```
-/
