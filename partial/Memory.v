(* Abstract specification of memory *)

Create HintDb memory.

Module Type Memory.

(* Types *)
Parameter Reg : Set.
Parameter Mem : Type -> Type.

(* Operations *)
Parameter empty : forall {T}, Mem T.
Parameter set : forall {T}, Reg -> T -> Mem T -> Mem T.
Parameter get : forall {T}, Reg -> Mem T -> option T.
Parameter first : Reg.
Parameter next : Reg -> Reg.

(* Predicates *)
Parameter freeFrom : forall {T}, Reg -> Mem T -> Prop.
Parameter memle : forall {T}, Mem T -> Mem T -> Prop.

(* Notations *)
Notation "s ≤ t" := (memle s t) (at level 70) : memory_scope.
Open Scope memory_scope.
Notation "s ≥ t" := (t ≤ s) (at level 70) : memory_scope.
Notation "s [ r ] = v" := (get r s = Some v) (at level 70).
Notation "s [ r := v ]" := (set r v s) (at level 70).


(* Property 1 *)
Axiom empty_mem_free : forall T, freeFrom first (@empty T). 

(* Property 2 *)

Axiom get_set : forall T (r : Reg) (v : T) (s :  Mem T),
    get r (set r v s) = Some v.

(* Property 3 *)

Axiom memle_set : forall {T} (s : Mem T) r v, freeFrom r s -> s ≤ set r v s.

(* Property 4 *)

Axiom freeFrom_set : forall {T} r (v : T) s, freeFrom r s ->  freeFrom (next r) (set r v s).

(* Property 5 *)

Axiom memle_refl : forall {T} (s : Mem T), s ≤ s.
Axiom memle_trans : forall {T} (s t u : Mem T), s ≤ t -> t ≤ u -> s ≤ u.

(* Property 6 *)

Axiom set_monotone : forall {T} (s t : Mem T) r v, s ≤ t -> set r v s ≤ set r v t .

(* Property 7 *)

Axiom memle_get : forall {T} (s t : Mem T) r v, s ≤ t -> get r s = Some v -> get r t = Some v.


Hint Resolve memle_set memle_get memle_refl set_monotone memle_trans freeFrom_set empty_mem_free : memory.
End Memory.


Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed.


(* Additional axioms not used in the paper. *)
Module Type MAxioms (Import mem: Memory).
  Axiom set_set : forall T (r : Reg) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
  
  Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto].
End MAxioms.

Module Type SetMem := Memory <+ MAxioms.

(* Extends the memory type with a truncation operation for proper
modelling of stack frames. *)
Module Type Truncate (Import mem:Memory).
Parameter truncate : forall {T}, Reg -> Mem T -> Mem T.

Axiom truncate_monotone : forall {T} (s t : Mem T) r, s ≤ t -> truncate r s ≤ truncate r t.
Axiom truncate_set : forall {T} (s : Mem T) v r , freeFrom r s -> truncate r (set r v s) = s.

Hint Resolve truncate_monotone truncate_set : memory.

End Truncate.

Module Type TruncMem := SetMem <+ Truncate.
