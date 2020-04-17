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
Declare Scope memory_scope.
Notation "m ⊑ m'" := (memle m m') (at level 70) : memory_scope.
Open Scope memory_scope.
Notation "m ⊒ m'" := (m' ⊑ m) (at level 70) : memory_scope.
Notation "m [ r ] = v" := (get r m = Some v) (at level 70).
Notation "m [ r := v ]" := (set r v m) (at level 70).


(* Property 1 *)
Axiom empty_mem_free : forall T, freeFrom first (@empty T). 

(* Property 2 *)

Axiom get_set : forall T (r : Reg) (v : T) (m :  Mem T),
    get r (set r v m) = Some v.

(* Property 3 *)

Axiom memle_set : forall {T} (m : Mem T) r v, freeFrom r m -> m ⊑ set r v m.

(* Property 4 *)

Axiom freeFrom_set : forall {T} r (v : T) m, freeFrom r m ->  freeFrom (next r) (set r v m).

(* Property 5 *)

Axiom memle_refl : forall {T} (m : Mem T), m ⊑ m.
Axiom memle_trans : forall {T} (m m' u : Mem T), m ⊑ m' -> m' ⊑ u -> m ⊑ u.

(* Property 6 *)

Axiom set_monotone : forall {T} (m m' : Mem T) r v, m ⊑ m' -> set r v m ⊑ set r v m' .

(* Property 7 *)

Axiom memle_get : forall {T} (m m' : Mem T) r v, m ⊑ m' -> get r m = Some v -> get r m' = Some v.


Hint Resolve memle_set memle_get memle_refl set_monotone memle_trans freeFrom_set empty_mem_free : memory.
End Memory.


Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed.


(* Additional axioms not used in the paper. *)
Module Type MAxioms (Import mem: Memory).
  Axiom set_set : forall T (r : Reg) (v v' : T) (m :  Mem T),
    set r v (set r v' m) = set r v m.
  
  Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto].
End MAxioms.

Module Type SetMem := Memory <+ MAxioms.

(* Extends the memory type with a truncation operation for proper
modelling of stack frames. *)
Module Type Truncate (Import mem:Memory).
Parameter truncate : forall {T}, Reg -> Mem T -> Mem T.

Axiom truncate_monotone : forall {T} (m m' : Mem T) r, m ⊑ m' -> truncate r m ⊑ truncate r m'.
Axiom truncate_set : forall {T} (m : Mem T) v r , freeFrom r m -> truncate r (set r v m) = m.

Hint Resolve truncate_monotone truncate_set : memory.

End Truncate.

Module Type TruncMem := SetMem <+ Truncate.
