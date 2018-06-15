(* Abstract specification of memory *)

Create HintDb memory.


Module Type Memory.

Parameter adr : Set.

Parameter adr0 : adr.
Parameter next : adr -> adr.

Parameter Mem : Type -> Type.


Parameter get : forall {T}, adr -> Mem T -> option T.
Parameter set : forall {T}, adr -> T -> Mem T -> Mem T.

Parameter freeFrom : forall {T}, adr -> Mem T -> Prop.
Parameter memle : forall {T}, Mem T -> Mem T -> Prop.


Notation "s ≤ t" := (memle s t) (at level 70) : memory_scope.
Open Scope memory_scope.
Notation "s ≥ t" := (t ≤ s) (at level 70) : memory_scope.


Axiom get_set : forall T (r : adr) (v : T) (s :  Mem T),
    get r (set r v s) = Some v.

Axiom set_set : forall T (r : adr) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.

Axiom freeFrom_set : forall {T} r (v : T) s, freeFrom r s ->  freeFrom (next r) (set r v s).


Axiom memle_refl : forall {T} (s : Mem T), s ≤ s.
Axiom memle_trans : forall {T} (s t u : Mem T), s ≤ t -> t ≤ u -> s ≤ u.


Axiom memle_set : forall {T} (s : Mem T) r v, freeFrom r s -> s ≤ set r v s.
Axiom memle_get : forall {T} (s t : Mem T) r v, s ≤ t -> get r s = v -> get r t = v.
Axiom set_monotone : forall {T} (s t : Mem T) r v, s ≤ t -> set r v s ≤ set r v t .


Notation "s [ r ] = v" := (get r s = Some v) (at level 70).
Notation "s [ r := v ]" := (set r v s) (at level 70).


Hint Resolve memle_set memle_get memle_refl set_monotone memle_trans freeFrom_set : memory.

End Memory.



Module Type Empty (Import mem:Memory).

Parameter empty_mem : forall T, Mem T.
Axiom empty_mem_free : forall T, freeFrom adr0 (empty_mem T).

Hint Resolve empty_mem_free : memory.

End Empty.

Module Type EmptyMem := Memory <+ Empty.




Module Type Truncate (Import mem:Memory).

Parameter truncate : forall {T}, adr -> Mem T -> Mem T.

Axiom truncate_monotone : forall {T} (s t : Mem T) r, s ≤ t -> truncate r s ≤ truncate r t.
Axiom truncate_set : forall {T} (s : Mem T) v r , freeFrom r s -> truncate r (set r v s) = s.

Hint Resolve truncate_monotone truncate_set : memory.

End Truncate.

Module Type TruncMem := EmptyMem <+ Truncate.
