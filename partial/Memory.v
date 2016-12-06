Module Type Memory.

Parameter adr : Set.

Parameter first : adr.
Parameter next : adr -> adr.



Parameter Mem : Type -> Type.

Parameter empty : forall {T}, Mem T.
Parameter get : forall {T}, adr -> Mem T -> T.
Parameter set : forall {T}, adr -> T -> Mem T -> Mem T.
Parameter free : forall {T}, adr -> Mem T -> Mem T.
Parameter freeFrom : forall {T}, adr -> Mem T -> Prop.

Axiom freeFrom_free : forall T (r : adr) (m : Mem T) (n : T), freeFrom r m -> free r (set r n m) = m.

Axiom freeFrom_set : forall T (r : adr) (m : Mem T) (n : T), freeFrom r m  ->  freeFrom (next r) (set r n m).

Axiom get_set : forall T (r : adr) (m : Mem T) (n : T), get r (set r n m) = n.

Axiom freeFrom_first : forall T, freeFrom first (@empty T).




End Memory.