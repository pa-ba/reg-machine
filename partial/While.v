(** Calculation for a language with state and while loops. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module While (Import mem : Memory).

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Get : Expr
| Put : Expr -> Expr -> Expr
| While : Expr -> Expr -> Expr.

Definition State := nat.
Definition Value := nat.

Reserved Notation "⟪ x , q ⟫ ⇓ ⟪ y , q' ⟫" (at level 80, no associativity).

Inductive eval : Expr -> State -> Value -> State -> Prop :=
| eval_val  n q : ⟪Val n, q⟫ ⇓ ⟪n, q⟫
| eval_add q q' q'' x y m n : ⟪x, q⟫ ⇓ ⟪m,q'⟫ -> ⟪y,q'⟫ ⇓ ⟪n, q''⟫ -> ⟪Add x y, q⟫ ⇓ ⟪m + n, q''⟫
| eval_get  q : ⟪Get, q⟫ ⇓ ⟪q, q⟫
| eval_put  q q' q'' v n x y : ⟪x, q⟫ ⇓ ⟪n,q'⟫ -> ⟪y, n⟫ ⇓ ⟪v, q''⟫ -> ⟪Put x y , q⟫ ⇓ ⟪v,q''⟫
| eval_step x y q n m q' q'' v q''':
    ⟪x, q⟫ ⇓ ⟪n,q'⟫ ->
    n <> 0 -> ⟪y,q'⟫ ⇓ ⟪m,q''⟫ -> ⟪While x y, q''⟫ ⇓ ⟪v,q'''⟫ ->
    ⟪While x y, q⟫ ⇓ ⟪v,q'''⟫
| eval_while_stop x y q n q' :
    ⟪x, q⟫ ⇓ ⟪n,q'⟫ ->
    n = 0 ->
    ⟪While x y, q⟫ ⇓ ⟪0,q'⟫
where "⟪ x , q ⟫ ⇓ ⟪ y , q' ⟫" := (eval x q y q').



(* Inductive eval : (Expr * State) -> (Value * State) -> Prop := *)
(* | eval_val  n q : (Val n, q) ⇓ (n, q) *)
(* | eval_add q q' q'' x y m n : (x, q) ⇓ (m,q') -> (y,q') ⇓ (n, q'') -> (Add x y, q) ⇓ (m + n, q'') *)
(* | eval_while x y q q' n r : (x, q) ⇓ (n,q') -> evalW n x y q r -> (While x y, q) ⇓ r *)
(* | eval_get  q : (Get, q) ⇓ (q, q) *)
(* | eval_put  q q' r n x y : (x, q) ⇓ (n,q') -> (y, n) ⇓ r -> (Put x y , q) ⇓ r *)
(* where "x ⇓ y" := (eval x y) *)

(* with evalW : Value -> Expr -> Expr -> State -> (Value * State) -> Prop := *)
(*      | evalW_zero x y q : evalW 0 x y q (0,q) *)
(*      | evalW_step x y q q' n m r : n > 0 -> (y,q) ⇓ (m,q') -> (While x y, q') ⇓ r -> evalW n x y q r *)
(* . *)

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| GET : Code -> Code                           
| JUMP : adr -> Code
| JMPZ : Code -> Code -> Code
| LABEL : adr -> Code -> Code
| PUT : Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (r : adr) (c : Code) : Code :=
  match e with
    | Val n => LOAD n c
    | Add x y => comp' x r (STORE r (comp' y (next r) (ADD r c)))
    | While x y => LABEL r (comp' x (next r) (JMPZ c (comp' y (next r) (JUMP r))))
    | Get => GET c
    | Put x y => comp' x r (PUT (comp' y r c))
  end.

Definition comp (e : Expr) : Code := comp' e adr0 HALT.


Inductive Elem : Set :=
| VAL : Value -> Elem 
| CODE : Code -> Elem
.



(** * Virtual Machine *)

Inductive Conf : Type := 
| conf : Code -> Value -> State -> Mem Elem -> Conf.

Notation "⟨ c , a , q , s ⟩" := (conf c a q s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n c s a q :  ⟨LOAD n c, a, q, s⟩ ==> ⟨c, n, q, s⟩
| vm_add c m n r s q : s[r] = VAL m -> ⟨ADD r c, n, q, s⟩ 
                                                 ==> ⟨c, m + n, q, s⟩
| vm_store c v r s q : ⟨STORE r c, v, q, s⟩  
                         ==> ⟨c, v, q, s[r:= VAL v]⟩
| vm_jump n r s q c : s[r] = CODE c -> ⟨JUMP r, n, q, s⟩ 
                                         ==> ⟨c, n, q, s⟩
| vm_jmpz_zero s q c c' : ⟨JMPZ c' c, 0, q, s⟩ 
                             ==> ⟨c', 0, q, s⟩
| vm_jmpz_nzero n s q c c' : n <> 0 ->
                            ⟨JMPZ c' c, n, q, s⟩ ==> ⟨c, n, q, s⟩
| vm_label n r s q c : ⟨LABEL r c, n, q, s⟩ ==> ⟨c, n, q, s[r:=CODE (LABEL r c)]⟩
| vm_get c s a q :  ⟨GET c, a, q, s⟩ ==> ⟨c, q, q, s⟩
| vm_put c s a q : ⟨PUT c, a, q, s⟩ ==> ⟨c, a, a, s⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  c a e s s' : s ≤ s' -> cle ⟨ c , a , e , s ⟩ ⟨ c , a , e , s' ⟩.

Hint Constructors cle.


(** * Calculation *)

(** Boilerplate to import calculation tactics *)
Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Definition MemElem := nat.
Lemma monotone : monotonicity cle VM.
prove_monotonicity. Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec p v q q' r c a s :
  freeFrom r s ->  ⟪p, q⟫ ⇓ ⟪v, q'⟫ ->
  ⟨comp' p r c, a, q, s⟩ =|> ⟨c ,  v, q', s⟩.

(** Setup the induction proof *)

Proof.
  intros F E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent s.
  generalize dependent r.
  dependent induction E;intros.

(** Calculation of the compiler *)

(** - [(Val n,q) ⇓ (n,q)]: *)

  begin
  ⟨c, n , q, s⟩.
  <== { apply vm_load }
  ⟨LOAD n c, a, q, s⟩.
  [].

(** - [(Add x y,q) ⇓ (m + n,q')]: *)

  begin
    ⟨c, m + n, q'', s⟩.
  ≤ { auto }
    ⟨c, m + n, q'', s[r:=VAL m]⟩ .
  <== { apply vm_add }
    ⟨ADD r c, n, q'', s[r:=VAL m]⟩ .
  <|= { apply IHE2 }
      ⟨comp' y (next r) (ADD r c), m, q', s[r:= VAL m]⟩ .
  <== { apply vm_store }
      ⟨STORE r (comp' y (next r) (ADD r c)), m, q', s⟩.
  <|= { apply IHE1 }
      ⟨comp' x r (STORE r (comp' y (next r) (ADD r c))), a, q, s⟩.
  [].

  (** - [(Get,q) ⇓ (q,q)]: *)

  begin
    ⟨ c, q, q, s ⟩.
  <== {apply vm_get}
    ⟨ GET c, a, q, s ⟩.
  []. 

  (** - [(Put x y,q) ⇓ (v,q'')]: *)
  begin
    ⟨ c, v, q'', s ⟩.
  <|= { apply IHE2 }
    ⟨ comp' y r c, n, n, s ⟩.
  ≤ {auto}
    ⟨ comp' y r c, n, n, s ⟩.
  <== { apply vm_put }
    ⟨ PUT (comp' y r c), n, q', s ⟩.
  <|= { apply IHE1 }
    ⟨ comp' x r (PUT (comp' y r c)), a, q, s ⟩.
  [].


    (** - [(While x y ,q) ⇓ (v,q''')]: *)
  begin
    ⟨ c, v, q''', s ⟩.
  <|= { eapply IHE3 }
    ⟨ comp' (While x y) r c, m, q'', s ⟩.
  ≤ { auto }
    ⟨ comp' (While x y) r c, m, q'', s[r:=CODE (comp' (While x y) r c)] ⟩.
  <== { apply vm_jump }
    ⟨ JUMP r, m, q'', s[r:=CODE (comp' (While x y) r c)] ⟩.
  <|= { apply IHE2 }
    ⟨ comp' y (next r) (JUMP r), n, q', s[r:=CODE (comp' (While x y) r c)] ⟩.
  <== { apply vm_jmpz_nzero }
    ⟨ JMPZ c (comp' y (next r) (JUMP r)), n, q', s[r:=CODE (comp' (While x y) r c)] ⟩.
  <|= { apply IHE1 }
      ⟨ comp' x (next r) (JMPZ c (comp' y (next r) (JUMP r))), a, q, s[r:=CODE (comp' (While x y) r c)] ⟩.
  <== { apply vm_label }
      ⟨ LABEL r (comp' x (next r) (JMPZ c (comp' y (next r) (JUMP r)))), a, q, s ⟩.
  [].

  begin
    ⟨ c, 0, q', s ⟩.
  <== { apply vm_jmpz_zero }
      ⟨ JMPZ c (comp' y (next r) (JUMP r)) , 0, q', s ⟩.
  ≤ { auto }
    ⟨ JMPZ c (comp' y (next r) (JUMP r)) , 0, q', s[r:=CODE (comp' (While x y) r c)] ⟩.
  <|= {eapply IHE}
    ⟨ comp' x (next r) (JMPZ c (comp' y (next r) (JUMP r))) , a, q, s[r:=CODE (comp' (While x y) r c)] ⟩.
  <== { apply vm_label }
      ⟨ LABEL r (comp' x (next r) (JMPZ c (comp' y (next r) (JUMP r)))), a, q, s ⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists n q, ⟪p, 0⟫ ⇓ ⟪n,q⟫.

Theorem sound p a s C : freeFrom adr0 s -> terminates p -> ⟨comp p, a, 0, s⟩ =>>! C -> 
                          exists n s' q, C = ⟨HALT , n, q, s'⟩ /\ ⟪p,0⟫ ⇓ ⟪n,q⟫.
Proof.
  unfold terminates. intros F T M. destruct T as [n T]. destruct T as [q T].
  pose (spec p n 0 q adr0 HALT a s F T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. exists n. eexists. exists q. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H1. assumption.
Qed.

End While.