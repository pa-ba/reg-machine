(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module LocalState (mem : Memory).
Import mem.

  
(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr 
| Catch : Expr -> Expr -> Expr
| Get : Expr
| Put : Expr -> Expr -> Expr.

Definition state := nat.

(** * Semantics *)

Fixpoint eval (x: Expr) (q : state) : option (nat * state) :=
  match x with
    | Val n => Some (n, q)
    | Add x1 x2 => match eval x1 q with
                   | Some (m, q') => match eval x2 q' with
                                   | Some (n, q'') => Some (m + n, q'')
                                   | None => None
                                   end
                   | None => None
                   end
    | Throw => None
    | Catch x h => match eval x q with
                   | Some (n, q') => Some (n, q')
                   | None => eval h q
                   end
    | Get => Some (q, q)
    | Put x y => match eval x q with
                 | Some (n, q') => eval y n
                 | None => None
                 end
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| THROW : Code
| UNMARK : Code -> Code
| MARK : adr -> Code -> Code -> Code
| READ : Code -> Code
| WRITE : Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : adr) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (next r) (ADD r c)))
  | Throw => THROW
  | Catch e1 e2 => MARK r (comp' e2 r c) (comp' e1 (next r) (UNMARK c))
  | Get => READ c
  | Put x y => comp' x r (WRITE (comp' y r c))
  end.

Definition comp (x : Expr) : Code := comp' x adr0 HALT.

Definition Han := option adr.

Inductive Elem : Set :=
| NUM : nat -> Elem
| HAN : Code -> Han -> state -> Elem.

(** * Virtual Machine *)

Inductive Conf : Type :=
| conf : Code -> nat -> Han -> state -> Conf
| fail : Han -> Conf.


Notation "⟨ x , y , z , q , s ⟩" := (conf x y z q, s).
Notation "⟪ x , s ⟫" := (fail x, s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf * Mem Elem -> Conf * Mem Elem -> Prop :=
| vm_load n a c s q p : ⟨LOAD n c, a , p, q, s⟩ ==> ⟨c , n, p, q, s⟩ 
| vm_add c s a r n q p : s[r]=  NUM n -> ⟨ADD r c, a , p, q, s⟩ ==> ⟨c , n + a, p, q, s⟩
| vm_store c s a r q p : ⟨STORE r c, a, p, q, s⟩ ==> ⟨c , a, p, q, s[r:=NUM a]⟩
| vm_throw a s q p : ⟨THROW, a, p, q, s⟩ ==> ⟪p, s⟫
| vm_fail p p' s q c : s[p] = HAN c p' q -> ⟪ Some p, s⟫ ==> ⟨c, 0, p', q, s⟩
| vm_unmark p p' s a q q' c c' : s[p] = HAN c' p' q' ->
                            ⟨UNMARK c, a, Some p, q, s⟩ ==> ⟨c, a, p', q, s⟩
| vm_mark p r s a c c' q :
    ⟨MARK r c' c, a, p, q, s⟩ ==> ⟨c, a, Some r, q, s[r:= HAN c' p q]⟩
| vm_read a c s q p : ⟨READ c, a , p, q, s⟩ ==> ⟨c , q, p, q, s⟩
| vm_write a c s q p : ⟨WRITE c, a , p, q, s⟩ ==> ⟨c , a, p, a, s⟩ 
where "x ==> y" := (VM x y).



(** * Calculation *)

(** Boilerplate to import calculation tactics *)
Module Mon := Monotonicity mem.
Import Mon.

Module VM <: (Machine mem).
Definition Conf := Conf.
Definition Rel := VM.
Definition MemElem := Elem.
Lemma monotone : monotonicity VM.
prove_monotonicity. Qed.
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.


(** Specification of the compiler *)

Theorem spec e r c a p s q :
  freeFrom r s ->
  ⟨comp' e r c, a, p, q, s⟩
    =|>
    match eval e q with
    | Some (n, q') => ⟨c , n, p, q', s⟩
    | None => ⟪p, s⟫
    end.


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent r.
  generalize dependent a.
  generalize dependent p.
  generalize dependent q.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) q with
    | Some (n', q') => ⟨c , n' ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = {auto}
      ⟨ c, n, p, q, s⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, a, p, q, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    match eval (Add e1 e2) q with
    | Some (n, q') => ⟨c , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = {auto}
    match eval e1 q with
    | Some (n, q') => match eval e2 q' with
                      | Some (n', q'') => ⟨c , n + n' , p, q'', s⟩
                      | None => ⟪p, s⟫
                      end
    | None => ⟪p, s⟫
    end.
  ≤ { auto }
    match eval e1 q with
    | Some (n, q') => match eval e2 q' with
                      | Some (n', q'') => ⟨c , n + n' ,p, q'', s[r:=NUM n]⟩
                      | None => ⟪p, s[r:=NUM n]⟫
                      end
    | None => ⟪p, s⟫
    end.
  <== { apply vm_add }
      match eval e1 q with
      | Some (n, q') => match eval e2 q' with
                        | Some (n', q'') => ⟨ADD r c , n' ,p, q'', s[r:=NUM n]⟩
                        | None => ⟪p, s[r:=NUM n]⟫
                        end
      | None => ⟪p, s⟫
      end.
  <|= {apply IHe2}
      match eval e1 q with
      | Some (n, q') => ⟨comp' e2 (next r) (ADD r c) , n ,p, q', s[r:=NUM n]⟩
      | None => ⟪p, s⟫
      end.
  <== { apply vm_store }
      match eval e1 q with
      | Some (n, q') => ⟨STORE r (comp' e2 (next r) (ADD r c)) , n ,p, q', s⟩
      | None => ⟪p, s⟫
      end.
  <|= { apply IHe1 }
    ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c))), a,p, q, s⟩.
  [].

(** - [x = Throw]: *)
  
  begin
    match eval Throw q with
    | Some (n, q') => ⟨c , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = { auto }
      ⟪p, s⟫.
  <== { apply vm_throw }
      ⟨THROW, a, p, q, s⟩.
  [].

(** - [x = Catch x1 x2]: *)
  
  begin
    match eval (Catch e1 e2) q with
    | Some (n, q') => ⟨c , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = { auto }
      match eval e1 q with
      | Some (n, q') => ⟨c , n ,p, q', s⟩
      | None => match eval e2 q with
                | Some (n', q'') => ⟨c , n' ,p, q'', s⟩
                | None => ⟪p,s⟫
                end
      end.
  <|= { apply IHe2 }
      match eval e1 q with
      | Some (n, q') => ⟨c, n ,p, q', s⟩
      | None => ⟨comp' e2  r c , 0 ,p, q, s⟩
      end.
  ≤ { eauto }
      match eval e1 q with
      | Some (n, q') => ⟨c , n ,p, q', s⟩
      | None => ⟨comp' e2  r c , 0 ,p, q, s[r:= HAN (comp' e2  r c) p q]⟩
      end.
  <== {apply vm_fail}
      match eval e1 q with
      | Some (n, q') => ⟨c , n ,p, q', s⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p q]⟫
      end.
  ≤ {auto}
      match eval e1 q with
      | Some (n, q') => ⟨c , n ,p, q', s[r:= HAN (comp' e2  r c) p q]⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p q]⟫
      end.
  <== {eapply vm_unmark}
      match eval e1 q with
      | Some (n, q') => ⟨UNMARK c , n,Some r, q', s[r:= HAN (comp' e2  r c) p q]⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p q]⟫
      end.
  <|= {apply IHe1}
      ⟨comp' e1 (next r) (UNMARK c) , a ,Some r, q, s[r:= HAN (comp' e2  r c) p q]⟩.
  <== {apply vm_mark}
      ⟨MARK r (comp' e2  r c) (comp' e1 (next r) (UNMARK c)) , a ,p, q, s⟩.
  [].


  begin
    match eval Get q with
    | Some (n, q') => ⟨c , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = {auto}
      ⟨c , q ,p, q, s⟩.
  <== {apply vm_read}
      ⟨READ c , a ,p, q, s⟩.
  [].
  
  begin
    match eval (Put e1 e2) q with
    | Some (n, q') => ⟨c , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  = {auto}
    match eval e1 q with
    | Some (n, q') => match eval e2 n with
                      | Some (n', q'') => ⟨c , n' ,p, q'', s⟩
                      | None => ⟪p, s⟫
                      end
    | None => ⟪p, s⟫
    end.
  <|= {apply IHe2}
    match eval e1 q with
    | Some (n, q') => ⟨comp' e2 r c , n ,p, n, s⟩
    | None => ⟪p, s⟫
    end.
  <== {apply vm_write}
    match eval e1 q with
    | Some (n, q') => ⟨WRITE (comp' e2 r c) , n ,p, q', s⟩
    | None => ⟪p, s⟫
    end.
  <|= {apply IHe1}
      ⟨comp' e1 r (WRITE (comp' e2 r c)) , a ,p, q, s⟩.
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst;eauto.
  rewrite H in *; dist. rewrite H in H3. dist. rewrite H in H6. dist.
Qed.


Theorem sound x a p q q' s n C :
  freeFrom adr0 s -> eval x q = Some (n, q')
  -> ⟨comp x, a, p, q, s⟩ =>>! C -> exists s', C = ⟨HALT, n,p, q', s'⟩.
Proof.
  intros F E M.
  pose (spec x adr0 HALT a p s q F). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. eexists. eapply D. apply M.
  rewrite E in *.
  split. inversion H1. subst.
  
  apply H. intro Contra. destruct Contra.
  inversion H3.
Qed.

End LocalState.
