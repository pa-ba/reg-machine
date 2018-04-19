Require Import List.
Import ListNotations.

  
Fixpoint tuple (ts : list Type) : Type :=
  match ts with
    | []       => unit
    | t :: ts' => (t * tuple ts')%type
  end.


Inductive SetCom (A : Type) : list Type -> Type :=
| BaseSet : A -> Prop -> SetCom A nil
| ExSet {t ts} : (t -> SetCom A ts) -> SetCom A (t :: ts).

Arguments BaseSet {A} a p.
Arguments ExSet {A} {t} {ts} p.

Definition funtail {t ts A} (x : t) (f : forall (args : tuple (t :: ts)),  A args) 
: forall (args : tuple ts), A (x, args) :=
  fun xs => f (x, xs).


Fixpoint mkSetCom {A ts} (C : tuple ts -> A) (P : tuple ts -> Prop) : SetCom A ts :=
  match ts return (tuple ts -> A) -> (tuple ts -> Prop) -> SetCom A ts with
    | nil => fun C P => BaseSet (C tt) (P tt)
    | t :: ts' => fun C P => @ExSet A t ts'  (fun x => @mkSetCom A ts' (funtail x C) (funtail x P))
  end C P.



Fixpoint getConf {A ts} (S : SetCom A ts) : tuple ts -> A :=
  match S with
    | BaseSet C P => fun xs => C
    | ExSet ex => fun xs =>  let (x, xs') := xs in  getConf (ex x) xs'
  end.

Fixpoint getProp {A ts} (S : SetCom A ts) : tuple ts -> Prop :=
  match S with
    | BaseSet C P => fun xs => P
    | ExSet ex => fun xs => let (x, xs') := xs in getProp (ex x) xs'
  end.

Lemma getConf_sound A ts (C : tuple ts -> A) P x : getConf (mkSetCom C P) x = C x.
Proof.
  intros. induction ts; destruct x. reflexivity. simpl. apply (IHts (funtail a0 C)).
Qed.


Lemma getProp_sound A ts (C : tuple ts -> A) P x : getProp (mkSetCom C P) x = P x.
Proof.
  intros. induction ts;destruct x. reflexivity. simpl. apply (IHts _ (funtail a0 P)).
Qed.

Fixpoint  SetComElem  {A ts} (C : A) (S : SetCom A ts) : Prop :=
  match S with
      | BaseSet C' P => C' = C /\ P 
      | ExSet e => exists x, SetComElem C (e x)
  end.

Lemma set_com_elem {A ts} (C : A) (S : SetCom A ts) : 
  SetComElem C S <-> exists xs, getConf S xs = C /\ getProp S xs.
Proof.
  split; intros. 
  * induction S.
    - exists tt. assumption.

    - simpl in H. destruct H. apply H0 in H.
      decompose [ex and] H.  exists (x, x0). auto.
  * induction S.
    - decompose [ex and] H. simpl in *. tauto.
    - decompose [ex and] H. simpl. destruct x.
      exists t0. apply H0. exists t1. tauto.
Qed.


Inductive SetOf (A : Type) : Type :=
  | Sing {ts} : SetCom A ts -> SetOf A
  | Empty : SetOf A
  | Union : SetOf A -> SetOf A -> SetOf A.

Arguments Sing {A} {ts} s.
Arguments Empty {A}.
Arguments Union {A} s1 s2.


Fixpoint ConfElem {A} (C : A) (S : SetOf A) : Prop :=
  match S with
    | Sing s => SetComElem C s
    | Empty => False
    | Union S1 S2 => ConfElem C S1 \/  ConfElem C S2
  end.


Notation "{| C | P |}" := (Sing (mkSetCom C P)) (at level 70, no associativity).
Infix "∈" := ConfElem (at level 80, no associativity).
Infix "∪" := Union (at level 76, left associativity).

Definition Subset {A : Type} (S T : SetOf A) := (forall x, x ∈ S -> x ∈ T).


Infix "⊆" := Subset (at level 80, no associativity).
Infix "=<" := Subset (at level 80, no associativity).
Notation "S == T" := (forall x, x ∈ S <-> x ∈ T) (at level 80, no associativity).


Lemma mkSetComCompl' {A ts} (S : SetCom A ts) : {| getConf S | getProp S |} == Sing S.
Proof.
  simpl. unfold Subset. split; intros; induction S; auto; simpl in *; destruct H; eexists; apply H0; apply H.
Qed.

Lemma sing_set_elem {A ts} (C' : A) (C : tuple ts -> A) P :
  C' ∈ {| C | P |} <-> exists xs, C xs = C' /\ P xs.
Proof.
  simpl. rewrite set_com_elem. split; intro H; decompose [ex and] H; eexists; 
  rewrite getConf_sound in *; rewrite getProp_sound in *; split; eassumption.
Qed.




Notation "{ x .. y , C | P }" := (Sing (ExSet ( fun x =>  .. (ExSet (fun y => BaseSet C P)) ..  )))
(at level 70, x binder, y binder, no associativity).


Notation "{, C | P }" := (Sing (BaseSet C  P))
(at level 70, no associativity).



(* Lemma union_incll {A} (S T : SetOf A) : S ⊆ S ∪ T. *)
(* Proof. simpl. auto. Qed. *)

(* Lemma union_inclr {A} (S T : SetOf A) : T ⊆ S ∪ T. *)
(* Proof. simpl. auto. Qed. *)

(* Hint Resolve union_incll union_inclr. *)


(* (* The above lemma cannot be used directly in a proof *)
(* calculation. Therefore, we reformulat it using [getProp] and [getConf] *)
(* instead of the [ {| C | P |} ] construction. *) *)

(* Lemma union_sub_left {A} (S1 S2 T : SetOf A): S1 ⊆ S2 -> S1 ∪ T ⊆ S2 ∪ T . *)
(* Proof. *)
(*   intros. simpl in *. destruct H0; auto. *)
(* Qed. *)

(* Lemma union_eq_left {A} (S1 S2 T : SetOf A) : S1 == S2 -> S1 ∪ T == S2 ∪ T . *)
(* Proof. *)
(*   simpl in *; split;intros; destruct H0; solve [left; destruct H; auto| right; destruct H; auto]. *)
(* Qed. *)

(* Lemma union_sub_eq {A} (S1 S2: SetOf A) : S1 == S2 -> S1 ⊆ S2 . *)
(* Proof. *)
(*   intros. simpl in *. destruct H. auto. *)
(* Qed. *)

(* Lemma set_eq_ref {A} (S T: SetOf A) : S == T -> T == S. *)
(* Proof. *)
(*   intros. destruct H. split; auto. *)
(* Qed. *)

Lemma sub_union {A} (S1 S2 T1 T2 : SetOf A): S1 ⊆ S2 -> T1 ⊆ T2 -> S1 ∪ T2 ⊆ S2 ∪ T2 .
Proof.
  unfold Subset. intros. simpl in *. destruct H1; auto.
Qed.

Lemma sub_refl {A} (S : SetOf A): S ⊆ S .
Proof. unfold Subset. auto. Qed.

Lemma sub_trans {A} (S T U : SetOf A): S =< T -> T =< U -> S =< U .
Proof. unfold Subset. auto. Qed.

Lemma sub_eq {A} (S T : SetOf A): S == T -> S =< T .
Proof. unfold Subset. intros.  apply (H x). auto. Qed.
