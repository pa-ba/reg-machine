Definition Admit {A} : A. admit. Admitted.

Ltac premise H := match type of  H with
                    forall (_ : ?A), _  =>
                    let P := fresh in assert A as P;[idtac | specialize (H P);clear P]
                  end.


Require Import List.

Require Export Machine.
Require Export Memory.
Module Calculation (mem: Memory)(mod : Machine).
Module Meta := MetaTheory mod.
Export Meta.
Export mem.



Import ListNotations.

Ltac autodestruct := match goal with
                     | [ H : _ /\ _ |- _] => destruct H
                     | [ H : exists _ , _ |- _] => destruct H
                     end.
Ltac rewr_assumption := idtac; match goal with
                          | [R: _ = _ |- _ ] => first [rewrite R| rewrite <- R]
                        end.




Ltac eval_inv ev := let do_inv e H := (first [is_var e; fail 1|inversion H; subst; clear H])
                    in idtac; match goal with
                          | [ H: ev ?e _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ _ |- _ ] => do_inv e H
                          | _ => eauto
                        end.
Ltac smart_destruct x := first[is_var x;destruct x| let x' := fresh in remember x as x'; destruct x' ].


Ltac dist' ev :=
  simpl in *; intros; subst; ev;
  match goal with
  | [ H : Some _ = Some _ |- _] => inversion H; clear H; dist' ev
  | [ H : Some _ = None |- _] => inversion H; dist' ev
  | [ H : None = Some _ |- _] => inversion H; dist' ev
  | [ H : pair _ _  = pair _ _ |- _] => inversion H; clear H; dist' ev
  | [ H: and _ _ |- _ ] => destruct H; dist' ev
  | [ H: ex _ |- _ ] => destruct H; dist' ev
  | [ H: or _ _ |- _ ] => destruct H; dist' ev
  | [ H: eq _ _ |- _ ] => rewrite H in *; dist' ev
  (* | [ |- and _ _ ] => split; repeat dist' ev *)
  (* | [ |- _ <-> _ ] => split; dist' ev *)
  (* | [ |- ex _ ] => eexists; dist' ev *)
  (* | [ |- or _ _] => solve [right;dist' ev|left; dist' ev] *)
  | [ |- context [let _ := ?x in _] ] => smart_destruct x;dist' ev
  | [ |- context [match ?x with _ => _ end]] => smart_destruct x; dist' ev
  | _ => idtac
  end.

Ltac dist := dist' eauto.


Ltac solve_memle t :=
  solve[
      apply memle_set;
      match goal with
      | [H: freeFrom _ _ |- _] => apply H; t
      (* | [H: exists v, empty_mem _ [_] =  v |- _ ] => apply empty_mem_free in H; contradiction; t *)
      | _ => t
      end
      | t
    ].


Ltac check_exp x y := let h := fresh "check" in assert (h: x = y) by dist; clear h.

Ltac check_rel Bidir Rel := first [check_exp Bidir Rel|
                             fail 2 "wrong goal; expected relation =>> but found" Rel].

Tactic Notation "[]" := apply Reach_refl.


Tactic Notation  (at level 2)    "≤" "{?}" constr(e2) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
                            let h := fresh "rewriting" in
                            assert(Pre rhs e2)
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "=" "{?}" constr(e2) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
                            let h := fresh "rewriting" in
                            assert(rhs = e2)
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<==" "{?}" constr(e2) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
                            let h := fresh "rewriting" in
                            assert(e2 ==> rhs)
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    "<|=" "{?}" constr(e2) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
        first [let h := fresh "rewriting" in
               assert(h : Reach e2 rhs) | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    "<|=" "{{"tactic(t1) "}}" constr(e2) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
        first [let h := fresh "rewriting" in
               assert(h : Reach e2 rhs) by t1;
                 apply (fun x => Reach_trans _ _ _ x h); clear h | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    "<|=" "{"tactic(t) "}" constr(e) :=
  let t' := try solve [t;eauto with memory|apply Reach_refl;eauto]
  in 
  <|= {{ dist' t' }} e .

Tactic Notation  (at level 2)    "≤" "{"tactic(t) "}" constr(e) :=
  <|= {{ apply Reach_cle; dist; constructor; solve_memle t }} e .

Tactic Notation  (at level 2)    "=" "{"tactic(t) "}" constr(e) :=
  match goal with
  | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
                           first[ let h := fresh "rewriting" in
                                  assert(h:rhs = e) by dist' t;
                                  rewrite h; clear h | fail 2]
  | _ => fail 1 "goal is not a VM"
  end.


Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed .

Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto].

Tactic Notation  (at level 2)    "<==" "{" tactic(t) "}" constr(e) :=
  let tt := try solve[apply trc_step; t; eauto using get_set|apply trc_refl;eauto]
  in <|= {{ apply Reach_trc;  dist' tt}} e.


Tactic Notation  (at level 2)  "begin" constr(rhs) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs'] => check_rel Reach Rel; check_exp rhs rhs'
    | _ => fail 1 "rhs does not match"
  end.

End Calculation.
