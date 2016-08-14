Definition Admit {A} : A. admit. Admitted.

Ltac premise H := match type of  H with
                    forall (_ : ?A), _  =>
                    let P := fresh in assert A as P;[idtac | specialize (H P);clear P]
                  end.

Ltac autodestruct := match goal with
                     | [ H : _ /\ _ |- _] => destruct H
                     | [ H : exists _ , _ |- _] => destruct H
                     end.



Require Export Machine.

Module Calculation (mod : Machine).
Module Meta := MetaTheory mod.
Export Meta.
Require Import List.
Import ListNotations.




Ltac destruct_tuple := idtac; match goal with
  | [l : tuple nil |- _ ] => destruct l; destruct_tuple
  | [l : tuple (_ :: _) |- _ ] => destruct l; destruct_tuple
  | _ => idtac
end.



Ltac lift_union t := first [apply Reach_union; first [apply Reach_refl| lift_union t]| t].




Ltac eval_inv ev := let do_inv e H := (first [is_var e; fail 1|inversion H; subst; clear H])
                    in idtac; match goal with
                          | [ H: ev ?e _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ |- _ ] => do_inv e H
                          | [ H: ev ?e _ _ _ _ |- _ ] => do_inv e H
                          | _ => eauto
                        end.


Ltac dist' ev := simpl; intros; subst; ev;
                match goal with
                  | [ H: and _ _ |- _ ] => destruct H; dist' ev
                  | [ H: ex _ |- _ ] => destruct H; dist' ev
                  | [ H: or _ _ |- _ ] => destruct H; dist' ev
                  | [ H: eq _ _ |- _ ] => rewrite H in *; dist' ev
                  | [ |- and _ _ ] => split; dist' ev
                  | [ |- _ <-> _ ] => split; dist' ev
                  | [ |- ex _ ] => eexists; dist' ev
                  | [ |- or _ _] => solve [right;dist' ev|left; dist' ev] 
                  | _ => idtac
                end.

Ltac dist := dist' eauto.



Ltac check_exp x y := let h := fresh "check" in assert (h: x = y) by reflexivity; clear h.

Ltac check_rel Bidir Rel := first [check_exp Bidir Rel|
                             fail 2 "wrong goal; expected relation =>> but found" Rel].

Tactic Notation "[]" := apply Reach_refl.


Tactic Notation  (at level 2)    "⊇" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
                            let h := fresh "rewriting" in 
                            assert(h : forall c, c ∈ e2  -> c ∈ rhs)
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    "<|=" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Reach e2 rhs) | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    "<|=" "{"tactic(t1) "}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Reach e2 rhs) by (lift_union t1); 
                 apply (fun x => Reach_trans _ _ _ x h); clear h | fail 2]
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

Tactic Notation  (at level 2)    "<|=" "{"tactic(t1) "}?"  := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Reach Rel;
        first [eapply Reach_trans; [idtac|solve[t1]] | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.


Tactic Notation  (at level 2)    "⊇" "{"tactic(t) "}" constr(e) := 
  <|= {{ apply Reach_refl_if; dist' t }} e .

Ltac Reach_repeat := first [apply Reach_step' | 
                            first [apply Reach_assoc1 | apply Reach_assoc2| apply Reach_comm]; Reach_repeat
                            ].

Ltac Reach_search := first [apply Reach_step_simp | Reach_repeat].



Tactic Notation  (at level 2)    "<==" "{" tactic(t) "}" constr(e) := 
  <|= {{  Reach_search; intro; destruct_tuple; simpl; intros; [t;tauto | auto;tauto] }} e.

Tactic Notation  (at level 2)  "begin" constr(rhs) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs'] => check_rel Reach Rel; check_exp rhs rhs'
    | _ => fail 1 "rhs does not match"
  end.

End Calculation.
