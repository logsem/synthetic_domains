
From Ltac2 Require Import Ltac2 Message Printf Pattern.
Set Default Proof Mode "Classic".

Definition type_of {T : Type} (x : T)
  := T.

Ltac2 type_of (x : constr) :=
  let tx := eval cbv in (type_of $x) in tx.

Ltac2 mutable cat_intro_patterns :
  ((constr -> bool) * (Std.intro_pattern list -> unit)) list :=
  [].

Ltac2 try_cat_intro
  (pats : ((constr -> bool) * (Std.intro_pattern list -> unit)) list)
  (p : Std.intro_pattern list) : unit :=
  let g := Control.goal () in
  let res := List.find_opt (fun (test, _) => test g) pats
  in
  match res with
  | Some (_, tac) => tac p
  | None => printf "Unrecognized pattern: %t" g
  end.

Ltac2 Notation "cat_intros" p(intropatterns)
  := try_cat_intro cat_intro_patterns p.
Tactic Notation "cat_intros"
  := ltac2:(cat_intros ).
Tactic Notation "cat_intros" simple_intropattern(I1)
  := ltac2:(cat_intros I1).
Tactic Notation "cat_intros" simple_intropattern(I1) simple_intropattern(I2)
  := ltac2:(cat_intros I1 I2).

(* Ltac2 Set cat_intro_patterns as old := *)
(*   ((fun x => match! (Std.eval_hnf x) with *)
(*           | ?a -> ?b => true *)
(*           | _ => false *)
(*           end) *)
(*     , (fun p => Control.enter (fun () => Std.intros true p))) :: old. *)

Ltac2 Set cat_intro_patterns as old :=
  ((fun x => Control.plus (fun () => Pattern.matches pat:(?a -> ?b) (Std.eval_hnf x); true)
            (fun _ => false))
    , (fun p => Control.enter (fun () => Std.intros true p))) :: old.

(* Ltac2 Notation "tactic" s(constr) := printf "%t" s. *)

Context (A B : Type).
Goal (A -> B).
  (* Ltac2 Eval (let g := Control.goal () *)
  (*             in match! (Std.eval_hnf g) with *)
  (*                | ?a -> ?b => print (of_constr g) *)
  (*                end). *)
  (* cat_intros. *)
  cat_intros [].
  cat_intros [].
  Unshelve.


Ltac gettype i :=
  let f :=
    ltac2val:(Ltac1.lambda (fun i =>
                              let i := Option.get (Ltac1.to_ident i) in
                              let ty := Constr.type (Control.hyp i) in
                              Ltac1.of_constr ty
             ))
  in
  f ident:(i).
(* let a := gettype PPP in *)
(* set (TTT := a). *)




(* Program Definition unopposite_func {C D} (F : functor (C ᵒᵖ) (D ᵒᵖ)) : functor C D := *)
(*   MkFunc (λ c : obj C, F ₒ c) (λ _ _ f, F ₕ f) _ _ _. *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   repeat intros ?. *) *)
(* (*   apply (h_map_proper _ _ F b a x y H). *) *)
(* (* Defined. *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   apply (h_map_comp _ _ F _ _ _ g f). *) *)
(* (* Defined. *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   apply (h_map_id _ _ F a). *) *)
(* (* Defined. *) *)
(* Solve All Obligations *)
(*   with repeat intros ?; rewrite /= ?h_map_comp ?h_map_id; solve_by_equiv_rewrite. *)
(* Fail Next Obligation. *)

(* (* Program Definition func_op_forward {C D} : *) *)
(* (*   functor ((FuncCat C D)ᵒᵖ) (FuncCat (C ᵒᵖ) (D ᵒᵖ)) := *) *)
(* (*   (MkFunc (λ x, opposite_func x) (λ _ _ f, MkNat (λ x, nat_map f x) _) _ _ _). *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   by rewrite naturality. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   solve_proper. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   by repeat intros ?; simpl. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   by repeat intros ?; simpl. *) *)
(* (* Qed. *) *)

(* (* Program Definition func_op_backward {C D} : *) *)
(* (*   functor (FuncCat (C ᵒᵖ) (D ᵒᵖ)) ((FuncCat C D)ᵒᵖ) := *) *)
(* (*   (MkFunc (λ x, unopposite_func x) (λ _ _ f, MkNat (λ x, nat_map f x) _) _ _ _). *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl in *. *) *)
(* (*   symmetry. *) *)
(* (*   pose proof (naturality f) as H. *) *)
(* (*   simpl in H. *) *)
(* (*   apply H. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   intros; simpl. *) *)
(* (*   solve_proper. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   by repeat intros ?; simpl. *) *)
(* (* Qed. *) *)
(* (* Next Obligation. *) *)
(* (*   by repeat intros ?; simpl. *) *)
(* (* Qed. *) *)

(* (* Program Definition func_op_iso {C D} : (FuncCat C D)ᵒᵖ ≃@{Cat} FuncCat (C ᵒᵖ) (D ᵒᵖ) *) *)
(* (*   := MkIsoIc *) *)
(* (*        func_op_forward *) *)
(* (*        func_op_backward *) *)
(* (*        _. *) *)
(* (* Next Obligation. *) *)
(* (*   intros; split; simpl. *) *)
(* (*   - unshelve refine (MkFuncEq _ _ _ _). *) *)
(* (*     + intros; simpl. *) *)
(* (*       destruct a. *) *)
(* (*       reflexivity. *) *)
(* (*     + intros; simpl. *) *)
(* (*       destruct a, b; simpl. *) *)
(* (*       rewrite hom_trans_refl. *) *)
(* (*       intro; simpl. *) *)
(* (*       reflexivity. *) *)
(* (*   - unshelve refine (MkFuncEq _ _ _ _). *) *)
(* (*     + intros; simpl. *) *)
(* (*       destruct a. *) *)
(* (*       reflexivity. *) *)
(* (*     + intros; simpl. *) *)
(* (*       destruct a, b; simpl. *) *)
(* (*       rewrite hom_trans_refl. *) *)
(* (*       intro; simpl. *) *)
(* (*       reflexivity. *) *)
(* (* Qed. *) *)
