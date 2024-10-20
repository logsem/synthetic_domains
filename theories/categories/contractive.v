From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category coprod ord_cat enriched domain.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Declare Scope contractive_scope.
Delimit Scope contractive_scope with contractive.

Local Open Scope contractive_scope.

Section functor_diag.
  Context {SI : indexT}.
  Context {C : category}.
  Context `{!Enriched C (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C C) (PSh (OrdCat SI)) := prod_enriched_def.

  Program Definition functor_diag_enr_def (a b : obj C)
    : natural (enr_hom a b) (enr_hom (functor_diag ₒ a) (functor_diag ₒ b))
    := MkNat (λ x, λset f, (f, f)) _.
  Next Obligation.
    repeat intros ?; solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; solve_by_eq_rewrite.
  Qed.

  Local Program Instance functor_diag_enr : EnrichedFunctor (@functor_diag C)
    := MkEnrFunc (λ a b, functor_diag_enr_def a b) _ _ _.
  Next Obligation.
    intros; simpl.
    rewrite enr_project_embed.
    intros ????; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ? [? ?] [? ?] [-> ->].
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ??? ->.
    reflexivity.
  Qed.
End functor_diag.

Section functor_prod.
  Context {SI : indexT}.
  Context {C C' D D' : category}.
  Context `{!Enriched C (PSh (OrdCat SI))} `{!Enriched D (PSh (OrdCat SI))}
    `{!Enriched C' (PSh (OrdCat SI))} `{!Enriched D' (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI)) := prod_enriched_def.
  Local Instance : Enriched (cat_prod C' D') (PSh (OrdCat SI)) := prod_enriched_def.
  Context (f : functor C C').
  Context (g : functor D D').
  Context `{!EnrichedFunctor f}.
  Context `{!EnrichedFunctor g}.

  Program Definition functor_prod_enr_def (a b : obj (cat_prod C D))
    : natural (enr_hom a b) (enr_hom (f ₒ a.1, g ₒ a.2) (f ₒ b.1, g ₒ b.2))
    := MkNat (λ x, λset h, (((enr_func_h_map f a.1 b.1 ₙ x) h.1),
                             ((enr_func_h_map g a.2 b.2 ₙ x) h.2)))
         _.
  Next Obligation.
    repeat intros ?; solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    intros ????? x y H.
    rewrite H /= !psh_naturality //.
  Qed.

  Local Program Instance functor_prod_enr : EnrichedFunctor (functor_prod f g)
    := MkEnrFunc (λ a b, functor_prod_enr_def a b) _ _ _.
  Next Obligation.
    intros; simpl.
    intros ??? ->; simpl.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Local Instance func_lift_lc_left `{!LocallyContractiveFunctor f}
    : LocallyContractiveFunctor (functor_prod f g).
  Proof.
    unshelve econstructor.
  Admitted.

  Local Instance func_lift_lc_right `{!LocallyContractiveFunctor g}
    : LocallyContractiveFunctor (functor_prod f g).
  Proof.
    unshelve econstructor.
  Admitted.
End functor_prod.

Section prod_func.
  Context {SI : indexT}.
  Context {C : category}.
  Context `{!HasProducts C}.
  Context `{!Enriched C (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C C) (PSh (OrdCat SI)) := prod_enriched_def.

  (* Program Definition prod_func_enr_def (a b : obj (cat_prod C C)) *)
  (*   : natural (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2) (enr_hom (a.1 ×ₒ a.2) (b.1 ×ₒ b.2)) *)
  (*   := MkNat (λ x, _) _. *)
  (* Next Obligation. *)
  (*   intros; simpl. *)
  (*   unshelve econstructor. *)
  (*   - intros; simpl in *. *)
  (*     destruct X. *)
  (*     epose proof (enr_embed s). *)

  (* Local Program Instance prod_func_enr : EnrichedFunctor (prod_func C). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - intros; simpl. *)
  (* Admitted. *)
End prod_func.

Section coprod_func.
  Context {SI : indexT}.
  Context {C : category}.
  Context `{!HasCoproducts C}.
  Context `{!Enriched C (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C C) (PSh (OrdCat SI)) := prod_enriched_def.

  (* Local Instance coprod_func_enr : EnrichedFunctor (coprod_func C). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - intros; simpl. *)
  (* Admitted. *)
End coprod_func.

Program Definition cod_func_prod {C D} `{!HasProducts D} (f g : functor C D)
  : functor C D
  := functor_compose
       functor_diag
       (functor_compose
          (functor_prod f g)
          (prod_func _)).

Infix "×ᵨ" := cod_func_prod (at level 40, left associativity)
    : contractive_scope.

Program Definition cod_func_sum {C D} `{!HasCoproducts D} (f g : functor C D)
  : functor C D
  := functor_compose
       functor_diag
       (functor_compose
          (functor_prod f g)
          (coprod_func _)).

Infix "+ᵨ" := cod_func_sum (at level 40, left associativity)
    : contractive_scope.

Program Definition func_lift {C D E} (f : functor D E)
  : functor (cat_prod C D) E
  := functor_compose (cat_proj2 _ _) f.

Notation "'↑ᵨ'" := func_lift (at level 40, no associativity)
    : contractive_scope.

Section cat_proj.
  Context {SI : indexT}.
  Context {C D : category}.
  Context `{!Enriched C (PSh (OrdCat SI))} `{!Enriched D (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI)) := prod_enriched_def.

  Program Definition cat_proj2_enr_def (a b : obj (cat_prod C D))
    : natural (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2) (enr_hom a.2 b.2)
    := MkNat (λ x, λset f, f.2) _.
  Next Obligation.
    repeat intros ?; solve_by_eq_rewrite.
  Qed.

  Local Program Instance cat_proj2_enr : EnrichedFunctor (cat_proj2 C D)
    := MkEnrFunc (λ a b, cat_proj2_enr_def a b) _ _ _.
  Next Obligation.
    intros; simpl.
    rewrite enr_project_embed.
    intros ????; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ? [? ?] [? ?] [-> ->].
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    intros ??? ->.
    reflexivity.
  Qed.
End cat_proj.

Section func_lift.
  Context {SI : indexT}.
  Context {C D F : category}.
  Context `{!Enriched C (PSh (OrdCat SI))} `{!Enriched D (PSh (OrdCat SI))}
    `{!Enriched F (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI)) := prod_enriched_def.
  Context (f : functor D F).
  Context `{!EnrichedFunctor f}.

  Local Instance func_lift_enr : EnrichedFunctor (func_lift f).
  Proof.
    eapply EnrichedFunctor_comp; last done.
    apply cat_proj2_enr.
  Admitted.

  Local Instance func_lift_lc : LocallyContractiveFunctor (func_lift f).
  Proof.
    unshelve econstructor.
  Admitted.
End func_lift.

Program Definition func_const {C D} (c : obj D)
  : functor (cat_prod C D) D
  := ((const_functor c : hom (C := Cat) _ _) ∘ (!ₕ ((cat_prod C D) : obj Cat))).
Next Obligation. reflexivity. Defined.

Notation "'Δᵨ'" := func_const (at level 40, no associativity)
    : contractive_scope.

Section func_const.
  Context {C D E : category} (c : obj D).
  Context `{!HasTerm E} `{!HasProducts E}.
  Context `{!Enriched C E} `{!Enriched D E}.
  Local Instance : Enriched (cat_prod C D) E := prod_enriched_def.

  Local Instance func_const_enr : EnrichedFunctor (func_const c).
  Proof.
    unshelve econstructor.
    - intros; simpl.
      apply (enr_embed (id _) ∘ !ₕ _).
    - intros a b f; simpl.
      rewrite -{1}(right_id (⌜ id c ⌝)).
      rewrite comp_assoc.
      f_equiv.
      rewrite (bang_unique (term_is_terminal _) (id (1ₒ))).
      rewrite (bang_unique (term_is_terminal _) ((!ₕ) (enr_hom a b) ∘ f)).
      reflexivity.
    - intros a b d; simpl.
      rewrite hom_prod_comp.
      rewrite -!comp_assoc.
      assert (enr_comp c c c ∘ (⌜ id c ⌝ ×ₕ ⌜ id c ⌝)
                ≡ ⌜ id c ⌝ ∘ !ₕ _) as ->.
      {

        (* rewrite -(right_id (⌜ id c ⌝ ×ₕ ⌜ id c ⌝)). *)
        (* rewrite -(hom_to_prod_of_prjs (id (1ₒ ×ₒ 1ₒ))). *)
        (* rewrite !right_id. *)
        (* rewrite -hom_to_prod_comp. *)
        admit.
      }
      rewrite !comp_assoc.
      f_equiv.
      do 2 rewrite (bang_unique (term_is_terminal _) (_ ∘ _)).
      reflexivity.
    - intros a; simpl.
      rewrite -{2}(right_id (⌜ id c ⌝)).
      rewrite comp_assoc.
      f_equiv.
      rewrite (bang_unique (term_is_terminal _) (id (1ₒ))).
      (* rewrite (bang_unique (term_is_terminal _) ((!ₕ) (enr_hom a a) ∘ _)). *)
      (* reflexivity. *)
  Admitted.

  (* Local Instance func_const_lc : LocallyContractiveFunctor (func_const c). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (* Admitted. *)
End func_const.

Opaque later next.

Section exp_func.
  Context {SI : indexT}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI))
    := (@self_enriched (PSh (OrdCat SI)) _).
  Local Instance : Enriched ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))
    := op_enriched_def.
  Local Instance : Enriched (cat_prod ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI)))
                     (PSh (OrdCat SI))
    := prod_enriched_def.

  Global Instance exp_psh_enr : EnrichedFunctor exp_func.
  Proof.
    unshelve econstructor.
    - intros.
      simpl.
  Admitted.

  (* Local Instance exp_psh_lc : LocallyContractiveFunctor exp_func. *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (* Admitted. *)
End exp_func.

Example pcf_dom {SI : indexT}
  : functor (cat_prod ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))) (PSh (OrdCat SI))
  := (functor_compose exp_func later)
     +ᵨ (Δᵨ (1ₒ@{PSh (OrdCat SI)}))
     +ᵨ (↑ᵨ later).
