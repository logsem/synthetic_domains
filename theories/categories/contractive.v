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
  Fail Next Obligation.

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
  Fail Next Obligation.
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
  Context `{!LocallyContractiveFunctor f}.
  Context `{!LocallyContractiveFunctor g}.

  Local Opaque next later.

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
  Fail Next Obligation.

  Local Program Instance functor_prod_enr : EnrichedFunctor (functor_prod f g)
    := MkEnrFunc (λ a b, functor_prod_enr_def a b) _ _ _.
  Next Obligation.
    intros; simpl.
    intros ??? ->; simpl.
    rewrite !enr_func_h_map_is_h_map /=.
    reflexivity.
  Qed.
  Next Obligation.
    intros a b c; simpl.
    intros d ? y ->; simpl.
    pose proof (enr_func_h_map_comp f a.1 b.1 c.1 d
                  (y.1.1, y.2.1) (y.1.1, y.2.1) (reflexivity _)) as H.
    simpl in H.
    rewrite H; clear H.
    pose proof (enr_func_h_map_comp g a.2 b.2 c.2 d
                  (y.1.2, y.2.2) (y.1.2, y.2.2) (reflexivity _)) as H.
    simpl in H.
    rewrite H; clear H.
    reflexivity.
  Qed.
  Next Obligation.
    intros a; simpl.
    intros b ? y ->; simpl.
    pose proof (enr_func_h_map_id f a.1 b y y (reflexivity _)) as H.
    simpl in H.
    rewrite H; clear H.
    pose proof (enr_func_h_map_id g a.2 b y y (reflexivity _)) as H.
    simpl in H.
    rewrite H; clear H.
    reflexivity.
  Qed.
  Fail Next Obligation.

  Program Definition func_prod_lc_def
    (a b : obj (cat_prod C D))
    : natural (later_func (enr_hom a.1 b.1 ×ₒ@{PSh (OrdCat SI)} enr_hom a.2 b.2))
        (enr_hom (f ₒ a.1) (f ₒ b.1) ×ₒ enr_hom (g ₒ a.2) (g ₒ b.2))
    := MkNat (λ x,
           λset h,
           ((((contr_func_h_map f a.1 b.1) ₙ x)
               ((forward (later_prod (enr_hom a.1 b.1) (enr_hom a.2 b.2)) ₙ x) h).1)
             , (((contr_func_h_map g a.2 b.2) ₙ x)
                  ((forward (later_prod (enr_hom a.1 b.1) (enr_hom a.2 b.2)) ₙ x) h).2))) _.
  Next Obligation.
    repeat intros ?.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    intros ???? j; simpl.
    intros ? y ->; simpl.
    pose proof (psh_naturality (contr_func_h_map f a.1 b.1) _ _ j) as H.
    simpl in H.
    rewrite -H; clear H.
    pose proof (psh_naturality (contr_func_h_map g a.2 b.2) _ _ j) as H.
    simpl in H.
    rewrite -H; clear H.
    f_equiv.
    - f_equiv.
      pose proof (@naturality _ _ _ _
                    (forward (later_preserves_prods_nat SI)ₙ
                       (enr_hom a.1 b.1, enr_hom a.2 b.2)) _ _ j
                    y y (reflexivity _)) as Hn.
      simpl in Hn.
      rewrite Hn; clear Hn.
      reflexivity.
    - f_equiv.
      pose proof (@naturality _ _ _ _
                    (forward (later_preserves_prods_nat SI)ₙ
                       (enr_hom a.1 b.1, enr_hom a.2 b.2)) _ _ j
                    y y (reflexivity _)) as Hn.
      simpl in Hn.
      rewrite Hn; clear Hn.
      reflexivity.
  Qed.
  Fail Next Obligation.

  Local Program Instance func_prod_lc
    : LocallyContractiveFunctor (functor_prod f g)
  := MkLocContrFunc (λ a b, func_prod_lc_def a b) _ _ _.
  Next Obligation.
    intros a b.
    intros c ? y ->; simpl.
    f_equiv.
    - rewrite (contr_func_h_map_is_h_map f a.1 b.1 c y.1 y.1 (reflexivity _)) /=.
      f_equiv.
      rewrite {1}/later_preserves_prods_nat
        right_adj_preserves_prods_forward /=.
      admit.
    - rewrite (contr_func_h_map_is_h_map g a.2 b.2 c y.2 y.2 (reflexivity _)) /=.
      f_equiv.
      rewrite {1}/later_preserves_prods_nat
        right_adj_preserves_prods_forward /=.
      admit.
  Admitted.
  Next Obligation.
    intros a b c d e e' ->.
    simpl.
    f_equiv.
    - epose proof (contr_func_h_map_comp f a.1 b.1 c.1 d).
      admit.
  Admitted.
  Next Obligation.
    intros a c e e' ->.
    simpl.
    f_equiv.
    - rewrite -(contr_func_h_map_id f a.1 c e' e' (reflexivity _)).
      simpl.
      f_equiv.
      rewrite {1}/later_preserves_prods_nat
        right_adj_preserves_prods_forward /=.
      set (T := func_prj1 _ _).
      set (T' := << _, _ >>).
      pose proof (h_map_comp _ _ later _ _ _ T' T c (((next ₙ 1ₒ)ₙ c) e')
                    (((next ₙ 1ₒ)ₙ c) e') (reflexivity _)) as H.
      simpl in H.
      rewrite -H; clear H.
      f_equiv.
      subst T T'.
      pose proof (hom_to_prod_prj1 ⌜ id a.1 ⌝ ⌜ id a.2 ⌝) as H.
      simpl in H.
      rewrite H; clear H.
      reflexivity.
    - rewrite -(contr_func_h_map_id g a.2 c e' e' (reflexivity _)).
      simpl.
      f_equiv.
      rewrite {1}/later_preserves_prods_nat
        right_adj_preserves_prods_forward /=.
      set (T := func_prj2 _ _).
      set (T' := << _, _ >>).
      pose proof (h_map_comp _ _ later _ _ _ T' T c (((next ₙ 1ₒ)ₙ c) e')
                    (((next ₙ 1ₒ)ₙ c) e') (reflexivity _)) as H.
      simpl in H.
      rewrite -H; clear H.
      f_equiv; last done.
      subst T T'.
      pose proof (hom_to_prod_prj2 ⌜ id a.1 ⌝ ⌜ id a.2 ⌝) as H.
      simpl in H.
      rewrite H; clear H.
      reflexivity.
  Qed.
  Fail Next Obligation.

End functor_prod.

Section prod_func.
  Context {SI : indexT}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI)) := @self_enriched _ _.
  Local Instance : Enriched (cat_prod (PSh (OrdCat SI)) (PSh (OrdCat SI)))
                     (PSh (OrdCat SI)) := prod_enriched_def.

  Program Definition prod_func_enr_def
    (a b : obj (cat_prod (PSh (OrdCat SI)) (PSh (OrdCat SI))))
    : natural (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2) (enr_hom (a.1 ×ₒ a.2) (b.1 ×ₒ b.2))
    := MkNat (λ x,
           λset f,
           MkNat (λ c,
               λset g,
               (((f.1 ₙ c) (g.1, g.2.1)), ((f.2 ₙ c) (g.1, g.2.2)))) _) _.
  Next Obligation.
    intros ??????? ->.
    reflexivity.
  Qed.
  Next Obligation.
    intros ??? M ?? F ?? H.
    rewrite (setoid_eq_reflect H) /=.
    rewrite -(psh_naturality M.2 _ _ F) /=; f_equiv.
    rewrite -(psh_naturality M.1 _ _ F) /=; f_equiv.
  Qed.
  Next Obligation.
    intros a b x r t H.
    rewrite (setoid_eq_reflect H).
    reflexivity.
  Qed.
  Next Obligation.
    intros ??????? -> ??? ->; simpl.
    reflexivity.
  Qed.
  Fail Next Obligation.

  Local Program Instance prod_func_enr : EnrichedFunctor (prod_func _)
    := MkEnrFunc (λ a b, prod_func_enr_def a b) _ _ _.
  Next Obligation.
    intros a b f; simpl.
    intros ? [] [] _ a' ? y ->; simpl.
    pose proof ((naturality f y.1 () () (reflexivity _))) as H.
    simpl in H.
    destruct H as [H1 H2].
    simpl in H1, H2.
    rewrite (H1 a') (H2 a') /=.
    split; by do 3 f_equiv.
  Qed.
  Next Obligation.
    intros a b c; simpl.
    intros d ? y -> ?? y' ->.
    simpl.
    reflexivity.
  Qed.
  Next Obligation.
    repeat intros ?.
    solve_by_eq_rewrite.
  Qed.
  Fail Next Obligation.
End prod_func.

Section coprod_func.
  Context {SI : indexT}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI)) := @self_enriched _ _.
  Local Instance : Enriched (cat_prod (PSh (OrdCat SI)) (PSh (OrdCat SI)))
                     (PSh (OrdCat SI)) := prod_enriched_def.

  Program Definition coprod_func_enr_def
    (a b : obj (cat_prod (PSh (OrdCat SI)) (PSh (OrdCat SI))))
    : natural (b.1 ↑ₒ a.1 ×ₒ (b.2 ↑ₒ a.2)) (b.1 +ₒ b.2 ↑ₒ (a.1 +ₒ a.2))
    := MkNat (λ x,
           λset f,
           MkNat (λ c,
               λset g,
               (sum_rect
                  (λ _, (b.1 ₒ c) +ₒ (b.2 ₒ c))
                  (λ g', inl ((f.1 ₙ c) (g.1, g')))
                  (λ g', inr ((f.2 ₙ c) (g.1, g'))) g.2)) _) _.
  Next Obligation.
    intros ??????? H.
    rewrite (setoid_eq_reflect H); clear H.
    reflexivity.
  Qed.
  Next Obligation.
    intros ??? M ?? F ? y H.
    rewrite (setoid_eq_reflect H) /=.
    destruct y as [? [g | g]]; simpl.
    - rewrite -(setoid_eq_reflect (psh_naturality M.1 _ _ F _)) /=.
      by do 2 f_equiv.
    - rewrite -(setoid_eq_reflect (psh_naturality M.2 _ _ F _)) /=.
      by do 2 f_equiv.
  Qed.
  Next Obligation.
    intros a b x r t H.
    rewrite (setoid_eq_reflect H).
    reflexivity.
  Qed.
  Next Obligation.
    intros ??????? -> ?? t ->; simpl.
    destruct t as [? [t | t]]; simpl.
    - by do 2 f_equiv.
    - by do 2 f_equiv.
  Qed.
  Fail Next Obligation.

  Local Program Instance coprod_func_enr : EnrichedFunctor (coprod_func _)
    := MkEnrFunc (λ a b, coprod_func_enr_def a b) _ _ _.
  Next Obligation.
    intros a b f; simpl.
    intros ? [] [] _ a' ? y ->; simpl.
    destruct y as [y1 [t | t]]; simpl.
    - f_equiv.
      pose proof ((naturality f y1 () () (reflexivity _))) as H.
      simpl in H.
      destruct H as [H1 H2].
      simpl in H1, H2.
      rewrite (H1 a') /=.
      by do 2 f_equiv.
    - f_equiv.
      pose proof ((naturality f y1 () () (reflexivity _))) as H.
      simpl in H.
      destruct H as [H1 H2].
      simpl in H1, H2.
      rewrite (H2 a') /=.
      by do 2 f_equiv.
  Qed.
  Next Obligation.
    intros a b c; simpl.
    intros d ? y -> ?? y' ->.
    simpl.
    destruct y' as [? [y' | y']]; simpl; by f_equiv.
  Qed.
  Next Obligation.
    intros ???? -> ?? t ->; simpl.
    destruct t as [? [t | t]]; simpl; by f_equiv.
  Qed.
  Fail Next Obligation.
End coprod_func.

Definition cod_func_prod {C D} `{!HasProducts D} (f g : functor C D)
  : functor C D
  := functor_compose
       functor_diag
       (functor_compose
          (functor_prod f g)
          (prod_func _)).

Infix "×ᵨ" := cod_func_prod (at level 40, left associativity)
    : contractive_scope.

Definition cod_func_sum {C D} `{!HasCoproducts D} (f g : functor C D)
  : functor C D
  := functor_compose
       functor_diag
       (functor_compose
          (functor_prod f g)
          (coprod_func _)).

Infix "+ᵨ" := cod_func_sum (at level 40, left associativity)
    : contractive_scope.

Definition func_lift {C D E} (f : functor D E)
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
  Fail Next Obligation.

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
  Fail Next Obligation.
End cat_proj.

Section func_lift.
  Context {SI : indexT}.
  Context {C D F : category}.
  Context `{!Enriched C (PSh (OrdCat SI))} `{!Enriched D (PSh (OrdCat SI))}
    `{!Enriched F (PSh (OrdCat SI))}.
  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI)) := prod_enriched_def.
  Context (f : functor D F).
  Context `{!LocallyContractiveFunctor f}.

  Local Program Instance func_lift_enr : EnrichedFunctor (func_lift f)
    := @EnrichedFunctor_comp _ _ _ _ _ _ _ _ _
         (cat_proj2 _ _) f cat_proj2_enr contr_enriched.

  Local Program Instance func_lift_lc : LocallyContractiveFunctor (func_lift f)
    := (@LocallyContractiveFunctor_comp_r SI _ _ _ _ _ _
          f (cat_proj2 C D) _ cat_proj2_enr).
End func_lift.

Definition func_const {SI} {C} (c : obj (PSh (OrdCat SI)))
  : functor (cat_prod C (PSh (OrdCat SI))) (PSh (OrdCat SI))
  := ((const_functor c : hom (C := Cat) _ _)
        ∘ (!ₕ ((cat_prod C (PSh (OrdCat SI))) : obj Cat))).

Notation "'Δᵨ'" := func_const (at level 40, no associativity)
    : contractive_scope.

Section func_const.
  Context {SI : indexT}.
  Context {C : category} (c : obj (PSh (OrdCat SI))).
  Context `{!Enriched C (PSh (OrdCat SI))}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI)) :=
    self_enriched (PSh (OrdCat SI)).
  Local Instance : Enriched (cat_prod C (PSh (OrdCat SI)))
                     (PSh (OrdCat SI)) := prod_enriched_def.

  Local Program Instance func_const_enr : EnrichedFunctor (func_const c)
    := MkEnrFunc (λ a b, (enr_embed (id _) ∘ !ₕ _)) _ _ _.
  Next Obligation.
    intros a b f.
    rewrite -{1}(right_id (⌜ id c ⌝)).
    rewrite comp_assoc.
    f_equiv; last done.
    rewrite (bang_unique (term_is_terminal _) (id (1ₒ))).
    rewrite (bang_unique (term_is_terminal _) ((!ₕ) (enr_hom a b) ∘ f)).
    reflexivity.
  Qed.
  Next Obligation.
    intros a b d.
    rewrite hom_prod_comp.
    rewrite -!comp_assoc.
    assert (enr_comp c c c ∘ (⌜ id c ⌝ ×ₕ ⌜ id c ⌝)
              ≡ ⌜ id c ⌝ ∘ !ₕ _) as ->.
    {
      intros ??? ->; simpl.
      simpl in *.
      destruct x as [[] []], y as [[] []]; simpl.
      intros ?? y ->; simpl.
      reflexivity.
    }
    rewrite !comp_assoc.
    f_equiv; last done.
    do 2 rewrite (bang_unique (term_is_terminal _) (_ ∘ _)).
    reflexivity.
  Qed.
  Next Obligation.
    intros a; simpl.
    rewrite natural_comp_assoc /=.
    intros ?? [] ->; simpl.
    intros ?? y ->; simpl.
    reflexivity.
  Qed.
  Fail Next Obligation.

  Program Definition func_const_lc_def (a b : obj (cat_prod C (PSh (OrdCat SI))))
    : natural (later_func (enr_hom a.1 b.1 ×ₒ (b.2 ↑ₒ a.2))) (c ↑ₒ c)
    := MkNat (λ x, λset f, MkNat (λ d, λset g, g.2) _) _.
  Next Obligation.
    repeat intros ?.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Fail Next Obligation.

  Local Program Instance func_const_lc : LocallyContractiveFunctor (func_const c)
    := MkLocContrFunc (λ a b, func_const_lc_def a b) _ _ _.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Next Obligation.
    repeat intros ?; simpl.
    solve_by_eq_rewrite.
  Qed.
  Fail Next Obligation.
End func_const.

Section exp_func.
  Context {SI : indexT}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI))
    := (@self_enriched (PSh (OrdCat SI)) _).
  Local Instance : Enriched ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))
    := op_enriched_def.
  Local Instance : Enriched (cat_prod ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI)))
                     (PSh (OrdCat SI))
    := prod_enriched_def.

  Local Opaque later next.

  Program Definition exp_psh_enr_def
    (a b : functor (OrdCat SI)ᵒᵖ Setoid * functor (OrdCat SI)ᵒᵖ Setoid)
    : natural (a.1 ↑ₒ b.1 ×ₒ (b.2 ↑ₒ a.2)) (b.2 ↑ₒ b.1 ↑ₒ (a.2 ↑ₒ a.1))
    := MkNat (λ x,
           λset f,
           MkNat (λ c,
               λset g,
               MkNat (λ d,
                   λset h,
                   ((f.2 ₙ d)
                      (g.1 ∘ h.1,
                        ((g.2 ₙ d) (h.1,
                             ((f.1 ₙ d) (g.1 ∘ h.1, h.2))))))) _) _) _.
  Next Obligation.
    intros ????????? ->.
    reflexivity.
  Qed.
  Next Obligation.
    intros ??? N ? M ?? F ?? H.
    rewrite (setoid_eq_reflect H) /=.
    rewrite -(psh_naturality N.2 _ _ F) /=; f_equiv.
    f_equiv; first done.
    rewrite -(psh_naturality M.2 _ _ F) /=; f_equiv.
    f_equiv; first done.
    rewrite -(psh_naturality N.1 _ _ F) /=; f_equiv.
    by f_equiv.
  Qed.
  Next Obligation.
    intros a b x f c.
    intros r t H.
    rewrite (setoid_eq_reflect H).
    reflexivity.
  Qed.
  Next Obligation.
    intros ????????? -> ??? ->; simpl.
    do 2 f_equiv; first done.
    do 2 f_equiv; first done.
    by do 2 f_equiv.
  Qed.
  Next Obligation.
    intros ????? H.
    rewrite (setoid_eq_reflect H).
    reflexivity.
  Qed.
  Next Obligation.
    intros ????? ?? -> ??? -> ??? ->; simpl.
    do 2 f_equiv; first done.
    do 2 f_equiv; first done.
    by do 2 f_equiv.
  Qed.
  Fail Next Obligation.

  Global Program Instance exp_psh_enr : EnrichedFunctor exp_func
    := MkEnrFunc (λ a b, exp_psh_enr_def a b) _ _ _.
  Next Obligation.
    intros a b f; simpl.
    intros ? [] [] _ a' ? y ->; simpl.
    intros d ? y' ->; simpl.
    pose proof ((naturality f y'.1 () () (reflexivity _))) as H.
    simpl in H.
    destruct H as [H1 H2].
    pose proof ((naturality f y.1 () () (reflexivity _))) as G.
    simpl in G.
    destruct G as [G1 G2].
    simpl in G1, G2.
    rewrite (H2 d) /=.
    rewrite (G2 d) /=.
    do 2 f_equiv; first done.
    do 2 f_equiv; first done.
    rewrite (H1 d) /=.
    rewrite (G1 d) /=.
    by f_equiv.
  Qed.
  Next Obligation.
    intros a b c; simpl.
    intros d ? y -> ?? y' -> ?? y'' ->; simpl.
    do 2 f_equiv; first done.
    do 2 f_equiv; first done.
    f_equiv; first done.
    f_equiv; first done.
    do 2 f_equiv; first done.
    by do 2 f_equiv.
  Qed.
  Next Obligation.
    intros a c ? y -> d ? y' -> e ? y'' ->; simpl.
    f_equiv.
    done.
  Qed.
  Fail Next Obligation.
End exp_func.

Example pcf_dom {SI : indexT}
  : functor (cat_prod ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))) (PSh (OrdCat SI))
  := (functor_compose exp_func later)
     +ᵨ (Δᵨ (1ₒ))
     +ᵨ (↑ᵨ later).
