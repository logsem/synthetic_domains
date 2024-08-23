From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat enriched.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Opaque later next.

Lemma transpose_compose_right {C} `{!HasTerm C, !HasProducts C
    , !HasExponentials C}
  {a b c d : obj C} (f : hom (b ×ₒ a) c) (g : hom d a) :
  transpose f ∘ g ≡ transpose (f ∘ (id _ ×ₕ g)).
Proof.
  unfold transpose.
  apply exp_hom_unique.
  rewrite -{2} (left_id (id b)).
  rewrite hom_prod_comp.
  rewrite -comp_assoc.
  by rewrite -(exp_hom_commutes (exponential_of b c)).
Qed.

Section later.
  Context {SI : indexT}.
  Local Instance : Enriched (PSh (OrdCat SI)) (PSh (OrdCat SI)) :=
    (@self_enriched (PSh (OrdCat SI)) _).

  Program Definition later_hom_action (F G : obj (PSh (OrdCat SI)))
  : hom (later ₒ (G ↑ₒ F)) ((later ₒ G) ↑ₒ (later ₒ F))
  := (transpose ((later ₕ eval _) ∘ (backward (later_prod _ _)))).

  Opaque comp.
  Opaque eval.
  Opaque id.
  Opaque prj1.
  Opaque prj2.

  Lemma later_hom_action_project_embed
    (F G : obj (PSh (OrdCat SI))) (f : hom (1ₒ) (G ↑ₒ F))
    : later_hom_action F G ∘ (next ₙ (G ↑ₒ F)) ∘ f
        ≡ transpose' (later ₕ untranspose' f).
  Proof.
    intros; simpl.
    unfold later_hom_action.
    rewrite comp_assoc.
    rewrite (naturality next f).
    rewrite -comp_assoc.
    rewrite transpose_compose_right.
    rewrite -h_map_id.
    rewrite comp_assoc.
    rewrite (@naturality _ _ _ _ (backward (later_preserves_prods_nat SI))
               (F, (1ₒ)) (F, (G ↑ₒ F)) (id F, f)).
    simpl.
    rewrite -comp_assoc.
    rewrite -h_map_comp.
    rewrite -{1} (transpose'_untranspose' f).
    unfold transpose' at 1.
    unfold transpose at 2.
    pose proof (exp_hom_commutes (exponential_of F G)
                  (untranspose' f ∘ term_times_proj F ∘ commutator F (1ₒ)))
      as HEQ.
    rewrite <-HEQ; clear HEQ.
    rewrite comp_assoc.
    rewrite commute_term_times_proj.
    rewrite h_map_comp.
    rewrite transpose_compose_right.
    rewrite comp_assoc.
    rewrite comp_assoc.
    assert ((later ₕ prj1 (product_of F (1ₒ))
        ∘ (backward (later_preserves_prods_nat SI)ₙ (F, term_func (OrdCat SI)ᵒᵖ Setoid)
             ∘ (id (later ₒ F) ×ₕ (next ₙ term_func (OrdCat SI)ᵒᵖ Setoid))))
              ≡ prj1 _) as ->.
    {
      unfold later_preserves_prods_nat.
      rewrite <-comp_assoc.
      rewrite (right_adj_preserves_prods_backward_prj1
                 later_adj _ _ _ _
                 (id (later ₒ F))
                 (next ₙ term_func (OrdCat SI)ᵒᵖ Setoid)).
      rewrite left_id.
      reflexivity.
    }
    unfold transpose'.
    rewrite comp_assoc.
    rewrite commute_term_times_proj.
    reflexivity.
  Qed.

  Lemma later_hom_action_contr_assoc
    (F G H : obj (PSh (OrdCat SI)))
    : (enr_comp _ _ _
         ∘ (later_hom_action F G ×ₕ (later_hom_action G H)))
        ≡ (later_hom_action F H ∘ (later ₕ enr_comp _ _ _) ∘ (backward (later_prod _ _))).
  Proof.
    simpl.
    rewrite transpose_compose_right.
    rewrite !comp_assoc.
    rewrite associator'_twist2.
    rewrite -(comp_assoc (associator' (later ₒ F) (later ₒ (G ↑ₒ F)) (later ₒ (H ↑ₒ G)))).
    rewrite -hom_prod_comp.
    rewrite left_id.
    unfold later_hom_action at 1.
    pose proof (eval_transpose
                  (later ₕ eval (exponential_of F G) ∘ backward (later_prod F (exp (exponential_of F G))))
                  (id (later ₒ F))) as HEQ.
    rewrite HEQ; clear HEQ.
    rewrite hom_prod_id.
    rewrite right_id.
    unfold later_hom_action at 1.
    rewrite <-comp_assoc.
    pose proof (eval_transpose
                  (later ₕ eval (exponential_of G H) ∘ backward (later_prod G (exp (exponential_of G H))))
                  (later ₕ eval (exponential_of F G) ∘ backward (later_prod F (exp (exponential_of F G))))) as HEQ.
    rewrite HEQ; clear HEQ.
    rewrite hom_prod_comp_right_id.
    simpl.
    rewrite <-h_map_id at 2.
    rewrite (comp_assoc _ (backward (later_preserves_prods_nat SI)ₙ (G, psh_exp G H))).
    rewrite -(comp_assoc _ _ (backward (later_preserves_prods_nat SI)ₙ (G, psh_exp G H))).
    epose proof (@naturality _ _ _ _
                   (backward (later_preserves_prods_nat SI))
                   ((F ×ₒ psh_exp F G), (psh_exp G H))
                   (G, (psh_exp G H))
                   ((eval (exponential_of F G)), id _)) as Hn.
    simpl in Hn; rewrite Hn; clear Hn.
    rewrite <-!comp_assoc.
    pose proof (h_map_comp _ _ later _ _ _ (eval (exponential_of F G) ×ₕ id (H ↑ₒ G))
                  (eval (exponential_of G H))) as HEQ.
    rewrite -HEQ; clear HEQ.
    rewrite ->!comp_assoc.
    assert ((backward (later_preserves_prods_nat SI)ₙ (F ×ₒ psh_exp F G, psh_exp G H)
               ∘ (backward (later_preserves_prods_nat SI)ₙ (F, psh_exp F G) ×ₕ id (later ₒ psh_exp G H)
                    ∘ associator' (later ₒ F) (later ₒ (G ↑ₒ F)) (later ₒ (H ↑ₒ G))))
               ≡ ((later ₕ (associator' F (G ↑ₒ F) (H ↑ₒ G)))
                    ∘ (backward (later_preserves_prods_nat SI)ₙ (F, (G ↑ₒ F ×ₒ (H ↑ₒ G)))))
               ∘ (id _ ×ₕ (backward (later_preserves_prods_nat SI)ₙ ((G ↑ₒ F), H ↑ₒ G)))) as ->.
    {
      rewrite -right_adj_preserves_prods_backward_assoc.
      simpl.
      unfold later_preserves_prods_nat.
      simpl.
      rewrite ->!comp_assoc.
      f_equiv.
      reflexivity.
    }
    rewrite <-!comp_assoc.
    rewrite -transpose_compose_right.
    epose proof (h_map_comp _ _ later _ _ _
                   (associator' F (G ↑ₒ F) (H ↑ₒ G))
                   (eval (exponential_of G H) ∘ (eval (exponential_of F G) ×ₕ id (H ↑ₒ G)))) as HEQ.
    rewrite -HEQ; clear HEQ.
    f_equiv.
    unfold later_hom_action.
    simpl.
    unfold inner_comp.
    simpl.
    rewrite transpose_compose_right.
    f_equiv.
    rewrite -h_map_id.
    epose proof (comp_assoc _ _ (later ₕ eval (exponential_of F H))) as HEQ.
    rewrite HEQ; clear HEQ.
    epose proof (@naturality _ _ _ _
                   (backward (later_preserves_prods_nat SI))
                   (F, (psh_exp F G ×ₒ psh_exp G H))
                   (F, (H ↑ₒ F))
                   (id F, (transpose
                             (eval (exponential_of G H) ∘ (eval (exponential_of F G) ×ₕ id (H ↑ₒ G))
                                ∘ associator' F (psh_exp F G) (psh_exp G H))))) as Hn.
    simpl in Hn.
    rewrite Hn; clear Hn.
    rewrite <-!comp_assoc.
    f_equiv.
    rewrite -h_map_comp.
    pose proof (eval_transpose2 ((eval (exponential_of G H) ∘ (eval (exponential_of F G) ×ₕ id (H ↑ₒ G))
                                     ∘ associator' F (psh_exp F G) (psh_exp G H)))) as HEQ.
    rewrite HEQ; clear HEQ.
    reflexivity.
  Qed.

  Lemma later_hom_action_enr_assoc
    (F G H : obj (PSh (OrdCat SI)))
    : enr_comp _ _ _
        ∘ (later_hom_action F G ∘ (next ₙ (G ↑ₒ F)) ×ₕ (later_hom_action G H ∘ (next ₙ (H ↑ₒ G))))
        ≡ later_hom_action F H ∘ (next ₙ (H ↑ₒ F)) ∘ enr_comp _ _ _.
  Proof.
    intros; simpl.
    rewrite hom_prod_comp.
    rewrite -!comp_assoc.
    rewrite later_hom_action_contr_assoc.
    rewrite ->!comp_assoc.
    f_equiv; last done.
    simpl.
    pose proof (naturality next (inner_comp F G H))
      as Hn'.
    simpl in Hn'; rewrite Hn'; clear Hn'.
    f_equiv; last done.
    rewrite <-(left_id (next ₙ (G ↑ₒ F ×ₒ (H ↑ₒ G)))).
    epose proof (iso_lr (is_iso (natural_iso_proj (later_preserves_prods_nat SI) (G ↑ₒ F, H ↑ₒ G)))) as HEQ.
    simpl in HEQ.
    rewrite <-HEQ; clear HEQ.
    rewrite ->!comp_assoc.
    f_equiv; last done.
    unfold later_preserves_prods_nat.
    rewrite (right_adj_preserves_prods_forward later_adj).
    simpl.
    rewrite hom_to_prod_comp_r.
    pose proof (naturality next (prj1 (product_of (G ↑ₒ F) (H ↑ₒ G)))) as HEQ.
    rewrite <-HEQ; clear HEQ.
    pose proof (naturality next (prj2 (product_of (G ↑ₒ F) (H ↑ₒ G)))) as HEQ.
    rewrite <-HEQ; clear HEQ.
    simpl.
    rewrite hom_to_prod_comp.
    rewrite <-(right_id (prj1 (product_of (G ↑ₒ F) (H ↑ₒ G)))).
    rewrite <-(right_id (prj2 (product_of (G ↑ₒ F) (H ↑ₒ G)))).
    rewrite hom_to_prod_of_prjs.
    rewrite right_id.
    reflexivity.
  Qed.

  Lemma later_hom_action_contr_id
    (F : obj (PSh (OrdCat SI)))
    : later_hom_action F _ ∘ (later ₕ (transpose' (id _))) ∘ (next ₙ (1ₒ))
        ≡ transpose' (id (later ₒ F)).
  Proof.
    unfold later_hom_action.
    rewrite transpose_compose_right.
    rewrite <-h_map_id.
    simpl.
    rewrite comp_assoc.
    epose proof (@naturality _ _ _ _
                   (backward (later_preserves_prods_nat SI))
                   (F, (1ₒ))
                   (F, psh_exp F F)
                   (id F, transpose' (id F)))
      as Hn.
    simpl in Hn; rewrite Hn; clear Hn.
    rewrite <-comp_assoc.
    rewrite <-h_map_comp.
    unfold transpose'.
    epose proof (eval_transpose
                   (id F ∘ term_times_proj F ∘ commutator F (1ₒ))
                   (id F))
      as HEQ.
    rewrite HEQ; clear HEQ.
    rewrite hom_prod_id.
    rewrite left_id right_id.
    rewrite h_map_id left_id.
    rewrite !commute_term_times_proj.
    rewrite transpose_compose_right.
    unfold later_preserves_prods_nat.
    rewrite right_adj_preserves_prods_backward_prj1.
    rewrite left_id.
    reflexivity.
  Qed.

  Lemma later_hom_action_enr_id
    (F : obj (PSh (OrdCat SI)))
    : later_hom_action F F ∘ (next ₙ _) ∘ (transpose' (id _))
        ≡ transpose' (id (later ₒ F)).
  Proof.
    intros; simpl.
    rewrite -later_hom_action_contr_id.
    rewrite ->!comp_assoc.
    f_equiv; last done.
    rewrite -naturality.
    f_equiv.
    reflexivity.
  Qed.

  Global Program Instance later_enriched
    : EnrichedFunctor (C := (PSh (OrdCat SI)))
        (D := (PSh (OrdCat SI)))
        (E := (PSh (OrdCat SI))) later
    := MkEnrFunc
         (λ a b, (later_hom_action _ _ ∘ (next ₙ _)))
         _
         _
         _.
  Next Obligation.
    intros; simpl.
    by rewrite later_hom_action_project_embed.
  Qed.
  Next Obligation.
    intros; simpl.
    by rewrite later_hom_action_enr_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    by rewrite later_hom_action_enr_id.
  Qed.

  Global Program Instance later_lc
    : @LocallyContractiveFunctor SI (PSh (OrdCat SI)) (PSh (OrdCat SI)) _ _ later
    := MkLocContrFunc
         (λ a b, later_hom_action a b)
         _
         _
         _.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    by rewrite later_hom_action_contr_assoc.
  Qed.
  Next Obligation.
    intros; simpl.
    by rewrite later_hom_action_contr_id.
  Qed.

  Transparent comp.
  Transparent eval.
  Transparent id.
  Transparent prj1.
  Transparent prj2.
End later.

Section solution_unique.
  Context {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
    (F : functor C C) `{!LocallyContractiveFunctor F}.

  Record solution := MkSolution { sol_obj : obj C; sol_iso : (F ₒ sol_obj) ≃ sol_obj}.

  Definition alg_of_solution (S : solution) : algebra F :=
    MkAlg (sol_obj S) (forward (sol_iso S)).

  Definition solution_to_alg (S : solution) (A : algebra F) :
    natural (enr_hom (sol_obj S) (car A)) (enr_hom (sol_obj S) (car A)) :=
    enr_comp_r (backward (sol_iso S)) ∘
    (enr_comp_l (cons A) ∘
    enr_func_h_map F (sol_obj S) (car A)).

  Program Definition fix_of_solution_to_alg_alg_hom (S : solution) (A : algebra F)
    (fx : natural (1ₒ) (enr_hom (sol_obj S) (car A)))
    (fx_fix : (solution_to_alg S A) ∘@{PSh _} fx ≡ fx) :
    alg_hom (alg_of_solution S) A :=
    MkAlgHom ⌞fx⌟ _.
  Next Obligation.
    intros S A fx fx_fix.
    rewrite -{1}fx_fix /solution_to_alg.
    rewrite comp_assoc enr_comp_r_comp -enr_comp_comp !enr_embed_project.
    rewrite comp_assoc enr_comp_l_comp -enr_comp_comp !enr_embed_project.
    rewrite -enr_func_h_map_is_h_map !enr_embed_project.
    rewrite !comp_assoc /alg_of_solution /=.
    pose proof (is_iso (sol_iso S)) as [-> _].
    rewrite right_id //.
  Qed.
  Fail Next Obligation.

  Lemma alg_hom_from_solution_is_fix (S : solution) (A : algebra F)
    (h : alg_hom (alg_of_solution S) A) :
    (solution_to_alg S A) ∘@{PSh _} ⌜alg_hom_map h⌝ ≡ ⌜alg_hom_map h⌝.
  Proof.
    rewrite /solution_to_alg.
    rewrite (comp_assoc _ _ (enr_comp_r _))
      (comp_assoc _ _ (enr_comp_l _)).
    rewrite -enr_func_h_map_is_h_map !enr_embed_project.
    rewrite enr_comp_l_comp -enr_comp_comp !enr_embed_project.
    rewrite enr_comp_r_comp -enr_comp_comp !enr_embed_project.
    rewrite -(alg_hom_commutes h).
    rewrite !comp_assoc /alg_of_solution /=.
    pose proof (is_iso (sol_iso S)) as [_ ->].
    rewrite right_id //.
  Qed.

  Program Definition alg_of_solution_is_initial S :
    @is_initial (Alg F) (alg_of_solution S) :=
    MkIsInit _
      (λ A, fix_of_solution_to_alg_alg_hom S A
              (contr_fix (solution_to_alg S A))
              (contr_fix_unfold (solution_to_alg S A)))
      _.
  Next Obligation.
    intros S A h; simpl.
    match goal with
    |- ?A ≡ ?B =>
      assert (alg_hom_map A ≡ alg_hom_map B); last done;
      rewrite -(enr_embed_project (alg_hom_map A))
        -(enr_embed_project (alg_hom_map B))
    end.
    f_equiv.
    apply (contr_fix_unique (solution_to_alg S A)).
    - apply alg_hom_from_solution_is_fix.
    - apply alg_hom_from_solution_is_fix.
  Qed.
  Fail Next Obligation.

  Definition solution_unique (S S' : solution) : sol_obj S ≃ sol_obj S' :=
    alg_iso
      (@is_initial_unique (Alg F) _ _
         (alg_of_solution_is_initial S)
         (alg_of_solution_is_initial S')).

End solution_unique.

Section op_enriched.
  Context `{!HasTerm E} `{!HasProducts E} `{!Enriched C E}.

  Program Definition op_enriched_def
    : Enriched (C ᵒᵖ) E :=
    MkEnr
      (λ x y, enr_hom (y : obj C) (x : obj C))
      (λ x y f, enr_embed (C := C) f)
      (λ x y f, enr_project (C := C) f)
      (λ x y z, enr_comp (C := C) z y x ∘ commutator _ _)
      _ _ _ _ _ _ _ _.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply enr_embed_project.
  Qed.
  Next Obligation.
    intros; simpl in *.
    apply enr_project_embed.
  Qed.
  Next Obligation.
    intros; simpl in *.
    rewrite comp_assoc commute_hom_to_prod.
    apply enr_comp_comp.
  Qed.
  Next Obligation.
    intros; simpl in *.

    rewrite !comp_assoc.
    rewrite hom_prod_comp_right_id.
    rewrite -(comp_assoc _ (enr_comp c b a ×ₕ id (enr_hom d c))).
    rewrite -commute_hom_prod.
    rewrite (comp_assoc
               (commutator (enr_hom b a) (enr_hom c b) ×ₕ id (enr_hom d c))).
    rewrite -!comp_assoc.
    rewrite enr_comp_assoc'.
    rewrite !comp_assoc.

    f_equiv.
    rewrite -commute_hom_prod.
    rewrite hom_prod_comp_left_id.
    rewrite -!comp_assoc.
    rewrite -commute_hom_prod.
    rewrite !comp_assoc.
    f_equiv.

    rewrite commute_hom_prod.
    rewrite hom_to_prod_comp_r.
    rewrite -!comp_assoc.
    rewrite hom_to_prod_prj1.
    rewrite left_id.
    rewrite hom_to_prod_prj2.
    rewrite prj1_associator.
    rewrite !comp_assoc.
    rewrite prj2_associator.
    rewrite commute_hom_to_prod.


    rewrite /associator' /commutator.
    rewrite commute_hom_to_prod.
    rewrite left_id.
    rewrite ->3 hom_to_prod_comp_r.
    rewrite !comp_assoc.
    rewrite hom_to_prod_prj2 hom_to_prod_prj2.
    rewrite hom_to_prod_prj1 hom_to_prod_prj1.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    by rewrite !comp_assoc -commute_hom_prod
                              -!comp_assoc
                              enr_right_id
                              commute_term_times_proj.
  Qed.
  Next Obligation.
    intros; simpl in *.
    by rewrite !comp_assoc -commute_hom_prod
                              -!comp_assoc
                              enr_left_id
                              /commutator hom_to_prod_prj1
    .
  Qed.
  Fail Next Obligation.

End op_enriched.

Section prod_enriched.
  Context `{!HasTerm E} `{!HasProducts E} `{!Enriched C E} `{!Enriched D E}.

  Program Definition prod_enriched_def
    : Enriched (cat_prod C D) E :=
    MkEnr
      (λ x y, enr_hom (x.1 : obj C) (y.1 : obj C)
                ×ₒ enr_hom (x.2 : obj D) (y.2 : obj D))
      (λ x y f, << enr_embed (C := C) f.1, enr_embed (C := D) f.2 >>)
      (λ x y f, (enr_project (C := C) ((prj1 _) ∘ f)
                  , (enr_project (C := D) ((prj2 _) ∘ f))))
      (λ x y z, << enr_comp _ _ _
                  ∘ (prj1 _ ×ₕ prj1 _)
        , enr_comp _ _ _
            ∘ (prj2 _ ×ₕ prj2 _)>>)
      _ _ _ _ _ _ _ _.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    solve_proper.
  Qed.
  Next Obligation.
    intros; simpl in *.
    by rewrite hom_to_prod_prj1 hom_to_prod_prj2 !enr_embed_project.
  Qed.
  Next Obligation.
    intros; simpl in *.
    by rewrite !enr_project_embed hom_to_prod_of_prjs.
  Qed.
  Next Obligation.
    intros; simpl in *.
    rewrite !enr_comp_comp.
    rewrite hom_to_prod_comp_r.
    f_equiv;
      (rewrite comp_assoc;
       rewrite hom_to_prod_comp;
       reflexivity).
  Qed.
  Next Obligation.
    intros; simpl in *.
    rewrite !comp_assoc.
    rewrite hom_to_prod_comp_r.
    rewrite (comp_assoc _ _ (enr_comp a.1 b.1 d.1)).
    rewrite (comp_assoc _ _ (enr_comp a.2 b.2 d.2)).
    rewrite -(comp_assoc _ _
                (prj1 (product_of (enr_hom a.1 b.1) (enr_hom a.2 b.2))
                   ×ₕ prj1 (product_of (enr_hom b.1 d.1) (enr_hom b.2 d.2)))).
    rewrite -(comp_assoc _ _
                (prj2 (product_of (enr_hom a.1 b.1) (enr_hom a.2 b.2))
                   ×ₕ prj2 (product_of (enr_hom b.1 d.1) (enr_hom b.2 d.2)))).
    rewrite -!hom_prod_comp.
    rewrite !right_id.
    rewrite hom_to_prod_prj1.
    rewrite hom_to_prod_prj2.
    assert (∀ (a b c d : obj C * obj D),
              (prj1 (product_of (enr_hom a.1 b.1) (enr_hom a.2 b.2))
                 ×ₕ (enr_comp b.1 c.1 d.1
                       ∘ (prj1 (product_of (enr_hom b.1 c.1) (enr_hom b.2 c.2))
                            ×ₕ prj1 (product_of (enr_hom c.1 d.1)
                                       (enr_hom c.2 d.2))))
                 ∘ associator (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2)
                 (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2)
                 (enr_hom c.1 d.1 ×ₒ enr_hom c.2 d.2))
                ≡
                (id (enr_hom a.1 b.1) ×ₕ enr_comp b.1 c.1 d.1)
                ∘ associator (enr_hom a.1 b.1) (enr_hom b.1 c.1) (enr_hom c.1 d.1)
                ∘ ((prj1 _ ×ₕ prj1 _) ×ₕ prj1 _)) as ->.
    {
      clear.
      intros.
      rewrite -associator'_twist1.
      rewrite -!comp_assoc.
      rewrite (comp_assoc (associator' (enr_hom a.1 b.1) (enr_hom b.1 c.1)
                             (enr_hom c.1 d.1))).
      rewrite associator_associator'.
      f_equiv.
      rewrite right_id.
      rewrite -hom_prod_comp.
      rewrite left_id.
      reflexivity.
    }
    assert (∀ (a b c d : obj C * obj D),
              (prj2 (product_of (enr_hom a.1 b.1)
                       (enr_hom a.2 b.2))
                 ×ₕ (enr_comp b.2 c.2 d.2
                       ∘ (prj2 (product_of (enr_hom b.1 c.1) (enr_hom b.2 c.2))
                            ×ₕ prj2
                            (product_of (enr_hom c.1 d.1) (enr_hom c.2 d.2))))
                 ∘ associator (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2)
                 (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2)
                 (enr_hom c.1 d.1 ×ₒ enr_hom c.2 d.2))
                ≡
                (id (enr_hom a.2 b.2) ×ₕ enr_comp b.2 c.2 d.2)
                ∘ associator (enr_hom a.2 b.2) (enr_hom b.2 c.2)
                (enr_hom c.2 d.2)
                ∘ ((prj2 _ ×ₕ prj2 _) ×ₕ prj2 _)) as ->.
    {
      clear.
      intros.
      rewrite -associator'_twist1.
      rewrite -!comp_assoc.
      rewrite (comp_assoc (associator' (enr_hom a.2 b.2) (enr_hom b.2 c.2)
                             (enr_hom c.2 d.2))).
      rewrite associator_associator'.
      f_equiv.
      rewrite right_id.
      rewrite -hom_prod_comp.
      rewrite left_id.
      reflexivity.
    }
    rewrite -!comp_assoc.
    rewrite !enr_comp_assoc.
    rewrite hom_to_prod_comp_r.
    f_equiv.
    - rewrite !comp_assoc.
      f_equiv.
      rewrite -!hom_prod_comp.
      rewrite hom_to_prod_prj1.
      f_equiv; first reflexivity.
      by rewrite right_id left_id.
    - rewrite !comp_assoc.
      f_equiv.
      rewrite -!hom_prod_comp.
      rewrite hom_to_prod_prj2.
      f_equiv; first reflexivity.
      by rewrite right_id left_id.
  Qed.
  Next Obligation.
    intros; simpl in *.
    rewrite hom_to_prod_comp_r.
    rewrite !comp_assoc.
    rewrite -!hom_prod_comp.
    rewrite !right_id.
    rewrite hom_to_prod_prj1 hom_to_prod_prj2.
    rewrite hom_prod_split.
    rewrite -comp_assoc.
    rewrite enr_left_id.
    rewrite (hom_prod_split (prj2 (product_of
                                     (enr_hom a.1 b.1) (enr_hom a.2 b.2)))).
    rewrite -comp_assoc.
    rewrite enr_left_id.
    rewrite !hom_prod_prj1.
    rewrite hom_to_prod_of_prjs.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl in *.
    rewrite hom_to_prod_comp_r.
    rewrite !comp_assoc.
    rewrite -!hom_prod_comp.
    rewrite !right_id.
    rewrite hom_to_prod_prj1 hom_to_prod_prj2.
    rewrite -(left_id (prj1 (product_of (enr_hom a.1 b.1) (enr_hom a.2 b.2)))).
    rewrite -(right_id (⌜ id a.1 ⌝)).
    rewrite hom_prod_comp.
    rewrite -comp_assoc.
    rewrite enr_right_id.
    rewrite -(left_id (prj2 (product_of (enr_hom a.1 b.1) (enr_hom a.2 b.2)))).
    rewrite -(right_id (⌜ id a.2 ⌝)).
    rewrite hom_prod_comp.
    rewrite -comp_assoc.
    rewrite enr_right_id.
    rewrite !hom_prod_prj2.
    rewrite hom_to_prod_of_prjs.
    reflexivity.
  Qed.
  Fail Next Obligation.

End prod_enriched.

Section psh_op_limits_enriched.
  Context {SI : indexT} {J} {F : functor J ((PSh (OrdCat SI)) ᵒᵖ)}
    {L : PreSheaf (OrdCat SI)} (il : is_limit F L).

  Local Instance : Enriched ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))
    := @op_enriched_def _ _ _ _ (self_enriched _).

  Opaque func_cat_colimits_pointwise.

  Program Definition psh_colimits_enriched_enr_cocone_to_pointwise_cocone
    {α} (cn : enr_cone F α) : cone (pointwise_func_colim F α) :=
    MkCone (enr_vertex cn ₒ α)
      (λ j, λset x, (enr_side cn j ₙ α) (id _, x)) _.
  Next Obligation. repeat intros ?; simpl in *; repeat f_equiv; done. Qed.
  Next Obligation.
    intros ?? j j' f x y <-; clear y; simpl in *.
    rewrite (λ z, enr_side_commutes cn f α
                    ((reflexivity _), z) _ (reflexivity _)) /=.
    repeat f_equiv; done.
  Qed.
  Fail Next Obligation.

  Program Definition enr_cocone_coherent_partial_cocone {α} (cn : enr_cone F α) :
    coherent_partial_cocone _ α :=
    MkCohParCocone _ _
      (psh_colimits_enriched_enr_cocone_to_pointwise_cocone cn)
      (λ _ f, (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                 (enr_cone_natural cn f)))
      (λ _ f, (enr_vertex cn ₕ f))
      _
      .
  Next Obligation.
    intros α cn β f j x y <-; clear y; simpl in *.
    epose proof (naturality (enr_side cn j) f (_, _) _ (reflexivity _)) as Hn;
      simpl in Hn; rewrite -Hn /=; clear Hn.
    repeat f_equiv; done.
  Qed.

  Program Definition psh_colimits_enriched_enr_cocone_hom_back {α}
    (cn : enr_cone F α) :
    enr_cone_hom cn (cone_to_enr_cone (cone_of_is_cone (il_is_cone il)) α) :=
    MkEnrConeHom
      (MkNat (λ c, λset f,
           (cone_hom_map
              (bang (il_is_limiting_cone _ _
                       (func_cat_colimits_pointwise F il c))
                 (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                    (enr_cone_natural cn f.1))) f.2)) _)
      _.
  Next Obligation.
    intros ??? [le1 ?] [le2 ?] [? ->];
      replace le1 with le2 by apply proof_irrel; done.
  Qed.
  Next Obligation.
    intros α cn β γ f [le x] [le' y] [? <-];
      replace le' with le by apply proof_irrel;
      clear dependent le'; clear y; simpl in *.
    replace (transitivity le (reflexivity α)) with le by apply proof_irrel.
    epose proof (func_cat_colimits_pointwise_natural F il
      (enr_cocone_coherent_partial_cocone (enr_cone_natural cn le))
      f x _ (reflexivity _)) as Hpln.
    simpl in Hpln; rewrite Hpln /=; clear Hpln.
    f_equiv; last done.
    apply (hom_to_limit_unique
             _ _ _ (func_cat_colimits_pointwise F il γ)
             (cone_is_cone
                (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                   (enr_cone_natural (enr_cone_natural cn le) f)))).
    - intros ??? ->; simpl in *.
      pose proof (cone_hom_commutes
                    (bang (il_is_limiting_cone
                             (pointwise_func_colim F γ) (L ₒ γ)
                             (func_cat_colimits_pointwise F il γ))
                       (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                          (enr_cone_natural cn (transitivity f le)))) j y) as HEQ.
      simpl in HEQ; rewrite -HEQ; clear HEQ; last done.
      do 2 f_equiv.
      f_equal.
    - intros ??? ->; simpl in *.
      pose proof (cone_hom_commutes
                    (bang (il_is_limiting_cone
                             (pointwise_func_colim F γ) (L ₒ γ)
                             (func_cat_colimits_pointwise F il γ))
                       (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                          (enr_cone_natural (enr_cone_natural cn le) f))) j y) as HEQ.
      simpl in HEQ; rewrite -HEQ; clear HEQ; last done.
      do 2 f_equiv.
  Qed.
  Next Obligation.
    intros α cn j β [le x] [le' y] [? <-];
      replace le' with le by apply proof_irrel;
      clear dependent le'; clear y; simpl in *.

    epose proof (cone_hom_commutes (bang
            (il_is_limiting_cone (pointwise_func_colim F β)
               (L ₒ β) (func_cat_colimits_pointwise F il β))
            (psh_colimits_enriched_enr_cocone_to_pointwise_cocone _))
      j _ _ (reflexivity _)) as Hn; simpl in Hn; rewrite -Hn /=; clear Hn.
    repeat f_equiv; done.
  Qed.
  Fail Next Obligation.

  Program Definition psh_colimits_enr_cocone_hom_to_cocone_hom {α cn β}
    (le : β ⪯ α)
    (h : enr_cone_hom cn
           (cone_to_enr_cone (cone_of_is_cone (il_is_cone il)) α)) :
      cone_hom
        (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
           (enr_cone_natural cn le))
        (cone_of_is_cone (il_is_cone (func_cat_colimits_pointwise F il β))) :=
  MkConeHom (λset x, (enr_cone_hom_map h ₙ β) (le, x)) _.
  Next Obligation. intros ??????? ->; done. Qed.
  Next Obligation.
    intros ???? h ??? ->; simpl in *.
    epose proof (enr_cone_hom_commutes h _ _ (_, _) _ (reflexivity _)) as Hsc;
    simpl in Hsc; rewrite Hsc; clear.
    repeat f_equiv; done.
  Qed.
  Fail Next Obligation.

  Program Definition psh_op_limits_enriched : enr_limit il :=
    λ α, MkEnrConeIsLimit (λ cn, psh_colimits_enriched_enr_cocone_hom_back cn) _.
  Next Obligation.
    intros α cn h h' β [le x] [le' y] [? <-];
      replace le' with le by apply proof_irrel;
      clear dependent le'; clear y; simpl in *.
    epose proof (@bang_unique _ _
                   (il_is_limiting_cone _ _
                      (func_cat_colimits_pointwise F il β))
                   (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                      (enr_cone_natural cn le))
                   (psh_colimits_enr_cocone_hom_to_cocone_hom le h) x _
                   (reflexivity _)) as Hbu;
      simpl in Hbu; rewrite Hbu; clear Hbu.
    epose proof (@bang_unique _ _
                   (il_is_limiting_cone _ _
                      (func_cat_colimits_pointwise F il β))
                   (psh_colimits_enriched_enr_cocone_to_pointwise_cocone
                      (enr_cone_natural cn le))
                   (psh_colimits_enr_cocone_hom_to_cocone_hom le h') x _
                   (reflexivity _)) as Hbu;
      simpl in Hbu; rewrite Hbu; clear Hbu.
    done.
  Qed.

End psh_op_limits_enriched.

Section psh_op_limits_enriched.
  Context {SI : indexT}.

  Local Instance : Enriched ((PSh (OrdCat SI)) ᵒᵖ) (PSh (OrdCat SI))
    := @op_enriched_def _ _ _ _ (self_enriched _).

  Global Instance op_limits_enriched : LimitsEnriched ((PSh (OrdCat SI)) ᵒᵖ)
    := λ J F c il, psh_op_limits_enriched il.

End psh_op_limits_enriched.

Section proj_limits.
  Context {C D : category}.

  Context {J} {F : functor J (cat_prod C D)}
    {L : obj (cat_prod C D)} (il : is_limit F L).

  Local Program Definition cone_from_limit_left
    (c : cone (functor_compose F (cat_proj1 C D)))
    : cone F := MkCone
                  (vertex c, L.2)
                  (λ j, ((side c j), (ic_side (il_is_cone il) j).2))
                  (λ j j' f,
                    conj
                      (side_commutes c f)
                      (proj2 (ic_side_commutes (il_is_cone il) f))).

  Local Definition cone_from_limit_left_proj
    (c : cone (functor_compose F (cat_proj1 C D)))
    : cone_hom (cone_from_limit_left c) (cone_of_is_cone (il_is_cone il)) :=
    (bang (il_is_limiting_cone _ _ il) (cone_from_limit_left c)).

  Local Program Definition cone_proj1
    : is_cone (functor_compose F (cat_proj1 C D)) L.1 :=
    MkIsCone
      L.1
      (λ j, (ic_side (il_is_cone il) j).1)
      (λ j j' f, proj1 (ic_side_commutes (il_is_cone il) f)).

  Local Program Definition extend_cone_proj1
    (c : cone (functor_compose F (cat_proj1 C D)))
    (f : cone_hom c (cone_of_is_cone cone_proj1))
    : cone_hom (cone_from_limit_left c) (cone_of_is_cone (il_is_cone il))
    := MkConeHom (cone_hom_map f, id _)
         (λ j, conj
                 (cone_hom_commutes f j)
                 (symmetry (right_id _))).

  Program Definition limit_proj1
    : is_limit (functor_compose F (cat_proj1 C D)) L.1
    := MkIsLimit
         cone_proj1
         (MkIsTerm
            _
            (λ c, MkConeHom
                    (cone_hom_map (cone_from_limit_left_proj c)).1
                    (λ j, (proj1 (cone_hom_commutes
                                    (cone_from_limit_left_proj c) j))))
            (λ c f, (proj1 (bang_unique (il_is_limiting_cone _ _ il)
                              (extend_cone_proj1 c f))))).

  Local Program Definition cone_from_limit_right
    (c : cone (functor_compose F (cat_proj2 C D)))
    : cone F := MkCone
                  (L.1, vertex c)
                  (λ j, ((ic_side (il_is_cone il) j).1, (side c j)))
                  (λ j j' f,
                    conj
                      (proj1 (ic_side_commutes (il_is_cone il) f))
                      (side_commutes c f)).

  Local Definition cone_from_limit_right_proj
    (c : cone (functor_compose F (cat_proj2 C D)))
    : cone_hom (cone_from_limit_right c) (cone_of_is_cone (il_is_cone il)) :=
    (bang (il_is_limiting_cone _ _ il) (cone_from_limit_right c)).

  Local Program Definition cone_proj2
    : is_cone (functor_compose F (cat_proj2 C D)) L.2 :=
    MkIsCone
      L.2
      (λ j, (ic_side (il_is_cone il) j).2)
      (λ j j' f, proj2 (ic_side_commutes (il_is_cone il) f)).

  Local Program Definition extend_cone_proj2
    (c : cone (functor_compose F (cat_proj2 C D)))
    (f : cone_hom c (cone_of_is_cone cone_proj2))
    : cone_hom (cone_from_limit_right c) (cone_of_is_cone (il_is_cone il))
    := MkConeHom (id _, cone_hom_map f)
         (λ j, conj
                 (symmetry (right_id _))
                 (cone_hom_commutes f j)).

  Program Definition limit_proj2
    : is_limit (functor_compose F (cat_proj2 C D)) L.2
    := MkIsLimit
         cone_proj2
         (MkIsTerm
            _
            (λ c, MkConeHom
                    (cone_hom_map (cone_from_limit_right_proj c)).2
                    (λ j, (proj2 (cone_hom_commutes
                                    (cone_from_limit_right_proj c) j))))
            (λ c f, (proj2 (bang_unique (il_is_limiting_cone _ _ il)
                              (extend_cone_proj2 c f))))).
End proj_limits.

Section prod_limits_enriched.
  Context {SI : indexT}
    `{!Enriched C (PSh (OrdCat SI)), !Enriched D (PSh (OrdCat SI))}.

  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI))
    := @prod_enriched_def (PSh (OrdCat SI)) _ _ _ _ _ _.

  Context `{HLE1 : !LimitsEnriched C, HLE2 : !LimitsEnriched D}.

  Context {J} {F : functor J (cat_prod C D)}
    {L : obj (cat_prod C D)} (il : is_limit F L).

  Local Program Definition restrict_enr_cone_left {α} (cn : enr_cone F α)
    : enr_cone (functor_compose F (cat_proj1 C D)) α
    := MkEnrCone
         (enr_vertex cn).1
         (λ j, (enr_side cn j).1)
         (λ j j' f, (proj1 (enr_side_commutes cn f))).

  Local Program Definition restrict_enr_cone_right {α} (cn : enr_cone F α)
    : enr_cone (functor_compose F (cat_proj2 C D)) α
    := MkEnrCone
         (enr_vertex cn).2
         (λ j, (enr_side cn j).2)
         (λ j j' f, (proj2 (enr_side_commutes cn f))).

  Local Program Definition restrict_enr_hom_left {α}
    (cn' : enr_cone F α)
    (h : enr_cone_hom cn'
           (cone_to_enr_cone (cone_of_is_cone (il_is_cone il)) α))
    : enr_cone_hom (restrict_enr_cone_left cn')
        (cone_to_enr_cone (cone_of_is_cone (il_is_cone (limit_proj1 _))) α)
    := MkEnrConeHom (enr_cone_hom_map h).1
         (λ j, proj1 (enr_cone_hom_commutes h j)).

  Local Program Definition restrict_enr_hom_right {α}
    (cn' : enr_cone F α)
    (h : enr_cone_hom cn'
           (cone_to_enr_cone (cone_of_is_cone (il_is_cone il)) α))
    : enr_cone_hom (restrict_enr_cone_right cn')
        (cone_to_enr_cone (cone_of_is_cone (il_is_cone (limit_proj2 _))) α)
    := MkEnrConeHom (enr_cone_hom_map h).2
         (λ j, proj2 (enr_cone_hom_commutes h j)).

  Local Program Definition prod_limits_enriched_enr_cone_hom_back {α}
    (cn : enr_cone F α) :
    enr_cone_hom cn (cone_to_enr_cone (cone_of_is_cone (il_is_cone il)) α) :=
    MkEnrConeHom
      ((enr_cone_hom_map (enr_limit_hom
                            (HLE1 J (functor_compose F (cat_proj1 _ _)) L.1
                               (limit_proj1 _) α)
                            (restrict_enr_cone_left cn))),
        (enr_cone_hom_map (enr_limit_hom
                             (HLE2 J (functor_compose F (cat_proj2 _ _)) L.2
                                (limit_proj2 _) α)
                             (restrict_enr_cone_right cn))))
      (λ j, conj
              (enr_cone_hom_commutes (enr_limit_hom
                                        (HLE1 J (functor_compose F
                                                   (cat_proj1 _ _)) L.1
                                           (limit_proj1 _) α)
                                        (restrict_enr_cone_left cn)) j)
              (enr_cone_hom_commutes (enr_limit_hom
                                        (HLE2 J (functor_compose F
                                                   (cat_proj2 _ _)) L.2
                                           (limit_proj2 _) α)
                                        (restrict_enr_cone_right cn)) j)).

  Program Definition prod_limits_enriched_lim : enr_limit il :=
    λ α, MkEnrConeIsLimit (λ cn, prod_limits_enriched_enr_cone_hom_back cn) _.
  Next Obligation.
    intros; simpl.
    split.
    - apply (@enr_limit_hom_unique _ _ _ _ _ _ _
               (HLE1 J (functor_compose F (cat_proj1 _ _)) L.1
                  (limit_proj1 _) α)
               (restrict_enr_cone_left cn')
               (restrict_enr_hom_left cn' h)
               (restrict_enr_hom_left cn' h')).
    - apply (@enr_limit_hom_unique _ _ _ _ _ _ _
               (HLE2 J (functor_compose F (cat_proj2 _ _)) L.2
                  (limit_proj2 _) α)
               (restrict_enr_cone_right cn')
               (restrict_enr_hom_right cn' h)
               (restrict_enr_hom_right cn' h')).
  Qed.

End prod_limits_enriched.

Section prod_limits_enriched.
  Context {SI : indexT}
    `{!Enriched C (PSh (OrdCat SI)), !Enriched D (PSh (OrdCat SI))}.

  Local Instance : Enriched (cat_prod C D) (PSh (OrdCat SI))
    := @prod_enriched_def (PSh (OrdCat SI)) _ _ _ _ _ _.

  Context `{!LimitsEnriched C, !LimitsEnriched D}.

  Global Instance prod_limits_enriched : LimitsEnriched (cat_prod C D)
    := λ J F c il, prod_limits_enriched_lim il.

End prod_limits_enriched.

Section enr_func_to_prod.
  Context {C D E Z}
    `{!HasTerm Z, !HasProducts Z}
    `{!Enriched C Z, !Enriched D Z, !Enriched E Z}
    {F : functor C D} {G : functor C E}
    `{!EnrichedFunctor F, !EnrichedFunctor G}.

  Local Instance : Enriched (cat_prod D E) Z := prod_enriched_def.

  Program Definition functor_to_prod_enr_def :
    EnrichedFunctor (functor_to_prod F G)
    := MkEnrFunc (λ a b, <<enr_func_h_map F a b, enr_func_h_map G a b>>)
         _ _ _.
  Next Obligation.
    intros; simpl.
    rewrite hom_to_prod_comp_r.
    f_equiv; apply enr_func_h_map_is_h_map.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !hom_to_prod_comp_r.
    f_equiv.
    - rewrite enr_func_h_map_comp comp_assoc.
      f_equiv.
      by rewrite -hom_prod_comp !hom_to_prod_prj1.
    - rewrite enr_func_h_map_comp comp_assoc.
      f_equiv.
      by rewrite -hom_prod_comp !hom_to_prod_prj2.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite hom_to_prod_comp_r.
    by rewrite !enr_func_h_map_id.
  Qed.

End enr_func_to_prod.

Section lc_func_to_prod.
  Context {SI} {C D E}
    `{!Enriched C (PSh (OrdCat SI))
      , !Enriched D (PSh (OrdCat SI))
      , !Enriched E (PSh (OrdCat SI))}
    {F : functor C D} {G : functor C E}.

  Local Instance : Enriched (cat_prod D E) (PSh (OrdCat SI)) :=
    prod_enriched_def.

  Context `{!LocallyContractiveFunctor F, !LocallyContractiveFunctor G}.

  Local Instance : EnrichedFunctor (functor_to_prod F G) :=
    functor_to_prod_enr_def.

  Opaque comp.
  Opaque prj1.
  Opaque prj2.

  Program Definition functor_to_prod_lc_def
    : LocallyContractiveFunctor (functor_to_prod F G)
    := MkLocContrFunc
         (λ a b, <<contr_func_h_map F a b, contr_func_h_map G a b>>)
         _ _ _.
  Next Obligation.
    intros; simpl.
    rewrite hom_to_prod_comp_r.
    f_equiv; apply contr_func_h_map_is_h_map.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !hom_to_prod_comp_r.
    f_equiv; rewrite contr_func_h_map_comp.
    - rewrite comp_assoc.
      f_equiv; last done.
      rewrite -hom_to_prod_comp.
      rewrite -!comp_assoc.
      rewrite !hom_to_prod_prj1.
      rewrite hom_to_prod_comp.
      rewrite -(right_id (prj1 (product_of (later ₒ enr_hom a b)
                                  (later ₒ enr_hom b c)))).
      rewrite -(right_id (prj2 (product_of (later ₒ enr_hom a b)
                                  (later ₒ enr_hom b c)))).
      rewrite hom_to_prod_of_prjs.
      rewrite right_id.
      reflexivity.
    - rewrite comp_assoc.
      f_equiv; last done.
      rewrite -hom_to_prod_comp.
      rewrite -!comp_assoc.
      rewrite !hom_to_prod_prj2.
      rewrite hom_to_prod_comp.
      rewrite -(right_id (prj1 (product_of (later ₒ enr_hom a b)
                                  (later ₒ enr_hom b c)))).
      rewrite -(right_id (prj2 (product_of (later ₒ enr_hom a b)
                                  (later ₒ enr_hom b c)))).
      rewrite hom_to_prod_of_prjs.
      rewrite right_id.
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !hom_to_prod_comp_r.
    f_equiv; apply contr_func_h_map_id.
  Qed.

  Transparent comp.
  Transparent prj1.
  Transparent prj2.

End lc_func_to_prod.

Program Definition flip_bifunc {C : category}
  (F : functor (cat_prod (C ᵒᵖ) C) C)
  : functor (cat_prod (C ᵒᵖ) C) (C ᵒᵖ) :=
  MkFunc (λ x, F ₒ (x.2, x.1))
    (λ a b f, @h_map (cat_prod (C ᵒᵖ) C) C F (b.2, b.1) (a.2, a.1) (f.2, f.1))
    _ _ _.
Next Obligation.
  solve_proper.
Qed.
Next Obligation.
  intros; simpl.
  by rewrite -h_map_comp.
Qed.
Next Obligation.
  intros; simpl.
  by rewrite h_map_id.
Qed.

Section enr_func_flip_bifunc.
  Context {C E : category}
    `{!HasTerm E, !HasProducts E, !Enriched C E}.

  Local Instance : Enriched (C ᵒᵖ) E := op_enriched_def.
  Local Instance : Enriched (cat_prod (C ᵒᵖ) C) E := prod_enriched_def.

  Program Definition flip_bifunc_enr_def
    (F : functor (cat_prod (C ᵒᵖ) C) C)
    `{!EnrichedFunctor F} :
    EnrichedFunctor (E := E) (D := C ᵒᵖ) (flip_bifunc F)
    := MkEnrFunc (λ a b,
           enr_func_h_map F (b.2, b.1) (a.2, a.1) ∘ commutator _ _)
         _ _ _.
  Next Obligation.
    intros; simpl.
    rewrite comp_assoc.
    pose proof (@enr_func_h_map_is_h_map _ _ _ _ _ _ _ F _
                  (b.2, b.1) (a.2, a.1) (commutator _ _ ∘ f)) as Heq.
    simpl in Heq; rewrite -Heq; clear Heq.
    rewrite -!comp_assoc hom_to_prod_prj1 hom_to_prod_prj2.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !comp_assoc.
    rewrite -!commute_hom_prod.
    rewrite hom_prod_comp.
    rewrite -!comp_assoc.
    pose proof (enr_func_h_map_comp F (c.2, c.1) (b.2, b.1) (a.2, a.1)) as HEQ.
    rewrite -HEQ //=; clear HEQ.
    rewrite !comp_assoc.
    f_equiv.
    rewrite ->1 hom_to_prod_comp_r.
    rewrite commute_hom_to_prod.
    f_equiv.
    - rewrite comp_assoc.
      f_equiv.
      rewrite comp_assoc.
      epose proof (comp_assoc _ _ (prj1 (product_of (enr_hom b.2 c.2)
                                           (enr_hom b.1 c.1))
                                     ×ₕ prj1 (product_of (enr_hom a.2 b.2)
                                                (enr_hom a.1 b.1 )))) as HEQ.
      rewrite -HEQ; clear HEQ.
      rewrite -hom_prod_comp.
      rewrite !hom_to_prod_prj1.
      rewrite commute_hom_prod.
      rewrite -comp_assoc.
      rewrite commutator_involutive.
      rewrite left_id.
      reflexivity.
    - rewrite comp_assoc.
      f_equiv.
      rewrite -comp_assoc.
      rewrite -hom_prod_comp.
      rewrite !hom_to_prod_prj2.
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite comp_assoc.
    rewrite commute_hom_to_prod.
    rewrite -(enr_func_h_map_id F (a.2, a.1)).
    by f_equiv.
  Qed.

End enr_func_flip_bifunc.

Section lc_func_flip_bifunc.
  Context {SI} {C}
    `{!Enriched C (PSh (OrdCat SI))}
    {F : functor (cat_prod (C ᵒᵖ) C) C}.

  Local Instance : Enriched (C ᵒᵖ) (PSh (OrdCat SI)) := op_enriched_def.
  Local Instance : Enriched (cat_prod (C ᵒᵖ) C) (PSh (OrdCat SI)) :=
    prod_enriched_def.

  Context `{!LocallyContractiveFunctor F}.

  Local Instance : EnrichedFunctor (flip_bifunc F) := flip_bifunc_enr_def F.

  Opaque comp.
  Opaque prj1.
  Opaque prj2.
  Opaque later_preserves_prods_nat.

  Program Definition flip_bifunc_lc_def
    : LocallyContractiveFunctor (flip_bifunc F)
    := MkLocContrFunc
         (λ a b, contr_func_h_map F (b.2, b.1) (a.2, a.1)
                   ∘ (later ₕ (commutator _ _)))
         _ _ _.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Defined.
  Next Obligation.
    intros; simpl.
    rewrite comp_assoc.
    pose proof (naturality next
                  (commutator (enr_hom a.1 b.1) (enr_hom a.2 b.2))) as Heq.
    simpl in Heq; rewrite -Heq; clear Heq.
    rewrite -comp_assoc.
    pose proof (contr_func_h_map_is_h_map F (b.2, b.1) (a.2, a.1)) as Heq.
    simpl in Heq; rewrite -Heq; clear Heq.
    f_equiv.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !comp_assoc.
    rewrite -!commute_hom_prod.
    rewrite hom_prod_comp.
    rewrite <-!comp_assoc.
    epose proof (contr_func_h_map_comp F (c.2, c.1) (b.2, b.1) (a.2, a.1)) as HEQ.
    rewrite -HEQ; clear HEQ.
    unfold later_prod.
    simpl.
    rewrite ->!comp_assoc.
    f_equiv.
    rewrite <-!comp_assoc.
    rewrite -h_map_comp.
    rewrite commute_hom_to_prod.
    rewrite ->!comp_assoc.
    epose proof (comp_assoc _ _ (backward (later_preserves_prods_nat SI) ₙ
                                   (enr_hom b.2 c.2 ×ₒ enr_hom b.1 c.1, enr_hom a.2 b.2 ×ₒ enr_hom a.1 b.1))) as HEQ.
    simpl in HEQ.
    rewrite -HEQ; clear HEQ.
    epose proof (@naturality _ _ _ _ (backward (later_preserves_prods_nat SI))
                   ((enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2), (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2))
                   ((enr_hom b.2 c.2 ×ₒ enr_hom b.1 c.1), (enr_hom a.2 b.2 ×ₒ enr_hom a.1 b.1))
                   (commutator (enr_hom b.1 c.1) (enr_hom b.2 c.2), commutator (enr_hom a.1 b.1) (enr_hom a.2 b.2))) as HEQ.
    simpl in HEQ.
    rewrite HEQ; clear HEQ.
    rewrite <-!comp_assoc.
    rewrite -h_map_comp.
    rewrite ->! comp_assoc.
    assert ((backward (later_preserves_prods_nat SI)ₙ
               (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2, enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2))
              ∘ commutator
              (later ₒ (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2))
              (later ₒ (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2))
              ≡
              later ₕ (commutator ((enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2)) ((enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2)))
              ∘ (backward (later_preserves_prods_nat SI)ₙ
                   (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2, enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2))) as HEQ.
    {
      rewrite right_adj_preserves_prods_backward_comm.
      reflexivity.
    }
    simpl in HEQ; rewrite HEQ; clear HEQ.
    rewrite <-! comp_assoc.
    f_equiv.
    rewrite -h_map_comp.
    rewrite !hom_to_prod_comp_r.
    rewrite h_map_proper; first reflexivity.
    f_equiv.
    - rewrite ->!comp_assoc.
      epose proof (comp_assoc (commutator (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2) (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2))) as HEQ.
      simpl in HEQ; rewrite <-HEQ; clear HEQ.
      rewrite -hom_prod_comp.
      rewrite !hom_to_prod_prj1.
      rewrite commute_hom_prod.
      rewrite -!comp_assoc.
      rewrite (comp_assoc _ _ (enr_comp a.2 b.2 c.2)).
      rewrite commutator_involutive.
      rewrite right_id.
      reflexivity.
    - rewrite ->!comp_assoc.
      f_equiv.
      epose proof (comp_assoc (commutator (enr_hom a.1 b.1 ×ₒ enr_hom a.2 b.2) (enr_hom b.1 c.1 ×ₒ enr_hom b.2 c.2))) as HEQ.
      simpl in HEQ; rewrite <-HEQ; clear HEQ.
      rewrite -hom_prod_comp.
      rewrite !hom_to_prod_prj2.
      rewrite commute_hom_prod.
      reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    rewrite !comp_assoc.
    epose proof (comp_assoc (next ₙ term_func (OrdCat SI)ᵒᵖ Setoid)
                  (later ₕ << ⌜ id a.1 ⌝, ⌜ id a.2 ⌝ >>)) as Heq.
    rewrite -Heq; clear Heq.
    rewrite <-h_map_comp.
    rewrite commute_hom_to_prod.
    rewrite -(contr_func_h_map_id F (a.2, a.1)).
    rewrite comp_assoc.
    f_equiv; done.
  Qed.

  Transparent comp.
  Transparent prj1.
  Transparent prj2.
  Transparent later_preserves_prods_nat.

End lc_func_flip_bifunc.

Program Definition iso_cat_prod_left {C D} {a c : obj C} {b d : obj D}
  (HISO : (a, b) ≃@{cat_prod C D} (c, d)) : a ≃ c
  := MkIsoIc (forward HISO).1 (backward HISO).1
       (MkIso (proj1 (iso_lr (is_iso HISO))) (proj1 (iso_rl (is_iso HISO)))).

Program Definition iso_cat_prod_right {C D} {a c : obj C} {b d : obj D}
  (HISO : (a, b) ≃@{cat_prod C D} (c, d)) : b ≃ d
  := MkIsoIc (forward HISO).2 (backward HISO).2
       (MkIso (proj2 (iso_lr (is_iso HISO))) (proj2 (iso_rl (is_iso HISO)))).

Section symmetrization.
  Context {SI : indexT} {C : category}
    `{!Enriched C (PSh (OrdCat SI))}
    `{!LimitsEnriched C}.

  Local Instance : Enriched (C ᵒᵖ) (PSh (OrdCat SI)) := op_enriched_def.
  Local Instance : Enriched (cat_prod (C ᵒᵖ) C) (PSh (OrdCat SI)) :=
    prod_enriched_def.

  Context {sol : ∀ {C : category}
                   `{!Enriched C (PSh (OrdCat SI))} `{!LimitsEnriched C}
                   (F : functor C C) `{!LocallyContractiveFunctor F},
             solution F}.

  Context {F : functor (cat_prod (C ᵒᵖ) C) C}
    `{LC : !LocallyContractiveFunctor F}.

  Record bifunc_solution :=
    MkBifuncSolution
      {
        bifunc_sol_obj :> obj C;
        bifunc_sol_iso : (F ₒ (bifunc_sol_obj, bifunc_sol_obj))
                           ≃ bifunc_sol_obj;
      }.

  Program Definition symmetrization
    : functor (cat_prod (C ᵒᵖ) C) (cat_prod (C ᵒᵖ) C)
    := functor_to_prod (flip_bifunc F) F.

  Local Program Instance symmetrization_enriched_func
    : EnrichedFunctor symmetrization := _.
  Next Obligation.
    unshelve eapply functor_to_prod_enr_def.
    apply flip_bifunc_enr_def; apply _.
  Qed.

  Local Program Instance symmetrization_locally_contractive
    : LocallyContractiveFunctor symmetrization := _.
  Next Obligation.
    unshelve eapply functor_to_prod_lc_def.
    apply flip_bifunc_lc_def.
  Qed.

  Lemma bifunc_solution_eq (s : obj (C ᵒᵖ)) (s' : obj C)
    (H : (symmetrization ₒ (s, s')) ≃ (s, s')) :
    (symmetrization ₒ (s', s)) ≃@{cat_prod (C ᵒᵖ) C} (s', s).
  Proof.
    assert (H1 : F ₒ (s, s') ≃@{C} s').
    {
      apply (iso_cat_prod_right H).
    }
    assert (H2 : F ₒ (s', s) ≃@{C ᵒᵖ} s).
    {
      apply (iso_cat_prod_left H).
    }
    rewrite /symmetrization //=.
    apply (MkIsoIc
             (((backward H1), (backward H2))
               : hom (C := cat_prod (C ᵒᵖ) C)
                   (F ₒ (s, s'), F ₒ (s', s)) (s', s))
             ((forward H1), (forward H2))).
    apply MkIso.
    - split.
      + apply (iso_lr (is_iso H1)).
      + apply (iso_lr (is_iso H2)).
    - split.
      + apply (iso_rl (is_iso H1)).
      + apply (iso_rl (is_iso H2)).
  Qed.

  Lemma bifunc_solution_flip (s : obj (C ᵒᵖ)) (s' : obj C)
    (H : (symmetrization ₒ (s, s')) ≃ (s, s')) :
    (s, s') ≃@{cat_prod (C ᵒᵖ) C} (s', s).
  Proof using LC SI.
    set (MkSolution symmetrization (s, s') H) as X.
    set (MkSolution symmetrization (s', s) (bifunc_solution_eq _ _ H)) as Y.
    apply (solution_unique (SI := SI) symmetrization X Y).
  Qed.

  Lemma bifunc_solution_symmetry (s : obj (C ᵒᵖ)) (s' : obj C)
    (H : (symmetrization ₒ (s, s')) ≃ (s, s')) :
    (symmetrization ₒ (s', s)) ≃@{cat_prod (C ᵒᵖ) C} (symmetrization ₒ (s, s')).
  Proof using LC SI.
    apply @isomorphic_trans with (s', s);
      first apply (bifunc_solution_eq _ _ H).
    apply isomorphic_sym.
    apply @isomorphic_trans with (s, s'); first apply H.
    by apply bifunc_solution_flip.
  Qed.

  Lemma symmetrization_sol `{!LimitsEnriched (cat_prod (C ᵒᵖ) C)}
    : bifunc_solution.
  Proof using LC SI sol.
    set (X := (sol (cat_prod (C ᵒᵖ) C) _ _ symmetrization _)).
    set (s := sol_obj _ X).
    set (s1 := cat_proj1 _ _ ₒ s).
    set (s2 := cat_proj2 _ _ ₒ s).
    assert (s = (s1, s2)) as HEQ.
    { subst s; destruct (sol_obj symmetrization X); reflexivity. }
    assert (s1 ≃@{C} s2) as HISO.
    {
      assert ((s2, s1) ≃@{cat_prod (C ᵒᵖ) C} (s1, s2)) as HISO.
      {
        apply bifunc_solution_flip.
        apply bifunc_solution_eq.
        rewrite <-HEQ.
        apply (sol_iso _ X).
      }
      apply (iso_cat_prod_right HISO).
    }
    refine {| bifunc_sol_obj := s1 |}.
    {
      assert ((F ₒ (s1, s1), F ₒ (s1, s1)) ≃@{cat_prod (C ᵒᵖ) C} (s1, s1)) as G.
      {
        apply @isomorphic_trans with (F ₒ (s2, s1), F ₒ (s1, s2)).
        - apply (@prod_of_isos (C ᵒᵖ) C).
          + apply iso_op.
            apply (@functor_preserves_iso (cat_prod (C ᵒᵖ) C) C F).
            apply (@prod_of_isos (C ᵒᵖ) C); last apply isomorphic_refl.
            apply iso_op, HISO.
          + apply functor_preserves_iso.
            apply (@prod_of_isos (C ᵒᵖ) C); first apply isomorphic_refl.
            apply HISO.
        - apply @isomorphic_trans with (s1, s2).
          + rewrite <-HEQ.
            apply (sol_iso _ X).
          + apply (@prod_of_isos (C ᵒᵖ) C); first apply isomorphic_refl.
            apply isomorphic_sym.
            apply HISO.
      }
      apply (iso_cat_prod_right G).
    }
  Defined.

  Program Definition bifunc_sol_unary_sol (bs : bifunc_solution)
    : solution symmetrization :=
    MkSolution _ (bifunc_sol_obj bs, bifunc_sol_obj bs) _.
  Next Obligation.
    intros; simpl.
    apply (@prod_of_isos (C ᵒᵖ) C).
    - apply iso_op.
      apply bifunc_sol_iso.
    - apply bifunc_sol_iso.
  Defined.

  Lemma bifunc_sol_unique `{!LimitsEnriched (cat_prod (C ᵒᵖ) C)}
    : ∀ X, F ₒ (X, X) ≃ X → X ≃ bifunc_sol_obj symmetrization_sol.
  Proof.
    intros X HEQ.
    pose proof (solution_unique symmetrization
                  (bifunc_sol_unary_sol (MkBifuncSolution X HEQ))
                  (bifunc_sol_unary_sol
                     (MkBifuncSolution symmetrization_sol
                        (bifunc_sol_iso symmetrization_sol)))) as HI.
    apply (iso_cat_prod_left HI).
  Qed.

End symmetrization.

Section solution.
  Context {SI : indexT} {C : category} `{!Complete C}
    `{!Enriched C (PSh (OrdCat SI))} `{!LimitsEnriched C}
    (F : functor C C) `{!LocallyContractiveFunctor F}.

  (* An F-algebra whose constructor map is α-iso for all α is the solution. *)
  Definition alg_cons_is_iso_upto_total_solution {A : algebra F}
    (iso : is_iso_upto (cons A) (total_dsp SI)) : (solution F) :=
    MkSolution _ (car A) (is_iso_upto_total (cons A) iso).

  (* Now, we will construc such an algebra. *)

  Record partial_solution (dsp: downset_pred SI) := MkParSol {
    parsol_func :> functor ((OrdDSCat dsp)ᵒᵖ) (Alg F);
    parsol_edge_iso : ∀ (α β : downset dsp) (Hle : β ⪯ α),
      is_iso_at (alg_hom_map (parsol_func ₕ Hle)) β;
    parsol_cons_iso : ∀ (α : downset dsp), is_iso_at (cons (parsol_func ₒ α)) α;
  }.
  Arguments MkParSol {_} _ _ _.
  Arguments parsol_func {_} _.
  Arguments parsol_edge_iso {_} _ [_ _] _.
  Arguments parsol_cons_iso {_} _ _.

  Record par_sol_extension {dsp} (ps : partial_solution dsp) := MkParSolExt {
    parsolext_cone :> cone ps;
    parsolext_side_iso : ∀ (α : downset dsp),
      is_iso_at (alg_hom_map (side parsolext_cone α)) α;
    parsolext_cons_iso : ∀ (α : SI),
      (∀ β, β ≺ α → dsp β) → is_iso_at (cons (vertex parsolext_cone)) α;
  }.
  Arguments MkParSolExt {_ _} _ _.
  Arguments parsolext_cone {_ _} _.
  Arguments parsolext_side_iso {_ _} _ _.
  Arguments parsolext_cons_iso {_ _} _ _.

  Program Definition apply_par_sol_extension {α} {ps : partial_solution (lt_dsp α)}
    (pse : par_sol_extension ps) : partial_solution (le_dsp α) :=
    MkParSol (extend_ord_ds_cat_func pse) _ _.
  Next Obligation.
    intros α ps pse β γ Hle; simpl.
    destruct (index_le_lt_eq_dec _ _ (ds_in_dsp β)) as [Hltβ|Heqβ];
      destruct (index_le_lt_eq_dec _ _ (ds_in_dsp γ)) as [Hltγ|Heqγ];
      simplify_extend_ord_ds_cat_func_h_map.
    - eapply is_iso_at_proper; last by rewrite hom_trans_alg_hom_map.
      apply iso_at_hom_trans, (parsol_edge_iso ps).
    - eapply is_iso_at_proper; last by rewrite hom_trans_alg_hom_map.
      apply iso_at_hom_trans, (parsolext_side_iso pse).
    - eapply is_iso_at_proper; last by rewrite hom_trans_alg_hom_map.
      apply iso_at_hom_trans, is_iso_at_id.
  Qed.
  Next Obligation.
    intros α ps pse β; simpl.
    destruct (index_le_lt_eq_dec _ _ (ds_in_dsp β)) as [Hltβ|Heqβ].
    - rewrite extend_ord_ds_cat_func_o_map_lt.
      apply (parsol_cons_iso ps).
    - rewrite extend_ord_ds_cat_func_o_map_at // Heqβ.
      apply parsolext_cons_iso; done.
  Qed.
  Fail Next Obligation.

  Program Definition extend_partial_solution_iso {α} {ps ps' : partial_solution (lt_dsp α)}
    (psiso : ps ≃@{FuncCat ((OrdDSCat (lt_dsp α))ᵒᵖ) (Alg F)} ps')
    {pse : par_sol_extension ps} {pse' : par_sol_extension ps'}
    (pseseq : equiv_cones psiso pse pse') :
    apply_par_sol_extension pse ≃@{FuncCat ((OrdDSCat (le_dsp α))ᵒᵖ) (Alg F)}
    apply_par_sol_extension pse' :=
    MkIsoIc
      (extend_ord_ds_cat_nat (forward psiso) (forward (eq_cones_vertexes pseseq))
         (eq_cones_sides pseseq))
      (extend_ord_ds_cat_nat (backward psiso) (backward (eq_cones_vertexes pseseq))
         (eq_cones_sides' pseseq))
      _.
  Next Obligation.
  intros α ps ps' psiso pse pse' pseseq; split; simpl in *.
  - intros β; simpl.
    destruct (index_le_lt_eq_dec _ _ (ds_in_dsp β)) as [Hltβ|Heqβ].
    + rewrite !(extend_ord_ds_cat_nat_map_lt _ _ Hltβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_lr (is_iso psiso) (MkDS (lt_dsp α) Hltβ)) as Hlr;
        apply alg_hom_map_eq' in Hlr; simpl in Hlr; rewrite Hlr; clear Hlr.
      rewrite hom_trans_id //.
    + rewrite !(extend_ord_ds_cat_nat_map_at _ _ Heqβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_lr (is_iso (eq_cones_vertexes pseseq))) as Hlr;
        apply alg_hom_map_eq' in Hlr; simpl in Hlr; rewrite Hlr; clear Hlr.
      rewrite hom_trans_id //.
  - intros β; simpl.
    destruct (index_le_lt_eq_dec _ _ (ds_in_dsp β)) as [Hltβ|Heqβ].
    + rewrite !(extend_ord_ds_cat_nat_map_lt _ _ Hltβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_rl (is_iso psiso) (MkDS (lt_dsp α) Hltβ)) as Hlr;
        apply alg_hom_map_eq' in Hlr; simpl in Hlr; rewrite Hlr; clear Hlr.
      rewrite hom_trans_id //.
    + rewrite !(extend_ord_ds_cat_nat_map_at _ _ Heqβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_rl (is_iso (eq_cones_vertexes pseseq))) as Hlr;
        apply alg_hom_map_eq' in Hlr; simpl in Hlr; rewrite Hlr; clear Hlr.
      rewrite hom_trans_id //.
  Qed.
  Fail Next Obligation.

  Program Definition the_extension {dsp} (ps : partial_solution dsp) : par_sol_extension ps :=
    MkParSolExt (alg_func_on_cone (term (complete ps))) _ _.
  Next Obligation.
    intros ? ps α; rewrite /=.
    apply is_iso_at_compose; last apply parsol_cons_iso.
    apply (is_iso_at_func F).
    rewrite -(ic_side_limiting_cone_is_limit _ _
      (term_is_terminal (complete (functor_compose ps (forgetful F))))).
    apply (limit_side_iso_at_cofinal
             (limiting_cone_is_limit
                (term_is_terminal (complete (functor_compose ps (forgetful F)))))
             α (ds_in_dsp α)); last done.
    intros; simpl.
    eapply is_iso_at_downwards; last by apply parsol_edge_iso.
    done.
  Qed.
  Next Obligation.
    intros ? ps α Hdsp; simpl.
    eapply (iso_upto_contr_func F); last by apply Hdsp.
    intros β.
    assert (is_iso_at (side (term (complete (functor_compose ps (forgetful F)))) β) β) as Hiso.
    { rewrite -(ic_side_limiting_cone_is_limit _ _
        (term_is_terminal (complete (functor_compose ps (forgetful F))))).
      apply (limit_side_iso_at_cofinal
             (limiting_cone_is_limit
                (term_is_terminal (complete (functor_compose ps (forgetful F)))))
             β (ds_in_dsp β)); last done.
      intros; simpl.
      eapply is_iso_at_downwards; last by apply parsol_edge_iso.
      done. }
    eapply is_iso_at_uncompose_r; first apply Hiso.
    eapply is_iso_at_proper; last by rewrite_cone_hom_commutes_back; reflexivity.
    simpl.
    apply is_iso_at_compose; last apply parsol_cons_iso.
    apply (is_iso_at_func F).
    done.
  Qed.
  Fail Next Obligation.

  Definition the_extension_eq_cones {α} {ps ps' : partial_solution (lt_dsp α)}
    (psiso : ps ≃@{FuncCat ((OrdDSCat (lt_dsp α))ᵒᵖ) (Alg F)} ps') :
    equiv_cones psiso (the_extension ps) (the_extension ps') :=
    alg_func_on_eq_cones (limit_of_isos_equiv_cones psiso (complete ps) (complete ps')).

  Definition extend_par_sol_lt_le {α} (ps : partial_solution (lt_dsp α)) :
    partial_solution (le_dsp α) :=
    apply_par_sol_extension (the_extension ps).

  Definition extend_par_sol_lt_le_iso {α} {ps ps' : partial_solution (lt_dsp α)}
    (psiso : ps ≃@{FuncCat ((OrdDSCat (lt_dsp α))ᵒᵖ) (Alg F)} ps') :
    extend_par_sol_lt_le ps ≃@{FuncCat ((OrdDSCat (le_dsp α))ᵒᵖ) (Alg F)}
    extend_par_sol_lt_le ps' :=
    extend_partial_solution_iso psiso (the_extension_eq_cones psiso).

  Program Definition cut_par_sol {dsp} (ps : partial_solution dsp) {dsp' : downset_pred SI}
    (Hdsps : dsp_included dsp' dsp) : partial_solution dsp' :=
    MkParSol (cut_ord_ds_cat_func dsp' Hdsps ps) _ _.
  Next Obligation. intros ? ps ?????; apply ps. Qed.
  Next Obligation. intros ? ps ???; apply ps. Qed.
  Fail Next Obligation.

  Lemma par_sol_extensional {dsp : downset_pred SI}
    (P Q : partial_solution dsp) :
    (∀ dsp' (H : dsp_included dsp' dsp),
       (cut_par_sol P H) ≃@{FuncCat ((OrdDSCat dsp')ᵒᵖ) (Alg F)} (cut_par_sol Q H))
    → P ≃@{FuncCat ((OrdDSCat dsp)ᵒᵖ) (Alg F)} Q.
  Proof.
    intros G.
    pose proof (G dsp (λ x α, α)).
    unshelve econstructor.
    - unshelve econstructor.
      + intros c.
        pose proof (nat_map (forward X) c) as Y.
        destruct c.
        apply Y.
      + simpl.
        intros a b f.
        pose proof (naturality (forward X) f) as Y.
        destruct a, b.
        simpl in *.
        unfold cut_ord_ds_cat_func_h_map in *.
        admit.
    - admit.
    - admit.
  Admitted.

  Record canonical_par_sol {dsp} (can_par_sol_ps : partial_solution dsp) :=
    MkCanParSol {
        can_par_sol_iso :> ∀ α : downset dsp,
          cut_par_sol can_par_sol_ps (le_dsp_included α)
            ≃@{FuncCat ((OrdDSCat (le_dsp α))ᵒᵖ) (Alg F)}
            extend_par_sol_lt_le (cut_par_sol can_par_sol_ps (lt_dsp_included α));
      }.

  Lemma canonicity_inductive {dsp} (P : partial_solution dsp) :
    (∀ α, canonical_par_sol (cut_par_sol P (lt_dsp_included α))
          → canonical_par_sol (cut_par_sol P (le_dsp_included α)))
    → canonical_par_sol P.
  Proof.
    intros H.
    cut (∀ α, canonical_par_sol (cut_par_sol P (le_dsp_included α))).
    - intros G.
      constructor.
      intros α.
      specialize (G α).
      unshelve epose proof (G _).
      + unshelve econstructor.
        * apply α.
        * simpl. reflexivity.
      + simpl in X.
        admit.
    - intros α.
      destruct α as [H1 H2].
      revert H2.
      simpl.
      induction (index_lt_wf _ H1) as [α' _ IHβ].
      intros H2.
      unshelve epose proof (H _).
      + apply (MkDS H2).
      + apply X.
        admit.
      (* eapply H. *)
      (* apply IHβ. *)
  Admitted.

  Lemma canonical_eq {dsp} (P Q : partial_solution dsp)
    (PC : canonical_par_sol P) (QC : canonical_par_sol Q) :
    P ≃@{FuncCat ((OrdDSCat _)ᵒᵖ) (Alg F)} Q.
  Proof.
    apply par_sol_extensional.
    intros dsp'.
    destruct dsp'.
    (* induction (index_lt_wf _ dsp') as [α' _ IHβ]. *)
  Admitted.

  Lemma patch {dsp : downset_pred SI} (collection : ∀ α, dsp α → partial_solution dsp)
    (canonical : ∀ α H, canonical_par_sol (collection α H)) :
    partial_solution dsp.
  Proof.
  Admitted.



  Lemma construct1 : ∀ β, partial_solution (le_dsp β) → partial_solution (total_dsp SI).
  Admitted.

  Lemma construct2 : ∀ β, partial_solution (le_dsp β).
  Proof.
    intros β.
    induction (index_lt_wf _ β) as [β _ IHβ].
    apply extend_par_sol_lt_le.
  Admitted.

  Lemma construct3 : partial_solution (total_dsp SI) → solution F.
  Proof.
  Admitted.

  Record partial_solution_dominates {dsp: downset_pred SI}
    (ps : partial_solution) (pss : partial_solution_set dsp) := MkParSolDom {
    dom_proj : ∀ β : downset dsp, hom ps (pss β);
    dom_proj_fold : ∀ (β : downset dsp),
      par_sol_fold (pss β) ∘ (F ₕ (dom_proj β)) ≡ (dom_proj β) ∘ par_sol_fold ps;
    dom_proj_iso : ∀ β : downset dsp, is_iso_at (dom_proj β) β;
    dom_fold_iso : ∀ (α : SI), (∀ β, β ≺ α → dsp β) → is_iso_at (par_sol_fold ps) α;
  }.
  Arguments MkParSolDom {_ _ _} _ _ _.
  Arguments dom_proj {_ _ _} _ _.
  Arguments dom_proj_iso {_ _ _} _ _.
  Arguments dom_fold_iso {_ _ _} _ _ _.

  Definition dominate_lim {dsp: downset_pred SI} (pss : partial_solution_set dsp) : obj C :=
    vertex (term (complete (par_sol_set_func pss))).

  Definition dominate_lim_is_limit {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    is_limit (par_sol_set_func pss) (dominate_lim pss) :=
    limiting_cone_is_limit (term_is_terminal (complete (par_sol_set_func pss))).

  Definition dominate_lim_cone_side_iso {dsp: downset_pred SI} (pss : partial_solution_set dsp)
    α : is_iso_at (ic_side (il_is_cone (dominate_lim_is_limit pss)) α) α :=
    limit_side_iso_at_cofinal
      (dominate_lim_is_limit pss)
      α (ds_in_dsp α) (parsol_set_func_isos pss α) α (reflexivity _).

  Definition dominate_proj {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    hom (F ₒ (dominate_lim pss)) (pss β) :=
    ((par_sol_fold (pss β)) ∘ (F ₕ (ic_side (il_is_cone (dominate_lim_is_limit pss)) β))).

  Definition dominate_proj_iso_at {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    is_iso_at (dominate_proj pss β) β :=
    is_iso_at_compose
      (is_iso_at_func F (ic_side (il_is_cone (dominate_lim_is_limit pss)) β)
         (dominate_lim_cone_side_iso pss β)) (parsolset_fold_iso pss β).

  Program Definition dominate_proj_cone {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    cone (par_sol_set_func pss) :=
    MkCone (F ₒ (dominate_lim pss)) (λ β, dominate_proj pss β) _.
  Next Obligation.
    repeat intros ?; rewrite /dominate_proj; simpl in *.
    rewrite -comp_assoc -parsolset_proj_fold.
    rewrite comp_assoc -h_map_comp.
    rewrite -(ic_side_commutes (il_is_cone (dominate_lim_is_limit pss))) //.
  Qed.

  Program Definition dominate_pre_fold {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    hom (F ₒ (dominate_lim pss)) (dominate_lim pss) :=
    cone_hom_map (bang (il_is_limiting_cone _ _ (dominate_lim_is_limit pss))
                    (dominate_proj_cone pss)).

  Lemma dominate_pre_fold_commutes {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    dominate_proj pss β ≡
    (ic_side (il_is_cone (dominate_lim_is_limit pss)) β) ∘ (dominate_pre_fold pss).
  Proof.
    apply (cone_hom_commutes (bang
         (il_is_limiting_cone (par_sol_set_func pss)
            (dominate_lim pss) (dominate_lim_is_limit pss))
         (dominate_proj_cone pss))).
  Qed.

  Program Definition dominate_pre_fold_iso
    {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    is_iso_upto (dominate_pre_fold pss) dsp :=
    λ β, is_iso_at_uncompose_r (dominate_lim_cone_side_iso pss β)
      (is_iso_at_proper (dominate_proj_iso_at pss β) (dominate_pre_fold_commutes pss β)).

  Definition dominate_fold {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    hom (F ₒ (F ₒ (dominate_lim pss))) (F ₒ (dominate_lim pss)) :=
    F ₕ (dominate_pre_fold pss).

  Definition dominate_fold_iso {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    ∀ (α : SI), (∀ β, β ≺ α → dsp β) → is_iso_at (dominate_fold pss) α :=
    λ α Hα, iso_upto_contr_func F (dominate_pre_fold pss) (dominate_pre_fold_iso pss) α Hα.

  Program Definition dominate {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    partial_solution := MkParSol (F ₒ (dominate_lim pss)) (dominate_fold pss).

  Program Definition dominate_dominates {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    partial_solution_dominates (dominate pss) pss :=
    MkParSolDom (dominate_proj pss) _ (dominate_proj_iso_at pss) (dominate_fold_iso pss).
  Next Obligation.
    intros ???.
    rewrite /= /dominate_fold /dominate_proj /dominate_pre_fold.
    rewrite comp_assoc -h_map_comp.
    rewrite_cone_hom_commutes_back.
    done.
  Qed.

  Definition extended_pss {γ} (pss : partial_solution_set (lt_dsp γ))
      (α : downset (le_dsp γ)) : partial_solution :=
    match index_le_lt_eq_dec _ _ (ds_in_dsp α) return partial_solution with
    | left Hlt => pss (MkDS (lt_dsp γ) Hlt)
    | right _ => dominate pss
    end.





  Goal ∀ {dsp} (ps ps' : canonical_par_sol dsp) (can_iso : ps ≃@{FuncCat ((OrdDSCat dsp)ᵒᵖ) (Alg F)} ps') (α : downset dsp), False.
    intros dsp ps ps' can_iso α.
    pose proof (backward (can_par_sol_iso _ ps α)).
    pose proof (forward (can_par_sol_iso _ ps' α)).
    pose proof (cut_ord_ds_cat_nat _ (le_dsp_included α) (forward can_iso)).
    simpl in *.
    unfold cut_ord_ds_cat_func_o_map in *.
    pose proof (X0 ∘@{FuncCat _ _} X1 ∘@{FuncCat _ _} X).



  Record canonical_iso {dsp} (ps ps' : canonical_par_sol dsp) := MkCanIso {
    can_iso : ps ≃@{FuncCat ((OrdDSCat dsp)ᵒᵖ) (Alg F)} ps';
    can_iso_lr : ∀ α, (forward (can_par_sol_iso _ ps' α) ₙ (MkDS (le_dsp α) (reflexivity _))) ∘ ((forward can_iso) ₙ α) ≡
                        (forward (can_par_sol_iso _ ps' α)) ∘ (forward can_iso α);
  }.


  Program Definition can_par_sols_iso {dsp} (ps ps' : canonical_par_sol dsp)


  Program Definition canonical_par_sols_iso_zero {dsp} (ps ps' : canonical_par_sol dsp) :
    cut_par_sol ps (lt_dsp_included (zero)) ≃@{FuncCat ((OrdDSCat dsp)ᵒᵖ) (Alg F)} ps' :=
    MkIsoIc _ _ _.
  Next Obligation.
    intros dsp ps ps'.

  Program Definition canonical_par_sols_iso {dsp} (ps ps' : canonical_par_sol dsp) :
    ps ≃@{FuncCat ((OrdDSCat dsp)ᵒᵖ) (Alg F)} ps' :=
    MkIsoIc _ _ _.
  Next Obligation.
    intros dsp ps ps'.


  Definition compat_zero {α} (ps : partial_solution (le_dsp α)) :=
    cut_par_sol ps (le_dsp_included (MkDS (le_dsp α) (index_zero_minimum α)))
    ≃@{FuncCat (OrdDSCat (le_dsp zero))ᵒᵖ (Alg F)}
    extend_par_sol_lt_le par_sol_set_emp.


  Lemma canonical_par_sols_iso {dsp} (ps : canonical_par_sol dsp)
    {dsp'} (ps' : canonical_par_sol dsp') {α} (Hα : dsp α) (Hα' : dsp' α) :


  Definition can_par_sol_glue_func_o_map {dsp : downset_pred SI}
    (pss : ∀ α, dsp α → canonical_par_sol (le_dsp α)) (α : downset dsp) : algebra F :=
    pss α (ds_in_dsp α) ₒ (MkDS (le_dsp α) (reflexivity _)).

  Definition can_par_sol_glue_func_h_map {dsp : downset_pred SI}
    (pss : ∀ α, dsp α → canonical_par_sol (le_dsp α)) {α β : downset dsp}
    (Hle : β ⪯ α) :
    alg_hom (can_par_sol_glue_func_o_map pss α) (can_par_sol_glue_func_o_map pss β).
    pose proof (pss α (ds_in_dsp α) ₕ (Hle : (MkDS (le_dsp α) Hle) ⪯ (MkDS (le_dsp α) (reflexivity _)))).
    simpl in *.


    :=
    pss α (ds_in_dsp α) ₒ (MkDS (le_dsp α) (reflexivity _)).

  Program Definition can_par_sol_glue_func {dsp : downset_pred SI}
    (pss : ∀ α, dsp α → canonical_par_sol (le_dsp α)) : functor ((OrdDSCat dsp)ᵒᵖ) (Alg F) :=
    MkFunc (λ α, pss α (ds_in_dsp α) ₒ (MkDS (le_dsp α) (reflexivity _))) _ _ _ _.

  Definition par_sols : ∀ α, canonical_par_sol (le_dsp α).

  Program Definition par_sol_set_func {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    functor ((OrdDSCat dsp)ᵒᵖ) C :=
    MkFunc (λ α, pss α) (λ α β Hle, parsolset_proj pss Hle) _ _ _.
  Next Obligation.
    intros ???? Hle Hle' _; replace Hle with Hle' by apply proof_irrel; done.
  Qed.
  Next Obligation. repeat intros; rewrite /= parsolset_proj_comp //. Qed.
  Next Obligation. repeat intros; rewrite /= parsolset_proj_id //. Qed.
  Fail Next Obligation.

  Definition parsol_set_func_isos
    {dsp: downset_pred SI} (pss : partial_solution_set dsp) α :
    ∀ (β γ : downset dsp) (Hβγ : β ⪯ γ) (Hβ : α ⪯ β) (Hγ : α ⪯ γ),
    is_iso_at (par_sol_set_func pss ₕ Hβγ) α :=
    λ _ _ Hβγ Hβ _, iso_at_downwards _ Hβ (parsolset_proj_iso pss Hβγ).


  Program Definition extend_proj {γ} (pss : partial_solution_set (lt_dsp γ))
    {α β : downset (le_dsp γ)} (Hle : α ⪯ β) : hom (extended_pss pss α) (extended_pss pss β).
  refine (match index_le_lt_eq_dec _ _ (ds_in_dsp α) as u with
          | left Hlt => _
          | right Heq => _
          end).

  Program Definition dominator_extends {γ} (pss : partial_solution_set (lt_dsp γ)) :
    partial_solution_set (le_dsp γ) :=
    MkParSolSet (extended_pss pss)
      _ _ _ _ _ _.
  Next Obligation.
    intros γ pss α β Hle.


    refine (match index_le_lt_eq_dec _ _ (ds_in_dsp α) as u with
            | left Hlt => _
            | right Heq => _
            end).


































zzzzzzzzzzzzzzzzzzz

  Record partial_solution_set (dsp: downset_pred SI) := MkParSolSet {
    parsolset :> ∀ β : downset dsp, partial_solution;
    parsolset_proj : ∀ α β : downset dsp, β ⪯ α → hom (parsolset α) (parsolset β);
    parsolset_proj_comp : ∀ (α β γ : downset dsp) (Hle : β ⪯ α) (Hle' : γ ⪯ β),
      parsolset_proj _ _ Hle' ∘ parsolset_proj _ _ Hle ≡
      parsolset_proj _ _ (transitivity Hle' Hle);
    parsolset_proj_id : ∀ α : downset dsp,
      parsolset_proj _ _ (reflexivity (α : SI)) ≡ id (parsolset α);
    parsolset_proj_iso : ∀ (α β : downset dsp) (Hle : β ⪯ α),
      is_iso_at (parsolset_proj α β Hle) β;
    parsolset_proj_fold : ∀ (α β : downset dsp) (Hle : β ⪯ α),
      par_sol_fold (parsolset β) ∘ (F ₕ (parsolset_proj _ _ Hle)) ≡
      (parsolset_proj _ _ Hle) ∘ par_sol_fold (parsolset α);
    parsolset_fold_iso : ∀ (α : downset dsp),
      is_iso_at (par_sol_fold (parsolset α)) α;
  }.
  Arguments MkParSolSet {_} _ _ _ _.
  Arguments parsolset {_} _ _.
  Arguments parsolset_proj {_} _ [_ _] _.
  Arguments parsolset_proj_comp {_} _ [_ _ _] _ _.
  Arguments parsolset_proj_id {_} _ _.
  Arguments parsolset_proj_iso {_} _ [_ _] _.
  Arguments parsolset_proj_fold {_} _ [_ _] _.
  Arguments parsolset_fold_iso {_} _ _.

  Program Definition par_sol_set_func {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    functor ((OrdDSCat dsp)ᵒᵖ) C :=
    MkFunc (λ α, pss α) (λ α β Hle, parsolset_proj pss Hle) _ _ _.
  Next Obligation.
    intros ???? Hle Hle' _; replace Hle with Hle' by apply proof_irrel; done.
  Qed.
  Next Obligation. repeat intros; rewrite /= parsolset_proj_comp //. Qed.
  Next Obligation. repeat intros; rewrite /= parsolset_proj_id //. Qed.
  Fail Next Obligation.

  Definition parsol_set_func_isos
    {dsp: downset_pred SI} (pss : partial_solution_set dsp) α :
    ∀ (β γ : downset dsp) (Hβγ : β ⪯ γ) (Hβ : α ⪯ β) (Hγ : α ⪯ γ),
    is_iso_at (par_sol_set_func pss ₕ Hβγ) α :=
    λ _ _ Hβγ Hβ _, iso_at_downwards _ Hβ (parsolset_proj_iso pss Hβγ).

  Record partial_solution_dominates {dsp: downset_pred SI}
    (ps : partial_solution) (pss : partial_solution_set dsp) := MkParSolDom {
    dom_proj : ∀ β : downset dsp, hom ps (pss β);
    dom_proj_fold : ∀ (β : downset dsp),
      par_sol_fold (pss β) ∘ (F ₕ (dom_proj β)) ≡ (dom_proj β) ∘ par_sol_fold ps;
    dom_proj_iso : ∀ β : downset dsp, is_iso_at (dom_proj β) β;
    dom_fold_iso : ∀ (α : SI), (∀ β, β ≺ α → dsp β) → is_iso_at (par_sol_fold ps) α;
  }.
  Arguments MkParSolDom {_ _ _} _ _ _.
  Arguments dom_proj {_ _ _} _ _.
  Arguments dom_proj_iso {_ _ _} _ _.
  Arguments dom_fold_iso {_ _ _} _ _ _.

  Definition dominate_lim {dsp: downset_pred SI} (pss : partial_solution_set dsp) : obj C :=
    vertex (term (complete (par_sol_set_func pss))).

  Definition dominate_lim_is_limit {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    is_limit (par_sol_set_func pss) (dominate_lim pss) :=
    limiting_cone_is_limit (term_is_terminal (complete (par_sol_set_func pss))).

  Definition dominate_lim_cone_side_iso {dsp: downset_pred SI} (pss : partial_solution_set dsp)
    α : is_iso_at (ic_side (il_is_cone (dominate_lim_is_limit pss)) α) α :=
    limit_side_iso_at_cofinal
      (dominate_lim_is_limit pss)
      α (ds_in_dsp α) (parsol_set_func_isos pss α) α (reflexivity _).

  Definition dominate_proj {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    hom (F ₒ (dominate_lim pss)) (pss β) :=
    ((par_sol_fold (pss β)) ∘ (F ₕ (ic_side (il_is_cone (dominate_lim_is_limit pss)) β))).

  Definition dominate_proj_iso_at {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    is_iso_at (dominate_proj pss β) β :=
    is_iso_at_compose
      (is_iso_at_func F (ic_side (il_is_cone (dominate_lim_is_limit pss)) β)
         (dominate_lim_cone_side_iso pss β)) (parsolset_fold_iso pss β).

  Program Definition dominate_proj_cone {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    cone (par_sol_set_func pss) :=
    MkCone (F ₒ (dominate_lim pss)) (λ β, dominate_proj pss β) _.
  Next Obligation.
    repeat intros ?; rewrite /dominate_proj; simpl in *.
    rewrite -comp_assoc -parsolset_proj_fold.
    rewrite comp_assoc -h_map_comp.
    rewrite -(ic_side_commutes (il_is_cone (dominate_lim_is_limit pss))) //.
  Qed.

  Program Definition dominate_pre_fold {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    hom (F ₒ (dominate_lim pss)) (dominate_lim pss) :=
    cone_hom_map (bang (il_is_limiting_cone _ _ (dominate_lim_is_limit pss))
                    (dominate_proj_cone pss)).

  Lemma dominate_pre_fold_commutes {dsp: downset_pred SI} (pss : partial_solution_set dsp) β :
    dominate_proj pss β ≡
    (ic_side (il_is_cone (dominate_lim_is_limit pss)) β) ∘ (dominate_pre_fold pss).
  Proof.
    apply (cone_hom_commutes (bang
         (il_is_limiting_cone (par_sol_set_func pss)
            (dominate_lim pss) (dominate_lim_is_limit pss))
         (dominate_proj_cone pss))).
  Qed.

  Program Definition dominate_pre_fold_iso
    {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    is_iso_upto (dominate_pre_fold pss) dsp :=
    λ β, is_iso_at_uncompose_r (dominate_lim_cone_side_iso pss β)
      (is_iso_at_proper (dominate_proj_iso_at pss β) (dominate_pre_fold_commutes pss β)).

  Definition dominate_fold {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    hom (F ₒ (F ₒ (dominate_lim pss))) (F ₒ (dominate_lim pss)) :=
    F ₕ (dominate_pre_fold pss).

  Definition dominate_fold_iso {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    ∀ (α : SI), (∀ β, β ≺ α → dsp β) → is_iso_at (dominate_fold pss) α :=
    λ α Hα, iso_upto_contr_func F (dominate_pre_fold pss) (dominate_pre_fold_iso pss) α Hα.

  Program Definition dominate {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    partial_solution := MkParSol (F ₒ (dominate_lim pss)) (dominate_fold pss).

  Program Definition dominate_dominates {dsp: downset_pred SI} (pss : partial_solution_set dsp) :
    partial_solution_dominates (dominate pss) pss :=
    MkParSolDom (dominate_proj pss) _ (dominate_proj_iso_at pss) (dominate_fold_iso pss).
  Next Obligation.
    intros ???.
    rewrite /= /dominate_fold /dominate_proj /dominate_pre_fold.
    rewrite comp_assoc -h_map_comp.
    rewrite_cone_hom_commutes_back.
    done.
  Qed.

  Definition extended_pss {γ} (pss : partial_solution_set (lt_dsp γ))
      (α : downset (le_dsp γ)) : partial_solution :=
    match index_le_lt_eq_dec _ _ (ds_in_dsp α) return partial_solution with
    | left Hlt => pss (MkDS (lt_dsp γ) Hlt)
    | right _ => dominate pss
    end.

  Program Definition extend_proj {γ} (pss : partial_solution_set (lt_dsp γ))
    {α β : downset (le_dsp γ)} (Hle : α ⪯ β) : hom (extended_pss pss α) (extended_pss pss β).
  refine (match index_le_lt_eq_dec _ _ (ds_in_dsp α) as u with
          | left Hlt => _
          | right Heq => _
          end).

  Program Definition dominator_extends {γ} (pss : partial_solution_set (lt_dsp γ)) :
    partial_solution_set (le_dsp γ) :=
    MkParSolSet (extended_pss pss)
      _ _ _ _ _ _.
  Next Obligation.
    intros γ pss α β Hle.


    refine (match index_le_lt_eq_dec _ _ (ds_in_dsp α) as u with
            | left Hlt => _
            | right Heq => _
            end).




  Program Definition par_sol_set_emp : partial_solution (lt_dsp zero) :=
    MkParSol
      (MkFunc
         (λ β, fun_on_empty_set β _)
         (λ β, fun_on_empty_set β _)
         (λ β, fun_on_empty_set β _)
         (λ β, fun_on_empty_set β _)
         (λ β, fun_on_empty_set β _))
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _).
