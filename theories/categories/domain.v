From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat.

Opaque later next.

Class LocallyContractiveFunctor {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  (F : functor C C) := MkLocContrFunc {
  contr_enriched :: EnrichedFunctor F;
  contr_func_h_map : ∀ a b : obj C, hom (later ₒ (enr_hom a b)) (enr_hom (F ₒ a) (F ₒ b));
  contr_func_h_map_is_h_map :
  ∀ a b : obj C, enr_func_h_map F a b ≡ (contr_func_h_map a b) ∘ (next ₙ (enr_hom a b));
  contr_func_h_map_comp : ∀ a b c,
    contr_func_h_map a c ∘
    (later ₕ (enr_comp a b c)) ∘
    (backward (later_prod (enr_hom a b) (enr_hom b c)))
    ≡
    (enr_comp (F ₒ a) (F ₒ b) (F ₒ c)) ∘
    ((contr_func_h_map a b) ×ₕ (contr_func_h_map b c));
  contr_func_h_map_id : ∀ a,
  (contr_func_h_map a a) ∘ (later ₕ ⌜id a⌝) ∘ (next ₙ (1ₒ)) ≡ ⌜id (F ₒ a)⌝
}.
Global Arguments MkLocContrFunc {_ _ _ _ _} _ _ _ _.
Global Arguments contr_func_h_map {_ _ _} _ {_} _ _.
Global Arguments contr_func_h_map_is_h_map {_ _ _} _ {_} _ _.
Global Arguments contr_func_h_map_comp {_ _ _} _ {_} _ _ _.
Global Arguments contr_func_h_map_id {_ _ _} _ {_} _.

Global Instance locally_contractive_contractive
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))} (F : functor C C)
  `{!LocallyContractiveFunctor F} a b :
  Contractive (enr_func_h_map F a b) :=
  MkContr (contr_func_h_map F a b) (contr_func_h_map_is_h_map F a b).

Global Program Instance LocallyContractiveFunctor_comp_l
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))} (F G : functor C C)
  `{!LocallyContractiveFunctor F} `{!EnrichedFunctor G} :
  LocallyContractiveFunctor (functor_compose F G) :=
  MkLocContrFunc (λ a b, enr_func_h_map G (F ₒ a) (F ₒ b) ∘ contr_func_h_map F a b) _ _ _.
Next Obligation.
  intros ??? F G ?? a b α f g Heq; simpl in *.
  pose proof (contr_func_h_map_is_h_map F a b α f g Heq) as Heq'.
  simpl in Heq'; rewrite -Heq' //.
Qed.
Next Obligation.
  intros ??? F G ?? a b c α [la lb] [z1 z2] [<- <-]; clear z1 z2; simpl in *.
  pose proof (contr_func_h_map_comp F a b c α (la, lb) _ (reflexivity _))
    as Hfg; simpl in Hfg; rewrite Hfg; clear Hfg.
  epose proof (enr_func_h_map_comp G _ _ _ α _ _ (reflexivity _)) as Hcmp;
    simpl in Hcmp; rewrite Hcmp; clear Hcmp.
  simpl; done.
Qed.
Next Obligation.
  intros ??? F G ?? a α [] [] _; simpl in *.
  pose proof (contr_func_h_map_id F a α () _ (reflexivity _)) as Hid;
    simpl in Hid; rewrite Hid; clear Hid.
  epose proof (enr_func_h_map_id G _ α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  done.
Qed.
Fail Next Obligation.

Global Program Instance LocallyContractiveFunctor_comp_r
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))} (F G : functor C C)
  `{!LocallyContractiveFunctor F} `{!EnrichedFunctor G} :
  LocallyContractiveFunctor (functor_compose G F) :=
  MkLocContrFunc (λ a b, contr_func_h_map F (G ₒ a) (G ₒ b) ∘ (later ₕ (enr_func_h_map G a b))) _ _ _.
Next Obligation.
  intros ??? F G ?? a b α f g <-; clear g; simpl in *.
  pose proof (contr_func_h_map_is_h_map
    F (G ₒ a) (G ₒ b) α ((enr_func_h_map G a b ₙ α) f) _ (reflexivity _))
    as Heq; simpl in Heq; rewrite Heq; clear Heq.
  f_equiv.
  pose proof (naturality next (enr_func_h_map G a b) α f _ (reflexivity _)); done.
Qed.
Next Obligation.
  intros ??? F G ?? a b c α [la lb] [z1 z2] [<- <-]; clear z1 z2; simpl in *.
  epose proof (h_map_comp _ _ later _ _ _
    (enr_comp a b c) (enr_func_h_map G a c) α _ _ (reflexivity _)) as Hlc;
    simpl in Hlc; rewrite -Hlc; clear Hlc.
  epose proof (enr_func_h_map_comp G _ _ _) as Hcmp.
  simpl in Hcmp; rewrite Hcmp; clear Hcmp.
  epose proof (h_map_comp _ _ later _ _ _
    _ (enr_comp _ _ _) α _ _ (reflexivity _)) as Hlc;
    simpl in Hlc; rewrite Hlc; clear Hlc.
  epose proof (@naturality _ _ _ _ (backward (later_preserves_prods_nat SI))
                 (_, _) (_, _) (_, _) _ (_, _) _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (contr_func_h_map_comp F _ _ _ _ _ _ (reflexivity _)) as Hcmp;
  simpl in Hcmp; rewrite Hcmp; clear Hcmp.
  done.
Qed.
Next Obligation.
  intros ??? F G ?? a α [] [] _; simpl in *.
  pose proof (naturality next ⌜ id a ⌝ α () _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (naturality next (enr_func_h_map G a a) α _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (enr_func_h_map_id G _ α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite !Hg; clear Hg.
  pose proof (naturality next ⌜ id (G ₒ a) ⌝ α () _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite Hn; clear Hn.
  pose proof (contr_func_h_map_id F (G ₒ a) α () _ (reflexivity _)) as Hid;
    simpl in Hid; rewrite Hid; done.
Qed.
Fail Next Obligation.

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
    rewrite -enr_func_h_map_is_hmap !enr_embed_project.
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
    rewrite -enr_func_h_map_is_hmap !enr_embed_project.
    rewrite enr_comp_l_comp -enr_comp_comp !enr_embed_project.
    rewrite enr_comp_r_comp -enr_comp_comp !enr_embed_project.
    rewrite -(alg_hom_commutes h).
    rewrite !comp_assoc /alg_of_solution /=.
    pose proof (is_iso (sol_iso S)) as [_ ->].
    rewrite right_id //.
  Qed.

  Program Definition alg_of_solution_is_initial S :
    @is_initial (alg_cat F) (alg_of_solution S) :=
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

  Program Definition solution_unique (S S' : solution) : sol_obj S ≃ sol_obj S' :=
    let iso :=
      @is_initial_unique (alg_cat F) _ _
        (alg_of_solution_is_initial S)
        (alg_of_solution_is_initial S')
    in
    MkIsoIc (alg_hom_map (forward iso)) (alg_hom_map (backward iso)) _.
  Next Obligation.
    intros S S' iso; destruct (is_iso iso) as [? ?]; split; done.
  Qed.

End solution_unique.

