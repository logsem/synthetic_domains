From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat enriched.

Opaque later next.

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
