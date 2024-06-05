From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat enriched.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

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

  Program Definition extend_partial_solution {α} {ps : partial_solution (lt_dsp α)}
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
    extend_partial_solution pse ≃@{FuncCat ((OrdDSCat (le_dsp α))ᵒᵖ) (Alg F)}
    extend_partial_solution pse' :=
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
    eapply iso_at_downwards; last by apply parsol_edge_iso.
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
      eapply iso_at_downwards; last by apply parsol_edge_iso.
      done. }
    eapply is_iso_at_uncompose_r; first apply Hiso.
    eapply is_iso_at_proper; last by rewrite_cone_hom_commutes_back; reflexivity.
    simpl.
    apply is_iso_at_compose; last apply parsol_cons_iso.
    apply (is_iso_at_func F).
    done.
  Qed.
  Fail Next Obligation.



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



  Definition par_sol_set_emp : partial_solution_set (lt_dsp zero) :=
    MkParSolSet
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _).

































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



  Definition par_sol_set_emp : partial_solution_set (lt_dsp zero) :=
    MkParSolSet
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _)
      (λ β, fun_on_empty_set β _).

