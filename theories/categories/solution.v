From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat enriched domain uip strict_complete.

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

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

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Program Definition iso_alg_hom_map {D} (G : functor D D)
  (a b : obj (Alg G)) (i : hom a b) (j : hom b a)
  (H : isomorphism i j) : isomorphism (alg_hom_map i) (alg_hom_map j)
  := MkIso
       _
       _.
Next Obligation.
  intros; simpl.
  by rewrite -alg_hom_map_comp (iso_lr H).
Qed.
Next Obligation.
  intros; simpl.
  by rewrite -alg_hom_map_comp (iso_rl H).
Qed.

Program Definition alg_func_on_alg_iso_cong {D} (G : functor D D)
  (a b : algebra G) (i : a ≃@{Alg G} b)
  : alg_func_on_alg a ≃@{Alg G} alg_func_on_alg b
  := MkIsoIc
       (MkAlgHom (G ₕ (alg_hom_map (forward i))) _)
       (MkAlgHom (G ₕ (alg_hom_map (backward i))) _)
       (MkIso _ _).
Next Obligation.
  intros; simpl.
  by rewrite -!h_map_comp alg_hom_commutes.
Qed.
Next Obligation.
  intros; simpl.
  by rewrite -!h_map_comp alg_hom_commutes.
Qed.
Next Obligation.
  intros; simpl.
  apply alg_hom_map_eq; simpl.
  rewrite -h_map_comp.
  rewrite iso_lr; first by rewrite h_map_id.
  apply iso_alg_hom_map, i.
Qed.
Next Obligation.
  intros; simpl.
  apply alg_hom_map_eq; simpl.
  rewrite -h_map_comp.
  rewrite iso_rl; first by rewrite h_map_id.
  apply iso_alg_hom_map, i.
Qed.

Program Definition alg_lim_alg_iso_cong {D} `{Complete D} {T : functor D D}
  {J : category}
  (I I' : functor J (Alg T)) (i : I ≃@{FuncCat _ _} I')
  : alg_lim_alg I ≃@{Alg _} alg_lim_alg I'
  := eq_cones_vertexes (limit_of_isos_equiv_cones i (alg_lim _) (alg_lim _)).

Opaque later next.

Section solution.
  Context {SI : indexT} {C : category} `{!Complete C} `{!StrictComplete C}
    `{!Enriched C (PSh (OrdCat SI))} `{!LimitsEnriched C}
    (F : functor C C) `{!LocallyContractiveFunctor F}.

  Definition dsp_included_refl {dsp : downset_pred SI} : dsp_included dsp dsp
    := λ _ P, P.

  Definition dsp_included_lt_le {α : SI} : dsp_included (lt_dsp α) (le_dsp α)
    := λ β P, index_lt_le_subrel _ _ P.

  Program Definition dsp_included_trans {dsp dsp' dsp'' : downset_pred SI} :
    dsp_included dsp dsp' → dsp_included dsp' dsp'' → dsp_included dsp dsp''
    := λ H G β P, (G _ (H _ P)).

  Definition dsp_le_top (α : SI) : downset (le_dsp α)
    := MkDS (le_dsp α) (squash (reflexivity _)).

  (* An F-algebra whose constructor map is α-iso for all α is the solution. *)
  Definition alg_cons_is_iso_upto_total_solution {A : algebra F}
    (iso : is_iso_upto (cons A) (total_dsp SI)) : (solution F) :=
    MkSolution _ (car A) (is_iso_upto_total (cons A) iso).

  (* Now, we will construct such an algebra. *)

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
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp β))) as [Hltβ|Heqβ];
      destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp γ))) as [Hltγ|Heqγ];
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
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp β))) as [Hltβ|Heqβ].
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
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp β))) as [Hltβ|Heqβ].
    + rewrite !(extend_ord_ds_cat_nat_map_lt _ _ Hltβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_lr (is_iso psiso) (MkDS (lt_dsp α) (squash Hltβ))) as Hlr;
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
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp β))) as [Hltβ|Heqβ].
    + rewrite !(extend_ord_ds_cat_nat_map_lt _ _ Hltβ) /=.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map.
      rewrite hom_trans_compose_take_in_l /= -hom_trans_trans.
      rewrite !eq_trans_sym_inv_r !eq_trans_refl_r.
      rewrite hom_trans_compose_take_in_r /= -hom_trans_trans.
      rewrite !eq_trans_refl_l !eq_trans_refl_r !hom_trans_refl /=.
      pose proof (iso_rl (is_iso psiso) (MkDS (lt_dsp α) (squash Hltβ))) as Hlr;
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
             α (unsquash (ds_in_dsp α))); last done.
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
             β (unsquash (ds_in_dsp β))); last done.
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

  Program Definition total_partial_sol_sol
    (ps : partial_solution (total_dsp SI))
    : solution F :=
    MkSolution F
      (car (vertex (the_extension ps)))
      (is_iso_upto_total (cons (vertex (the_extension ps)))
         (λ α, (parsolext_cons_iso (the_extension ps) α (λ _ _, I)))).

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

  Definition cut_ord_ds_cat_func_trivial {dsp : downset_pred SI}
    (P : partial_solution dsp)
    : ∀ a : downset dsp,
    P ₒ a
    = P ₒ dsp_include (le_dsp_included a) (dsp_le_top a)
  := λ _, eq_refl.

  Lemma cut_ord_ds_cat_func_trivial_refl {dsp : downset_pred SI}
    {P : partial_solution dsp} : ∀ a, (cut_ord_ds_cat_func_trivial P a = eq_refl).
  Proof. intros; reflexivity. Qed.

  Program Definition cut_par_sol {dsp} (ps : partial_solution dsp)
    {dsp' : downset_pred SI}
    (Hdsps : dsp_included dsp' dsp) : partial_solution dsp' :=
    MkParSol (cut_ord_ds_cat_func dsp' Hdsps ps) _ _.
  Next Obligation.
    intros ? ps ?????.
    rewrite /cut_ord_ds_cat_func /= /cut_ord_ds_cat_func_h_map.
    apply (parsol_edge_iso ps).
  Qed.
  Next Obligation.
    intros ? ps ???.
    rewrite /cut_ord_ds_cat_func /= /cut_ord_ds_cat_func_h_map.
    apply (parsol_cons_iso ps).
  Qed.
  Fail Next Obligation.

  Program Definition par_sol_extensional {dsp : downset_pred SI}
    (P Q : partial_solution dsp)
    (eqs : ∀ α : downset dsp,
       functor_equiv
         (cut_ord_ds_cat_func _ (le_dsp_included α) P)
         (cut_ord_ds_cat_func _ (le_dsp_included α) Q))
    : functor_equiv P Q
    := MkFuncEq
         (λ a, eq_trans
                 (eq_trans
                    (cut_ord_ds_cat_func_trivial P a)
                    (func_eq_o_map (eqs a) (dsp_le_top a)))
                 (eq_sym (cut_ord_ds_cat_func_trivial Q a)))
         _.
  Next Obligation.
    intros dsp P Q eqs α β f; simpl.
    rewrite !hom_trans_trans.
    symmetry.
    rewrite !cut_ord_ds_cat_func_trivial_refl.
    rewrite hom_trans_refl.
    epose proof (λ δ γ g, func_eq_h_map (eqs α) (a := δ) (b := γ) g) as HEQ.
    rewrite /= /cut_ord_ds_cat_func_h_map /= in HEQ.
    match goal with
    | |- context G [_ ₕ ?a ≡ _] =>
        set (f' := a)
    end.
    simpl in f'.
    assert (f' = f) as ->.
    { apply proof_irrel. }
    simpl in f.
    rewrite -(HEQ
                (dsp_le_top α)
                  (MkDS (le_dsp α) (squash f))
                  f).
    f_equiv; last done.
    apply ProofIrrelevance.proof_irrelevance.
  Qed.

  Record compat_iso_fam {dsp : downset_pred SI}
    (P Q : partial_solution dsp)
    := MkCompatIsoFam {
           iso_fam : ∀ a : downset dsp,
             isomorphic (C := FuncCat _ _)
               (cut_ord_ds_cat_func _ (le_dsp_included a) P)
               (cut_ord_ds_cat_func _ (le_dsp_included a) Q);
           iso_fam_compat_forward : ∀ (a b : downset dsp) (f : le_dsp b a),
             forward (iso_fam a) ₙ (dsp_le_top a)
               ≡ forward (iso_fam b) ₙ (MkDS (le_dsp b)
                                          (squash f));
           iso_fam_compat_backward : ∀ (a b : downset dsp) (f : le_dsp b a),
             backward (iso_fam a) ₙ (dsp_le_top a)
               ≡ backward (iso_fam b) ₙ (MkDS (le_dsp b)
                                           (squash f));
         }.

  Program Definition par_sol_extensional_iso {dsp : downset_pred SI}
    (P Q : partial_solution dsp)
    (eqs : compat_iso_fam P Q)
    : isomorphic (C := FuncCat _ _) P Q
    := MkIsoIc
         (MkNat (λ β, (forward (iso_fam _ _ eqs β) ₙ
                         (dsp_le_top β))) _)
         (MkNat (λ β, (backward (iso_fam _ _ eqs β) ₙ
                         (dsp_le_top β))) _)
         _.
  Next Obligation.
    intros; simpl.
    simpl in f.
    epose proof (@naturality _ _ _ _ (forward (iso_fam _ _ eqs a))
                   (dsp_le_top a)
                   (MkDS (le_dsp a) (squash f)) f) as H.
    simpl in H.
    rewrite -H; clear H.
    f_equiv.
    match goal with
    | |- context G [MkDS ?a ?b] =>
        set (T := MkDS a b)
    end.
    pose proof (forward (iso_fam P Q eqs b)ₙ (dsp_le_top b)).
    pose proof (forward (iso_fam P Q eqs a)ₙ T).
    apply (iso_fam_compat_forward _ _ eqs b).
  Qed.
  Next Obligation.
    intros; simpl.
    simpl in f.
    epose proof (@naturality _ _ _ _ (backward (iso_fam _ _ eqs a))
                   (dsp_le_top a)
                   (MkDS (le_dsp a) (squash f)) f) as H.
    simpl in H.
    rewrite -H; clear H.
    f_equiv.
    apply (iso_fam_compat_backward _ _ eqs b).
  Qed.
  Next Obligation.
    intros; simpl.
    split.
    - intros ?; simpl.
      pose proof (iso_lr (is_iso (iso_fam _ _ eqs a))
                    (dsp_le_top a)) as H.
      simpl in H.
      rewrite H; clear H.
      reflexivity.
    - intros ?; simpl.
      pose proof (iso_rl (is_iso (iso_fam _ _ eqs a))
                    (dsp_le_top a)) as H.
      simpl in H.
      rewrite H; clear H.
      reflexivity.
  Qed.

  Opaque comp id.
  Program Definition extend_par_sol_lt_le_iso_lt {α}
    (ps : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    : isomorphic (C := FuncCat _ _)
        (cut_par_sol (extend_par_sol_lt_le ps) H)
        ps
    := MkIsoIc
         (MkNat (λ c,
            (hom_trans
               eq_refl
               (extend_ord_ds_cat_func_o_map_lt
                  (β := (dsp_include H c))
                  (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp c)))
               (id _))) _)
         (MkNat (λ c,
            (hom_trans
               (extend_ord_ds_cat_func_o_map_lt
                  (β := (dsp_include H c))
                  (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp c)))
               eq_refl
               (id _))) _)
         _.
  Next Obligation.
    intros α ps H.
    intros β γ Hle; simpl in *.
    rewrite !hom_trans_compose_take_in_l.
    rewrite right_id.
    rewrite hom_trans_refl.
    rewrite !hom_trans_compose_take_in_r.
    rewrite left_id.
    rewrite -!hom_trans_trans eq_trans_refl_r eq_trans_refl_l.
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp (dsp_include H β)))) as [Hltβ|Heqβ];
      destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp (dsp_include H γ)))) as [Hltγ|Heqγ];
      repeat simplify_extend_ord_ds_cat_func_h_map.
    - rewrite -!hom_trans_trans eq_trans_refl_r.
      f_equiv; last reflexivity.
      + apply proof_irrelevance.
      + apply proof_irrelevance.
    - exfalso.
      eapply index_lt_le_contradict; first apply (unsquash (ds_in_dsp β)).
      rewrite Heqβ; reflexivity.
    - exfalso.
      eapply index_lt_le_contradict; first apply (unsquash (ds_in_dsp β)).
      rewrite Heqβ; reflexivity.
  Qed.
  Next Obligation.
    intros α ps H.
    intros β γ Hle; simpl in *.
    rewrite !hom_trans_compose_take_in_l.
    rewrite right_id.
    rewrite hom_trans_refl.
    rewrite !hom_trans_compose_take_in_r.
    rewrite left_id.
    rewrite -!hom_trans_trans eq_trans_refl_l eq_trans_refl_r.
    destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp (dsp_include H β)))) as [Hltβ|Heqβ];
      destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp (dsp_include H γ)))) as [Hltγ|Heqγ];
      repeat simplify_extend_ord_ds_cat_func_h_map.
    - rewrite -!hom_trans_trans eq_trans_refl_r.
      f_equiv; last reflexivity.
      + apply proof_irrelevance.
      + apply proof_irrelevance.
    - exfalso.
      eapply index_lt_le_contradict; first apply (unsquash (ds_in_dsp β)).
      rewrite Heqβ; reflexivity.
    - exfalso.
      eapply index_lt_le_contradict; first apply (unsquash (ds_in_dsp β)).
      rewrite Heqβ; reflexivity.
  Qed.
  Transparent comp id.
  Next Obligation.
    intros; simpl; split.
    - intros ?; simpl.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map /=.
      rewrite !hom_trans_compose_take_in_l.
      rewrite -!hom_trans_trans !eq_trans_sym_inv_r.
      rewrite !hom_trans_refl.
      rewrite left_id.
      reflexivity.
    - intros ?; simpl.
      apply alg_hom_map_eq; simpl.
      rewrite !hom_trans_alg_hom_map /=.
      rewrite !hom_trans_compose_take_in_l.
      rewrite -!hom_trans_trans !eq_trans_sym_inv_r eq_trans_refl_r.
      rewrite !hom_trans_compose_take_in_r.
      rewrite -!hom_trans_trans !eq_trans_refl_r /= !hom_trans_refl.
      rewrite eq_trans_refl_l.
      rewrite left_id.
      rewrite hom_trans_id.
      reflexivity.
  Qed.

  Program Definition cut_partial_solution_equiv
    {dsp dsp'} {ps ps' : partial_solution dsp}
    (H : dsp_included dsp' dsp)
    (psequiv : functor_equiv ps ps')
    : functor_equiv
        (cut_par_sol ps H)
        (cut_par_sol ps' H)
    := MkFuncEq
         (λ a, func_eq_o_map psequiv (dsp_include H a))
         _.
  Next Obligation.
    intros; simpl.
    unfold cut_ord_ds_cat_func_h_map.
    rewrite func_eq_h_map.
    reflexivity.
  Qed.

  Program Definition extend_par_sol_lt_le_equiv_lt {α}
    (ps : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    : functor_equiv
        (cut_par_sol (extend_par_sol_lt_le ps) H)
        ps :=
    MkFuncEq (λ a, (extend_ord_ds_cat_func_o_map_lt (alg_func_on_cone (alg_lim_cone ps))
                      (β := dsp_include H a) (unsquash (ds_in_dsp a)))) _.
  Next Obligation.
    intros; simpl.
    rewrite (extend_ord_ds_cat_func_h_map_lt_lt (alg_func_on_cone (alg_lim_cone ps))).
    { apply (unsquash (ds_in_dsp a)). }
    { apply (unsquash (ds_in_dsp b)). }
    intros J1 J2.
    rewrite -!hom_trans_trans.
    assert (J1 = unsquash (ds_in_dsp a)) as -> by apply proof_irrelevance.
    assert (J2 = unsquash (ds_in_dsp b)) as -> by apply proof_irrelevance.
    rewrite !eq_trans_sym_inv_l.
    rewrite hom_trans_refl.
    reflexivity.
  Qed.

  Program Definition extend_partial_solution_equiv
    {α : SI} {ps ps' : partial_solution (lt_dsp α)}
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (psequiv : functor_equiv ps ps')
    : functor_equiv
        (cut_par_sol (extend_par_sol_lt_le ps) H)
        (cut_par_sol (extend_par_sol_lt_le ps') H)
    := transitivity (extend_par_sol_lt_le_equiv_lt ps H)
         (transitivity psequiv
            (symmetry (extend_par_sol_lt_le_equiv_lt ps' H))).

  Lemma extend_par_sol_lt_le_iso_lt_fwd_pointwise {α}
    (ps : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    : ∀ (β : downset (lt_dsp α)),
    forward (extend_par_sol_lt_le_iso_lt ps H) ₙ β ≡
      hom_trans
      eq_refl
      (extend_ord_ds_cat_func_o_map_lt
         (β := (dsp_include H β))
         (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β)))
      (id _).
  Proof.
    intros; simpl.
    reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_fwd_pointwise {α}
    (ps ps' : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (Hiso : ps ≃@{FuncCat _ _} ps')
    (β : downset (lt_dsp α))
    : (hom_trans
             (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β)))
             (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps')) (unsquash (ds_in_dsp β)))
             (forward (extend_par_sol_lt_le_iso Hiso) ₙ (dsp_include H β)))
        ≡ (forward Hiso ₙ β).
  Proof.
    simpl.
    unshelve rewrite extend_ord_ds_cat_nat_map_lt.
    { apply (unsquash (ds_in_dsp β)). }
    rewrite -!hom_trans_trans.
    rewrite !eq_trans_sym_inv_l.
    rewrite hom_trans_refl.
    reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_bwd_pointwise {α}
    (ps ps' : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (Hiso : ps ≃@{FuncCat _ _} ps')
    (β : downset (lt_dsp α))
    : (hom_trans
             (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps')) (unsquash (ds_in_dsp β)))
             (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β)))
             (backward (extend_par_sol_lt_le_iso Hiso) ₙ (dsp_include H β)))
        ≡ (backward Hiso ₙ β).
  Proof.
    simpl.
    unshelve rewrite extend_ord_ds_cat_nat_map_lt.
    { apply (unsquash (ds_in_dsp β)). }
    rewrite -!hom_trans_trans.
    rewrite !eq_trans_sym_inv_l.
    rewrite hom_trans_refl.
    reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_bwd_pointwise' {α}
    (ps ps' : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (Hiso : ps ≃@{FuncCat _ _} ps')
    (β : downset (lt_dsp α))
    : backward (extend_par_sol_lt_le_iso Hiso) ₙ (dsp_include H β)
        ≡ hom_trans
             (eq_sym (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps')) (unsquash (ds_in_dsp β))))
             (eq_sym (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β))))
             (backward Hiso ₙ β).
  Proof.
    simpl.
    unshelve rewrite extend_ord_ds_cat_nat_map_lt.
    { apply (unsquash (ds_in_dsp β)). }
    f_equiv.
    reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_fwd_pointwise' {α}
    (ps ps' : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (Hiso : ps ≃@{FuncCat _ _} ps')
    (β : downset (lt_dsp α))
    : forward (extend_par_sol_lt_le_iso Hiso) ₙ (dsp_include H β)
        ≡ hom_trans
             (eq_sym (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β))))
             (eq_sym (extend_ord_ds_cat_func_o_map_lt
                (β := (dsp_include H β))
                (alg_func_on_cone (alg_lim_cone ps')) (unsquash (ds_in_dsp β))))
             (forward Hiso ₙ β).
  Proof.
    simpl.
    unshelve rewrite extend_ord_ds_cat_nat_map_lt.
    { apply (unsquash (ds_in_dsp β)). }
    f_equiv.
    reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_lt_bwd_pointwise {α}
    (ps : partial_solution (lt_dsp α))
    (H : dsp_included (lt_dsp α) (le_dsp α))
    : ∀ (β : downset (lt_dsp α)),
    backward (extend_par_sol_lt_le_iso_lt ps H) ₙ β ≡
      hom_trans
      (extend_ord_ds_cat_func_o_map_lt
         (β := (dsp_include H β))
         (alg_func_on_cone (alg_lim_cone ps)) (unsquash (ds_in_dsp β)))
      eq_refl
      (id _).
  Proof.
    intros; simpl.
    reflexivity.
  Qed.

  Program Definition partial_sol_cone_at {dsp} (ps : partial_solution dsp)
    (α : downset dsp) : cone (cut_par_sol ps (lt_dsp_included α))
    := MkCone (parsol_func ps ₒ α)
         (λ j, MkAlgHom
                 ((alg_hom_map
                     (ps ₕ index_lt_le_subrel j α
                        (unsquash (ds_in_dsp j))))) _) _.
  Next Obligation.
    intros; simpl.
    reflexivity.
  Defined.
  Next Obligation.
    intros; simpl.
    rewrite alg_hom_commutes.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    apply alg_hom_map_eq; simpl.
    unfold cut_ord_ds_cat_func_h_map.
    rewrite -alg_hom_map_comp.
    rewrite -h_map_comp.
    do 2 f_equiv.
    reflexivity.
  Qed.

  Lemma iso_forward_trans {D : category} {a b c : obj D}
    (H1 : a ≃ b) (H2 : b ≃ c) :
    forward (isomorphic_trans H1 H2)
      ≡ (forward H2) ∘ (forward H1).
  Proof. reflexivity. Qed.

  Lemma iso_backward_trans {D : category} {a b c : obj D}
    (H1 : a ≃ b) (H2 : b ≃ c) :
    backward (isomorphic_trans H1 H2)
      ≡ (backward H1) ∘ (backward H2).
  Proof. reflexivity. Qed.

  Lemma iso_forward_sym {D : category} {a b : obj D}
    (H : a ≃ b) :
    forward (isomorphic_sym H)
      ≡ backward H.
  Proof. reflexivity. Qed.

  Lemma iso_backward_sym {D : category} {a b : obj D}
    (H : a ≃ b) :
    backward (isomorphic_sym H)
      ≡ forward H.
  Proof. reflexivity. Qed.

  Lemma iso_backward_equiv {D E : category} {a b : functor D E}
    (H : a ≡ b) x
    : backward (functor_eq_natural_iso H) ₙ x
        ≡ hom_trans (func_eq_o_map H _) eq_refl (id _).
  Proof.
    unfold functor_eq_natural_iso.
    simpl.
    destruct (func_eq_o_map H x).
    reflexivity.
  Qed.

  Lemma iso_forward_equiv {D E : category} {a b : functor D E}
    (H : a ≡ b) x
    : forward (functor_eq_natural_iso H) ₙ x
        ≡ hom_trans eq_refl (func_eq_o_map H _) (id _).
  Proof.
    unfold functor_eq_natural_iso.
    simpl.
    destruct (func_eq_o_map H x).
    reflexivity.
  Qed.

  Lemma functor_eq_natural_iso_trans_fwd {D E : category} {a b : functor D E}
    (H : a ≡ b)
    : forward (functor_eq_natural_iso H) ≡ functor_eq_natural H.
  Proof.
    intros ?; simpl.
    reflexivity.
  Qed.

  Lemma functor_eq_natural_iso_trans_bwd {D E : category} {a b : functor D E}
    (H : a ≡ b)
    : backward (functor_eq_natural_iso H) ≡ functor_eq_natural_backward H.
  Proof.
    intros ?; simpl.
    reflexivity.
  Qed.

  Lemma iso_backward_equiv' {D E : category} {a b : functor D E}
    (H : a ≡ b)
    : backward (functor_eq_natural_iso H)
        ≡ forward (functor_eq_natural_iso (symmetry H)).
  Proof.
    unfold functor_eq_natural_iso.
    simpl.
    intros ?.
    rewrite -functor_eq_natural_iso_trans_bwd /=.
    f_equiv.
    apply proof_irrelevance.
  Qed.

  Definition pointwise_id_right {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps ps')
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    := ∀ (β : downset dsp'),
    η ₙ (dsp_include H β)
      ≡ hom_trans
      eq_refl
      (Heq β)
      (id _).

  Global Instance pointwise_id_right_proper
    {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    : Proper ((≡) ==> (forall_relation (λ _, (=))) ==> (iff))
        ((pointwise_id_right (ps := ps) (ps' := ps') dsp' H) ).
  Proof.
    intros η η' Hη P Q J.
    split; intros G β.
    - rewrite -Hη.
      rewrite -(J β).
      apply G.
    - rewrite Hη.
      rewrite (J β).
      apply G.
  Qed.

  Lemma pointwise_id_right_trans_r {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps ps')
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    (qs : partial_solution dsp)
    (Hequiv : functor_equiv ps' qs)
    (Heq' : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = qs ₒ (dsp_include H β))
    : pointwise_id_right dsp' H η Heq →
      pointwise_id_right dsp' H
        ((functor_eq_natural Hequiv) ∘ η)
        Heq'.
  Proof.
    intros G.
    assert (Heq' = (λ β, eq_trans (Heq β) (func_eq_o_map Hequiv (dsp_include H β)))) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    rewrite hom_trans_compose_r.
    rewrite -hom_trans_compose left_id G /=.
    rewrite -{2}(eq_trans_refl_r eq_refl).
    assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
    { intros [] []; reflexivity. }
    rewrite hom_trans_trans.
    f_equiv.
    rewrite hom_trans_alg_hom_map /=.
    reflexivity.
  Qed.

  Lemma pointwise_id_right_trans_l {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    (η : hom (C := FuncCat _ _) ps ps')
    (qs : partial_solution dsp)
    (Hequiv : functor_equiv qs ps)
    (Heq' : ∀ (β : downset dsp'),
       qs ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    : pointwise_id_right dsp' H η Heq →
      pointwise_id_right dsp' H
        (η ∘ (functor_eq_natural Hequiv : hom (C := FuncCat _ _) _ _))
        Heq'.
  Proof.
    intros G.
    assert (Heq' = (λ β, eq_trans (func_eq_o_map Hequiv (dsp_include H β)) (Heq β))) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    apply alg_hom_map_eq; simpl.
    rewrite G.
    rewrite !hom_trans_alg_hom_map /=.
    rewrite hom_trans_compose_take_in_l right_id hom_trans_refl.
    symmetry.
    match goal with
    | |- context G [_ ≡ hom_trans _ ?a _]
      => assert (a = eq_sym a) as ->
    end; first by reflexivity.
    apply hom_trans_sym.
    rewrite -hom_trans_trans.
    rewrite eq_trans_refl_l eq_trans_refl_r.
    assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
    { intros [] []; reflexivity. }
    rewrite -{1}(eq_trans_refl_r (car_eq _)).
    rewrite hom_trans_trans.
    f_equiv.
    rewrite hom_trans_id.
    reflexivity.
  Qed.

  Lemma pointwise_id_right_comp {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps ps')
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    {qs : partial_solution dsp}
    (η' : hom (C := FuncCat _ _) ps' qs)
    (Heq' : ∀ (β : downset dsp'),
       ps' ₒ (dsp_include H β) = qs ₒ (dsp_include H β))
    (Heq'' : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = qs ₒ (dsp_include H β))
    : pointwise_id_right dsp' H η Heq →
      pointwise_id_right dsp' H η' Heq' →
      pointwise_id_right dsp' H
        (η' ∘ η)
        Heq''.
  Proof.
    intros G1 G2.
    assert (Heq'' = (λ β, eq_trans (Heq β) (Heq' β))) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    rewrite G1 G2.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
    { intros [] []; reflexivity. }
    rewrite -{2}(eq_trans_refl_r eq_refl).
    rewrite hom_trans_trans.
    rewrite hom_trans_compose_r.
    rewrite -hom_trans_compose left_id /=.
    reflexivity.
  Qed.

  Definition pointwise_id_left {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps' ps)
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    := ∀ (β : downset dsp'),
    η ₙ (dsp_include H β)
      ≡ hom_trans
      (Heq β)
      eq_refl
      (id _).

  Global Instance pointwise_id_left_proper
    {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    : Proper ((≡) ==> (forall_relation (λ _, (=))) ==> (iff))
        ((pointwise_id_left (ps := ps) (ps' := ps') dsp' H) ).
  Proof.
    intros η η' Hη P Q J.
    split; intros G β.
    - rewrite -Hη.
      rewrite -(J β).
      apply G.
    - rewrite Hη.
      rewrite (J β).
      apply G.
  Qed.

  Lemma pointwise_id_left_trans_r {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps ps')
    (Heq : ∀ (β : downset dsp'),
       ps' ₒ (dsp_include H β) = ps ₒ (dsp_include H β))
    (qs : partial_solution dsp)
    (Hequiv : functor_equiv qs ps')
    (Heq' : ∀ (β : downset dsp'),
       qs ₒ (dsp_include H β) = ps ₒ (dsp_include H β))
    : pointwise_id_left dsp' H η Heq →
      pointwise_id_left dsp' H
        ((functor_eq_natural_backward Hequiv) ∘ η)
        Heq'.
  Proof.
    intros G.
    assert (Heq' = (λ β, eq_trans (func_eq_o_map Hequiv (dsp_include H β)) (Heq β) )) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    rewrite hom_trans_compose_r.
    rewrite -hom_trans_compose left_id G /=.
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    match goal with
    | |- context G [hom_trans ?a _ _ ≡ _]
      => assert (a = eq_sym a) as ->
    end; first by reflexivity.
    symmetry.
    apply hom_trans_sym.
    rewrite hom_trans_alg_hom_map /=.
    rewrite -!hom_trans_trans.
    rewrite eq_trans_refl_l.
    rewrite eq_trans_refl_r.
    assert ((car_eq (func_eq_o_map Hequiv (dsp_include H β)))
            = eq_trans (car_eq (func_eq_o_map Hequiv (dsp_include H β))) eq_refl) as ->.
    { by rewrite eq_trans_refl_r. }
    assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
    { intros [] []; reflexivity. }
    rewrite hom_trans_trans.
    f_equiv.
    rewrite hom_trans_id.
    reflexivity.
  Qed.

  Lemma pointwise_id_left_trans_l {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    (η : hom (C := FuncCat _ _) ps' ps)
    (qs : partial_solution dsp)
    (Hequiv : functor_equiv ps' qs)
    (Heq' : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = qs ₒ (dsp_include H β))
    : pointwise_id_left dsp' H η Heq →
      pointwise_id_left dsp' H
        (η ∘ (functor_eq_natural_backward Hequiv : hom (C := FuncCat _ _) _ _))
        Heq'.
  Proof.
    intros G.
    assert (Heq' = (λ β, eq_trans (Heq β) (func_eq_o_map Hequiv (dsp_include H β)))) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    apply alg_hom_map_eq; simpl.
    rewrite G.
    rewrite !hom_trans_alg_hom_map /=.
    rewrite hom_trans_compose_take_in_l right_id hom_trans_refl.
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    rewrite eq_sym_involutive.
    rewrite -!hom_trans_trans.
    f_equiv; last reflexivity.
    apply proof_irrelevance.
  Qed.

  Lemma pointwise_id_left_comp {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (η : hom (C := FuncCat _ _) ps ps')
    (Heq : ∀ (β : downset dsp'),
       ps' ₒ (dsp_include H β) = ps ₒ (dsp_include H β))
    {qs : partial_solution dsp}
    (η' : hom (C := FuncCat _ _) ps' qs)
    (Heq' : ∀ (β : downset dsp'),
       qs ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    (Heq'' : ∀ (β : downset dsp'),
       qs ₒ (dsp_include H β) = ps ₒ (dsp_include H β))
    : pointwise_id_left dsp' H η Heq →
      pointwise_id_left dsp' H η' Heq' →
      pointwise_id_left dsp' H
        (η' ∘ η)
        Heq''.
  Proof.
    intros G1 G2.
    assert (Heq'' = (λ β, eq_trans (Heq' β) (Heq β))) as ->.
    { apply proof_irrelevance. }
    intros β; simpl.
    rewrite G1 G2.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
    { intros [] []; reflexivity. }
    match goal with
    | |- context G [_ ≡ hom_trans _ ?a _]
      => assert (a = eq_trans eq_refl a) as ->
    end; first by reflexivity.
    rewrite hom_trans_trans.
    rewrite eq_trans_refl_r.
    assert ((car_eq (Heq' β)) = eq_sym (eq_sym (car_eq (Heq' β)))) as ->.
    { by rewrite eq_sym_involutive. }
    rewrite -hom_trans_compose_l.
    rewrite left_id.
    symmetry.
    match goal with
    | |- context G [_ ≡ hom_trans ?a _ _]
      => assert (a = eq_sym (eq_sym a)) as ->
    end; first by rewrite eq_sym_involutive.
    apply hom_trans_sym.
    rewrite !eq_sym_involutive.
    rewrite -!hom_trans_trans.
    rewrite eq_trans_sym_inv_r.
    rewrite eq_trans_refl_r.
    rewrite !eq_trans_refl_l.
    rewrite hom_trans_id.
    reflexivity.
  Qed.

  Record canon_iso {dsp} (ps : partial_solution dsp)
    (α : downset dsp) :=
    MkCanonIsoAt {
        canon_iso_at : isomorphic (C := FuncCat _ _)
                         (extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α)))
                         (cut_par_sol ps (le_dsp_included α));
        iso_pointwise_iso_id_forward :
        pointwise_id_right
          (lt_dsp α)
          dsp_included_lt_le
          (forward canon_iso_at)
          (λ β, extend_ord_ds_cat_func_o_map_lt _ (β := (dsp_include _ β))
                  (unsquash (ds_in_dsp β)));
        iso_pointwise_iso_id_backward :
        pointwise_id_left
          (lt_dsp α)
          dsp_included_lt_le
          (backward canon_iso_at)
          (λ β, extend_ord_ds_cat_func_o_map_lt _ (β := (dsp_include _ β))
                  (unsquash (ds_in_dsp β)));
      }.

  Definition canon {dsp} (ps : partial_solution dsp) := ∀ α, canon_iso ps α.

  Program Definition cut_equiv_cong {dsp dsp'} (ps ps' : partial_solution dsp)
    (H : dsp_included dsp' dsp)
    (Hequiv : functor_equiv ps ps')
    : functor_equiv (cut_par_sol ps H) (cut_par_sol ps' H)
    := MkFuncEq (λ a, (func_eq_o_map Hequiv (dsp_include H a))) _.
  Next Obligation.
    intros; simpl.
    rewrite func_eq_h_map.
    reflexivity.
  Qed.

  Program Definition cut_iso_cong {dsp dsp'} (ps ps' : partial_solution dsp)
    (H : dsp_included dsp' dsp)
    (Hiso : ps ≃@{FuncCat _ _} ps')
    : cut_par_sol ps H ≃@{FuncCat _ _} cut_par_sol ps' H
    := MkIsoIc
         (MkNat (λ c, forward Hiso ₙ (dsp_include H c)) _)
         (MkNat (λ c, backward Hiso ₙ (dsp_include H c)) _)
         _.
  Next Obligation.
    intros; simpl.
    pose proof (@naturality _ _ _ _ (forward Hiso)
                  (dsp_include H a)
                  (dsp_include H b)
                  f) as G.
    simpl in G.
    rewrite G.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    pose proof (@naturality _ _ _ _ (backward Hiso)
                  (dsp_include H a)
                  (dsp_include H b)
                  f) as G.
    simpl in G.
    rewrite G.
    reflexivity.
  Qed.
  Next Obligation.
    intros; simpl.
    split.
    - intros ?; simpl.
      pose proof (iso_lr (is_iso Hiso)
                    (dsp_include H a)) as G.
      simpl in G.
      rewrite G.
      reflexivity.
    - intros ?; simpl.
      pose proof (iso_rl (is_iso Hiso)
                    (dsp_include H a)) as G.
      simpl in G.
      rewrite G.
      reflexivity.
  Qed.

  Opaque cut_equiv_cong canon_iso_at
    extend_ord_ds_cat_nat_map
    functor_eq_natural_iso
    the_extension_eq_cones.

  Lemma extend_par_sol_lt_le_iso_bwd_pointwise''
    {dsp} (ps ps' : partial_solution dsp)
    (Hequiv : functor_equiv ps ps')
    (α : downset dsp)
    (Hequiv' : functor_equiv
                 (cut_par_sol ps (lt_dsp_included α))
                 (cut_par_sol ps' (lt_dsp_included α)))
    (eq1 : ∀ β : downset (lt_dsp α),
       extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
         dsp_include dsp_included_lt_le β =
         cut_par_sol ps (le_dsp_included α)ₒ dsp_include dsp_included_lt_le β)
    (eq2 : ∀ β : downset (lt_dsp α),
       extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
         dsp_include dsp_included_lt_le β =
         extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α))ₒ
           dsp_include dsp_included_lt_le β)
    : pointwise_id_right (lt_dsp α) dsp_included_lt_le
        (backward
           (extend_par_sol_lt_le_iso
              (functor_eq_natural_iso
                 Hequiv'))) eq2.
  Proof.
    intros ?.
    rewrite extend_par_sol_lt_le_iso_bwd_pointwise'.
    rewrite iso_backward_equiv.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    symmetry.
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    apply hom_trans_sym.
    rewrite -hom_trans_trans.
    rewrite eq_trans_refl_l.
    match goal with
    | |- context G [hom_trans _ ?a]
      => set (eq3 := a)
    end.
    clearbody eq3.
    assert (eq3 = car_eq (eq1 β)) as ->.
    { apply proof_irrelevance. }
    match goal with
    | |- context G [hom_trans ?a]
      => set (eq3 := a)
    end.
    clearbody eq3.
    assert (eq3 = eq_trans (car_eq (eq1 β)) (car_eq (func_eq_o_map Hequiv _))) as ->.
    { apply proof_irrelevance. }
    set (eq3 := (car_eq (eq1 β))).
    clearbody eq3.
    clear eq1 eq2.
    rewrite -{2}(eq_trans_refl_r eq3).
    rewrite hom_trans_trans.
    rewrite hom_trans_id.
    f_equiv.
    - apply proof_irrelevance.
    - reflexivity.
    - reflexivity.
  Qed.

  Lemma extend_par_sol_lt_le_iso_fwd_pointwise''
    {dsp} (ps ps' : partial_solution dsp)
    (Hequiv : functor_equiv ps ps')
    (α : downset dsp)
    (eq1 : ∀ β : downset (lt_dsp α),
       extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
         dsp_include dsp_included_lt_le β =
         cut_par_sol ps (le_dsp_included α)ₒ dsp_include dsp_included_lt_le β)
    (eq2 : ∀ β : downset (lt_dsp α),
       extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
         dsp_include dsp_included_lt_le β =
         extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α))ₒ
           dsp_include dsp_included_lt_le β)
    : pointwise_id_left (lt_dsp α) dsp_included_lt_le
        (forward
           (extend_par_sol_lt_le_iso
              (functor_eq_natural_iso
                 (cut_equiv_cong ps ps' (lt_dsp_included α) Hequiv)))) eq2.
  Proof.
    intros ?.
    rewrite extend_par_sol_lt_le_iso_fwd_pointwise'.
    rewrite iso_forward_equiv.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    symmetry.
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
    { intros []; reflexivity. }
    apply hom_trans_sym.
    rewrite -hom_trans_trans.
    rewrite eq_trans_refl_l.
    match goal with
    | |- context G [hom_trans ?a]
      => set (eq3 := a)
    end.
    clearbody eq3.
    assert (eq3 = car_eq (eq1 β)) as ->.
    { apply proof_irrelevance. }
    match goal with
    | |- context G [hom_trans _ ?a _]
      => set (eq3 := a)
    end.
    clearbody eq3.
    assert (eq3 = eq_trans (car_eq (eq1 β)) (car_eq (func_eq_o_map Hequiv _))) as ->.
    { apply proof_irrelevance. }
    set (eq3 := (car_eq (eq1 β))).
    clearbody eq3.
    clear eq1 eq2.
    rewrite -{1}(eq_trans_refl_r eq3).
    rewrite hom_trans_trans.
    rewrite hom_trans_id.
    reflexivity.
  Qed.

  Lemma canon_equiv {dsp} (ps ps' : partial_solution dsp)
    (Hequiv : functor_equiv ps ps') : canon ps → canon ps'.
  Proof.
    intros H α.
    unshelve econstructor.
    - refine (isomorphic_trans _
                (isomorphic_trans (canon_iso_at _ _ (H α))
                   (functor_eq_natural_iso (cut_equiv_cong _ _ _ Hequiv)))).
      apply isomorphic_sym.
      apply extend_par_sol_lt_le_iso.
      apply functor_eq_natural_iso.
      apply cut_equiv_cong.
      apply Hequiv.
    - unshelve eapply (pointwise_id_right_proper (lt_dsp α)
               dsp_included_lt_le
               _ _
               _
               _ _ (λ _, eq_refl)).
      2: {
        rewrite !iso_forward_trans.
        rewrite iso_forward_sym.
        rewrite functor_eq_natural_iso_trans_fwd.
        rewrite !comp_assoc.
        reflexivity.
      }
      assert (T : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol ps (le_dsp_included α)ₒ dsp_include dsp_included_lt_le β).
      {
        intros β.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        apply (eq_sym (func_eq_o_map Hequiv (dsp_include (lt_dsp_included _) β))).
      }
      apply pointwise_id_right_trans_r with T.
      assert (T' : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le β =
                  extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α))ₒ dsp_include
                    dsp_included_lt_le β).
      {
        intros; simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        apply (eq_sym (func_eq_o_map Hequiv (dsp_include (lt_dsp_included _) β))).
      }
      eapply pointwise_id_right_comp with T' _;
        last apply (iso_pointwise_iso_id_forward _ _ (H α)).
      apply extend_par_sol_lt_le_iso_bwd_pointwise''.
      { apply Hequiv. }
      { intros; apply T. }
    - unshelve eapply (pointwise_id_left_proper (lt_dsp α)
               dsp_included_lt_le
               _ _
               _
               _ _ (λ _, eq_refl)).
      2: {

        rewrite !iso_backward_trans.
        rewrite iso_backward_sym.
        rewrite functor_eq_natural_iso_trans_bwd.
        rewrite -!comp_assoc.
        reflexivity.
      }
      assert (T : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol ps (le_dsp_included α)ₒ dsp_include dsp_included_lt_le β).
      {
        intros β.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        apply (eq_sym (func_eq_o_map Hequiv (dsp_include (lt_dsp_included _) β))).
      }
      apply pointwise_id_left_trans_l with T.
      assert (T' : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol ps' (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le β =
                  extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α))ₒ dsp_include
                    dsp_included_lt_le β).
      {
        intros; simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        apply (eq_sym (func_eq_o_map Hequiv (dsp_include (lt_dsp_included _) β))).
      }
      eapply pointwise_id_left_comp with _ T';
        first apply (iso_pointwise_iso_id_backward _ _ (H α)).
      apply (extend_par_sol_lt_le_iso_fwd_pointwise'' ps ps' Hequiv
        α T T').
  Qed.

  Transparent cut_equiv_cong canon_iso_at
    extend_ord_ds_cat_nat_map
    functor_eq_natural_iso
    the_extension_eq_cones.

  (* Lemma canon_iso_fam_compat {dsp} (ps ps' : partial_solution dsp) *)
  (*   (H1 : ∀ α, canon_iso ps α) (H2 : ∀ α, canon_iso ps' α) : *)
  (*   compat_iso_fam ps ps'. *)

  Program Definition canon_ext_equiv {dsp dsp1 dsp2} (P : partial_solution dsp)
    (H : dsp_included dsp1 dsp2)
    (H1 : dsp_included dsp1 dsp)
    (H2 : dsp_included dsp2 dsp)
    :
    functor_equiv
      (cut_par_sol P H1)
      (cut_par_sol
         (cut_par_sol P H2) H)
    := MkFuncEq (λ a, eq_refl) _.
  Next Obligation.
    intros; simpl.
    rewrite hom_trans_refl.
    reflexivity.
  Qed.

  Program Definition canon_carrier_simp
    {dsp} (ps : partial_solution dsp)
    (α : downset dsp)
    (H : dsp_included (lt_dsp α) (le_dsp α))
    (H' : dsp_included (le_dsp α) (le_dsp α))
    (Hiso : isomorphic (C := FuncCat _ _)
              (extend_par_sol_lt_le (cut_par_sol (cut_par_sol ps (le_dsp_included α)) H))
              (cut_par_sol (cut_par_sol ps (le_dsp_included α)) H')) :
    isomorphic (C := FuncCat _ _)
      (extend_par_sol_lt_le (cut_par_sol ps (lt_dsp_included α)))
      (cut_par_sol ps (le_dsp_included α))
    := isomorphic_sym (isomorphic_trans (
                           isomorphic_trans
                             (functor_eq_natural_iso
                                ((canon_ext_equiv ps
                                    H'
                                    (le_dsp_included α)
                                    (le_dsp_included α))))
                             (isomorphic_sym Hiso))
                         (extend_par_sol_lt_le_iso
                            (functor_eq_natural_iso
                               (symmetry (canon_ext_equiv ps H
                                            (lt_dsp_included α)
                                            (le_dsp_included α)))))).

  Lemma canonicity_extend
    {dsp} (P : partial_solution dsp)
    (H : ∀ α, canon (cut_par_sol P (le_dsp_included α)))
    : canon P.
  Proof.
    intros α.
    apply (MkCanonIsoAt _ _ _ (canon_carrier_simp P α
                                 (lt_dsp_included (dsp_le_top α))
                                 (le_dsp_included (dsp_le_top α))
                                 (canon_iso_at _ _ (H α (dsp_le_top α))))).
    - unfold canon_carrier_simp.
      unshelve eapply (pointwise_id_right_proper (lt_dsp α)
                         dsp_included_lt_le
                         _ _
                         _
                         _ _ (λ _, eq_refl)).
      2: {
        rewrite iso_forward_sym.
        rewrite !iso_backward_trans.
        rewrite iso_backward_sym.
        rewrite iso_backward_equiv'.
        rewrite !comp_assoc.
        reflexivity.
      }
      assert (T : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol P (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le
                  β =
                  cut_par_sol (cut_par_sol P (le_dsp_included α))
                    (le_dsp_included (dsp_le_top α))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        reflexivity.
      }
      apply pointwise_id_right_trans_r with T.
      assert (T' : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol P (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le
                  β =
                  extend_par_sol_lt_le
                    (cut_par_sol (cut_par_sol P (le_dsp_included α))
                       (lt_dsp_included (dsp_le_top α)))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        simpl.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        reflexivity.
      }
      eapply pointwise_id_right_comp with T' _;
        last apply (iso_pointwise_iso_id_forward _ _ (H α (dsp_le_top α))).
      intros ?.
      rewrite extend_par_sol_lt_le_iso_bwd_pointwise'.
      symmetry.
      rewrite iso_backward_equiv.
      apply alg_hom_map_eq.
      rewrite !hom_trans_alg_hom_map /=.
      assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
      { intros []; reflexivity. }
      assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
      { intros []; reflexivity. }
      apply hom_trans_sym.
      rewrite -hom_trans_trans.
      rewrite eq_trans_refl_l.
      match goal with
      | |- context G [hom_trans ?a]
        => set (Q := a)
      end.
      match goal with
      | |- context G [eq_trans _ ?a]
        => set (Q' := a)
      end.
      assert (Q = (eq_trans (car_eq (T' β)) Q')) as ->.
      { apply proof_irrelevance. }
      rewrite hom_trans_trans.
      rewrite !hom_trans_id.
      clear Q'.
      match goal with
      | |- context G [hom_trans ?a]
        => set (Q := a)
      end.
      assert (Q = eq_refl) as ->.
      { apply proof_irrelevance. }
      rewrite hom_trans_refl.
      reflexivity.
    - unfold canon_carrier_simp.
      unshelve eapply (pointwise_id_left_proper (lt_dsp α)
                         dsp_included_lt_le
                         _ _
                         _
                         _ _ (λ _, eq_refl)).
      2: {
        rewrite iso_backward_sym.
        rewrite !iso_forward_trans.
        rewrite -!comp_assoc.
        match goal with
        | |- context G [forward (functor_eq_natural_iso ?a)]
          => assert (a = symmetry
                          (symmetry a)) as ->
        end.
        { apply proof_irrelevance. }
        rewrite -iso_backward_equiv'.
        rewrite functor_eq_natural_iso_trans_bwd.
        rewrite iso_forward_sym.
        reflexivity.
      }
      assert (T' : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol P
                                        (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le
                  β =
                  cut_par_sol (cut_par_sol P (le_dsp_included α))
                    (le_dsp_included (dsp_le_top α))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        unfold cut_ord_ds_cat_func_o_map; simpl.
        reflexivity.
      }
      apply pointwise_id_left_trans_l with T'.
      assert (T'' : ∀ β : downset (lt_dsp α),
                extend_par_sol_lt_le (cut_par_sol P (lt_dsp_included α))ₒ
                  dsp_include dsp_included_lt_le
                  β =
                  extend_par_sol_lt_le
                    (cut_par_sol (cut_par_sol P (le_dsp_included α))
                       (lt_dsp_included (dsp_le_top α)))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        reflexivity.
      }
      eapply pointwise_id_left_comp with _ T'';
        first apply (iso_pointwise_iso_id_backward _ _ (H α (dsp_le_top α))).
      intros ?.
      rewrite extend_par_sol_lt_le_iso_fwd_pointwise'.
      symmetry.
      rewrite iso_forward_equiv.
      apply alg_hom_map_eq.
      rewrite !hom_trans_alg_hom_map /=.
      assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
      { intros []; reflexivity. }
      assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
      { intros []; reflexivity. }
      apply hom_trans_sym.
      rewrite -hom_trans_trans.
      rewrite eq_trans_refl_l.
      match goal with
      | |- context G [hom_trans _ ?a]
        => set (Q := a)
      end.
      match goal with
      | |- context G [eq_trans _ ?a]
        => set (Q' := a)
      end.
      assert (Q = (eq_trans (car_eq (T'' β)) Q')) as ->.
      { apply proof_irrelevance. }
      rewrite hom_trans_trans.
      rewrite !hom_trans_id.
      clear Q'.
      match goal with
      | |- context G [hom_trans _ ?a]
        => set (Q := a)
      end.
      assert (Q = eq_refl) as ->.
      { apply proof_irrelevance. }
      rewrite hom_trans_refl.
      reflexivity.
  Qed.

  Lemma canon_ind_cut_sol_eq {dsp : downset_pred SI}
    (P : partial_solution dsp)
    {α : SI}
    (α' : downset (lt_dsp α))
    (T : dsp_included (lt_dsp α) dsp)
    (T' : dsp_included (le_dsp α') dsp)
    :
    (cut_par_sol (cut_par_sol P T) (lt_dsp_included α'))
    = (cut_par_sol (cut_par_sol P T') (lt_dsp_included (dsp_le_top α'))) :> functor _ _.
  Proof.
    apply FunctorEqUnpack.
    unshelve econstructor.
    - intros; simpl.
      unfold cut_ord_ds_cat_func_o_map.
      reflexivity.
    - intros; simpl.
      rewrite hom_trans_refl.
      reflexivity.
  Qed.

  Lemma canon_ind_cut_sol_equiv {dsp : downset_pred SI}
  (P : partial_solution dsp)
  {α : SI}
  (α' : downset (lt_dsp α))
  (T : dsp_included (lt_dsp α) dsp)
  (T' : dsp_included (le_dsp α') dsp)
    : functor_equiv
        (cut_par_sol (cut_par_sol P T) (le_dsp_included α'))
        (cut_par_sol (cut_par_sol P T') (le_dsp_included (dsp_le_top α'))).
  Proof.
    unshelve econstructor.
    - intros; simpl.
      simpl in *.
      unfold cut_ord_ds_cat_func_o_map.
      reflexivity.
    - intros; simpl.
      rewrite hom_trans_refl.
      reflexivity.
  Qed.

  Lemma canon_ind_ext_sol_equiv {dsp : downset_pred SI}
    (P : partial_solution dsp)
    {α : SI}
    (α' : downset (lt_dsp α))
    (T : dsp_included (lt_dsp α) dsp)
    (T' : dsp_included (le_dsp α') dsp)
    : functor_equiv (extend_par_sol_lt_le
                       (cut_par_sol (cut_par_sol P T')
                          (lt_dsp_included (dsp_le_top α'))))
        (extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T) (lt_dsp_included α'))).
  Proof.
    simpl.
    epose proof (canon_ind_cut_sol_eq P α' T T') as J.
    simpl in J.
    rewrite J.
    reflexivity.
  Qed.

  Lemma pointwise_id_right_equiv {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (Heq : ∀ (β : downset dsp'),
       ps ₒ (dsp_include H β) = ps' ₒ (dsp_include H β))
    (η : functor_equiv ps ps')
    : pointwise_id_right dsp' H
        ((functor_eq_natural η : hom (C := FuncCat _ _) _ _))
       Heq.
  Proof.
    intros β.
    simpl.
    f_equiv.
    apply proof_irrelevance.
  Qed.

  Lemma pointwise_id_left_equiv {dsp}
    {ps : partial_solution dsp}
    {ps' : partial_solution dsp}
    dsp'
    (H : dsp_included dsp' dsp)
    (Heq : ∀ (β : downset dsp'),
       ps' ₒ (dsp_include H β) = ps ₒ (dsp_include H β))
    (η : functor_equiv ps ps')
    : pointwise_id_left dsp' H
        ((functor_eq_natural η : hom (C := FuncCat _ _) _ _))
       Heq.
  Proof.
    intros β.
    simpl.
    apply alg_hom_map_eq; simpl.
    rewrite !hom_trans_alg_hom_map /=.
    match goal with
    | |- context G [hom_trans _ ?a _]
      => assert (a = eq_trans (car_eq (Heq β)) (eq_sym (car_eq (Heq β)))) as ->
    end; first by rewrite eq_trans_sym_inv_r.
    match goal with
    | |- context G [hom_trans ?a _ _]
      => assert (a = eq_trans (car_eq (Heq β)) eq_refl) as ->
    end; first by rewrite eq_trans_refl_r.
    rewrite hom_trans_trans.
    f_equiv.
    - apply proof_irrelevance.
    - rewrite eq_trans_refl_r.
      rewrite hom_trans_id.
      reflexivity.
  Qed.

  Lemma canon_ind_iso {dsp : downset_pred SI}
  {P : partial_solution dsp}
  {α : SI}
  (α' : downset (lt_dsp α))
  (T : dsp_included (lt_dsp α) dsp)
  (T' : dsp_included (le_dsp α') dsp)
  (IHβ : canon_iso (cut_par_sol P T') (dsp_le_top α'))
    : canon_iso (cut_par_sol P T) α'.
  Proof.
    unshelve econstructor.
    - apply (isomorphic_trans
               (isomorphic_trans
                  (functor_eq_natural_iso
                     (symmetry (canon_ind_ext_sol_equiv P α' T T')))
                  (canon_iso_at _ _ IHβ))
               (functor_eq_natural_iso
                  (symmetry (canon_ind_cut_sol_equiv P α' T T')))).
    - unshelve eapply (pointwise_id_right_proper (lt_dsp α')
                         dsp_included_lt_le
                         _ _
                         _
                         _ _ (λ _, eq_refl)).
      2: {
        rewrite !iso_forward_trans.
        reflexivity.
      }
      assert (Q : ∀ β : downset (lt_dsp α'),
                extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T)
                                        (lt_dsp_included α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol (cut_par_sol P T')
                    (le_dsp_included (dsp_le_top α'))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        reflexivity.
      }
      assert (Q' : ∀ β : downset (lt_dsp α'),
                cut_par_sol (cut_par_sol P T')
                  (le_dsp_included (dsp_le_top α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol (cut_par_sol P T) (le_dsp_included α')ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        reflexivity.
      }
      eapply pointwise_id_right_comp with Q Q';
        last apply pointwise_id_right_equiv.
      assert (Q'' : ∀ β : downset (lt_dsp α'),
                extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T)
                                        (lt_dsp_included α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T')
                                          (lt_dsp_included (dsp_le_top α')))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        reflexivity.
      }
      eapply pointwise_id_right_comp with Q'' _;
        first apply pointwise_id_right_equiv.
      apply (iso_pointwise_iso_id_forward _ _ IHβ).
    - unshelve eapply (pointwise_id_left_proper (lt_dsp α')
                         dsp_included_lt_le
                         _ _
                         _
                         _ _ (λ _, eq_refl)).
      2: {
        rewrite !iso_backward_trans.
        rewrite !iso_backward_equiv'.
        reflexivity.
      }
      assert (Q : ∀ β : downset (lt_dsp α'),
                extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T)
                                        (lt_dsp_included α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol (cut_par_sol P T')
                    (le_dsp_included (dsp_le_top α'))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        reflexivity.
      }
      assert (Q' : ∀ β : downset (lt_dsp α'),
                cut_par_sol (cut_par_sol P T')
                  (le_dsp_included (dsp_le_top α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  cut_par_sol (cut_par_sol P T) (le_dsp_included α')ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        reflexivity.
      }
      apply pointwise_id_left_comp with Q' Q;
        first apply pointwise_id_left_equiv.
      assert (Q'' : ∀ β : downset (lt_dsp α'),
                extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T)
                                        (lt_dsp_included α'))ₒ
                  dsp_include dsp_included_lt_le β =
                  extend_par_sol_lt_le (cut_par_sol (cut_par_sol P T')
                                          (lt_dsp_included (dsp_le_top α')))ₒ
                    dsp_include dsp_included_lt_le β).
      {
        intros; simpl.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        { apply (unsquash (ds_in_dsp β)). }
        intros.
        rewrite extend_ord_ds_cat_func_o_map_lt.
        reflexivity.
      }
      eapply pointwise_id_left_comp with _ Q'';
        last apply pointwise_id_left_equiv.
      apply (iso_pointwise_iso_id_backward _ _ IHβ).
  Qed.

  Lemma canonicity_inductive {dsp} (P : partial_solution dsp) :
    (∀ α, canon (cut_par_sol P (lt_dsp_included α))
          → canon (cut_par_sol P (le_dsp_included α)))
    → canon P.
  Proof.
    intros H.
    apply canonicity_extend.
    intros α.
    destruct α as [α G].
    revert G.
    induction (index_lt_wf _ α) as [α _ IHα]; intros G.
    apply H; clear H.
    set (β := MkDS _ G).
    intros α'.
    pose proof (IHα α' (unsquash (ds_in_dsp α'))
                  (squash (dsp_included_trans
                             (le_dsp_included α')
                             (lt_dsp_included β) α'
                             (reflexivity _)))
                  (dsp_le_top α')) as IHβ.
    revert IHβ.
    match goal with
    | |- context G [cut_par_sol P ?a]  => set (T := a)
    end.
    simpl in T.
    assert (T' : dsp_included (le_dsp α') dsp).
    {
      apply T.
    }
    assert (T = T') as ->; first by apply proof_irrelevance.
    intros IHβ.
    assert (T : dsp_included (lt_dsp β) dsp).
    { apply (lt_dsp_included β). }
    assert (lt_dsp_included β = T) as ->; first by apply proof_irrelevance.
    subst β.
    simpl in *.
    clear G.
    clear IHα.
    eapply canon_ind_iso; apply IHβ.
  Qed.

  Record good_fam dsp :=
    {
      collection : ∀ (α : downset dsp), partial_solution (le_dsp α);
      canon_fam : ∀ (α : downset dsp), canon (collection α);
      coh : ∀ (α : downset dsp) (α' : downset (lt_dsp α)),
        (collection α) ₒ (dsp_include dsp_included_lt_le α')
          ≃@{Alg F} (alg_func_func F ₒ
                       (alg_lim_alg
                          (cut_par_sol
                             (collection
                                (dsp_include
                                   (lt_dsp_included _) α'))
                             dsp_included_lt_le)));
    }.

  Program Definition tower {dsp} (M : good_fam dsp)
    : functor (OrdDSCat dsp)ᵒᵖ (Alg F)
    := MkFunc (λ x, (collection _ M x ₒ (dsp_le_top x)))
      (λ a b f, _) _ _ _.
  Next Obligation.
    intros; simpl in f.
    Opaque hom.
    destruct (index_le_lt_eq_dec _ _ f) as [H | H].
    - set (b' := MkDS (le_dsp a) (squash f)).
      apply (comp _ (@h_map _ _ (collection _ M a) (dsp_le_top a) b' f)).
      refine (comp _ (backward (canon_iso_at _ _
                                  (canon_fam _ M a (dsp_le_top a))) ₙ
                        b') _).
      refine (comp _ _ (forward (canon_iso_at _ _
                                   (canon_fam _ M b (dsp_le_top b))) ₙ
                          (dsp_le_top b))).

      rewrite /= extend_ord_ds_cat_func_o_map_lt /=.
      rewrite extend_ord_ds_cat_func_o_map_at /=; last reflexivity.
      rewrite /cut_ord_ds_cat_func_o_map /=.

      refine (hom_trans eq_refl _ (forward (coh _ M a (MkDS (lt_dsp a) (squash H))))).
      apply (o_map_eq (alg_func_func _)); simpl.
      apply f_equal.
      f_equal.
      apply proof_irrelevance.
    - simpl in *.
      assert (b = a) as ->.
      { destruct a, b; simpl in *; destruct H; reflexivity. }
      apply id.
  Defined.
  Next Obligation.
    Transparent hom.
    intros; simpl.
    intros ???.
    assert (x = y) as -> by apply proof_irrelevance.
    f_equal.
  Qed.
  Next Obligation.
    intros; simpl.
    unfold tower_obligation_1.
    simpl in *.

  Admitted.
  Next Obligation.
    intros; simpl.
    unfold tower_obligation_1.
    destruct index_le_lt_eq_dec as [H | H].
    - exfalso.
      admit.
    - assert (H = eq_refl) as ->.
      { apply proof_irrelevance. }
      unfold eq_rect_r.
      simpl.
      reflexivity.
  Admitted.

  Program Definition PPP {dsp} (M : good_fam dsp)
    : partial_solution dsp
    := MkParSol (tower _) _ _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.

  Definition TTT : ∀ (β : SI) (H : ∀ y : SI, y ≺ β → good_fam (le_dsp y)),
    good_fam (lt_dsp β).
  Proof.
  Admitted.

  Program Definition ind_step : ∀ β, good_fam (le_dsp β).
  Proof.
    intros β.
    induction (index_lt_wf _ β) as [β _ IHβ].
    apply TTT in IHβ.
    unshelve econstructor.
    - intros.
      apply extend_par_sol_lt_le.
      apply PPP.
      admit.
    - intros; simpl.
      admit.
    - Opaque cut_par_sol extend_par_sol_lt_le.
      intros; simpl.
      match goal with
      | |- context G [cut_par_sol ?a]
        => set (T := a)
      end.
      Transparent extend_par_sol_lt_le.
      simpl.
      rewrite extend_ord_ds_cat_func_o_map_lt.
      { apply (unsquash (ds_in_dsp α')). }
      intros; unfold tower at 1; simpl.
      subst T.
      match goal with
      | |- context G [extend_par_sol_lt_le ?a]
        => set (T := a)
      end.
      pose proof (extend_par_sol_lt_le_equiv_lt T dsp_included_lt_le).
      assert ((cut_par_sol (extend_par_sol_lt_le T) dsp_included_lt_le)
              = T) as ->.
      { admit. }
      clear H.
      subst T.
      epose proof (coh _ IHβ).
      destruct (index_le_lt_eq_dec _ _ (unsquash (ds_in_dsp α))) as [H | H];
        last first.
      + admit.
      + simpl.
        epose proof (X _ (* α *) _ (* α' *)).
  Abort.

  Program Definition patch_functor {dsp : downset_pred SI}
    (collection : ∀ α : downset dsp, partial_solution (le_dsp α))
    (canon_fam : ∀ α : downset dsp, canon (collection α))
    : functor (OrdDSCat dsp)ᵒᵖ (Alg F) :=
    MkFunc (λ x, (collection x ₒ (dsp_le_top x)))
      (λ a b f, _) _ _ _.
  Next Obligation.
    intros; simpl in *.
    set (b' := MkDS (le_dsp a) (squash f)).
    apply (comp _ (@h_map _ _ (collection a) (dsp_le_top a) b' f)).
    refine (comp _ (backward (canon_iso_at _ _
                                (canon_fam a (dsp_le_top a))) ₙ
                      b') _).
    refine (comp _ _ (forward (canon_iso_at _ _
                                 (canon_fam b (dsp_le_top b))) ₙ
                        (dsp_le_top b))).
    (* TODO: Ext(G|<a) ₒ b = F(lim (G|<b)) for b < a *)
    simpl.
    rewrite extend_ord_ds_cat_func_o_map_lt.
    { admit. }
    intros.
    simpl.
    unshelve rewrite extend_ord_ds_cat_func_o_map_at.
    2: {
      unfold dsp_le_top.
      simpl.
      reflexivity.
    }
    simpl.
    unfold cut_ord_ds_cat_func_o_map; simpl.
    unshelve econstructor.
    - simpl.
      unfold alg_lim_obj.
      simpl.

    (* set (cut_par_sol (collection a) (lt_dsp_included (dsp_le_top a))). *)
    (* set (cut_par_sol (collection b) (lt_dsp_included (dsp_le_top b))). *)
    (* simpl in p. *)
    (* (* epose proof (extend_par_sol_lt_le). *) *)
    unshelve epose proof (forward (@extend_par_sol_lt_le_iso _
                            (cut_par_sol (collection a) (lt_dsp_included (dsp_le_top a)))
                            _ _) ₙ b').
    {
      simpl.
      eapply (cut_par_sol (collection a) (lt_dsp_included (dsp_le_top a))).
      (* admit. *)
    }
    {
      simpl.
      apply isomorphic_refl.
      (* admit. *)
    }
    unshelve eapply (hom_trans eq_refl _ X).
    {
      simpl.
      rewrite extend_ord_ds_cat_func_o_map_lt.
      {
        subst b'.
        simpl.
        admit.
      }
      intros J1.
      simpl.
      unshelve rewrite extend_ord_ds_cat_func_o_map_at.
      2: {
        unfold dsp_le_top.
        simpl.
        reflexivity.
      }
      simpl.
      unfold cut_ord_ds_cat_func_o_map.
      simpl.
      subst b'.
      simpl in *.
    }
    admit.
  Admitted.
  Next Obligation.
    intros; simpl.
    intros ???.
    assert (x = y) as -> by apply proof_irrelevance.
    f_equal.
  Qed.
  Next Obligation.
    intros; simpl.
    admit.
  Admitted.
  Next Obligation.
    intro; simpl.
    intros a.

    admit.
  Admitted.

  Lemma patch_partial_sol {dsp : downset_pred SI}
    (collection : ∀ α, dsp α → partial_solution (le_dsp α))
    (canon_fam : ∀ α (H : dsp α), canon (collection α H))
    : partial_solution dsp.
  Proof.
  Admitted.

  Lemma functor_collection
    : ∀ α, { sol : partial_solution (le_dsp α) & canon sol }.
  Proof.
    intros α.
    induction (index_lt_wf _ α) as [α _ IHα].
    unshelve econstructor.
    - unshelve epose proof (parsolext_cone (the_extension _)).
      + apply (lt_dsp α).
      + unshelve econstructor.
        * unshelve econstructor.
          -- intros; simpl in *.
             eapply (projT1 (IHα X (unsquash (ds_in_dsp X))) ₒ (MkDS (le_dsp X) (squash _))).
          -- intros; simpl.
  Admitted.

  Theorem solver : solution F.
  Proof using Complete0 Enriched0 LimitsEnriched0 LocallyContractiveFunctor0.
    apply total_partial_sol_sol.
    unshelve eapply patch_partial_sol.
    - intros α _; simpl.
      apply (projT1 (functor_collection α)).
    - intros α ?; simpl.
      apply (projT2 (functor_collection α)).
  Qed.
  (*   apply (patch_partial_sol functor_collection functor_collection_canon). *)
  (* Qed. *)

  (* Program Definition partial_solution_set_gen (ind : ∀ β, partial_solution_set (le_dsp β)) : *)
  (*   partial_solution_set (total_dsp SI) (* := MkParSolSet _ _ _ _ _ _ *). *)
  (* Proof. *)
  (*   intros. *)
  (*   unshelve econstructor. *)
  (*   - intros. *)
  (*     unshelve econstructor. *)
  (*     + unshelve econstructor. *)
  (*       * intros; simpl. *)
  (*         apply (parsolset (ind X) (@MkDS SI (le_dsp X) X (reflexivity _)) ₒ *)
  (*                  (@MkDS SI (le_dsp X) X (reflexivity _))). *)
  (*       * intros; simpl. *)
  (*         pose proof (naturality (@parsolset_proj _ (ind a) (@MkDS SI (le_dsp a) a (reflexivity _)) *)
  (*                       (@MkDS SI (le_dsp a) b X) X)).           *)
  (*         simpl in H. *)

  (*         simpl in X. *)

  (*             parsolset_proj_fold : ∀ (α β : downset dsp) (Hle : β ⪯ α), *)
  (*     par_sol_fold (parsolset β) ∘ (F ₕ (parsolset_proj _ _ Hle)) ≡ *)
  (*     (parsolset_proj _ _ Hle) ∘ par_sol_fold (parsolset α); *)
  (*   parsolset_fold_iso : ∀ (α : downset dsp), *)
  (*     is_iso_at (par_sol_fold (parsolset α)) α; *)

  (*         pose proof (parsolset (X a) (@MkDS SI (le_dsp a) a (reflexivity _)) ₕ). *)
  (*         simpl in X1. *)
  (*   Search total_dsp. *)
  (* Admitted. *)

  (* Lemma construct2 : ∀ β, partial_solution_set (le_dsp β). *)
  (* Proof. *)
  (*   intros β. *)
  (*   induction (index_lt_wf _ β) as [β _ IHβ]. *)
  (*   unshelve econstructor. *)
  (*   - intros. *)
  (*     apply extend_par_sol_lt_le. *)
  (*     unshelve econstructor. *)
  (*     + unshelve econstructor. *)
  (*       * intros x. *)
  (*         simpl in *. *)
  (*         apply (parsolset (IHβ (ds_idx x) (ds_in_dsp x)) (@MkDS SI (le_dsp x) x (reflexivity _)) ₒ (@MkDS SI (le_dsp x) x (reflexivity _))). *)
  (*       * intros; simpl. *)
  (*         simpl in X. *)
  (*         (* epose proof (naturality ((@parsolset_proj _ (IHβ (ds_idx a) (ds_in_dsp a)) *) *)
  (*         (*                         (@MkDS SI (le_dsp a) a (reflexivity _)) *) *)
  (*         (*                         (@MkDS SI (le_dsp a) b X) X))). *) *)
  (*         (* simpl in H. *) *)
  (*         unshelve epose proof (@parsolset_proj _ (IHβ (ds_idx a) (ds_in_dsp a)) *)
  (*                                 (@MkDS SI (le_dsp a) a (reflexivity _)) *)
  (*                                 (@MkDS SI (le_dsp a) b X) X ₙ (@MkDS SI (le_dsp a) a (reflexivity _))). *)
  (*         simpl in *. *)
  (*         apply (alg_hom_comp X0). *)

  (*         simpl in X. *)
  (*         -- econstructor. *)
  (*            simpl. *)
  (*         destruct X. *)

  Lemma construct3 : partial_solution (total_dsp SI) → solution F.
  Proof.
    intros.
    apply (alg_cons_is_iso_upto_total_solution (A := (vertex (term (complete (unlift_func X)))))).
    intros β.
    simpl.
    epose proof (cone_hom_map (bang (term_is_terminal (complete (functor_compose (unlift_func X) (forgetful F))))
          (alg_lim_cone_for_cons (unlift_func X)))).
    simpl in X0.
    epose proof (parsol_cons_iso X β).

    epose proof limit_side_iso_at.
    simpl in X0.
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
