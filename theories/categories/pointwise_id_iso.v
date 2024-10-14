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
