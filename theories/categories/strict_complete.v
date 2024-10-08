From SynthDom Require Import prelude.
From SynthDom.categories Require Import category uip.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Class StrictComplete D `{!Complete D}
  := MkStrictComplete {
         strict_complete
         : ∀ J
             (I I' : functor J D)
             (eq : functor_equiv I I'),
           cones_equiv eq (term (complete I)) (term (complete I'));
       }.

Program Definition setoid_vert_eq_obj_packed {J : category}
  {I_obj I'_obj : obj J → setoid}
  {I_arr : ∀ a b : obj J, hom a b → setoid_fun (I_obj a) (I_obj b)}
  {I'_arr : ∀ a b : obj J, hom a b → setoid_fun (I'_obj a) (I'_obj b)}
  (equiv_obj : ∀ x, I_obj x = I'_obj x)
  (equiv_arr : ∀ a b (f : hom a b),
     hom_trans (equiv_obj a : @eq (obj Setoid) _ _) (equiv_obj b) (I_arr _ _ f)
       ≡ I'_arr _ _ f)
  : SigmaEq (λ (p : ∀ j : obj J, I_obj j),
        ∀ (j j' : obj J) (f : hom j j'), (I_arr _ _ f) (p j) ≡ p j')
      (λ (p : ∀ j : obj J, I'_obj j),
        ∀ (j j' : obj J) (f : hom j j'), (I'_arr _ _ f) (p j) ≡ p j')
  := MkSigmaEq
       (forall_extensionality
          (λ x, f_equal setoid_set (equiv_obj x)))
       _.
Next Obligation.
  intros J I_obj I'_obj I_arr I'_arr equiv_obj equiv_arr b; simpl.
  split; intros.
  - assert (I_obj = I'_obj) as Hf.
    {
      apply functional_extensionality.
      apply equiv_obj.
    }
    destruct Hf.
    assert (equiv_obj = λ _, eq_refl) as ->.
    { apply proof_irrelevance. }
    simpl.
    assert ((forall_extensionality (λ x : obj J, eq_refl))
            = eq_refl) as ->.
    { apply proof_irrelevance. }
    simpl.
    rewrite -(H j j' f).
    symmetry.
    by apply equiv_arr.
  - specialize (H j j' f).
    assert (I_obj = I'_obj) as Hf.
    {
      apply functional_extensionality.
      apply equiv_obj.
    }
    destruct Hf.
    assert (equiv_obj = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    rewrite Hf in H, equiv_arr; clear Hf.
    simpl in H.
    eassert ((forall_extensionality (C := λ j : obj J, I_obj j) (λ x : obj J, eq_refl))
             = eq_refl) as Hf.
    { apply proof_irrelevance. }
    Unshelve.
    rewrite Hf in H; clear Hf.
    simpl in H.
    rewrite -H.
    apply equiv_arr.
    reflexivity.
Qed.

Program Definition setoid_vert_eq_obj {J : category}
  {I_obj I'_obj : obj J → setoid}
  {I_arr : ∀ a b : obj J, hom a b → setoid_fun (I_obj a) (I_obj b)}
  {I'_arr : ∀ a b : obj J, hom a b → setoid_fun (I'_obj a) (I'_obj b)}
  (equiv_obj : ∀ x, I_obj x = I'_obj x)
  (equiv_arr : ∀ a b (f : hom a b),
     hom_trans (equiv_obj a : @eq (obj Setoid) _ _) (equiv_obj b) (I_arr _ _ f)
       ≡ I'_arr _ _ f)
  :
  {p : ∀ j : obj J, I_obj j
  | ∀ (j j' : obj J) (f : hom j j'), (I_arr _ _ f) (p j) ≡ p j'}
  = {p : ∀ j : obj J, I'_obj j
    | ∀ (j j' : obj J) (f : hom j j'), (I'_arr _ _ f) (p j) ≡ p j'}
  := SigmaEqUnpack (setoid_vert_eq_obj_packed equiv_obj equiv_arr).

Program Definition setoid_vert_eq_packed {J : category}
  {I I' : functor J Setoid}
  (equiv_obj : ∀ x, I ₒ x = I' ₒ x)
  (equiv_arr : ∀ a b (f : hom a b),
     hom_trans (equiv_obj a) (equiv_obj b) (I ₕ f) ≡ I' ₕ f)
  :
  SetoidEq (vertex (term (complete I))) (vertex (term (complete I')))
  := MkSetoidEq (setoid_vert_eq_obj equiv_obj equiv_arr) _.
Next Obligation.
  intros J I I' equiv_obj equiv_arr x y; simpl.
  rewrite /sig_eq.
  pose proof (setoid_vert_eq_obj_packed equiv_obj equiv_arr) as K.
  destruct I as [I_obj I_arr T1 T2 T3];
    destruct I' as [I'_obj I'_arr R1 R2 R3];
    simpl in *.
  clear T1 T2 T3.
  clear R1 R2 R3.
  assert (I_obj = I'_obj) as Hf.
  {
    apply functional_extensionality.
    apply equiv_obj.
  }
  destruct Hf.
  assert (equiv_obj = λ _, eq_refl) as Hf.
  { apply proof_irrelevance. }
  subst equiv_obj.
  rewrite (SigmaEqCanon _ _ K (setoid_vert_eq_obj (λ x0 : obj J, eq_refl) equiv_arr)).
  rewrite (SigmaEqTransportProj1 K x) (SigmaEqTransportProj1 K y).
  assert ((sigma_proj1_eq K) = eq_refl) as ->.
  { apply proof_irrelevance. }
  reflexivity.
Qed.

Program Definition setoid_vert_eq {J : category}
  {I I' : functor J Setoid}
  (equiv_obj : ∀ x, I ₒ x = I' ₒ x)
  (equiv_arr : ∀ a b (f : hom a b),
     hom_trans (equiv_obj a) (equiv_obj b) (I ₕ f) ≡ I' ₕ f)
  :
  (vertex (term (complete I))) = (vertex (term (complete I')))
  := SetoidEqUnpack (setoid_vert_eq_packed equiv_obj equiv_arr).

Lemma SetoidMapPI {A B : setoid}
  (f g : setoid_fun A B) :
  (setoid_fun_map A B f = setoid_fun_map A B g)
  → f = g :> setoid_fun A B.
Proof.
  intros Hf.
  destruct f as [f1 f2]; destruct g as [g1 g2]; simpl in *.
  destruct Hf.
  assert (f2 = g2) as -> by apply proof_irrelevance.
  reflexivity.
Qed.

Instance SetoidStrictComplete : StrictComplete Setoid.
Proof.
  constructor.
  intros J I I' equiv.
  destruct equiv as [oe he].
  apply (MkConesEq (setoid_vert_eq oe he)).
  intros j; simpl.
  rewrite /setoid_lim_side.
  intros x y Hxy; simpl.
  rewrite -Hxy; clear Hxy y.
  destruct I as [I_obj I_arr T1 T2 T3];
    destruct I' as [I'_obj I'_arr R1 R2 R3];
    simpl in *.
  assert (I_obj = I'_obj) as Hf.
  { apply functional_extensionality, oe. }
  destruct Hf.
  assert (oe = λ _, eq_refl) as Hf.
  { apply proof_irrelevance. }
  subst oe.
  rewrite hom_trans_setoid_conv.
  rewrite hom_trans_refl /=.
  unfold hom_trans in he.
  unfold setoid_vert_eq.
  rewrite SetoidEqUnpackSymm.
  rewrite SetoidEqSetoidConv.
  match goal with
  | |- context G [castT ?a] =>
      set (S := a)
  end.
  simpl in S.
  rewrite (SigmaEqCanon _ _ (SigmaEqSymm (setoid_vert_eq_obj_packed (λ _, eq_refl) he)) S).
  rewrite SigmaEqTransportProj1.
  assert ((sigma_proj1_eq
             (SigmaEqSymm
                (setoid_vert_eq_obj_packed (λ x0 : obj J, eq_refl) he))) = eq_refl) as Hf.
  { apply proof_irrelevance. }
  rewrite Hf; clear Hf.
  reflexivity.
Qed.

Lemma pointwise_func_equiv_lift {C} `{!Complete C} `{!StrictComplete C}
  {J : category}
  {I I' : functor J (PSh C)}
  (eq : functor_equiv I I')
  x
  : functor_equiv (pointwise_func I x) (pointwise_func I' x).
Proof.
  destruct eq as [oe he]; simpl.
  destruct I as [om am H1 H2 H3];
    destruct I' as [om' am' G1 G2 G3].
  simpl in *.
  assert (om = om') as Hf.
  {
    apply functional_extensionality.
    intros; apply oe.
  }
  destruct Hf.
  assert (oe = λ _, eq_refl) as Hf.
  { apply proof_irrelevance. }
  subst oe; simpl.
  unshelve eapply MkFuncEq.
  - intros; simpl.
    reflexivity.
  - intros; simpl.
    rewrite hom_trans_refl.
    apply he.
Defined.

Program Definition pointwise_func_equiv_cones {C} `{!Complete C} `{!StrictComplete C}
  (J : category)
  (I I' : functor J (PSh C))
  (eq : functor_equiv I I')
  : ∀ x, cones_equiv (pointwise_func_equiv_lift eq x)
           (term (complete (pointwise_func I x)))
           (term (complete (pointwise_func I' x)))
  := λ x, strict_complete _ _ _ (pointwise_func_equiv_lift eq x).

Lemma pointwise_o_map {J C}
  (I I' : J → obj (PSh C))
  (eq : ∀ x, I x = I' x)
  : ∀ r x, ((I r) ₒ x) = ((I' r) ₒ x).
Proof.
  intros r x.
  rewrite (eq r).
  reflexivity.
Qed.

Lemma pointwise_o_map_lift_refl {J C}
  (I : J → obj (PSh C))
  : pointwise_o_map I I (λ _, eq_refl) = λ r x, eq_refl.
Proof.
  apply proof_irrelevance.
Qed.

Lemma pointwise_h_map {J C}
  (F G : functor J (PSh C))
  (eq : functor_equiv F G)
  (r : obj J)
  {x y : obj (C ᵒᵖ)} (f : hom x y)
  : ((G ₒ r) ₕ f)
    = hom_trans
        (pointwise_o_map _ _ (func_eq_o_map eq) r x)
        (pointwise_o_map _ _ (func_eq_o_map eq) r y)
        ((F ₒ r) ₕ f).
Proof.
  simpl.
  destruct F as [F1 F2 F3 F4 F5];
    destruct G as [G1 G2 G3 G4 G5];
    destruct eq as [eq1 eq2];
    simpl in *.
  assert (F1 = G1) as Hf.
  { apply functional_extensionality; intros ?; apply eq1. }
  destruct Hf.
  assert (eq1 = λ _, eq_refl) as Hf.
  { apply proof_irrelevance. }
  subst eq1.
  rewrite pointwise_o_map_lift_refl.
  reflexivity.
Qed.

Program Definition PShVertEq {C} `{!Complete C} `{!StrictComplete C}
  (J : category)
  (F G : functor J (PSh C))
  (eq : functor_equiv F G)
  : vertex (func_limit_cone F) = vertex (func_limit_cone G).
Proof.
  apply FunctorEqUnpack.
  unshelve eapply MkFunctorEq.
  - intros x; simpl.
    apply (cones_eq_vertexes (pointwise_func_equiv_cones _ _ _ eq x)).
  - intros; simpl.
    unfold func_limit_func_h_map.
    unfold setoid_fun_to_setoid_lim_cone.
    apply SetoidMapPI; simpl.
    apply functional_extensionality; intros z.
    apply (eq_sig_hprop (λ t p q, proof_irrelevance _ p q)); simpl.
    apply functional_extensionality_dep; intros r; simpl.
    rewrite (pointwise_h_map F G eq r f).
    set (hom_trans (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) r x)
           (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) r y) ((F ₒ r)ₕ f)) as h.
    set (setoid_fun_to_setoid_lim_cone (pointwise_func F y)
           (cone_on_pointwise_func F f)) as g.
    set (pointwise_func_equiv_cones J F G eq) as k.
    simpl in *.
    set (cones_eq_vertexes (k x)) as c1.
    set (cones_eq_vertexes (k y)) as c2.
    simpl in *.

    unfold func_limit_func_o_map in g.
    simpl in g.
    rewrite hom_trans_setoid_conv'.
    assert (SetoidEq (setoid_lim_obj (pointwise_func G x)) (setoid_lim_obj (pointwise_func F x))).
    {
      apply SetoidEqPack.
      symmetry.
      apply c1.
    }
    rewrite -(SetoidEqPackUnpack (eq_sym c1)).
    rewrite SetoidEqSetoidConv.
    rewrite -(SetoidEqPackUnpack c2).
    rewrite SetoidEqSetoidConv.
    unshelve eassert ((setoid_carrier_eq (SetoidEqPack c2))
                      = SigmaEqUnpack _) as p.
    {
      unshelve econstructor.
      - apply PiEqUnpack.
        apply (MkPiEq eq_refl).
        intros i; simpl.
        apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i y))).
      - intros; simpl; clear.
        rewrite PiEqTransportApp.
        {
          intros i; simpl.
          apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i y))).
        }
        intros P.
        destruct F as [F1 F2 F3 F4 F5];
          destruct G as [G1 G2 G3 G4 G5];
          destruct eq as [eq1 eq2]; simpl in *.
        assert (F1 = G1) as Hf.
        {
          apply functional_extensionality; intros.
          apply eq1.
        }
        destruct Hf.
        assert (eq1 = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst eq1.
        assert (P = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst P.
        simpl.
        split.
        + intros H ???; rewrite -eq2.
          apply H.
        + intros H ???.
          unfold hom_trans in eq2.
          rewrite eq2.
          apply H.
    }
    { apply proof_irrelevance. }
    rewrite p; clear p.
    rewrite SigmaEqTransportProj1 /=.
    rewrite PiEqTransportApp.
    {
      intros i; simpl.
      apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i y))).
    }
    intros P; simpl.
    unshelve eassert ((setoid_carrier_eq (SetoidEqPack (eq_sym c1)))
                      = SigmaEqUnpack _) as p.
    {
      unshelve econstructor.
      - apply PiEqUnpack.
        apply (MkPiEq eq_refl).
        intros i; simpl.
        symmetry.
        apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i x))).
      - intros; simpl; clear.
        rewrite PiEqTransportApp.
        {
          intros i; simpl.
          apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (G ₒ) (F ₒ) (λ x, eq_sym (func_eq_o_map eq x)) i x))).
        }
        intros P.
        destruct F as [F1 F2 F3 F4 F5];
          destruct G as [G1 G2 G3 G4 G5];
          destruct eq as [eq1 eq2]; simpl in *.
        assert (F1 = G1) as Hf.
        {
          apply functional_extensionality; intros.
          apply eq1.
        }
        destruct Hf.
        assert (eq1 = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst eq1.
        assert (P = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst P.
        simpl.
        split.
        + intros H ???.
          unfold hom_trans in eq2.
          rewrite eq2.
          apply H.
        + intros H ???; rewrite -eq2.
          apply H.
    }
    { apply proof_irrelevance. }
    rewrite p; clear p.
    rewrite SigmaEqTransportProj1 /=.
    rewrite PiEqTransportApp.
    {
      intros i; simpl.
      symmetry.
      apply (setoid_carrier_eq (SetoidEqPack (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i x))).
    }
    intros Q.
    subst h.
    clear H.
    clear c1 c2 k g.
    destruct F as [F1 F2 F3 F4 F5];
      destruct G as [G1 G2 G3 G4 G5];
      destruct eq as [eq1 eq2]; simpl in *.
    assert (F1 = G1) as Hf.
    {
      apply functional_extensionality; intros.
      apply eq1.
    }
    destruct Hf.
    assert (eq1 = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    subst eq1.
    rewrite pointwise_o_map_lift_refl.
    assert (P = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    subst P.
    assert (Q = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    subst Q.
    reflexivity.
Qed.

Instance PShStrictComplete {C} `{!Complete C} `{!StrictComplete C}
  : StrictComplete (PSh C).
Proof.
  constructor.
  intros J F G eq; simpl.
  unshelve econstructor.
  - apply (PShVertEq _ _ _ eq).
  - intros j; simpl.
    unfold func_limit_cone_side.
    intros a; simpl.
    intros x y ->; simpl; clear x.
    unfold pointwise_func, setoid_lim_side; simpl.
    rewrite hom_trans_nat /=.
    rewrite hom_trans_setoid_conv' /=.
    rewrite -(SetoidEqPackUnpack (eq_sym (category.equal_f a (f_equal o_map (PShVertEq J F G eq))))).
    rewrite SetoidEqSetoidConv.
    rewrite -(SetoidEqPackUnpack (category.equal_f a (f_equal o_map (func_eq_o_map eq j)))).
    rewrite SetoidEqSetoidConv.
    unshelve eassert ((setoid_carrier_eq
                         (SetoidEqPack
                            (eq_sym (category.equal_f a
                                       (f_equal o_map (PShVertEq J F G eq))))))
                      = SigmaEqUnpack _) as p.
    {
      unshelve eapply MkSigmaEq.
      - apply PiEqUnpack.
        apply (MkPiEq eq_refl).
        intros i; simpl.
        symmetry.
        apply (setoid_carrier_eq
                 (SetoidEqPack
                    (pointwise_o_map (F ₒ) (G ₒ) (func_eq_o_map eq) i _))).
      - intros; simpl.
        rewrite PiEqTransportApp /=.
        {
          intros b.
          symmetry.
          f_equal.
          apply (category.equal_f a (f_equal o_map (func_eq_o_map eq b))).
        }
        intros J1.
        destruct F as [F1 F2 F3 F4 F5];
          destruct G as [G1 G2 G3 G4 G5];
          destruct eq as [eq1 eq2]; simpl in *.
        assert (F1 = G1) as Hf.
        {
          apply functional_extensionality; intros.
          apply eq1.
        }
        destruct Hf.
        assert (J1 = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst J1.
        simpl.
        assert (eq1 = λ _, eq_refl) as Hf.
        { apply proof_irrelevance. }
        subst eq1.
        rewrite /hom_trans in eq2.
        split; intros J2 ???.
        + rewrite eq2 J2.
          reflexivity.
        + rewrite -eq2 J2.
          reflexivity.
    }
    { apply proof_irrelevance. }
    rewrite p /=; clear p.
    rewrite SigmaEqTransportProj1 /=.
    rewrite PiEqTransportApp /=.
    {
      intros b.
      symmetry.
      f_equal.
      apply (category.equal_f a (f_equal o_map (func_eq_o_map eq b))).
    }
    intros J1.
    unshelve eassert ((setoid_carrier_eq
                         (SetoidEqPack
                            (category.equal_f a (f_equal o_map (func_eq_o_map eq j)))))
                      = eq_sym (J1 _)) as p.
    { apply proof_irrelevance. }
    rewrite p /=; clear p.
    destruct F as [F1 F2 F3 F4 F5];
      destruct G as [G1 G2 G3 G4 G5];
      destruct eq as [eq1 eq2]; simpl in *.
    assert (F1 = G1) as Hf.
    {
      apply functional_extensionality; intros.
      apply eq1.
    }
    destruct Hf.
    assert (J1 = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    subst J1.
    simpl.
    reflexivity.
Qed.
