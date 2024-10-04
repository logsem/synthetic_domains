From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat enriched domain.

Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Definition castT {A B : Type} (Heq : A = B) (a : A) : B :=
  match Heq in _ = u return u with eq_refl => a end.

Definition castP {A B : Prop} (Heq : A = B) (a : A) : B :=
  match Heq in _ = u return u with eq_refl => a end.

Lemma hom_trans_refl_eq {C : category} {a b : obj C} (f : hom a b)
  : hom_trans eq_refl eq_refl f = f.
Proof. by rewrite /hom_trans. Qed.

Lemma hom_trans_id_eq {C a b} (Heq : a = b) : hom_trans Heq Heq (@id C a) = id b.
Proof. destruct Heq; done. Qed.

Lemma hom_trans_trans_eq {C a b c d c' d'}
  (heq1 : a = c) (heq1' : b = d) (heq2 : c = c') (heq2' : d = d') (f : hom C a b) :
  hom_trans (eq_trans heq1 heq2) (eq_trans heq1' heq2') f =
  hom_trans heq2 heq2' (hom_trans heq1 heq1' f).
Proof. destruct heq1; destruct heq1'; destruct heq2; destruct heq2'; done. Qed.

Lemma hom_trans_sym_eq {C a b c d} heq heq' (f : hom C a b) (g : hom C c d) :
  hom_trans heq heq' f = g → f = hom_trans (eq_sym heq) (eq_sym heq') g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_sym_eq' {C a b c d} heq heq' (f : hom C a b) (g : hom C c d) :
  hom_trans (eq_sym heq) (eq_sym heq') f = g → f = hom_trans heq heq' g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_eq {C} {a b c d e : obj C} (heq : a = d) (heq' : c = e)
  (f : hom a b) (g : hom b c) :
  hom_trans heq heq' (g ∘ f) = hom_trans eq_refl heq' g ∘ hom_trans heq eq_refl f.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_l_eq {C} {a b c d e : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom d e) :
  g ∘ hom_trans heq heq' f = hom_trans (eq_sym heq') eq_refl g ∘ hom_trans heq eq_refl f.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_r_eq {C} {e a b c d : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom e c) :
  hom_trans heq heq' f ∘ g = hom_trans eq_refl heq' f ∘ hom_trans eq_refl (eq_sym heq) g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_take_in_l_eq {C} {a b c d e : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom d e) :
  g ∘ hom_trans heq heq' f = hom_trans heq eq_refl (hom_trans (eq_sym heq') eq_refl g ∘ f).
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_take_in_r_eq {C} {e a b c d : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom e c) :
  hom_trans heq heq' f ∘ g = hom_trans eq_refl heq' (f ∘ hom_trans eq_refl (eq_sym heq) g).
Proof. destruct heq; destruct heq'; done. Qed.

Lemma alg_hom_map_eq_eq {C : category} {T : functor C C} {A B : algebra T}
  (f g : alg_hom A B) :
  alg_hom_map f = alg_hom_map g → f = g.
Proof.
  destruct f as [f1 f2].
  destruct g as [g1 g2].
  simpl; intros H.
  destruct H.
  assert (f2 = g2) as -> by apply proof_irrelevance.
  reflexivity.
Qed.

Lemma alg_hom_map_eq_eq_inv {C : category} {T : functor C C} {A B : algebra T}
  (f g : alg_hom A B) :
  f = g → alg_hom_map f = alg_hom_map g.
Proof.
  intros ->.
  reflexivity.
Qed.

Lemma hom_trans_alg_hom_map_eq {C : category} {T : functor C C}
  {A A' B B' : algebra T} (Heq : A = A') (Heq' : B = B') (h : alg_hom A B) :
  alg_hom_map (hom_trans (C := Alg T) Heq Heq' h) =
    hom_trans (car_eq Heq) (car_eq Heq') (alg_hom_map h).
Proof. destruct Heq; destruct Heq'; rewrite /= !hom_trans_refl_eq //. Qed.

Record functor_equiv' {C D} (F G : functor C D) : Prop :=
  MkFuncEq' {
      func_eq_o_map' : ∀ a, F ₒ a = G ₒ a;
      func_eq_h_map' : ∀ a b (f : hom C a b),
        hom_trans (func_eq_o_map' a) (func_eq_o_map' b) (F ₕ f)
        = G ₕ f;
}.
Global Arguments MkFuncEq' {_ _ _ _} _ _, {_ _} _ _ _ _.
Global Arguments func_eq_o_map' {_ _ _ _} _ _.
Global Arguments func_eq_h_map' {_ _ _ _} _ [_ _] _.

Lemma functor_equiv'_eq {C D} (F G : functor C D) :
  functor_equiv' F G = (F = G).
Proof.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct F as [om hm hmp hmc hmi].
    destruct G as [om' hm' hmp' hmc' hmi'].
    assert (om = om') as ->.
    {
      apply functional_extensionality.
      apply (func_eq_o_map' H).
    }
    assert (hm = hm') as ->.
    {
      apply functional_extensionality_dep.
      intros a.
      apply functional_extensionality_dep.
      intros b.
      apply functional_extensionality.
      intros f.
      pose proof (func_eq_h_map' H f) as G.
      simpl in G; rewrite -G; clear G.
      assert (func_eq_o_map' H a = eq_refl) as -> by apply proof_irrelevance.
      assert (func_eq_o_map' H b = eq_refl) as -> by apply proof_irrelevance.
      by rewrite hom_trans_refl_eq.
    }
    assert (hmp = hmp') as -> by apply proof_irrelevance.
    assert (hmc = hmc') as -> by apply proof_irrelevance.
    assert (hmi = hmi') as -> by apply proof_irrelevance.
    reflexivity.
  - intros ->.
    apply (MkFuncEq' (λ a, eq_refl)).
    intros; simpl.
    by rewrite hom_trans_refl_eq.
Qed.


Global Instance functor_equiv'_equiv {C D} : Equivalence (@functor_equiv' C D).
Proof.
  split.
  - intros F.
    apply (MkFuncEq' (λ _, eq_refl)).
    by intros; rewrite hom_trans_refl_eq.
  - intros F G H.
    apply (MkFuncEq' (λ a, eq_sym (func_eq_o_map' H a))).
    intros; simpl.
    symmetry.
    apply hom_trans_sym_eq.
    apply (func_eq_h_map' H).
  - intros K L M H G.
    apply (MkFuncEq' (λ a, eq_trans (func_eq_o_map' H a) (func_eq_o_map' G a))).
    intros; simpl.
    rewrite hom_trans_trans_eq.
    rewrite (func_eq_h_map' H).
    apply (func_eq_h_map' G).
Qed.

Definition cone_trans {J C} {F F' : functor J C}
  (heq : F = F') (cn : cone F) : cone F' :=
  match heq in _ = F' return cone F' with
      eq_refl => cn
  end.

Definition cones_eq {J C} {F F' : functor J C}
  (Fequiv : F = F') (cn : cone F) (cn' : cone F') :=
  cn' = cone_trans Fequiv cn.

Record cones_equiv {J C} {F F' : functor J C}
  (Fequiv : functor_equiv' F F') (cn : cone F) (cn' : cone F') :=
  MkConesEq {
      cones_eq_vertexes : vertex cn = vertex cn';
      cones_eq_sides :
      ∀ j, side cn' j
           = hom_trans cones_eq_vertexes (func_eq_o_map' Fequiv j) (side cn j);
    }.
Arguments MkConesEq {_ _ _ _ _ _ _} _ _.
Arguments cones_eq_vertexes {_ _ _ _ _ _ _} _.
Arguments cones_eq_sides {_ _ _ _ _ _ _} _ _.

Lemma cones_equiv_eq {J C} {F F' : functor J C}
  (Fequiv : functor_equiv' F F') (Fequiv' : F = F') (cn : cone F) (cn' : cone F')
  : cones_equiv Fequiv cn cn'
    = (cones_eq Fequiv' cn cn').
Proof.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct ((castP (functor_equiv'_eq F F') Fequiv)).
    assert (Fequiv' = eq_refl) as -> by apply proof_irrelevance.
    rewrite /cones_eq /=.
    destruct cn as [v s p].
    destruct cn' as [v' s' p'].
    assert (v = v') as ->.
    { apply (cones_eq_vertexes H). }
    assert (s = s') as ->.
    {
      apply functional_extensionality_dep.
      intros x.
      pose proof (cones_eq_sides H x) as G.
      simpl in G.
      rewrite G.
      clear.
      assert (func_eq_o_map' Fequiv x = eq_refl) as -> by apply proof_irrelevance.
      assert (cones_eq_vertexes H = eq_refl) as -> by apply proof_irrelevance.
      by rewrite hom_trans_refl_eq.
    }
    assert (p = p') as -> by apply proof_irrelevance.
    reflexivity.
  - intros ->.
    destruct (castP (functor_equiv'_eq _ _) Fequiv).
    assert (Fequiv' = eq_refl) as -> by apply proof_irrelevance.
    apply (MkConesEq eq_refl).
    intros j; simpl.
    assert ((func_eq_o_map' Fequiv j) = eq_refl) as -> by apply proof_irrelevance.
    by rewrite hom_trans_refl_eq.
Qed.

Lemma cones_over_eq_diagrams_eq {J C} {F F' : functor J C}
  (Fequiv : F = F')
  (cn : cone F) (cn' : cone F)
  : cone_trans Fequiv cn = cone_trans Fequiv cn' → cn = cn'.
Proof.
  intros H.
  destruct Fequiv.
  by rewrite /cones_eq /cone_trans /= in H.
Qed.

(* Lemma functors_lim_transport {J C} {F F' : functor J C} *)
(*   (Fequiv : functor_equiv' F F') j *)
(*   (H : vertex (term (complete F')) = vertex (term (complete F))) *)
(*   G *)
(*   : side (term (complete F)) j *)
(*     = hom_trans H G (side (term (complete F')) j). *)

Record alg_equiv {D} {T : functor D D}
  (a b : obj (Alg T)) :=
  MkAlgEq {
      car_equiv : car a = car b;
      cons_equiv : cons b = hom_trans (o_map_eq T car_equiv) car_equiv (cons a);
    }.
Arguments MkAlgEq {_ _} _ _.
Arguments car_equiv {_ _ _ _}.
Arguments cons_equiv {_ _ _ _}.

Lemma alg_equiv_eq {D} (T : functor D D) (a b : obj (Alg T)) :
  alg_equiv a b = (a = b).
Proof.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct a as [car cons].
    destruct b as [car' cons'].
    assert (car = car') as ->.
    {
      apply (car_equiv H).
    }
    assert (cons = cons') as ->.
    {
      pose proof (cons_equiv H) as G.
      simpl in G; rewrite G; clear G.
      assert (car_equiv H = eq_refl) as -> by apply proof_irrelevance.
      assert (o_map_eq T eq_refl = eq_refl) as -> by apply proof_irrelevance.
      by rewrite hom_trans_refl_eq.
    }
    reflexivity.
  - intros ->.
    apply (MkAlgEq _ _ eq_refl).
    reflexivity.
Qed.

Lemma alg_fun_alg_eq_cong' {D} `{Complete D} {T : functor D D}
  {J : category}
  (I I' : obj (Alg T)) (i : alg_equiv I I')
  : alg_equiv (alg_func_on_alg I) (alg_func_on_alg I').
Proof.
  rewrite alg_equiv_eq in i.
  rewrite i.
  apply (MkAlgEq _ _ eq_refl).
  reflexivity.
Qed.

Lemma functor_equiv_lim {J D} `{!Complete D} {I I' : functor J D}
  (eq : functor_equiv' I I')
  : cones_equiv eq
      (term (complete I))
      (term (complete I')).
Proof.
  rewrite cones_equiv_eq.
  - by rewrite -functor_equiv'_eq.
  - intros H.
    destruct H.
    reflexivity.
Qed.

Lemma cones_equiv_f_alg_fun {J C T} {F F' : functor J (@Alg C T)}
  (cn : cone F) (cn' : cone F') (H : functor_equiv' F F') (HC : cones_equiv H cn cn') :
  cones_equiv H (alg_func_on_cone cn) (alg_func_on_cone cn').
Proof.
  rewrite cones_equiv_eq.
  - by rewrite -functor_equiv'_eq.
  - intros HEQ.
    destruct HEQ.
    rewrite /cones_eq /cone_trans.
    f_equal.
    rewrite cones_equiv_eq in HC.
    rewrite /cones_eq /cone_trans in HC.
    rewrite HC.
    reflexivity.
Qed.

Lemma alg_lim_alg_iso_cong' {D} `{Complete D} {T : functor D D}
  {J : category}
  (I I' : functor J (Alg T)) (i : functor_equiv' I I')
  : alg_equiv (alg_lim_alg I) (alg_lim_alg I').
Proof.
  rewrite alg_equiv_eq.
  f_equal.
  rewrite -functor_equiv'_eq.
  apply i.
Qed.

Lemma cones_equiv_f_alg_lim {J C T} `{!Complete C} {F F' : functor J (@Alg C T)}
  (H : functor_equiv' F F') :
  cones_equiv H (alg_lim_cone F) (alg_lim_cone F').
Proof.
  pose proof H as H'.
  rewrite functor_equiv'_eq in H'.
  rewrite cones_equiv_eq.
  destruct H'.
  reflexivity.
Qed.

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
  Context {SI : indexT} {C : category} `{!Complete C}
    `{!Enriched C (PSh (OrdCat SI))} `{!LimitsEnriched C}
    (F : functor C C) `{!LocallyContractiveFunctor F}.

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

  Program Definition cut_ord_ds_cat_func_trivial {dsp : downset_pred SI}
    (P : partial_solution dsp)
    : ∀ a : downset dsp,
    P ₒ a
    = P ₒ dsp_include (le_dsp_included a) (MkDS (le_dsp a) (squash (reflexivity _)))
  := λ a, o_map_eq P (le_dsp_included_eq a).

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
       functor_equiv'
         (cut_ord_ds_cat_func _ (le_dsp_included α) P)
         (cut_ord_ds_cat_func _ (le_dsp_included α) Q))
    : functor_equiv' P Q
    := MkFuncEq'
         (λ a, eq_trans
                 (eq_trans
                    (cut_ord_ds_cat_func_trivial P a)
                    (func_eq_o_map' (eqs a) (MkDS (le_dsp a) (squash (reflexivity _)))))
                 (eq_sym (cut_ord_ds_cat_func_trivial Q a)))
         _.
  Next Obligation.
    intros dsp P Q eqs α β f; simpl.
    rewrite !hom_trans_trans_eq.
    symmetry.
    apply (hom_trans_sym_eq
                   (cut_ord_ds_cat_func_trivial Q α)
                   (cut_ord_ds_cat_func_trivial Q β)).
    unfold cut_ord_ds_cat_func_trivial.
    rewrite !h_map_eq.
    epose proof (λ δ γ g, func_eq_h_map' (eqs α) (a := δ) (b := γ) g) as HEQ.
    rewrite /= /cut_ord_ds_cat_func_h_map /= in HEQ.
    match goal with
    | |- context G [_ ₕ ?a = _] =>
        set (f' := a)
    end.
    simpl in f'.
    assert (f' = f) as ->.
    { apply proof_irrel. }
    simpl in f.
    rewrite -(HEQ
                (MkDS (le_dsp α) (squash (reflexivity _)))
                  (MkDS (le_dsp α) (squash f))
                  f).
    f_equiv; last done.
    apply ProofIrrelevance.proof_irrelevance.
  Qed.

  Lemma par_sol_extensional' {dsp : downset_pred SI}
    (P Q : partial_solution dsp)
    (eqs : ∀ α : downset dsp,
         (cut_ord_ds_cat_func _ (le_dsp_included α) P)
         = (cut_ord_ds_cat_func _ (le_dsp_included α) Q) :> functor _ _)
    : P = Q :> functor _ _.
  Proof.
    rewrite -(functor_equiv'_eq P Q).
    apply par_sol_extensional.
    intros.
    rewrite functor_equiv'_eq.
    apply eqs.
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

  Definition canonical_par_sol {dsp} (ps : partial_solution dsp)
    := ∀ (α : downset dsp),
    cones_equiv (reflexivity _) (parsolext_cone
         (the_extension
            (cut_par_sol ps (lt_dsp_included α))))
      (partial_sol_cone_at ps α).

  Lemma canon_ext_equiv {dsp dsp1 dsp2} (P : partial_solution dsp)
    (H : dsp_included dsp1 dsp2)
    (H1 : dsp_included dsp1 dsp)
    (H2 : dsp_included dsp2 dsp)
    :
    functor_equiv'
      (cut_ord_ds_cat_func dsp1 H1 P)
      (cut_ord_ds_cat_func dsp1
         H
         (cut_ord_ds_cat_func dsp2 H2 P)).
  Proof.
    unshelve econstructor.
    + intros; simpl.
      unfold cut_ord_ds_cat_func_o_map.
      reflexivity.
    + intros; simpl.
      rewrite hom_trans_refl_eq.
      reflexivity.
  Qed.

  Lemma canon_ext_eq {dsp dsp1 dsp2} (P : partial_solution dsp)
    (H : dsp_included dsp1 dsp2)
    (H1 : dsp_included dsp1 dsp)
    (H2 : dsp_included dsp2 dsp)
    :
      (cut_ord_ds_cat_func dsp1 H1 P)
      = (cut_ord_ds_cat_func dsp1
           H
           (cut_ord_ds_cat_func dsp2 H2 P)).
  Proof.
    rewrite -functor_equiv'_eq.
    by apply canon_ext_equiv.
  Qed.

  Lemma canonicity_extend_v {dsp} (P : partial_solution dsp)
    (H : ∀ α, canonical_par_sol (cut_par_sol P (le_dsp_included α)))
    (α : downset dsp)
    : vertex (the_extension (cut_par_sol P (lt_dsp_included α))) =
        vertex (partial_sol_cone_at P α).
  Proof.
    rewrite -(cones_eq_vertexes (H α (MkDS (squash (reflexivity _))))).
    simpl.
    do 2 f_equal.
    apply canon_ext_eq.
  Qed.

  Lemma canonicity_extend
    {dsp} (P : partial_solution dsp)
    (H : ∀ α, canonical_par_sol (cut_par_sol P (le_dsp_included α)))
    : canonical_par_sol P.
  Proof.
    intros α.
    rewrite cones_equiv_eq /cones_eq /cone_trans.
    set (α' := (MkDS (le_dsp α) (squash (reflexivity _)))).
    pose proof (H α α') as G; clear H.
    assert (cones_equiv (reflexivity _)
              (partial_sol_cone_at P α)
              (the_extension (cut_par_sol P (lt_dsp_included α)))).
    {
      unshelve eapply MkConesEq.
      - pose proof (cones_eq_vertexes G) as G'; clear G.
        rewrite /= /cut_ord_ds_cat_func_o_map in G'.
        rewrite /=.
        eapply (eq_trans (eq_sym G')).
        apply (o_map_eq (alg_func_func F)).
        apply cones_equiv_f_alg_lim.
        symmetry.
        apply canon_ext_equiv.
      - intros; simpl.
        apply alg_hom_map_eq_eq; simpl.
        rewrite hom_trans_alg_hom_map_eq /=.
        pose proof (cones_eq_sides G j) as G'.
        simpl in G'.
        apply alg_hom_map_eq_eq_inv in G'.
        simpl in G'.
        rewrite hom_trans_alg_hom_map_eq in G'.
        simpl in G'.
        unfold cut_ord_ds_cat_func_h_map in G'.
        simpl.
        rewrite G'; clear G'.
        rewrite -hom_trans_trans_eq /=.
        assert ((func_eq_o_map'
                   (reflexivity
                      _) j)
                = eq_refl) as -> by apply proof_irrelevance.
        rewrite /=.

        rewrite hom_trans_trans_eq /=.
        rewrite hom_trans_compose_eq.
        rewrite hom_trans_refl_eq.
        assert ((func_eq_o_map'
                   (reflexivity
                      _) j)
                = eq_refl) as -> by apply proof_irrelevance.
        rewrite /=.
        rewrite hom_trans_compose_eq.
        rewrite hom_trans_refl_eq.
        f_equal.
        assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
        {
          intros H J; destruct H; destruct J.
          reflexivity.
        }
        rewrite -hom_trans_trans_eq /=.
        assert (∀ H, car_eq (eq_sym H) = eq_sym (car_eq H)) as ->.
        {
          intros H; destruct H.
          reflexivity.
        }
        rewrite eq_trans_assoc.
        rewrite eq_trans_sym_inv_r.
        rewrite eq_trans_refl_l.
        eassert ((car_eq
                    (o_map_eq
                       (alg_func_func F)
                       (cones_eq_vertexes
                          (cones_equiv_f_alg_lim
                             (symmetry
                                (canon_ext_equiv P (lt_dsp_included α') (lt_dsp_included α)
                      (le_dsp_included α)))))))
                 = (o_map_eq F
                      (car_eq
                         (cones_eq_vertexes
                            (cones_equiv_f_alg_lim
                               (symmetry
                                  (canon_ext_equiv P (lt_dsp_included α') (lt_dsp_included α)
                      (le_dsp_included α))))))))
          as HEQ.
        {
          destruct (cones_eq_vertexes
                      (cones_equiv_f_alg_lim
                         (symmetry (canon_ext_equiv P (lt_dsp_included α') (lt_dsp_included α)
                      (le_dsp_included α))))).
          reflexivity.
        }
        rewrite HEQ; clear HEQ.
        rewrite h_map_eq_l.
        f_equal.
        clear.
        assert (FEQ :
                 functor_equiv'
                   (functor_compose
                      (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included α')
                         (cut_ord_ds_cat_func (le_dsp α) (le_dsp_included α) P))
                      (forgetful F))
                   (functor_compose
                      (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included α) P)
                      (forgetful F))).
        {
          unshelve econstructor.
          - intros; simpl.
            reflexivity.
          - intros; simpl.
            rewrite hom_trans_refl_eq.
            reflexivity.
        }
        assert (CEQ : cones_equiv
                        FEQ
                        (term
                           (complete
                              (functor_compose
                                 (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included α')
                                    (cut_ord_ds_cat_func (le_dsp α) (le_dsp_included α) P))
                                 (forgetful F))))
                        (term
                           (complete
                              (functor_compose
                                 (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included α) P)
                                 (forgetful F))))).
        {
          apply functor_equiv_lim.
        }
        rewrite (cones_eq_sides CEQ j).
        f_equal.
        + apply proof_irrelevance.
        + apply proof_irrelevance.
    }
    rewrite cones_equiv_eq /cones_eq /cone_trans in H.
    rewrite -H.
    reflexivity.
  Qed.

  (* Lemma asdasdasd {dsp : downset_pred SI} *)
  (*   (P : partial_solution dsp) *)
  (*   (Q : partial_solution dsp) *)
  (*   (α β : downset dsp) *)
  (*   Y *)
  (*   (H : functor_equiv' P Q) *)
  (*   (* (Y : functor_equiv' (cut_par_sol P (lt_dsp_included α)) *) *)
  (*   (*    (cut_par_sol Q (lt_dsp_included β))) *) *)
  (*   : *)
  (*   cones_equiv Y (partial_sol_cone_at P α) *)
  (*     (partial_sol_cone_at Q α). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - simpl.       *)
  (*     apply (func_eq_o_map' H). *)
  (*   - intros; simpl. *)
  (*     apply alg_hom_map_eq_eq; simpl. *)
  (*     rewrite hom_trans_alg_hom_map_eq /=. *)
  (*     rewrite -hom_trans_alg_hom_map_eq. *)
  (*     apply alg_hom_map_eq_eq_inv. *)

  (*     (* epose proof (func_eq_h_map' H). *) *)
  (* Admitted. *)

  Lemma canonicity_inductive {dsp} (P : partial_solution dsp) :
    (∀ α, canonical_par_sol (cut_par_sol P (lt_dsp_included α))
          → canonical_par_sol (cut_par_sol P (le_dsp_included α)))
    → canonical_par_sol P.
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
    set (ζ := MkDS _ (squash (dsp_lt (unsquash (ds_in_dsp α')) (unsquash G)))).
    set (γ := MkDS (le_dsp α') (squash (reflexivity _))).
    pose proof (IHα α' (unsquash (ds_in_dsp α'))
                  (ds_in_dsp ζ)
                  γ) as X.
    clear IHα.
    revert X.
    match goal with
    | |- context G [le_dsp_included ?a] =>
        set (ζ' := a)
    end.
    intros X.
    assert (cut_ord_ds_cat_func (lt_dsp α') (lt_dsp_included α')
              (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included β) P)
            = (cut_par_sol (cut_par_sol P (le_dsp_included ζ')) (lt_dsp_included γ))).
    {
      rewrite -functor_equiv'_eq.
      unshelve econstructor.
      + intros; simpl.
        unfold cut_ord_ds_cat_func_o_map.
        reflexivity.
      + intros; simpl.
        rewrite hom_trans_refl_eq.
        reflexivity.
    }
    rewrite cones_equiv_eq /cones_eq /cone_trans /=.
    eapply (cones_over_eq_diagrams_eq H).
    assert (cone_trans H (partial_sol_cone_at (cut_par_sol P (lt_dsp_included β)) α')
            = partial_sol_cone_at (cut_par_sol P (le_dsp_included ζ')) γ) as HEQ.
    {
      symmetry.
      assert (Y : functor_equiv'
                    (cut_ord_ds_cat_func (lt_dsp α') (lt_dsp_included α')
                       (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included β) P))
                    (cut_par_sol (cut_par_sol P (le_dsp_included ζ')) (lt_dsp_included γ))).
      {
        rewrite functor_equiv'_eq.
        rewrite H.
        reflexivity.
      }
      pose proof (cones_equiv_eq Y H) as J.
      unfold cones_eq in J.
      rewrite -J; clear J.
      unshelve econstructor.
      - reflexivity.
      - intros; simpl.
        apply alg_hom_map_eq_eq; simpl.
        rewrite hom_trans_alg_hom_map_eq /=.
        clear.
        assert (eq_refl = car_eq eq_refl) as ->.
        { reflexivity. }
        rewrite -hom_trans_alg_hom_map_eq.
        apply alg_hom_map_eq_eq_inv.
        rewrite /cut_ord_ds_cat_func_h_map /=.
        match goal with
        | |- context G [dsp_include_le _ ?a]
          => set (f := a)
        end.
        clearbody f.
        subst ζ.
        simpl in *.
        match goal with
        | |- context G [h_map _ ?a]
          => set (T := a)
        end.
        simpl in T.
        match goal with
        | |- context G [hom_trans _ _ (h_map _ ?a)]
          => set (T' := a)
        end.
        simpl in T'.
        clearbody T T'.
        assert (T = T') as -> by apply proof_irrelevance.
        clear.
        set (J := (func_eq_o_map' Y j)).
        clearbody J.
        clear.
        assert (J = eq_refl) as ->.
        { apply proof_irrelevance. }
        rewrite hom_trans_refl_eq.
        reflexivity.
    }
    rewrite HEQ.
    assert (Y : functor_equiv'
                  (cut_ord_ds_cat_func (lt_dsp α') (lt_dsp_included α')
                     (cut_ord_ds_cat_func (lt_dsp α) (lt_dsp_included β) P))
                  (cut_par_sol (cut_par_sol P (le_dsp_included ζ')) (lt_dsp_included γ))).
    {
      rewrite functor_equiv'_eq.
      rewrite H.
      reflexivity.
    }
    unshelve epose proof (cones_equiv_eq Y H) as J.
    unfold cones_eq in J.
    rewrite -J; clear J.
    unshelve econstructor.
    {
      simpl.
      pose proof (cones_eq_vertexes X) as J; simpl in J.
      unshelve eapply (eq_trans _ J).
      apply (o_map_eq (alg_func_func F)).
      apply cones_equiv_f_alg_lim.
      apply Y.
    }
    {
      intros; simpl.
      apply alg_hom_map_eq_eq.
      rewrite hom_trans_alg_hom_map_eq /=.
      unfold cut_ord_ds_cat_func_h_map.
      assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
      {
        intros H' J; destruct H'; destruct J.
        reflexivity.
      }
      clear.
      pose proof (cones_eq_sides X j) as J; simpl in J.
      apply alg_hom_map_eq_eq_inv in J.
      simpl in J.
      unfold cut_ord_ds_cat_func_h_map in J.
      rewrite J; clear J.
      simpl.
      rewrite hom_trans_alg_hom_map_eq /=.
      rewrite hom_trans_compose_eq.
      rewrite hom_trans_compose_eq.
      f_equal.
      - rewrite -{2} (eq_trans_refl_l eq_refl).
        rewrite hom_trans_trans_eq.
        f_equal.
        eassert ((car_eq
                    (o_map_eq
                       (alg_func_func F)
                       (cones_eq_vertexes (cones_equiv_f_alg_lim Y))))
                 = (o_map_eq F
                      (car_eq
                         (cones_eq_vertexes (cones_equiv_f_alg_lim Y)))))
          as HEQ.
        {
          destruct (cones_eq_vertexes (cones_equiv_f_alg_lim Y)).
          reflexivity.
        }
        rewrite HEQ; clear HEQ.
        rewrite h_map_eq_l.
        f_equal.
        match goal with
        | |- context G [functor_compose ?a ?b]
          => set (T1 := functor_compose a b)
        end.
        match goal with
        | |- context G [functor_compose ?a ?b]
          => set (T2 := functor_compose a b)
        end.
        assert (FEQ :
                 functor_equiv'
                   T1
                   T2).
        {
          unshelve econstructor.
          - intros; simpl.
            reflexivity.
          - intros; simpl.
            rewrite hom_trans_refl_eq.
            reflexivity.
        }
        assert (CEQ : cones_equiv
                        FEQ
                        (term
                           (complete T1))
                        (term
                           (complete T2))).
        {
          apply functor_equiv_lim.
        }
        rewrite (cones_eq_sides CEQ j).
        rewrite -hom_trans_trans_eq.
        rewrite -(hom_trans_refl_eq (side (term (complete T1)) j)).
        f_equal.
        + apply proof_irrelevance.
        + apply proof_irrelevance.
      - f_equal.
        apply proof_irrelevance.
    }
  Qed.

  (* Lemma dfsdfds {dsp dsp' : downset_pred SI} *)
  (*   (H : dsp_included dsp' dsp) *)
  (*   (P Q : functor ((OrdDSCat dsp) ᵒᵖ) (Alg F)) *)
  (*   : functor_equiv' (cut_ord_ds_cat_func dsp' H P) *)
  (*       (cut_ord_ds_cat_func dsp' H Q). *)

  (* Lemma extend_functor_eq_lt_le {dsp} *)
  (*   (P Q : functor ((OrdDSCat dsp) ᵒᵖ) (Alg F)) *)
  (*   (α : SI) *)
  (*   (H : dsp_included (le_dsp α) dsp) *)
  (*   (H' : dsp_included (lt_dsp α) dsp) *)
  (*   (EQ : functor_equiv' (cut_ord_ds_cat_func (lt_dsp α) H' P) *)
  (*           (cut_ord_ds_cat_func (lt_dsp α) H' Q)) *)
  (*   (ext1 : ∀ (β : downset (le_dsp α)), *)
  (*      ds_idx β = α → *)
  (*      P ₒ dsp_include H β *)
  (*      = Q ₒ dsp_include H β) *)
  (*   (* (ext2 : ∀ (a b : obj (OrdDSCat (le_dsp α))) (f : hom a b) *) *)
  (*   (*           (K1 : ds_idx a = α) (K2 : ds_idx b = α), *) *)
  (*   (*    hom_trans (ext1 a K1) (ext1 b K2) *) *)
  (*   (*      (cut_ord_ds_cat_func_h_map (le_dsp α) H P f) = *) *)
  (*   (*      cut_ord_ds_cat_func_h_map (le_dsp α) H Q f) *) *)
  (*   : functor_equiv' (cut_ord_ds_cat_func (le_dsp α) H P) *)
  (*       (cut_ord_ds_cat_func (le_dsp α) H Q). *)
  (* Proof. *)
  (*   unshelve econstructor. *)
  (*   - intros γ; simpl. *)
  (*     rewrite /cut_ord_ds_cat_func_o_map. *)
  (*     destruct (index_le_eq_or_lt _ _ (unsquash (ds_in_dsp γ))) as [K | K]. *)
  (*     + apply ext1, K. *)
  (*     + apply (func_eq_o_map' EQ (dsp_include (λ _ x, x) (MkDS (lt_dsp α) (squash K)))). *)
  (*   - intros a b f; simpl. *)
  (*     destruct (index_le_eq_or_lt _ _ _) as [K1 | K1]; *)
  (*       destruct (index_le_eq_or_lt _ _ _) as [K2 | K2]; simpl. *)
  (*     + revert K1 K2. *)
  (*       revert f. *)
  (*       revert a b. *)
  (*       admit. *)
  (*     + admit. *)
  (*     + admit. *)
  (*     + pose proof (func_eq_h_map' EQ). *)
  (*       rewrite /cut_ord_ds_cat_func_h_map /=. *)
  (*     (*   rewrite /cut_ord_ds_cat_func_h_map /= in H2. *) *)
  (*     (*   rewrite /cut_ord_ds_cat_func_h_map /= in H2. *) *)
  (*     (* destruct (index_le_eq_or_lt a α (unsquash (ds_in_dsp a))) as [K1 | K1]; simpl. *) *)

  (* Admitted. *)

  Lemma canonical_eq {dsp} (P Q : partial_solution dsp)
    (PC : canonical_par_sol P) (QC : canonical_par_sol Q) :
    functor_equiv' P Q.
  Proof.
    apply par_sol_extensional.
    intros α.
    destruct α as [α G].
    simpl le_dsp.
    revert PC QC.
    revert P Q.
    induction (index_lt_wf _ α) as [α _ IHα].
    intros P Q PC QC.
    set (α' := MkDS dsp G).
    assert (∀ γ : downset (lt_dsp α),
              ∀ H : dsp_included (le_dsp γ) dsp,
              functor_equiv'
                (cut_ord_ds_cat_func (le_dsp γ) H P)
                (cut_ord_ds_cat_func (le_dsp γ) H Q)) as IH.
    {
      intros γ H.
      pose proof (IHα γ (unsquash (ds_in_dsp γ)) (squash (H γ (reflexivity _))))
        as J.
      match goal with
      | J : context G [cut_ord_ds_cat_func _ ?a] |- _ =>
          assert (a = H) as <-
      end; last apply J; [| done | done].
      apply proof_irrelevance.
    }
    rename IHα into IHremember.
    assert (∀ a : obj ((OrdDSCat (le_dsp α)) ᵒᵖ),
                (cut_ord_ds_cat_func (lt_dsp a)
                   (lt_dsp_included (dsp_include (le_dsp_included α') a)) P)
                = (cut_ord_ds_cat_func (lt_dsp a)
                     (lt_dsp_included (dsp_include (le_dsp_included α') a)) Q))
      as IHα.
    {
      intros a.
      rewrite -functor_equiv'_eq.
      unshelve econstructor.
      - intros b; simpl.
        rewrite /cut_ord_ds_cat_func_o_map.
        simpl in IH.
        pose proof
          (func_eq_o_map' (IH
             (MkDS (lt_dsp α)
                (squash (index_lt_le_trans _ _ _
                           (unsquash (ds_in_dsp b))
                           (unsquash (ds_in_dsp a)))))
             (λ x H, (dsp_pred_downwards dsp H
                        (dsp_pred_downwards dsp
                           (index_lt_le_subrel _ _ (unsquash (ds_in_dsp b)))
                           (dsp_pred_downwards dsp
                              (unsquash (ds_in_dsp a))
                              (unsquash G))))))
             (MkDS _ (squash (reflexivity _)))) as H;
          simpl in H.
        apply H.
      - intros γ1 γ2 f; simpl.
        match goal with
        | |- context G [func_eq_o_map' (IH ?a ?b) ?c]
          => set (p1 := a); set (p2 := b); set (p3 := c)
        end.
        clearbody p2.
        match goal with
        | |- context G [hom_trans _ (func_eq_o_map' (IH ?a ?b) ?c)]
          => set (t1 := a); set (t2 := b); set (t3 := c)
        end.
        clearbody t2.
        epose proof (λ δ γ g, func_eq_h_map' (IH p1 p2) (a := δ) (b := γ) g)
          as HEQ.
        rewrite /= /cut_ord_ds_cat_func_h_map /= in HEQ.
        rewrite /cut_ord_ds_cat_func_h_map.
        symmetry.
        match goal with
        | |- context G [_ ₕ ?a = _] =>
            set (f' := a)
        end.
        simpl in f'.
        assert (f' = f) as ->.
        { apply proof_irrel. }
        simpl in f.
        rewrite -(HEQ
                    (MkDS (le_dsp γ1) (squash (reflexivity _)))
                    (MkDS (le_dsp γ1) (squash f))).
        f_equiv; last done.
        apply ProofIrrelevance.proof_irrelevance.
    }
    clear IH.
    assert (∀ a : obj ((OrdDSCat (le_dsp α)) ᵒᵖ),
              functor_equiv'
                (cut_ord_ds_cat_func (lt_dsp a)
                   (lt_dsp_included (dsp_include (le_dsp_included α') a)) P)
                (cut_ord_ds_cat_func (lt_dsp a)
                   (lt_dsp_included (dsp_include (le_dsp_included α') a)) Q))
      as IHβ.
    {
      intros; rewrite IHα.
      reflexivity.
    }
    clear IHα.

    unshelve econstructor.
    - intros; simpl.
      rewrite /cut_ord_ds_cat_func_o_map /=.
      pose proof (eq_sym (cones_eq_vertexes (PC (dsp_include (le_dsp_included α') a))))
        as K1.
      pose proof (cones_eq_vertexes (QC (dsp_include (le_dsp_included α') a)))
        as K2.
      simpl in *.
      eapply (eq_trans K1).
      unshelve eapply (eq_trans _ K2).
      apply (o_map_eq (alg_func_func F)).
      apply cones_equiv_f_alg_lim.
      apply IHβ.
    - intros; simpl.
      rewrite hom_trans_trans_eq.
      rewrite hom_trans_trans_eq.
      rewrite /cut_ord_ds_cat_func_h_map.
      simpl in f.
      match goal with
      | |- context G [cones_eq_vertexes ?a]
        => set (C1 := a)
      end.
      match goal with
      | |- context G [hom_trans _ (cones_eq_vertexes ?a)]
        => set (C2 := a)
      end.
      match goal with
      | |- context G [o_map_eq _ (cones_eq_vertexes ?a)]
        => set (C3 := a)
      end.
      match goal with
      | |- context G [hom_trans _ (o_map_eq _ (cones_eq_vertexes ?a))]
        => set (C4 := a)
      end.
      match goal with
      | |- context G [eq_sym (cones_eq_vertexes ?a)]
        => set (C5 := a)
      end.
      match goal with
      | |- context G [hom_trans _ (eq_sym (cones_eq_vertexes ?a))]
        => set (C6 := a)
      end.
      clearbody C1 C2 C3 C4 C5 C6.
      destruct (index_le_eq_or_lt _ _ f) as [K | K].
      + assert (b = a :> downset (le_dsp α)) as ->.
        {
          destruct a, b; simpl in K; destruct K.
          reflexivity.
        }
        clear K.
        assert (C2 = C1) as -> by apply proof_irrelevance.
        assert (C4 = C3) as -> by apply proof_irrelevance.
        assert (C6 = C5) as -> by apply proof_irrelevance.
        assert (f = id _ :> hom (C := OrdDSCat _) _ _) as ->.
        {
          simpl; apply proof_irrelevance.
        }
        admit.
      +
      admit.
  Admitted.

  Lemma cut_par_sol_canon {dsp} (ps : partial_solution dsp)
    {dsp' : downset_pred SI}
    (Hdsps : dsp_included dsp' dsp)
    (HC : canonical_par_sol ps)
    : canonical_par_sol (cut_par_sol ps Hdsps).
  Proof.
    intros α.
    unshelve econstructor.
    - simpl.
      unfold cut_ord_ds_cat_func_o_map.
      simpl.
      pose proof (cones_eq_vertexes (HC (MkDS _ (squash (Hdsps α (unsquash (ds_in_dsp α))))))) as H.
      simpl in H.
      unshelve eapply (eq_trans _ H).
      apply (o_map_eq (alg_func_func F)).
      apply cones_equiv_f_alg_lim.
      symmetry.
      apply canon_ext_equiv.
    - intros; simpl.
      apply alg_hom_map_eq_eq; simpl.
      rewrite hom_trans_alg_hom_map_eq /=.
      assert (∀ H G, car_eq (eq_trans H G) = eq_trans (car_eq H) (car_eq G)) as ->.
      {
        intros H J; destruct H; destruct J.
        reflexivity.
      }
      assert (func_eq_o_map' (reflexivity _) _ = eq_refl) as ->.
      { apply proof_irrelevance. }
      match goal with
      | |- context G [hom_trans _ ?a]
        => assert (a = eq_trans eq_refl eq_refl) as ->
      end; first by apply proof_irrelevance.
      rewrite hom_trans_trans_eq /=.
      match goal with
      | |- context G [hom_trans (car_eq (cones_eq_vertexes ?a))]
        => set (A := a)
      end.
      (* clearbody A. *)
      simpl in A.
      match goal with
      | |- context G [hom_trans _ _
                       (hom_trans (car_eq (o_map_eq (alg_func_func F)
                                             (cones_eq_vertexes ?a))) _ _)]
        => set (B := a)
      end.
      (* clearbody B. *)
      simpl in B.
      rewrite /cut_ord_ds_cat_func_h_map /=.
      pose proof (cones_eq_sides A j) as HEQ.
      simpl in HEQ.
      apply alg_hom_map_eq_eq_inv in HEQ.
      rewrite hom_trans_alg_hom_map_eq /= in HEQ.
      rewrite HEQ; clear HEQ.
      f_equal.
      + apply proof_irrelevance.
      + eassert ((car_eq
                    (o_map_eq (alg_func_func F) (cones_eq_vertexes B)))
                 = (o_map_eq F
                      (car_eq
                         (cones_eq_vertexes B))))
          as HEQ.
        {
          destruct (cones_eq_vertexes B).
          reflexivity.
        }
        rewrite HEQ; clear HEQ.
        rewrite hom_trans_compose_eq.
        rewrite h_map_eq_l.
        rewrite hom_trans_refl_eq.
        f_equal.
        f_equal.
        pose proof (cones_eq_sides B j) as HEQ.
        simpl in HEQ.
        apply alg_hom_map_eq_eq_inv in HEQ.
        rewrite hom_trans_alg_hom_map_eq /= in HEQ.
        rewrite HEQ; clear HEQ.
        f_equal.
        apply proof_irrelevance.
  Qed.

  (* need eq or additional props *)
  Program Definition patch_functor {dsp : downset_pred SI}
    (collection : ∀ α : downset dsp, partial_solution (le_dsp α))
    (canon : ∀ α : downset dsp, canonical_par_sol (collection α))
    : functor (OrdDSCat dsp)ᵒᵖ (Alg F) := _.
  Next Obligation.
    intros; simpl.
    unshelve econstructor.
    - intros.
      apply (collection X ₒ
               (MkDS (le_dsp X) (squash (reflexivity _)))).
    - intros; simpl in *.
      eapply (comp _ (@h_map _ _ (collection a)
                     (MkDS _ (squash (reflexivity _)))
                     (MkDS (le_dsp a) (squash X)) X)).
      assert ((cut_ord_ds_cat_func (le_dsp b) (λ x P, transitivity P X : le_dsp a x)
                 (collection a)) ₒ (MkDS _ (squash (reflexivity _))) =
                (collection a ₒ (MkDS (le_dsp a) (squash X)))) as H.
      {
        simpl.
        unfold cut_ord_ds_cat_func_o_map.
        reflexivity.
      }
      rewrite -H; clear H.
      assert ((cut_ord_ds_cat_func (le_dsp b) (λ x P, transitivity P X : le_dsp a x)
                 (collection a)) ₒ (MkDS _ (squash (reflexivity _)))
              = parsol_func (cut_par_sol
                              (collection a)
                              (λ x (P : le_dsp b x), transitivity  P X : le_dsp a x))
                  ₒ (MkDS _ (squash (reflexivity _)))) as ->.
      {
        simpl.
        reflexivity.
      }
      assert (canonical_par_sol (cut_par_sol
                              (collection a)
                              (λ x (P : le_dsp b x), transitivity  P X : le_dsp a x))) as T.
      {
        simpl.
        apply cut_par_sol_canon.
        apply canon.
      }
      pose proof (canonical_eq
                    (collection b)
                    (cut_par_sol
                       (collection a)
                       (λ x (P : le_dsp b x), transitivity  P X : le_dsp a x))
                    (canon b) T).
      rewrite functor_equiv'_eq in H.
      rewrite H.
      apply id.
    - intros; simpl.
      intros ???.
      assert (x = y) as -> by apply proof_irrelevance.
      f_equal.
    - intros; simpl.

      admit.
    - intro; simpl.
      admit.
  Admitted.

  Lemma patch_partial_sol {dsp : downset_pred SI}
    (collection : ∀ α, dsp α → partial_solution (le_dsp α))
    (canon : ∀ α (H : dsp α), canonical_par_sol (collection α H))
    : partial_solution dsp.
  Proof.
  Admitted.

  Lemma functor_collection
    : ∀ α, { sol : partial_solution (le_dsp α) & canonical_par_sol sol }.
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
