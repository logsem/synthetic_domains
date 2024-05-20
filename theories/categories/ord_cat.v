Require Import Coq.Logic.ProofIrrelevance.
From SynthDom Require Import prelude.
From SynthDom.categories Require Import category.
From SynthDom Require Import stepindex.
From Coq.Logic Require Import FunctionalExtensionality.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Open Scope category_scope.

Global Instance index_le_equiv (SI : indexT) (α β : SI) : Equiv (α ⪯ β) := λ _ _, True.

Program Definition OrdCat (SI : indexT) : category :=
  MkCat SI (λ α β, α ⪯ β)
    (λ _, reflexivity _)
    (λ _ _ _ f g, transitivity f g)
    (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

(* successor as a functor *)

Program Definition Succ SI : functor (OrdCat SI) (OrdCat SI) :=
  MkFunc (λ α, succ α) (λ _ _ h, index_le_succ_mono _ _ h) _ _ _.
Solve All Obligations with repeat intros ?; done.

Program Definition ord_pred {SI : indexT} : index_rect (λ _ : SI, SI) :=
  MkIR zero (λ α _, α) (λ α _, α) _.
Next Obligation. done. Qed.
Fail Next Obligation.

Lemma ord_pred_le {SI : indexT} (α : SI) : ord_pred α ⪯ α.
Proof.
  destruct α using index_destruct; simpl_index_rect; [done| |done].
  apply index_lt_le_subrel, index_succ_greater.
Qed.

Lemma ord_pred_mono {SI : indexT} {α β : SI} : α ⪯ β → ord_pred α ⪯ ord_pred β.
Proof.
  intros Hαβ.
  destruct β as [|β|β]using index_destruct; simpl_index_rect.
  - etrans; first apply ord_pred_le.
    by simpl_index_rect.
  - destruct α as [|α|]using index_destruct; simpl_index_rect.
    + apply index_zero_minimum.
    + apply index_le_succ_inj; done.
    + assert (index_is_limit α) as Hil by apply α.
      pose proof (index_limit_not_succ α Hil β).
      apply index_le_eq_or_lt in Hαβ as [?|?%index_succ_iff_proj_r2l]; done.
  - destruct α as [|α|]using index_destruct; simpl_index_rect; last done.
    + apply index_zero_minimum.
    + etrans; last apply Hαβ.
      apply index_lt_le_subrel, index_succ_greater.
Qed.

Program Definition Pred SI : functor (OrdCat SI) (OrdCat SI) :=
  MkFunc (λ α, ord_pred α) (λ _ _ h, ord_pred_mono h) _ _ _.
Solve All Obligations with repeat intros ?; done.

Polymorphic Record downset_pred (SI : indexT) := MkDownSetPred {
  dsp_pred :> SI → Prop;
  dsp_pred_downwards : ∀ α β, α ⪯ β → dsp_pred β → dsp_pred α;
}.
Global Arguments MkDownSetPred {_} _ _.
Global Arguments dsp_pred {_} _ _.
Global Arguments dsp_pred_downwards {_} _ {_ _} _ _.

Lemma dsp_lt {SI} {dsp : downset_pred SI} {α β} : α ≺ β → dsp β → dsp α.
Proof. intros ? ?; eapply dsp_pred_downwards; [|eassumption]; apply index_lt_le_subrel; done. Qed.

Lemma dsp_unsucc {SI} {dsp : downset_pred SI} {α} : dsp (succ α) → dsp α.
Proof. intros ?; eapply dsp_lt; eauto. Qed.

Program Definition total_dsp SI : downset_pred SI := MkDownSetPred (λ _, True) _.
Solve All Obligations with done.
Fail Next Obligation.
Program Definition le_dsp {SI} α : downset_pred SI := MkDownSetPred (λ β, β ⪯ α ) _.
Next Obligation. intros ??????; simpl in *; etrans; eauto. Qed.
Fail Next Obligation.
Program Definition lt_dsp {SI} α : downset_pred SI := MkDownSetPred (λ β, β ≺ α ) _.
Next Obligation. intros ??????; simpl in *; eapply index_le_lt_trans; eauto. Qed.
Fail Next Obligation.

Record downset {SI} (dsp : downset_pred SI) := MkDS {
  ds_idx :> SI;
  ds_in_dsp : dsp ds_idx;
}.
Global Arguments MkDS {_ _ _} _, {_} _ {_} _.
Global Arguments ds_idx {_ _} _.
Global Arguments ds_in_dsp {_ _} _.

Lemma downset_eq {SI} {dsp : downset_pred SI} (ds ds' : downset dsp) : ds = ds' :> SI → ds = ds'.
Proof. destruct ds; destruct ds'; simpl; intros ->; f_equal; apply proof_irrelevance. Qed.

Program Definition OrdDSCat {SI} (dsp : downset_pred SI) : category :=
  MkCat (downset dsp) (λ α β, α ⪯ β)
    (λ α, reflexivity (α : SI))
    (λ α β γ (f : α ⪯ β) (g : β ⪯ γ), transitivity f g)
    (λ _ _ _ _, True) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

Program Definition lift_func {SI} (dsp : downset_pred SI) {C} (F : functor ((OrdCat SI)ᵒᵖ) C) :
  functor ((OrdDSCat dsp)ᵒᵖ) C :=
  MkFunc (λ α, F ₒ (ds_idx α)) (λ _ _ f, F ₕ f) _ _ _.
Next Obligation.
Proof. intros ???? [] []; rewrite /=; intros ?? ->; done. Qed.
Next Obligation.
Proof. intros ???? [] [] []; rewrite /=; intros ??; rewrite h_map_comp //. Qed.
Next Obligation.
Proof. intros ???? []; rewrite /= h_map_id //. Qed.
Fail Next Obligation.

Definition lift_in_lt_ds
  {SI : indexT} {α β : SI} (Hle : β ⪯ α) (γ : downset (lt_dsp β)) : downset (lt_dsp α) :=
  MkDS (lt_dsp α) (index_lt_le_trans _ _ _ (ds_in_dsp γ) Hle).

Lemma in_lt_dsp_le {SI : indexT} {α β : SI} :
  β ⪯ α → ∀ γ : downset (lt_dsp β), γ ⪯ α.
Proof.
  intros ? γ; etrans; last eassumption.
  apply index_lt_le_subrel, (ds_in_dsp γ).
Qed.

Lemma in_lt_dsp_succ {SI : indexT} (α : SI) : ∀ β : downset (lt_dsp (succ α)), β ⪯ α.
Proof. intros ?; apply index_succ_iff_proj_r2l, (ds_in_dsp β). Qed.

Lemma in_lt_dsp {SI : indexT} (α : SI) : ∀ β : downset (lt_dsp α), β ⪯ α.
Proof. intros ?; apply index_lt_le_subrel, (ds_in_dsp β). Qed.

Section limit_at.
  Context {SI : indexT} {C : category}.

  Variable (F : functor ((OrdCat SI)ᵒᵖ) C).

  Program Definition cone_at α dsp (Hle : ∀ β : downset dsp, β ⪯ α) : cone (lift_func dsp F) :=
    MkCone (F ₒ α) (λ β, F ₕ (Hle β)) _.
  Next Obligation. by repeat intros ?; rewrite /= -h_map_comp; f_equiv. Qed.
  Fail Next Obligation.
  Arguments cone_at {_} _ _, {_ _} _.

  Program Definition is_limit_at {α dsp} (Hle : ∀ β : downset dsp, β ⪯ α)
    (Hin : dsp α) : is_limit (lift_func dsp F) (F ₒ α) :=
    MkIsLimit _ (cone_is_cone (cone_at Hle))
      (MkIsTerm _ (λ cn, MkConeHom (side cn (MkDS Hin)) _) _).
  Next Obligation.
    intros ????? δ; apply (@side_commutes _ _ _ cn (MkDS Hin)).
  Qed.
  Next Obligation.
    intros ???? cn [f fcomm]; simpl in *.
    rewrite /equiv /cone_hom_eq /= fcomm.
    rewrite -{1}(left_id f) -h_map_id; repeat f_equiv; done.
  Qed.
  Fail Next Obligation.

  Program Definition is_limit_at_zero {t} (Hterm : is_terminal t) :
    is_limit (lift_func (lt_dsp zero) F) t :=
    MkIsLimit _ (MkIsCone (λ β, False_rect _ (index_lt_zero_is_normal β (ds_in_dsp β))) _)
      (MkIsTerm _
         (λ cn, MkConeHom (bang Hterm _) _) _).
  Next Obligation.
  Proof. intros ?? β; exfalso; exact (index_lt_zero_is_normal _ (ds_in_dsp β)). Qed.
  Next Obligation.
  Proof. intros ??? β; exfalso; exact (index_lt_zero_is_normal _ (ds_in_dsp β)). Qed.
  Next Obligation.
  Proof. intros ????; apply bang_unique. Qed.
  Fail Next Obligation.

End limit_at.

Section later_func_gen.
  Context {SI : indexT} {C : category}.

  Variable (F : functor ((OrdCat SI)ᵒᵖ) C).

  Program Definition proj_cone {α β} (Hle : β ⪯ α) (cn : cone (lift_func (lt_dsp α) F)) :
    cone (lift_func (lt_dsp β) F) :=
    MkCone (vertex cn) (λ γ, side cn (lift_in_lt_ds Hle γ)) _.
  Next Obligation.
    intros ??? cn γ γ' f.
    exact (@side_commutes _ _ _ cn (lift_in_lt_ds Hle γ) (lift_in_lt_ds Hle γ') f).
  Qed.
  Fail Next Obligation.

  Variable (lo_map : SI → obj C).
  Hypothesis lo_map_il : ∀ α, is_limit (lift_func (lt_dsp α) F) (lo_map α).

  Lemma il_side_eq α β Hβ1 Hβ2 :
    il_side (lo_map_il α) (@MkDS _ _ β Hβ1) = il_side (lo_map_il α) (MkDS Hβ2).
  Proof. by replace Hβ1 with Hβ2 by apply proof_irrel. Qed.

  Definition proj_cone_hom {α β} (Hle : β ⪯ α) :
    cone_hom
      (proj_cone Hle (cone_of_is_limit (lo_map_il α)))
      (cone_of_is_limit (lo_map_il β)) :=
    bang
      (is_limit_limiting_cone (lo_map_il β))
      (proj_cone Hle (cone_of_is_limit (lo_map_il α))).

  Program Definition later_func_gen : functor ((OrdCat SI)ᵒᵖ) C :=
    MkFunc lo_map (λ _ _ f, cone_hom_map (proj_cone_hom f)) _ _ _.
  Next Obligation.
  Proof. intros ?? Hle Hle'; rewrite (proof_irrel Hle Hle'); done. Qed.
  Next Obligation.
  Proof.
    intros ??? Hle Hle'; rewrite /=.
    apply (hom_to_limit_unique _ _ _ (lo_map_il _)
             (cone_is_cone (proj_cone _ (cone_of_is_limit (lo_map_il _))))).
    - intros ?. rewrite_cone_hom_commutes_back; done.
    - intros.
      rewrite -comp_assoc -(cone_hom_commutes (proj_cone_hom Hle')) /=.
      rewrite_cone_hom_commutes_back; simpl.
      match goal with |- ?A ≡ ?B => assert (A = B) as ->; last done end.
      apply il_side_eq.
  Qed.
  Next Obligation.
  Proof.
    intros ?; rewrite /=.
    apply (hom_to_limit_unique _ _ _ (lo_map_il _)
             (cone_is_cone (proj_cone _ (cone_of_is_limit (lo_map_il _))))).
    - intros; rewrite_cone_hom_commutes_back; done.
    - intros δ; rewrite /= right_id.
      match goal with |- ?A ≡ ?B => assert (A = B) as ->; last done end.
      destruct δ; apply il_side_eq.
  Qed.
  Fail Next Obligation.

End later_func_gen.

Section later.
  Context {SI : indexT} {C : category} `{!HasTerm C} `{!Complete C}.

  Program Definition later_func_o_map_il (F : functor ((OrdCat SI)ᵒᵖ) C) :
    index_rect (λ α, {c : obj C & is_limit (lift_func (lt_dsp α) F) c}) :=
    MkIR
      (existT _ (is_limit_at_zero F (term_is_terminal (term_of C))))
      (λ α _, existT _ (is_limit_at F (dsp := lt_dsp (succ α)) (in_lt_dsp_succ α)
                          (index_succ_greater α)))
      (λ α _, existT _ (limiting_cone_is_limit (term_is_terminal (complete _))))
      _.
  Next Obligation. done. Qed.
  Fail Next Obligation.

  Definition later_func_o_map F α : obj C := projT1 (later_func_o_map_il F α).

  Lemma later_func_o_map_zero F : later_func_o_map F zero = (term (term_of C)).
  Proof. by rewrite /later_func_o_map; simpl_index_rect. Qed.

  Lemma later_func_o_map_succ F α : later_func_o_map F (succ α) = F ₒ α.
  Proof. by rewrite /later_func_o_map; simpl_index_rect. Qed.

  Lemma later_func_o_map_lim F (α : limit_idx SI) :
    later_func_o_map F α = vertex (term (complete (lift_func (lt_dsp α) F))).
  Proof. by rewrite /later_func_o_map; simpl_index_rect. Qed.

  Definition later_func_o_map_is_limit F α :
    is_limit (lift_func (lt_dsp α) F) (later_func_o_map F α) :=
    projT2 (later_func_o_map_il F α).

  Lemma later_func_o_map_is_limit_zero F :
    later_func_o_map_is_limit F zero =
    is_limit_trans (eq_sym (later_func_o_map_zero F))
      (is_limit_at_zero F (term_is_terminal (term_of C))).
  Proof.
    rewrite /later_func_o_map_is_limit.
    assert (later_func_o_map_il F zero =
      existT _ (is_limit_at_zero F (term_is_terminal (term_of C)))) as Heq.
    { by simpl_index_rect. }
    pose proof (projT2_eq Heq) as Heq'; simpl in *; rewrite -Heq'; clear Heq'.
    replace (projT1_eq Heq) with (later_func_o_map_zero F)
      by apply proof_irrelevance.
    destruct (later_func_o_map_zero F); simpl; done.
  Qed.

  Lemma later_func_o_map_is_limit_succ F α :
    later_func_o_map_is_limit F (succ α) =
    is_limit_trans (eq_sym (later_func_o_map_succ F α))
      (is_limit_at F (dsp := lt_dsp (succ α)) (in_lt_dsp_succ α)
         (index_succ_greater α)).
  Proof.
    assert (later_func_o_map_il F (succ α) =
      existT _ (is_limit_at F (dsp := lt_dsp (succ α)) (in_lt_dsp_succ α)
         (index_succ_greater α))) as Heq.
    { by simpl_index_rect. }
    pose proof (projT2_eq Heq) as Heq'; simpl in *; rewrite -Heq'; clear Heq'.
    replace (projT1_eq Heq) with (later_func_o_map_succ F α)
      by apply proof_irrelevance.
    destruct (later_func_o_map_succ F α); simpl; done.
  Qed.

  Lemma later_func_o_map_is_limit_lim F (α : limit_idx SI) :
    later_func_o_map_is_limit F α =
    is_limit_trans (eq_sym (later_func_o_map_lim F α))
      (limiting_cone_is_limit (term_is_terminal (complete _))).
  Proof.
    assert (later_func_o_map_il F α =
      existT _ (limiting_cone_is_limit (term_is_terminal (complete _)))) as Heq.
    { by simpl_index_rect. }
    pose proof (projT2_eq Heq) as Heq'; simpl in *; rewrite -Heq'; clear Heq'.
    replace (projT1_eq Heq) with (later_func_o_map_lim F α)
      by apply proof_irrelevance.
    destruct (later_func_o_map_lim F α); simpl; done.
  Qed.

  Program Definition later_func F : functor ((OrdCat SI)ᵒᵖ) C :=
    later_func_gen F (later_func_o_map F) (later_func_o_map_is_limit F).

  Program Definition later_h_map_cone {F G} (η : natural F G) α :
    cone (lift_func (lt_dsp α) G) :=
    MkCone (later_func_o_map F α)
      (λ δ, η ₙ (ds_idx δ) ∘ il_side (later_func_o_map_is_limit F α) δ) _.
  Next Obligation.
    intros ???????; simpl in *. rewrite -comp_assoc -naturality /= comp_assoc.
    rewrite -(il_side_commutes (later_func_o_map_is_limit F α)); done.
  Qed.
  Fail Next Obligation.

  Program Definition later_h_map {F G} (η : natural F G) : natural (later_func F) (later_func G) :=
    MkNat
      (λ α, cone_hom_map (bang (il_is_limiting_cone _ _ (later_func_o_map_is_limit G α))
        (later_h_map_cone η α)))
      _.
  Next Obligation.
  Proof.
    intros ?? η α β f; simpl in *.
    pose (proj_cone _ f (later_h_map_cone η α)) as cn.
    apply (hom_to_limit_unique _ _ _
              (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
              (cone_is_cone cn)).
    - intros ?. rewrite -comp_assoc.
      rewrite_cone_hom_commutes_back.
      rewrite /= comp_assoc.
      rewrite_cone_hom_commutes_back; done.
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      repeat (rewrite_cone_hom_commutes_back; simpl); done.
  Qed.
  Fail Next Obligation.

  Definition later_h_map_comp {F G H} (η : natural F G) (η' : natural G H) :
    later_h_map (natural_comp η η') ≡ natural_comp (later_h_map η) (later_h_map η').
  Proof.
    intros α; rewrite /=.
    pose (later_h_map_cone (natural_comp η η') α) as cn.
    apply (hom_to_limit_unique _ _ _
      (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
      (cone_is_cone cn)).
    - intros ?; rewrite /=. rewrite_cone_hom_commutes_back; done.
    - intros ?; rewrite /= -comp_assoc.
      rewrite_cone_hom_commutes_back.
      rewrite /= !comp_assoc.
      rewrite_cone_hom_commutes_back; done.
  Qed.

  Definition later_h_map_id F : later_h_map (natural_id F) ≡ natural_id (later_func F).
  Proof.
    intros α; rewrite /=; symmetry.
    pose (later_h_map_cone (natural_id F) α) as cn.
    apply (hom_to_limit_unique _ _ _
      (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
      (cone_is_cone cn)).
    - intros ?; rewrite /= left_id right_id //.
    - intros ?; rewrite /= left_id.
      rewrite_cone_hom_commutes_back; rewrite /= left_id //.
  Qed.

  Program Definition later : functor (FuncCat ((OrdCat SI)ᵒᵖ) C) (FuncCat ((OrdCat SI)ᵒᵖ) C) :=
    MkFunc later_func (λ _ _ η, later_h_map η) _ (λ _ _ _, later_h_map_comp) later_h_map_id.
  Next Obligation.
    intros F G η η' Heq α; rewrite /later_h_map /=.
    apply (hom_to_limit_unique _ _ _
      (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
      (cone_is_cone (later_h_map_cone _ _))).
    - intros ?; rewrite /=; rewrite_cone_hom_commutes_back; done.
    - intros ?; rewrite /=; rewrite_cone_hom_commutes_back; rewrite Heq //.
  Qed.
  Fail Next Obligation.

  Program Definition next_cone {F G : functor ((OrdCat SI)ᵒᵖ) C} (η : natural F G)
    {α} (cn : cone (lift_func (lt_dsp α) F)) : cone (lift_func (lt_dsp α) G) :=
    MkCone (vertex cn) (λ α, η ₙ (α : SI) ∘ side cn α) _.
  Next Obligation. repeat intros ?; rewrite /= -comp_assoc -naturality comp_assoc -side_commutes //. Qed.
  Fail Next Obligation.

  Program Definition next : natural (id_functor _) later :=
    MkNat (λ F,
      MkNat (λ α,
        cone_hom_map
          (bang (il_is_limiting_cone _ _ (later_func_o_map_is_limit F α))
            (cone_at F α (lt_dsp α) (in_lt_dsp α)))) _) _.
  Next Obligation.
    intros F α β Hle; rewrite /=.
    apply (hom_to_limit_unique _ _ _
            (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit F β)))
            (cone_is_cone (cone_at F α (lt_dsp β) (in_lt_dsp_le Hle)))).
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      rewrite_cone_hom_commutes_back.
      rewrite -h_map_comp; f_equiv; done.
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
    repeat (rewrite_cone_hom_commutes_back; simpl); f_equiv; done.
  Qed.
  Next Obligation.
    intros F G η α; rewrite /=.
    apply (hom_to_limit_unique _ _ _
             (limiting_cone_is_limit
                (il_is_limiting_cone (lift_func _ _) _ (later_func_o_map_is_limit G α)))
             (cone_is_cone
                (next_cone η (cone_at F α (lt_dsp α) (in_lt_dsp α))))).
    - intros ?; rewrite /= -comp_assoc; rewrite_cone_hom_commutes_back.
      rewrite naturality. f_equiv; done.
    - intros ?; rewrite /= -comp_assoc; rewrite_cone_hom_commutes_back.
      rewrite comp_assoc; rewrite_cone_hom_commutes_back; f_equiv; done.
  Qed.

End later.

Section earlier.
  Context {SI : indexT} {C : category}.

  Program Definition earlier : functor (FuncCat ((OrdCat SI)ᵒᵖ) C) (FuncCat ((OrdCat SI)ᵒᵖ) C) :=
    MkFunc (λ F, functor_compose (opposite_func (Succ _)) F)
      (λ _ _ η, hor_comp (natural_id (opposite_func (Succ _))) η) _ _ _.
  Next Obligation. repeat intros ?; rewrite /=; solve_by_equiv_rewrite. Qed.
  Next Obligation. repeat intros ?; rewrite /= !h_map_id !right_id //. Qed.
  Next Obligation. repeat intros ?; rewrite //= !h_map_id !right_id //. Qed.
  Fail Next Obligation.

End earlier.

Section Adjunction.
  Context {SI : indexT} {C : category} `{!HasTerm C} `{!Complete C}.

  Lemma later_succ F : functor_compose (opposite_func (Succ SI)) (later_func F) ≡ F.
  Proof.
    refine (MkFuncEq
      (functor_compose (opposite_func (Succ SI)) (later_func F)) F
      (later_func_o_map_succ F) _).
    intros ?? Hle; rewrite /=.
    symmetry; apply hom_trans_sym'; symmetry.
    apply (hom_to_limit_unique _ _ _
             (limiting_cone_is_limit (il_is_limiting_cone (lift_func _ _) _
                                        (later_func_o_map_is_limit _ _)))
             (cone_is_cone (proj_cone _ (index_le_succ_mono _ _ Hle)
                              (cone_of_is_limit (later_func_o_map_is_limit _ _))))).
    - intros ?; rewrite /=. rewrite_cone_hom_commutes_back; done.
    - intros ?; rewrite /=.
      rewrite !later_func_o_map_is_limit_succ.
      rewrite !trans_side_of_is_limit_trans.
      rewrite !hom_trans_compose_take_in_l.
      rewrite -hom_trans_trans eq_trans_sym_inv_r hom_trans_refl.
      f_equiv.
      rewrite /ic_side /= -h_map_comp; f_equiv; done.
  Qed.

  Program Definition later_earlier_forward :
    natural
    (functor_compose
      (functor_prod (id_functor ((FuncCat ((OrdCat SI)ᵒᵖ) C) ᵒᵖ)) later)
      (Hom (FuncCat ((OrdCat SI)ᵒᵖ) C)))
    (functor_compose
       (functor_prod (opposite_func earlier) (id_functor (FuncCat ((OrdCat SI)ᵒᵖ) C)))
       (Hom (FuncCat ((OrdCat SI)ᵒᵖ) C))) :=
    MkNat (λ FG, λset η,
        natural_comp
          (hor_comp (natural_id (opposite_func (Succ _))) η)
          (functor_eq_natural (later_succ FG.2))) _.
  Next Obligation. repeat intros ?; simpl; solve_by_equiv_rewrite. Qed.
  Next Obligation.
    repeat intros [F1 G1] [F2 G2] [η1 η2] δ1 δ2 -> α; rewrite /=.
    rewrite !hom_trans_compose_take_in_r !left_id /= !hom_trans_refl.
    rewrite !later_func_o_map_is_limit_succ.
    rewrite !h_map_id !right_id.
    rewrite bang_of_is_limit_trans.
    rewrite !hom_trans_compose_take_in_r -hom_trans_trans /= !hom_trans_refl.
    rewrite !hom_trans_compose !hom_trans_refl.
    f_equiv.
    rewrite !later_func_o_map_is_limit_succ /il_side.
    rewrite !trans_side_of_is_limit_trans /=.
    replace (eq_trans (eq_sym (later_func_o_map_succ G2 α)) (func_eq_o_map (later_succ G2) α))
      with (eq_refl (G2 ₒ α)) by apply proof_irrelevance.
    rewrite hom_trans_refl !comp_assoc.
    f_equiv.
    apply hom_trans_sym'.
    rewrite !hom_trans_compose !hom_trans_refl.
    rewrite -hom_trans_trans eq_trans_refl_r eq_trans_refl_l.
    match goal with |- hom_trans _ _ ?A ∘ _ ≡ _ => assert (A ≡ id _) as -> end.
    { rewrite -h_map_id; f_equiv; done. }
    replace (later_func_o_map_succ G1 α) with (func_eq_o_map (later_succ G1) α)
      by apply proof_irrelevance.
    rewrite hom_trans_id left_id //.
  Qed.
  Fail Next Obligation.

  Program Definition to_later_F_succ_cone (F : functor (OrdCat SI ᵒᵖ) C) α :
    is_cone (lift_func (lt_dsp α) (functor_compose (opposite_func (Succ SI)) F)) (F ₒ α) :=
    MkIsCone (λ β, F ₕ (index_succ_iff_proj_r2l _ _ _ (index_lt_succ_mono _ _ (ds_in_dsp β)))) _.
  Next Obligation. repeat intros ?; rewrite /= -h_map_comp; f_equiv; done. Qed.

  Program Definition to_later_F_succ F :
    natural F (later_func (functor_compose (opposite_func (Succ SI)) F)) :=
    MkNat (λ α,
        cone_hom_map
          (bang (is_limit_limiting_cone (later_func_o_map_is_limit _ α))
             (cone_of_is_cone (to_later_F_succ_cone F α)))) _.
  Next Obligation.
    intros ??? Hle; rewrite /=.
    apply (hom_to_limit_unique _ _ _
             (later_func_o_map_is_limit
                (functor_compose (opposite_func (Succ SI)) _) _)
             (cone_is_cone (proj_cone _ Hle (cone_of_is_cone (to_later_F_succ_cone _ _))))).
    - intros ?; rewrite /= -comp_assoc. rewrite_cone_hom_commutes_back.
      rewrite /to_later_F_succ_cone /= -h_map_comp.
      f_equiv; done.
    - intros ?; rewrite /= -comp_assoc; repeat (rewrite_cone_hom_commutes_back; simpl); done.
  Qed.
  Fail Next Obligation.

  Program Definition cone_for_later_earlier_backward
    {F1 : functor (OrdCat SI ᵒᵖ) C}
    {G1 : functor (OrdCat SI ᵒᵖ) C}
    {F2 : functor (OrdCat SI ᵒᵖ) C}
    {G2 : functor (OrdCat SI ᵒᵖ) C}
    (η1 : natural F2 F1)
    (η2 : natural G1 G2)
    (δ : natural (functor_compose (opposite_func (Succ SI)) F1) G1)
    (α : SI)
    : cone (lift_func (lt_dsp α) G2) :=
    MkCone (F2 ₒ α)
      (λ j, (η2 ₙ (j : SI)) ∘ (δ ₙ (j : SI)) ∘ (η1 ₙ (succ j)) ∘
              (F2 ₕ (index_succ_least _ _ (ds_in_dsp j)))) _.
  Next Obligation.
    intros ???? η1 η2 δ ????; rewrite /=.
    rewrite -!comp_assoc -!(naturality η2) !comp_assoc. f_equiv.
    rewrite -!comp_assoc -(naturality δ) /= !comp_assoc. f_equiv.
    rewrite -!comp_assoc -(naturality η1) /= !comp_assoc. f_equiv.
    rewrite -h_map_comp. f_equiv.
    done.
  Qed.
  Fail Next Obligation.

  Program Definition later_earlier_backward :
    natural
    (functor_compose
       (functor_prod (opposite_func earlier) (id_functor (FuncCat ((OrdCat SI)ᵒᵖ) C)))
       (Hom (FuncCat ((OrdCat SI)ᵒᵖ) C)))
    (functor_compose
      (functor_prod (id_functor ((FuncCat ((OrdCat SI)ᵒᵖ) C) ᵒᵖ)) later)
      (Hom (FuncCat ((OrdCat SI)ᵒᵖ) C))) :=
    MkNat (λ FG, λset η, natural_comp (to_later_F_succ FG.1) (later ₕ η)) _.
  Next Obligation. intros ??? ->; done. Qed.
  Next Obligation.
    intros [F1 G1] [F2 G2] [η1 η2] z δ -> α; clear z; simpl in *.
    apply (hom_to_limit_unique _ _ _
             (later_func_o_map_is_limit G2 α)
             (cone_is_cone (cone_for_later_earlier_backward η1 η2 δ α))).
    - intros ?; rewrite /=.
      rewrite -!comp_assoc; rewrite_cone_hom_commutes_back.
      rewrite !comp_assoc; rewrite_cone_hom_commutes_back.
      rewrite h_map_id left_id /=; repeat f_equiv; done.
    - intros ?; rewrite /=.
      rewrite -!comp_assoc.
      rewrite_cone_hom_commutes_back; simpl.
      rewrite !comp_assoc; f_equiv.
      rewrite -!comp_assoc.
      rewrite_cone_hom_commutes_back; simpl.
      rewrite !comp_assoc; f_equiv.
      rewrite -!comp_assoc.
      rewrite_cone_hom_commutes_back; simpl.
      rewrite naturality; repeat f_equiv; done.
  Qed.

  Program Definition later_adj : adjunction (@earlier SI C) later :=
    MkIsoIc later_earlier_forward later_earlier_backward _.
  Next Obligation.
    split.
    - intros [F G] η η' <- α; clear η'; simpl in *.
      pose (extend_cone
              (cone_of_is_cone (il_is_cone (later_func_o_map_is_limit G α)))
              (η ₙ α)) as cn.
      apply (hom_to_limit_unique _ _ _
             (later_func_o_map_is_limit G α)
             (cone_is_cone cn)); last done.
      intros j; rewrite /= -comp_assoc.
      rewrite_cone_hom_commutes_back.
      rewrite /= !comp_assoc.
      rewrite_cone_hom_commutes_back.
      rewrite /= h_map_id left_id.
      rewrite hom_trans_compose_take_in_r left_id /= hom_trans_refl.
      rewrite (naturality η) /=.
      rewrite hom_trans_compose hom_trans_refl.
      f_equiv.
      rewrite /proj_cone_hom.
      rewrite later_func_o_map_is_limit_succ.
      rewrite bang_of_is_limit_trans /= -hom_trans_trans.
      match goal with
        |- context [eq_trans (eq_sym ?A) ?B] =>
          pose proof (proof_irrelevance _ A B) as ->
      end.
      rewrite eq_trans_sym_inv_l hom_trans_refl /=.
      rewrite /lift_in_lt_ds /=.
      match goal with
        |- ic_side _ _ ≡ ic_side _ (MkDS _ ?A) =>
          replace A with (ds_in_dsp j) by by apply proof_irrelevance
      end.
      by destruct j.
    - intros [F G] η η' <- α; clear η'; simpl in *.
      rewrite h_map_id right_id.
      rewrite hom_trans_compose_take_in_r left_id /= hom_trans_refl.
      symmetry; apply hom_trans_sym'; symmetry.
      pose (hom_trans
              (func_eq_o_map
                 (later_succ (functor_compose (opposite_func (Succ SI)) F)) α)
              eq_refl
              (later ₕ η ₙ (succ α))) as f.
      pose (extend_cone
              (cone_of_is_cone
                 (il_is_cone (later_func_o_map_is_limit G (succ α)))) f)
        as cn.
      apply (hom_to_limit_unique _ _ _
             (later_func_o_map_is_limit G (succ α))
             (cone_is_cone cn)).
      + intros ?; rewrite /= -comp_assoc.
        rewrite_cone_hom_commutes_back.
        rewrite /= !comp_assoc.
        rewrite_cone_hom_commutes_back.
        rewrite /f /=.
        rewrite hom_trans_compose_take_in_l /= hom_trans_refl.
        rewrite_cone_hom_commutes_back.
        rewrite /later_h_map_cone /=.
        rewrite hom_trans_compose /= hom_trans_refl.
        rewrite later_func_o_map_is_limit_succ.
        rewrite /il_side trans_side_of_is_limit_trans.
        rewrite -hom_trans_trans /=.
        match goal with
          |- context [eq_trans (eq_sym ?A) ?B] =>
            pose proof (proof_irrelevance _ A B) as ->
        end.
        rewrite eq_trans_sym_inv_l hom_trans_refl /=.
        repeat f_equiv; done.
      + intros ?; rewrite /= /f /=.
        rewrite !hom_trans_compose_take_in_l /= !hom_trans_refl eq_sym_involutive.
        rewrite_cone_hom_commutes_back.
        rewrite /later_h_map_cone /=.
        rewrite hom_trans_compose /= hom_trans_refl.
        rewrite !later_func_o_map_is_limit_succ.
        rewrite /il_side !trans_side_of_is_limit_trans /=.
        rewrite -!hom_trans_trans /=.
        repeat match goal with
          |- context [eq_trans (eq_sym ?A) ?B] =>
            pose proof (proof_irrelevance _ A B) as ->
        end.
        rewrite !eq_trans_sym_inv_l !hom_trans_refl /=.
        rewrite (naturality η) //.
  Qed.

End Adjunction.

Section fixpoint.
  Context {SI : indexT}.

  (* TODO: consider moving if useful in other places. *)
  Definition le_conv_l {α β γ : SI} (Heq : α = β) (Hle : α ⪯ γ) : β ⪯ γ :=
    match Heq in _ = z return z ⪯ γ with eq_refl => Hle end.
  Definition le_conv_r {α β γ : SI} (Heq : γ = β) (Hle : α ⪯ γ) : α ⪯ β :=
    match Heq in _ = z return α ⪯ z with eq_refl => Hle end.
  Definition psh_conv (X : PreSheaf (OrdCat SI))
    {α β : SI} (Heq : α = β) (x : X ₒ α) : X ₒ β :=
    match Heq in _ = z return X ₒ z with eq_refl => x end.
  Definition psh_conv_sym (X : PreSheaf (OrdCat SI))
    {α β : SI} (Heq : α = β) (x : X ₒ α) (y : X ₒ β) :
    psh_conv X Heq x ≡ y ↔ x ≡ psh_conv X (eq_sym Heq) y.
  Proof. destruct Heq; done. Qed.
  Definition psh_conv_trans (X : PreSheaf (OrdCat SI))
    {α β γ: SI} (Heq : α = β) (Heq' : β = γ) (x : X ₒ α) :
    psh_conv X (eq_trans Heq Heq') x ≡ psh_conv X Heq' (psh_conv X Heq x).
  Proof. destruct Heq; destruct Heq'; done. Qed.
  Lemma psh_conv_hom_action (X : PreSheaf (OrdCat SI))
    {α β γ : SI} (Hle : γ ⪯ β) (Heq : α = β) (x : X ₒ α) :
    (X ₕ Hle) (psh_conv X Heq x) ≡ (X ₕ (le_conv_r (eq_sym Heq) Hle)) x.
  Proof. destruct Heq; done. Qed.
  Lemma psh_conv_hom_action' (X : PreSheaf (OrdCat SI))
    {α β γ : SI} (Hle : α ⪯ γ) (Heq : α = β) (x : X ₒ γ) :
    psh_conv X Heq ((X ₕ Hle) x) ≡ (X ₕ (le_conv_l Heq Hle)) x.
  Proof. destruct Heq; done. Qed.
  Global Instance psh_conv_proper (X : PreSheaf (OrdCat SI))
    {α β : SI} (Heq : α = β) :
    Proper ((≡) ==> (≡)) (psh_conv X Heq).
  Proof. destruct Heq; intros ???; done. Qed.
  Lemma psh_setoid_conv {X : PreSheaf (OrdCat SI)}
    {α β : SI} (Heq : α = β) (x : X ₒ α) :
    psh_conv X Heq x ≡ setoid_conv (f_equal (X ₒ) Heq) x.
  Proof. destruct Heq; done. Qed.
  Lemma psh_exp_push_conv (X Y : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ X) Y) {β} (Hle : β ⪯ α) (x : X ₒ β)
    {γ} (Heq : β = γ) :
    psh_conv Y Heq ((η ₙ β) (Hle, x)) ≡ (η ₙ γ) (le_conv_l Heq Hle, psh_conv X Heq x).
  Proof. destruct Heq; done. Qed.

  Lemma psh_is_lim_side_setoid_conv {J} {F : functor J Setoid}
    {X} (il : is_limit F X) δ {Y : setoid} (Heq : Y = X) (y : Y) :
  ic_side (il_is_cone il) δ (setoid_conv Heq y) ≡
  ic_side (il_is_cone (is_limit_trans (C := Setoid) (eq_sym Heq) il)) δ y.
  Proof. destruct Heq; done. Qed.

  Record fx_raw (X : PreSheaf (OrdCat SI)) (dsp : downset_pred SI) := Mkfxr
    { fxr_map :> ∀ α : downset dsp, X ₒ (α : SI);
      fxr_map_commutes : ∀ (β α : downset dsp) (Hβα : β ⪯ α),
        fxr_map β ≡ (X ₕ Hβα) (fxr_map α);
    }.
  Global Arguments Mkfxr {_ _} _ _.
  Global Arguments fxr_map {_ _} _ _.
  Global Arguments fxr_map_commutes {_ _} _ [_ _] _.

  Lemma fx_raw_applied_eq {X : PreSheaf (OrdCat SI)} {dsp : downset_pred SI}
    (fx : fx_raw X dsp) (α : SI) (Hα Hα' : dsp α) :
    fx (MkDS Hα) ≡ fx (MkDS Hα').
  Proof. replace Hα with Hα'; first done. apply proof_irrelevance. Qed.

  Program Definition fx_raw_down_le
    (X : PreSheaf (OrdCat SI)) {dsp : downset_pred SI}
    (fx : fx_raw X dsp) {α} (Hin : dsp α) : fx_raw X (le_dsp α) :=
  Mkfxr (λ β, fx (MkDS (dsp_pred_downwards _ (ds_in_dsp β) Hin))) _.
  Next Obligation.
    repeat intros ????? β γ ?; rewrite /=.
    rewrite -(@fxr_map_commutes _ _ fx
                (MkDS (dsp_pred_downwards _ (ds_in_dsp β) Hin))
                (MkDS (dsp_pred_downwards _ (ds_in_dsp γ) Hin))) //.
  Qed.

  Program Definition fx_raw_down_lt
    (X : PreSheaf (OrdCat SI)) {dsp : downset_pred SI}
    (fx : fx_raw X dsp) {α} (Hin : dsp α) : fx_raw X (lt_dsp α) :=
  Mkfxr (λ β, fx (MkDS (dsp_pred_downwards _
    (index_lt_le_subrel _ _ (ds_in_dsp β)) Hin))) _.
  Next Obligation.
    repeat intros ????? β γ ?; rewrite /=.
    rewrite -(@fxr_map_commutes _ _ fx
     (MkDS (dsp_pred_downwards _
              (index_lt_le_subrel _ _ (ds_in_dsp β)) Hin))
     (MkDS (dsp_pred_downwards _
              (index_lt_le_subrel _ _ (ds_in_dsp γ)) Hin))) //.
  Qed.

  Definition fx_raw_zero (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X) : X ₒ zero :=
    (η ₙ zero)
      (index_zero_minimum _,
       setoid_conv (eq_sym (later_func_o_map_zero X)) ()).

  Lemma fx_raw_zero_ext X
    {α} (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {α'} (η' : natural (yoneda α' ×ₒ (later ₒ X)) X) :
    (∀ Hle Hle' x, (η ₙ zero) (Hle, x) ≡ (η' ₙ zero) (Hle', x)) →
    fx_raw_zero X η ≡ fx_raw_zero X η'.
  Proof. rewrite /fx_raw_zero; intros ->; done. Qed.

  Lemma fx_raw_zero_ext' X {α} (η η' : natural (yoneda α ×ₒ (later ₒ X)) X) :
    (η ₙ zero ≡ η' ₙ zero) →
    fx_raw_zero X η ≡ fx_raw_zero X η'.
  Proof.
    intros Heq; apply fx_raw_zero_ext; intros ???; rewrite Heq; by f_equiv.
  Qed.

  Program Definition fx_raw_succ (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {β} (Hβ : succ β ⪯ α) (x : X ₒ β) : X ₒ (succ β) :=
    (η ₙ (succ β))
      (Hβ, setoid_conv (eq_sym (later_func_o_map_succ X β)) x).

  Lemma fx_raw_succ_ext X
    {α} (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {α'} (η' : natural (yoneda α' ×ₒ (later ₒ X)) X)
    {β} (Hβ : succ β ⪯ α) (Hβ' : succ β ⪯ α') x y :
    (∀ Hle Hle' x, (η ₙ (succ β)) (Hle, x) ≡ (η' ₙ (succ β)) (Hle', x)) →
    x ≡ y → fx_raw_succ X η Hβ x ≡ fx_raw_succ X η' Hβ' y.
  Proof. rewrite /fx_raw_succ; intros -> ->; f_equiv; split; done. Qed.

  Lemma fx_raw_succ_ext' X {α} (η η' : natural (yoneda α ×ₒ (later ₒ X)) X)
    {β} (Hβ Hβ' : succ β ⪯ α) x y :
    (η ₙ (succ β) ≡ η' ₙ (succ β)) →
    x ≡ y → fx_raw_succ X η Hβ x ≡ fx_raw_succ X η' Hβ' y.
  Proof.
    intros Heq; apply fx_raw_succ_ext; intros ???; rewrite Heq; by f_equiv.
  Qed.

  Global Instance fx_raw_succ_proper (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X) {β} (Hβ : succ β ⪯ α) :
    Proper ((≡) ==> (≡)) (fx_raw_succ X η Hβ).
  Proof. repeat intros ?; eapply fx_raw_succ_ext'; done. Qed.

  Global Instance fx_raw_succ_proper' (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X) β :
    Proper ((≡) ==> (≡) ==> (≡)) (fx_raw_succ X η (β := β)).
  Proof. repeat intros ?; eapply fx_raw_succ_ext'; done. Qed.

  Program Definition fx_raw_cone (X : PreSheaf (OrdCat SI)) α
    (fx : fx_raw X (lt_dsp α)) : cone (lift_func (lt_dsp α) X) :=
    MkCone (1ₒ) (λ j, λset _, fx j) _.
  Next Obligation. repeat intros ?; apply fxr_map_commutes. Qed.
  Fail Next Obligation.

  Definition fx_raw_lim (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {β : limit_idx SI} (Hβ : β ⪯ α) (fx : fx_raw X (lt_dsp β)) : X ₒ (β : SI) :=
    (η ₙ (β : SI))
      (Hβ,
       setoid_conv
         (eq_sym (later_func_o_map_lim X β))
         (cone_hom_map
            (bang
               (term_is_terminal (complete (lift_func (lt_dsp β) X)))
               (fx_raw_cone X β fx))
            ())).

  Lemma fx_raw_lim_ext (X : PreSheaf (OrdCat SI)) {α} (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {α'} (η' : natural (yoneda α' ×ₒ (later ₒ X)) X)
    {β : limit_idx SI} (Hβ : β ⪯ α) (Hβ' : β ⪯ α') (fx fx' : fx_raw X (lt_dsp β)) :
    (∀ Hle Hle' x, (η ₙ (β : SI)) (Hle, x) ≡ (η' ₙ (β : SI)) (Hle', x)) →
    (∀ γ (Hγ : γ ≺ β), fx (MkDS (lt_dsp β) Hγ) ≡ fx' (MkDS (lt_dsp β) Hγ)) →
    fx_raw_lim X η Hβ fx ≡ fx_raw_lim X η' Hβ' fx'.
  Proof.
    rewrite /fx_raw_lim; intros Heq Hfxfx'.
    rewrite (Heq Hβ Hβ').
    repeat f_equiv.
    apply (hom_to_limit_unique _ _ _
             (limiting_cone_is_limit
                (term_is_terminal (complete (lift_func (lt_dsp β) X))))
             (cone_is_cone (fx_raw_cone X β fx))).
    - intros ????; rewrite //=.
    - intros [] ???; rewrite /= Hfxfx' //.
  Qed.

  Lemma fx_raw_lim_ext' (X : PreSheaf (OrdCat SI)) {α}
    (η η': natural (yoneda α ×ₒ later_func X) X)
    {β : limit_idx SI} (Hβ Hβ' : β ⪯ α) (fx fx' : fx_raw X (lt_dsp β)) :
    (η ₙ (β : SI) ≡ η' ₙ (β : SI)) →
    (∀ γ (Hγ : γ ≺ β), fx (MkDS (lt_dsp β) Hγ) ≡ fx' (MkDS (lt_dsp β) Hγ)) →
    fx_raw_lim X η Hβ fx ≡ fx_raw_lim X η' Hβ' fx'.
  Proof.
    intros Heq; apply fx_raw_lim_ext; intros ???; rewrite Heq; by f_equiv.
  Qed.

  Definition fx_raw_compat_zero (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {dsp} (fx : fx_raw X dsp) (Hz : dsp zero) : Prop :=
    fx (MkDS Hz) ≡ fx_raw_zero X η.

  Definition fx_raw_compat_succ (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {dsp} (fx : fx_raw X dsp) {β}
    (Hsβ : dsp (succ β)) (Hβα : succ β ⪯ α) : Prop :=
    fx (MkDS Hsβ) ≡
        fx_raw_succ X η Hβα
         (fx (MkDS (dsp_pred_downwards _
           (index_lt_le_subrel _ _ (index_succ_greater β)) Hsβ))).

  Definition fx_raw_compat_lim (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {dsp} (fx : fx_raw X dsp) {β : limit_idx SI}
    (Hβ : dsp β) (Hβα : β ⪯ α) : Prop :=
    fx (MkDS Hβ) ≡ fx_raw_lim X η Hβα (fx_raw_down_lt X fx Hβ).

  Program Definition fx_raw_compat (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {dsp} (fx : fx_raw X dsp) :
    index_rect (λ β, dsp β → β ⪯ α → Prop) :=
    MkIR
      (λ Hz _, fx (MkDS Hz) ≡ fx_raw_zero X η)
      (λ β _ Hsβ Hsβ',
        fx (MkDS Hsβ) ≡
        fx_raw_succ X η Hsβ'
         (fx (MkDS (dsp_pred_downwards _
           (index_lt_le_subrel _ _ (index_succ_greater β)) Hsβ))))
      (λ β _ Hβ Hsβ',
        fx (MkDS Hβ) ≡ fx_raw_lim X η Hsβ' (fx_raw_down_lt X fx Hβ))
      _.
  Next Obligation.
    split; last reflexivity.
    intros β Hβ1 Hβ2 ?; simpl.
    destruct β as [β Hβ2' Hβ1']; simpl in *.
    replace Hβ1 with Hβ1' by apply proof_irrelevance.
    replace Hβ2 with Hβ2' by apply proof_irrelevance.
      reflexivity.
  Qed.

  Lemma fx_raw_compat_equiv (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X)
    {dsp} (fx : fx_raw X dsp) {dsp'} (fx' : fx_raw X dsp')
    {β} (Hβid : dsp β) (Hβid' : dsp' β) (Hβle : β ⪯ α) :
    (∀ γ (Hγ : dsp γ) (Hγ' : dsp' γ), fx (MkDS Hγ) ≡ fx' (MkDS Hγ')) →
    fx_raw_compat X η fx β Hβid Hβle ↔ fx_raw_compat X η fx' β Hβid' Hβle.
  Proof.
    intros Hfxfx'.
    destruct β as [|β|β] using index_destruct; simpl_index_rect.
    - rewrite /fx_raw_compat_zero Hfxfx' //.
    - rewrite /fx_raw_compat_succ !Hfxfx' //.
    - rewrite /fx_raw_compat_lim Hfxfx'.
      f_equiv.
      rewrite fx_raw_lim_ext'; [done|done|].
      intros ??; rewrite /fx_raw_down_lt /= Hfxfx' //.
  Qed.

  Record fx_data (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) (dsp : downset_pred SI) := Mkfxd
    { fxd_fx :> fx_raw X dsp;
      fxd_compat : ∀ β Hβid Hβle, fx_raw_compat X η fxd_fx β Hβid Hβle;
    }.
  Global Arguments Mkfxd {_ _ _ _} _ _.
  Global Arguments fxd_fx {_ _ _ _} _.
  Global Arguments fxd_compat {_ _ _ _} _ [_] _ _.

  Local Opaque setoid_complete setoid_lim_side.

  (* TODO: move *)
  Tactic Notation "eta_expand_equation" uconstr(a) :=
    match goal with
      |- _ ≡ _ =>
        pattern a;
        match goal with
        | |- (λ z : ?T, ?A ≡ ?B) _ =>
            let Hf := fresh "Hf" in
            unshelve eassert ((λset z : T, A) ≡ (λset z : T, B)) as Hf;
            last by eapply Hf
        end
    end.

  Tactic Notation "eta_expand_equation" uconstr(a) "of" "type" uconstr(T) :=
    match goal with
      |- _ ≡ _ =>
        pattern a;
        match goal with
        | |- (λ z, ?A ≡ ?B) _ =>
            let Hf := fresh "Hf" in
            unshelve eassert ((λset z : T, A) ≡ (λset z : T, B)) as Hf;
            last by eapply Hf
        end
    end.

  Lemma fx_data_succ_back (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X) {dsp : downset_pred SI}
    (fxd : fx_data X η dsp) :
    ∀ (β : downset dsp) (Hsβ : succ β ⪯ α),
      (X ₕ (index_lt_le_subrel _ _ (index_succ_greater β)))
        (fx_raw_succ X η Hsβ (fxd β)) ≡ fxd β.
  Proof.
    intros [β Hβid] Hsβ; simpl in *.
    pose proof (fxd_compat fxd) as Hcmp.
    induction β as [|β IHβ|β IHβ] using index_ind;
      specialize (Hcmp _ Hβid);
      simpl_index_rect in Hcmp; simpl in Hcmp.
    - rewrite Hcmp; last by auto.
      rewrite /fx_raw_zero /fx_raw_succ /= -(psh_naturality η).
      f_equiv; split; simpl; first done.
      apply setoid_conv_sym; done.
    - assert (succ β ⪯ α) as Hβα.
      { apply index_succ_le; done. }
      rewrite (Hcmp Hβα).
      rewrite /fx_raw_succ -(psh_naturality η) /=.
      f_equiv; split; simpl; first done.
      rewrite -{2}(IHβ _ Hβα).
      rewrite /fx_raw_succ /=.
      match goal with
      |- context ctx [setoid_fun_map _ _ (η ₙ succ β) ?B] =>
        remember (setoid_fun_map _ _ (η ₙ succ β) B) as s;
        rewrite -Heqs; clear Heqs
      end.
      eta_expand_equation s; [intros ?? ->; done|intros ?? ->; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X (succ β))
               (cone_is_cone (cone_at X (succ β) (lt_dsp (succ β))
                 (in_lt_dsp_le (reflexivity (succ β)))))).
      + intros ??? ->; rewrite /=.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        do 2 f_equiv; apply proof_irrel.
      + intros ??? ->; rewrite /=.
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite -psh_h_map_comp.
        do 2 f_equiv; apply proof_irrel.
    - assert (β ⪯ α) as Hβα.
      { eapply index_lt_le_subrel, index_lt_le_trans;
          [apply index_succ_greater|done]. }
      rewrite (Hcmp Hβα).
      rewrite /fx_raw_lim -(psh_naturality η) /=.
      f_equiv; split; simpl; first done.
      eta_expand_equation () of type terminal_setoid;
        [intros [] [] _; done|intros [] [] _; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X β)
               (cone_is_cone (fx_raw_cone X β (fx_raw_down_lt X fxd Hβid)))).
      + intros δ [] [] _; simpl in *.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        assert (succ δ ⪯ β) as Hsδ.
        { apply index_lt_le_subrel, limit_index_is_limit, (ds_in_dsp δ). }
        assert (succ δ ⪯ α) as Hsδα.
        { etrans; [done|apply Hβα]. }
        match goal with
          |- _ ≡ setoid_fun_map _ _ (X ₕ ?B) _ =>
            setoid_replace B with
            (transitivity (index_lt_le_subrel _ _ (index_succ_greater _)) Hsδ)
            by done
        end.
        rewrite h_map_comp /=.
        rewrite -(IHβ _ (ds_in_dsp δ) _ Hsδα).
        f_equiv.
        rewrite -(psh_naturality η) /=.
        rewrite /(fx_raw_succ X η Hsδα).
        f_equiv; split; simpl; first reflexivity.
        rewrite /proj_cone_hom /=.
        rewrite later_func_o_map_is_limit_succ.
        rewrite bang_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        f_equiv.
        rewrite later_func_o_map_is_limit_lim /=.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite_cone_hom_commutes_back; simpl.
        apply fx_raw_applied_eq.
      + intros δ [] [] _; simpl in *.
        rewrite psh_is_lim_side_setoid_conv eq_sym_involutive /=.
        match goal with
        | |- context [setoid_fun_map _ _ (ic_side _ ?j)
                        (setoid_fun_map _ _ (cone_hom_map ?c) _)] =>
            pose proof (setoid_cone_hom_commutes c j) as Hcheq;
            simpl in Hcheq; rewrite Hcheq; clear Hcheq
        end.
        f_equiv; last done.
        rewrite trans_side_of_is_limit_trans.
        rewrite later_func_o_map_is_limit_lim /=.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite -hom_trans_trans eq_trans_sym_inv_l /= hom_trans_refl //=.
  Qed.

  Lemma fx_data_lim_back (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {β : limit_idx SI} (Hβ : β ⪯ α)
    (fxd : fx_data X η (lt_dsp β))
    {γ} (Hγβ : γ ≺ β) :
      (X ₕ (index_lt_le_subrel _ _ Hγβ))
        (fx_raw_lim X η Hβ fxd) ≡ fxd (MkDS (lt_dsp _) Hγβ).
  Proof.
    pose proof (fxd_compat fxd) as Hcmp.
    induction γ as [|γ IHγ|γ IHγ] using index_strong_ind;
      specialize (Hcmp _ Hγβ);
      simpl_index_rect in Hcmp; simpl in Hcmp.
    - rewrite Hcmp; last by auto.
      rewrite /fx_raw_zero /fx_raw_succ /= -(psh_naturality η).
      f_equiv; split; simpl; first done.
      apply setoid_conv_sym; done.
    - assert (succ γ ⪯ α) as Hsγα.
      { eapply index_lt_le_subrel, index_lt_le_trans; eassumption. }
      rewrite (Hcmp Hsγα) /fx_raw_succ.
      rewrite -IHγ // -!(psh_naturality η) /=.
      f_equiv; split; simpl; first done.
      eta_expand_equation () of type terminal_setoid;
        [intros [] [] _; done|intros [] [] _; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X (succ γ))
               (cone_is_cone (fx_raw_cone X (succ γ) (fx_raw_down_lt X fxd Hγβ)))).
      + intros ??? ->; rewrite /=.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite later_func_o_map_is_limit_lim.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite_cone_hom_commutes_back; simpl.
        apply fx_raw_applied_eq.
      + intros δ' [] [] _; rewrite /=.
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite -IHγ; last first.
        { by apply index_succ_iff_proj_r2l, (ds_in_dsp δ'). }
        rewrite /fx_raw_lim -!(psh_naturality η) /=.
        f_equiv; split; simpl; first done.
        eta_expand_equation () of type terminal_setoid;
          [intros [] [] _; done|intros [] [] _; done|].
        apply (hom_to_limit_unique _ _ _
                 (later_func_o_map_is_limit X δ')
                 (cone_is_cone (fx_raw_cone X δ'
                   (fx_raw_down_lt X fxd (transitivity (ds_in_dsp δ') Hγβ))))).
        * intros δ'' [] [] _; rewrite /=.
          rewrite_cone_hom_commutes_back; simpl.
          rewrite later_func_o_map_is_limit_lim.
          rewrite trans_side_of_is_limit_trans /=.
          rewrite hom_trans_setoid_conv' /=.
          rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
          rewrite_cone_hom_commutes_back; simpl.
          apply fx_raw_applied_eq.
      * intros δ'' [] [] _; rewrite /=.
        repeat (rewrite_cone_hom_commutes_back; simpl).
        rewrite later_func_o_map_is_limit_lim.
        rewrite trans_side_of_is_limit_trans /=.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite_cone_hom_commutes_back; simpl.
        apply fx_raw_applied_eq.
    - assert (γ ⪯ α) as Hγα.
      { eapply index_lt_le_subrel, index_lt_le_trans; done. }
      rewrite (Hcmp Hγα).
      rewrite /fx_raw_lim /fx_raw_succ -(psh_naturality η) /=.
      f_equiv; split; simpl; first done.
      eta_expand_equation () of type terminal_setoid;
          [intros [] [] _; done|intros [] [] _; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X γ)
               (cone_is_cone (fx_raw_cone X γ (fx_raw_down_lt X fxd Hγβ)))).
      + intros δ [] [] _; simpl in *.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite later_func_o_map_is_limit_lim.
        rewrite trans_side_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite_cone_hom_commutes_back; simpl.
        apply fx_raw_applied_eq.
      + intros δ [] [] _; simpl in *.
        rewrite later_func_o_map_is_limit_lim.
        rewrite trans_side_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite_cone_hom_commutes_back; done.
  Qed.

  Lemma fx_data_agree (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) (dsp dsp' : downset_pred SI)
    (fx : fx_data X η dsp) (fx' : fx_data X η dsp') {β}
    (Hle : β ⪯ α) (Hβ : dsp β) (Hβ' : dsp' β) :
    fx (MkDS Hβ) ≡ fx' (MkDS Hβ').
  Proof.
    induction β as [|β IHβ|β IHβ]using index_ind;
      pose proof (fxd_compat fx Hβ) as Hcmp;
      pose proof (fxd_compat fx' Hβ') as Hcmp';
      simpl_index_rect in Hcmp; simpl_index_rect in Hcmp'.
    - rewrite Hcmp // Hcmp' //.
    - rewrite (Hcmp Hle) (Hcmp' Hle).
      rewrite IHβ; first reflexivity.
      by etrans; first apply index_lt_le_subrel, index_succ_greater.
    - rewrite (Hcmp Hle) (Hcmp' Hle).
      rewrite fx_raw_lim_ext'; [done|done|].
      intros ??; rewrite /fx_raw_down_lt /=.
      apply IHβ; first done.
      by etrans; first apply index_lt_le_subrel.
  Qed.

  Program Definition fx_data_zero (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) :
    fx_data X η (le_dsp zero) :=
    Mkfxd (Mkfxr
      (λ δ, psh_conv X (eq_sym (le_zero_zero _ (ds_in_dsp δ)))
        (fx_raw_zero X η)) _) _.
  Next Obligation.
    intros ?? η ???; simpl.
    rewrite !psh_setoid_conv.
    apply setoid_conv_sym.
    rewrite -!eq_sym_map_distr.
    rewrite -hom_trans_setoid_conv'.
    rewrite hom_trans_setoid_conv.
    rewrite !eq_sym_map_distr.
    rewrite -psh_setoid_conv hom_trans_setoid_conv'.
    rewrite /fx_raw_zero.
    rewrite psh_exp_push_conv /=.
    rewrite -(psh_naturality η).
    rewrite -psh_setoid_conv.
    rewrite psh_exp_push_conv /=.
    f_equiv; split; first done.
    rewrite /= !psh_setoid_conv.
    apply setoid_conv_sym; done.
  Qed.
  Next Obligation.
    intros ???? Hβid ?; simpl.
    pose proof (le_zero_zero _ Hβid); subst.
    simpl_index_rect; simpl.
    rewrite /fx_raw_zero psh_exp_push_conv.
    f_equiv; split; simpl; first done.
    apply setoid_conv_sym; done.
  Qed.
  Fail Next Obligation.

  Program Definition fx_data_succ (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) {β} (Hsβ : succ β ⪯ α)
    (fxd : fx_data X η (le_dsp β)) : fx_data X η (le_dsp (succ β)) :=
    Mkfxd (Mkfxr
      (λ δ, match le_succ_dec (ds_in_dsp δ) return X ₒ (δ : SI) with
            | left Hle => fxd (MkDS (le_dsp β) Hle)
            | right Heq =>
                psh_conv X (eq_sym Heq)
                  (fx_raw_succ X η Hsβ
                     (fxd (MkDS (le_dsp β) (reflexivity _))))
            end) _) _.
  Next Obligation.
    intros ????? fxd γ γ' Hγγ'; simpl in *.
    destruct le_succ_dec as [Hle|Heq];
      destruct le_succ_dec as [Hle'|Heq'].
    - rewrite -(@fxr_map_commutes _ _ (fxd_fx fxd)
        (MkDS (le_dsp β) Hle) (MkDS (le_dsp β) Hle')); done.
    - rewrite psh_conv_hom_action.
      setoid_replace (le_conv_r (eq_sym (eq_sym Heq')) Hγγ') with
        (transitivity Hle
           (index_lt_le_subrel _ _ (index_succ_greater _)))
        by done.
      rewrite h_map_comp /=.
      etrans; first apply (@fxr_map_commutes _ _ fxd (MkDS (le_dsp β) Hle) (MkDS (le_dsp β)
        (reflexivity _)) Hle).
      f_equiv.
      rewrite (fx_data_succ_back X η fxd (MkDS (reflexivity _))) //.
    - exfalso.
      apply (index_le_lt_contradict γ γ'); first done.
      eapply index_le_lt_trans; last by rewrite Heq; apply index_succ_greater.
      done.
    - assert (γ = γ') as -> by by apply downset_eq; rewrite Heq Heq' //.
      setoid_replace Hγγ' with (reflexivity _ : γ' ⪯ γ') by done.
      rewrite h_map_id /=.
      apply psh_conv_sym.
      rewrite -psh_conv_trans.
      replace Heq' with Heq by apply proof_irrel.
      rewrite eq_trans_sym_inv_r //=.
  Qed.
  Next Obligation.
    intros ??? γ Hγ fxd β Hsβ Hβα; simpl.
    destruct (le_succ_dec Hsβ) as [Hle| ->].
    { pose proof (fxd_compat fxd Hle Hβα) as Hcmp.
      rewrite fx_raw_compat_equiv in Hcmp; first exact Hcmp.
      intros γ' Hγ'id Hsγγ'; rewrite /=; destruct le_succ_dec as [|Heq];
        first by apply fx_raw_applied_eq.
      exfalso.
      apply (index_le_lt_contradict γ' γ); first done.
      rewrite Heq; apply index_succ_greater. }
    simpl_index_rect; rewrite /fx_raw_compat_succ /=.
    assert (¬ (succ γ ⪯ γ)).
    { intros Hle; apply index_succ_le_lt in Hle; eapply index_lt_irrefl; done. }
    destruct (le_succ_dec Hsβ) as [|Heq]; first done.
    destruct le_succ_dec as [|Heq'].
    - replace Heq with (eq_refl (succ γ)) by apply proof_irrel.
      simpl; f_equiv; first done.
      apply fx_raw_applied_eq.
    - exfalso.
      eapply (index_lt_irrefl γ), index_succ_le_lt; rewrite {2}Heq'; done.
  Qed.
  Fail Next Obligation.

  Program Definition fx_data_glue (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) {β}
    (Hle : β ⪯ α)
    (fxds : ∀ γ, γ ≺ β → fx_data X η (le_dsp γ)) : fx_data X η (lt_dsp β) :=
    Mkfxd (Mkfxr (λ γ, fxds _ (ds_in_dsp γ) (MkDS (reflexivity _))) _) _.
  Next Obligation.
    intros ??? β Hβ ?; revert Hβ; simpl in *.
    intros Hβα γ' γ Hγ'γ.
    rewrite -(@fxr_map_commutes _ _ (fxds γ (ds_in_dsp γ))
      (MkDS (le_dsp γ) Hγ'γ) (MkDS (reflexivity _)) Hγ'γ).
    apply fx_data_agree.
    etrans; first done.
    etrans; first apply index_lt_le_subrel, (ds_in_dsp γ); done.
  Qed.
  Next Obligation.
    intros ??? β Hβ fxds γ Hγid Hγle.
    rewrite fx_raw_compat_equiv.
    { apply (fxd_compat (fxds γ Hγid) (β := γ) (reflexivity _) Hγle). }
    simpl; intros γ' Hγ'1 Hγ'2; apply fx_data_agree.
    etrans; done.
  Qed.
  Fail Next Obligation.

  Program Definition fx_data_lim' (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) {β : limit_idx SI} (Hβ : β ⪯ α)
    (fxd : fx_data X η (lt_dsp β)) : fx_data X η (le_dsp β) :=
    Mkfxd (Mkfxr
      (λ δ, match index_le_lt_eq_dec _ _ (ds_in_dsp δ) return X ₒ (δ : SI) with
            | left Hlt => fxd (MkDS (lt_dsp β) Hlt)
            | right Heq => psh_conv X (eq_sym Heq) (fx_raw_lim X η Hβ fxd)
            end) _) _.
  Next Obligation.
    intros ??? β ?? γ γ' Hγγ'; simpl.
    destruct (index_le_lt_eq_dec γ) as [Hltγ|Heqγ];
      destruct (index_le_lt_eq_dec γ') as [Hltγ'|Heqγ'].
    - rewrite -(@fxr_map_commutes _ _ fxd
        (MkDS (lt_dsp _) Hltγ) (MkDS (lt_dsp _) Hltγ')) //.
    - rewrite psh_conv_hom_action.
      replace (le_conv_r (eq_sym (eq_sym Heqγ')) Hγγ') with
        (index_lt_le_subrel _ _ Hltγ) by apply proof_irrel.
      rewrite fx_data_lim_back //.
    - exfalso.
      apply (index_le_lt_contradict γ γ'); [done|rewrite Heqγ //].
    - rewrite psh_conv_hom_action psh_conv_sym.
      rewrite psh_conv_hom_action'.
      match goal with
        |- context [_ ₕ ?A] =>
          replace A with (reflexivity (β : SI)) by apply proof_irrel
      end.
      rewrite h_map_id //.
  Qed.
  Next Obligation.
    intros ??? β ?? γ Hγid Hγα; simpl.
    destruct (index_le_lt_eq_dec _ _ Hγid) as [Hlt|Heq].
    - pose proof (fxd_compat fxd Hlt Hγα) as Hcmp.
      rewrite fx_raw_compat_equiv in Hcmp; first exact Hcmp.
      intros γ' Hγ'id Hsγγ'; rewrite /=; destruct index_le_lt_eq_dec as [|Heq];
        first by apply fx_raw_applied_eq.
      exfalso; apply (index_lt_irrefl γ'); rewrite {2}Heq //.
    - subst.
      simpl_index_rect; rewrite /fx_raw_compat_lim /=.
      destruct index_le_lt_eq_dec as [|Heq].
      { exfalso; eapply index_lt_irrefl; eassumption. }
      replace Heq with (eq_refl (β : SI)) by apply proof_irrel.
      simpl.
      apply fx_raw_lim_ext'; first done.
      intros ??; simpl.
      destruct index_le_lt_eq_dec as [|Heq']; first by apply fx_raw_applied_eq.
      exfalso; eapply (index_lt_irrefl γ); rewrite {2}Heq' //.
  Qed.
  Fail Next Obligation.

  Definition fx_data_lim (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) {β : limit_idx SI} (Hβ : β ⪯ α)
    (fxds : ∀ γ, γ ≺ β → γ ⪯ α → fx_data X η (le_dsp γ)) : fx_data X η (le_dsp β) :=
    fx_data_lim' X η Hβ
      (fx_data_glue X η Hβ
         (λ γ Hγ, fxds γ Hγ (transitivity (index_lt_le_subrel _ _ Hγ) Hβ))).

  Program Definition make_fx_data (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) :
    index_rect (λ β, β ⪯ α → fx_data X η (le_dsp β)) :=
    MkIR
      (λ _, fx_data_zero X η)
      (λ _ f Hle, fx_data_succ X η Hle (f (index_succ_le _ _ Hle)))
      (λ _ f Hle, fx_data_lim X η Hle f)
      _.
  Next Obligation.
    split.
    - intros β Hβ1 Hβ2 ?; simpl.
      destruct β as [β Hβ2' Hβ1']; simpl in *.
      replace Hβ1 with Hβ1' by apply proof_irrel.
      replace Hβ2 with Hβ2' by apply proof_irrelevance.
      reflexivity.
    - intros β f g Hfg; simpl.
      destruct β as [β Hβ2' Hβ1']; simpl in *.
      extensionality Hle.
      rewrite /fx_data_lim /=.
      repeat f_equal.
      extensionality γ; extensionality Hγ; rewrite Hfg //.
  Qed.

  Lemma make_fx_data_ext (X : PreSheaf (OrdCat SI))
    {α} (η : natural (yoneda α ×ₒ (later ₒ X)) X)
    {α'} (η' : natural (yoneda α' ×ₒ (later ₒ X)) X)
    β Hβα Hβα' γ :
    (∀ δ, δ ⪯ β → ∀ Hle Hle' x, (η ₙ δ) (Hle, x) ≡ (η' ₙ δ) (Hle', x)) →
    make_fx_data X η β Hβα γ ≡ make_fx_data X η' β Hβα' γ.
  Proof.
    revert Hβα Hβα' γ.
    induction β as [|β IHβ|β IHβ] using index_ind;
      intros Hβα Hβα' γ Hηη'.
    - simpl_index_rect; rewrite /fx_data_zero /=.
      rewrite fx_raw_zero_ext; first done.
      apply Hηη'; done.
    - simpl_index_rect; rewrite /fx_data_succ /=.
      destruct le_succ_dec.
      + rewrite IHβ; first done.
        intros; apply Hηη'.
        apply index_lt_le_subrel, index_succ_iff; done.
      + f_equiv.
        rewrite fx_raw_succ_ext; [done|apply Hηη'; done|].
        rewrite IHβ; first done.
        intros; apply Hηη'.
        apply index_lt_le_subrel, index_succ_iff; done.
    - simpl_index_rect; rewrite /fx_data_lim /=.
      destruct index_le_lt_eq_dec.
      + rewrite IHβ; [done|done|].
        intros; apply Hηη';
          by etrans; last by apply index_lt_le_subrel.
      + f_equiv.
        apply fx_raw_lim_ext; simpl; first by apply Hηη'.
        repeat intros ?; rewrite IHβ; [done|done|].
        intros; apply Hηη';
          by etrans; last by apply index_lt_le_subrel.
  Qed.

  Lemma make_fx_data_ext' (X : PreSheaf (OrdCat SI)) {α}
    (η η' : natural (yoneda α ×ₒ later_func X) X) β Hle γ :
    (∀ δ, δ ⪯ β → η ₙ δ ≡ η' ₙ δ) →
    make_fx_data X η β Hle γ ≡ make_fx_data X η' β Hle γ.
  Proof.
    intros Heq; apply make_fx_data_ext;
      intros ?????; rewrite Heq; [f_equiv|]; done.
  Qed.

  Lemma make_fx_data_stable (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) β Hle β' Hle' {γ} (Hγ : γ ⪯ β) (Hγ' : γ ⪯ β')
    (Hβ'β : β' ⪯ β) :
    make_fx_data X η β Hle (MkDS (le_dsp _) Hγ) ≡ make_fx_data X η β' Hle' (MkDS (le_dsp _) Hγ').
  Proof.
    revert Hle β' Hβ'β Hle' γ Hγ Hγ'.
    induction (index_lt_wf _ β) as [β _ IHβ].
    specialize (λ z β' Hlt Hle , IHβ z Hlt Hle β').
    intros Hle β' Hβ'β Hle' γ Hγ Hγ'.
    destruct (index_le_lt_eq_dec _ _ Hβ'β) as [Hβ'ltβ| ->]; last first.
    { replace Hγ with Hγ' by apply proof_irrel.
      replace Hle with Hle' by apply proof_irrel.
      apply make_fx_data_ext'; done. }
    destruct (index_is_zero β) as [->| Hnz].
    { exfalso; eapply index_lt_zero_is_normal; done. }
    destruct (index_dec_limit β) as [[δ ->]|Hil].
    - simpl_index_rect; rewrite /fx_data_succ /=.
      destruct le_succ_dec as [Hγ'2| ->]; simpl.
      + rewrite (IHβ δ β'); [done|by apply index_succ_greater|].
        by apply index_succ_iff_proj_r2l.
      + by exfalso; eapply (index_lt_le_contradict β' (succ δ)).
    - change β with (mklimitidx β Hil Hnz : SI).
      simpl_index_rect; rewrite /fx_data_lim /=.
      destruct index_le_lt_eq_dec as [| ->].
      + rewrite (IHβ β' γ); done.
      + by exfalso; apply (index_lt_le_contradict β' β).
  Qed.

  Lemma make_fx_data_stable' (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) β Hle (γ : downset (le_dsp β)):
    make_fx_data X η β Hle γ ≡
    make_fx_data X η γ (transitivity (ds_in_dsp γ) Hle) (MkDS (le_dsp _) (reflexivity _)).
  Proof.
    destruct γ as [γ Hγ].
    rewrite -(make_fx_data_stable _ _ β _ γ) /=; done.
  Qed.

  Lemma make_fx_data_natural (X : PreSheaf (OrdCat SI)) {α}
    (η : natural (yoneda α ×ₒ later_func X) X) β (Hβα : β ⪯ α) γ (Hγβ : γ ⪯ β) δ (Hδγ : δ ⪯ γ) :
    make_fx_data X η β Hβα (MkDS (le_dsp _) (transitivity Hδγ Hγβ)) ≡
    (X ₕ Hδγ) (make_fx_data X η β Hβα (MkDS (le_dsp _) Hγβ)).
  Proof.
    revert γ Hγβ δ Hδγ.
    induction (index_lt_wf _ β) as [β _ IHβ].
    specialize (λ z γ δ Hlt Hzα Hγz, IHβ z Hlt Hzα γ Hγz δ).
    intros γ Hγβ δ Hδγ.
    destruct (index_le_lt_eq_dec _ _ Hγβ) as [Hβ'ltβ| ->].
    { rewrite !(make_fx_data_stable' _ _ β) /=.
      rewrite -IHβ; last done.
      rewrite (make_fx_data_stable' _ _ γ) /=.
      rewrite make_fx_data_ext; first done.
      intros; f_equiv; done. }
    destruct (index_is_zero β) as [->| Hnz].
    { assert (δ = zero) as -> by by apply le_zero_zero.
      replace Hδγ with (reflexivity (zero : SI))
        by by apply proof_irrel.
      rewrite h_map_id /=. apply fx_raw_applied_eq. }
    destruct (index_dec_limit β) as [[γ ->]|Hil].
    - simpl_index_rect; rewrite /fx_data_succ /=.
      destruct le_succ_dec as [Hγ'2| ->]; simpl.
      + destruct le_succ_dec.
        { exfalso; eapply index_le_lt_contradict;
            [done|by apply index_succ_greater]. }
        rewrite psh_conv_hom_action.
        replace (le_conv_r (eq_sym (eq_sym e)) Hδγ) with
          (transitivity Hγ'2 (index_lt_le_subrel _ _ (index_succ_greater γ)))
          by by apply proof_irrel.
        rewrite h_map_comp /=.
        rewrite (fx_data_succ_back _ _ _ (MkDS (reflexivity γ))).
        rewrite -IHβ; last apply index_succ_greater.
        apply fx_raw_applied_eq.
      + destruct le_succ_dec as [|Heq].
        { exfalso; eapply index_le_lt_contradict;
            [done|by apply index_succ_greater]. }
        replace Hδγ with (reflexivity (succ γ))
          by by apply proof_irrel.
        rewrite h_map_id /=.
        replace Heq with (eq_refl (succ γ))
          by apply proof_irrel.
        done.
    - change β with (mklimitidx β Hil Hnz : SI).
      simpl_index_rect; simpl.
      destruct index_le_lt_eq_dec as [Hlt| ->].
      + destruct index_le_lt_eq_dec as [|Heq].
        { exfalso; eapply index_lt_irrefl; done. }
        replace Heq with (eq_refl β) by apply proof_irrel.
        replace Hδγ with (index_lt_le_subrel _ _ Hlt)
          by by apply proof_irrel.
        rewrite (fx_data_lim_back X η
          (β := mklimitidx β Hil Hnz) Hβα (fx_data_glue X η Hβα
               (λ (γ : SI) (Hγ : γ ≺ β),
                 make_fx_data X η γ
                   (transitivity (index_lt_le_subrel γ β Hγ) Hβα))) Hlt).
        done.
      + destruct index_le_lt_eq_dec as [|Heq].
        { exfalso; eapply index_lt_irrefl; done. }
        replace Heq with (eq_refl β) by apply proof_irrel.
        simpl.
        replace Hδγ with (reflexivity β) by by apply proof_irrel.
        rewrite h_map_id; done.
        Qed.

  Program Definition fixpoint_combinator (X : PreSheaf (OrdCat SI)) : natural (X ↑ₒ (later ₒ X)) X :=
    MkNat (λ α, λset η, make_fx_data X η α (reflexivity α) (MkDS (reflexivity α))) _.
  Next Obligation. repeat intros ?; rewrite make_fx_data_ext'; done. Qed.
  Next Obligation.
    intros ? β γ Hγβ η' η ->; clear η'; simpl in *.
    rewrite -make_fx_data_natural.
    rewrite (make_fx_data_stable X η β (reflexivity _) γ Hγβ); last done.
    rewrite make_fx_data_ext; first done.
    repeat intros ?; simpl; f_equiv; done.
  Qed.

  Definition fixpoint {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X) : natural Y X :=
    (fixpoint_combinator X ∘ (transpose η)).

  Definition fixpoint_seed (X : PreSheaf (OrdCat SI)) : (later ₒ X) ₒ zero :=
    setoid_conv (eq_sym (later_func_o_map_zero X)) ().

  Lemma fixpoint_zero {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X)
    (y : Y ₒ zero) :
    (fixpoint η ₙ zero) y ≡ (η ₙ zero) (fixpoint_seed X, y).
  Proof.
    simpl; simpl_index_rect; simpl.
    rewrite /fx_data_zero /fx_raw_zero /=.
    replace (le_zero_zero zero (reflexivity zero)) with (eq_refl (zero : SI))
        by apply proof_irrel.
    rewrite /=.
    f_equiv; first done.
    f_equiv; last first.
    { replace (index_zero_minimum zero) with (reflexivity (zero: SI))
          by apply proof_irrel.
      rewrite h_map_id //. }
    apply setoid_conv_sym; done.
  Qed.

  Lemma fixpoint_succ {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X) α y :
    ((fixpoint η) ₙ (succ α)) y ≡
      (η ₙ (succ α))
       (setoid_conv (eq_sym (later_func_o_map_succ X α))
          ((fixpoint η ₙ α) ((Y ₕ (index_lt_le_subrel _ _ (index_succ_greater α))) y)), y).
  Proof.
    simpl; simpl_index_rect; simpl.
    rewrite /fx_data_succ /fx_raw_succ /=.
    destruct le_succ_dec as [Hle| Heq].
    { exfalso; eapply index_lt_le_contradict; [apply index_succ_greater|apply Hle]. }
    replace Heq with (eq_refl (succ α)) by apply proof_irrel.
    rewrite /=.
    f_equiv; first done.
    f_equiv; last by rewrite h_map_id.
    f_equiv.
    rewrite make_fx_data_ext; first done.
    intros ? Hle Hle' Hle'' ?; simpl in *.
    replace Hle' with (transitivity Hle'' (index_lt_le_subrel α (succ α) (index_succ_greater α)))
      by apply proof_irrel.
    rewrite h_map_comp; done.
  Qed.

  Program Definition fixpoint_lim_cone {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X)
    {α : SI} (y : Y ₒ (α : SI)) : cone (lift_func (lt_dsp α) X) :=
    MkCone terminal_setoid
      (λ j, λset _, (fixpoint η ₙ (j : SI)) ((Y ₕ (index_lt_le_subrel _ _ (ds_in_dsp j))) y))
      _.
  Next Obligation.
    intros ??????? h [] [] _; simpl in *.
    rewrite -make_fx_data_natural.
    rewrite (make_fx_data_stable _ _ _ _ _ h _ (reflexivity _) h).
    rewrite make_fx_data_ext; first done.
    intros ?????; simpl.
    repeat f_equiv; rewrite -!psh_h_map_comp; repeat f_equiv; done.
  Qed.

  Lemma fixpoint_lim {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X)
    (α : limit_idx SI) (y : Y ₒ (α : SI)) :
    ((fixpoint η) ₙ (α : SI)) y ≡
      (η ₙ (α : SI))
      (setoid_conv (eq_sym (later_func_o_map_lim X α))
        (cone_hom_map
           (bang (term_is_terminal (complete (lift_func (lt_dsp α) X)))
              (fixpoint_lim_cone η y)) ()), y).
  Proof.
    simpl; simpl_index_rect; simpl.
    rewrite /fx_data_lim /= /fx_raw_lim /=.
    destruct index_le_lt_eq_dec as [Hlt| Heq].
    { exfalso; eapply index_lt_irrefl; done. }
    replace Heq with (eq_refl (α : SI)) by apply proof_irrel.
    rewrite /=.
    f_equiv; first done.
    f_equiv; last by rewrite h_map_id.
    f_equiv.
    apply (hom_to_limit_unique _ _ _
                   (limiting_cone_is_limit
                      (term_is_terminal (complete (lift_func (lt_dsp α) X))))
      (cone_is_cone (fixpoint_lim_cone η y))).
    - intros ??? ->; rewrite /=.
      rewrite_cone_hom_commutes_back; simpl.
      rewrite make_fx_data_ext; first done.
      repeat intros ?; simpl; repeat f_equiv.
      rewrite -psh_h_map_comp; repeat f_equiv; done.
    - intros ??? ->; done.
    - done.
  Qed.

  Global Opaque fixpoint.

  Lemma fixpoint_unfold {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X) :
    fixpoint η ≡ η ∘ << next ₙ X ∘@{PSh (OrdCat SI)} fixpoint η, @id (PSh (OrdCat SI)) Y>>.
  Proof.
    intros α y x <-; clear x.
    induction α as [|α IHα|α IHα] using index_ind.
    - rewrite /= fixpoint_zero.
      f_equiv; split; simpl; last done.
      apply setoid_conv_sym; done.
    - rewrite /= !fixpoint_succ.
      f_equiv; split; simpl; last done.
      rewrite later_func_o_map_is_limit_succ.
      rewrite bang_of_is_limit_trans.
      rewrite hom_trans_setoid_conv' /=.
      f_equiv.
      rewrite -(psh_naturality η) /=.
      rewrite {1}IHα /=.
      f_equiv; first done.
      split; simpl; last by repeat f_equiv; apply proof_irrel.
      eta_expand_equation ((fixpoint η ₙ α)
       ((Y ₕ index_lt_le_subrel _ _ (index_succ_greater α)) y));
      [intros ?? ->; done|intros ?? ->; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X α)
               (cone_is_cone (extend_cone
                 (cone_of_is_cone (il_is_cone (later_func_o_map_is_limit X α)))
                 ((next ₙ X) ₙ α)))).
      + intros ??? ->; done.
      + intros ??? ->; rewrite /=.
        repeat (rewrite_cone_hom_commutes_back; simpl).
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        repeat f_equiv; apply proof_irrel.
    - rewrite /= fixpoint_lim.
      f_equiv; split; simpl; last done.
      rewrite later_func_o_map_is_limit_lim.
      rewrite bang_of_is_limit_trans.
      rewrite hom_trans_setoid_conv' /=.
      f_equiv.
      eta_expand_equation () of type terminal_setoid.
      apply (hom_to_limit_unique _ _ _
               (limiting_cone_is_limit
                  (term_is_terminal (complete (lift_func (lt_dsp α) X))))
               (cone_is_cone (@fixpoint_lim_cone _ _ η α y))).
      + intros ? [] [] _; done.
      + intros β [] [] _; rewrite /=.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite -psh_naturality.
        repeat f_equiv; done.
  Qed.

  Lemma fixpoint_unique' {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X)
    (FX : natural Y X) :
    FX ≡ η ∘ << next ₙ X ∘@{PSh (OrdCat SI)} FX, @id (PSh (OrdCat SI)) Y>> →
    FX ≡ fixpoint η.
  Proof.
    intros HFX α y x <-; clear x.
    induction α as [|α IHα|α IHα] using index_ind.
    - rewrite /= fixpoint_zero HFX /=.
      rewrite /fixpoint_seed.
      f_equiv; split; simpl; last done.
      apply setoid_conv_sym; done.
    - rewrite /= fixpoint_succ HFX /= -IHα.
      f_equiv; split; simpl; last done.
      rewrite psh_naturality.
      eta_expand_equation ((FX ₙ (succ α)) y);
        [intros ?? ->; done|intros ?? ->; done|].
      apply (hom_to_limit_unique _ _ _
               (later_func_o_map_is_limit X (succ α))
               (cone_is_cone
                  (cone_at X (succ α) (lt_dsp (succ α))
                     (in_lt_dsp_le (reflexivity (succ α)))))).
      + intros ??? ->; simpl.
        rewrite_cone_hom_commutes_back; simpl.
        repeat f_equiv; done.
      + intros ??? ->; rewrite /=.
        rewrite later_func_o_map_is_limit_succ.
        rewrite trans_side_of_is_limit_trans.
        rewrite hom_trans_setoid_conv' /=.
        rewrite -setoid_conv_trans eq_trans_sym_inv_r /=.
        rewrite -psh_h_map_comp /=.
        repeat f_equiv; apply proof_irrel.
    - rewrite fixpoint_lim HFX /=.
      f_equiv; first done.
      split; simpl; last done.
      rewrite later_func_o_map_is_limit_lim.
      rewrite bang_of_is_limit_trans.
      rewrite hom_trans_setoid_conv' /=.
      f_equiv.
      eta_expand_equation () of type terminal_setoid.
      apply (hom_to_limit_unique _ _ _
               (limiting_cone_is_limit
                  (term_is_terminal (complete (lift_func (lt_dsp α) X))))
               (cone_is_cone (@fixpoint_lim_cone _ _ η _ y))).
      + intros β [] [] _; simpl.
        rewrite_cone_hom_commutes_back; simpl.
        rewrite -psh_naturality.
        rewrite IHα; last apply (ds_in_dsp β).
        repeat f_equiv; done.
      + intros β [] [] _; rewrite /=.
        rewrite_cone_hom_commutes_back; simpl; done.
  Qed.

  Lemma fixpoint_unique {X Y : PreSheaf (OrdCat SI)} (η : natural ((later ₒ X) ×ₒ Y) X)
    (FX FX' : natural Y X) :
    FX ≡ η ∘ << next ₙ X ∘@{PSh (OrdCat SI)} FX, @id (PSh (OrdCat SI)) Y>> →
    FX' ≡ η ∘ << next ₙ X ∘@{PSh (OrdCat SI)} FX', @id (PSh (OrdCat SI)) Y>> →
    FX ≡ FX'.
  Proof.
    intros ? ?; rewrite (fixpoint_unique' _ FX) // (fixpoint_unique' _ FX') //.
  Qed.

End fixpoint.
