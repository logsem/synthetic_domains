From SynthDom Require Import prelude.
From SynthDom.categories Require Import category enriched.
From SynthDom Require Import stepindex.

Local Set Universe Polymorphism.
Local Unset Universe Minimization ToSet.

Open Scope category_scope.

(* FIXME: move axiom. *)
Axiom ProofIrrelevance : ∀ (P : Prop) (p q : P), p = q.
Lemma index_le_irrel : ∀ {SI : indexT} (α β : SI) (Hle Hle' : α ⪯ β), Hle = Hle'.
Proof. intros; apply ProofIrrelevance. Qed.

Program Definition OrdCat (SI : indexT) : category :=
  MkCat SI (λ α β, α ⪯ β)
    (λ _, reflexivity _)
    (λ _ _ _ f g, transitivity f g)
    (λ _ _ _ _, True) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

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
Proof. destruct ds; destruct ds'; simpl; intros ->; f_equal; apply ProofIrrelevance. Qed.

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

Section limit_at.
  Context {SI : indexT} {C : category}.

  Variable (F : functor ((OrdCat SI)ᵒᵖ) C).

  Program Definition cone_down {α β} (Hle : β ⪯ succ α) : cone (lift_func (lt_dsp β) F) :=
    MkCone (F ₒ α)
      (λ γ, F ₕ (index_succ_iff_proj_r2l _ _ _ (index_lt_le_trans _ _ _ (ds_in_dsp γ) Hle)))
      _.
  Next Obligation.
    repeat intros ?; rewrite /= -h_map_comp; f_equiv; done.
  Qed.
  Fail Next Obligation.

  Program Definition is_limit_at α : is_limit (lift_func (lt_dsp (succ α)) F) (F ₒ α) :=
    MkIsLimit _ (cone_is_cone (cone_down (reflexivity _)))
      (MkIsTerm _
         (λ cn, MkConeHom (side cn (MkDS (lt_dsp (succ α)) (index_succ_greater α))) _) _).
  Next Obligation.
    intros ?? δ; rewrite /=.
    apply (@side_commutes _ _ _ cn (MkDS (lt_dsp (succ α)) (index_succ_greater α))).
  Qed.
  Next Obligation.
    intros ? cn [f fcomm]; simpl in *.
    rewrite /equiv /cone_hom_eq /=.
    rewrite (fcomm (MkDS (lt_dsp (succ α)) (index_succ_greater α))) /=.
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
  Proof. by replace Hβ1 with Hβ2 by apply ProofIrrelevance. Qed.

  Definition proj_cone_hom {α β} (Hle : β ⪯ α) :
    cone_hom (proj_cone Hle (cone_of_is_limit (lo_map_il α))) (cone_of_is_limit (lo_map_il β)) :=
    bang (is_limit_limiting_cone (lo_map_il β)) (proj_cone Hle (cone_of_is_limit (lo_map_il α))).

  Program Definition later_func_gen : functor ((OrdCat SI)ᵒᵖ) C :=
    MkFunc lo_map (λ _ _ f, cone_hom_map (proj_cone_hom f)) _ _ _.
  Next Obligation.
  Proof. intros ?? Hle Hle' _; rewrite (index_le_irrel _ _ Hle Hle'); done. Qed.
  Next Obligation.
  Proof.
    intros ??? Hle Hle'; rewrite /=.
    apply (hom_to_limit_unique _ _ _ (lo_map_il _)
             (cone_is_cone (proj_cone _ (cone_of_is_limit (lo_map_il _))))).
    - apply (cone_hom_commutes (proj_cone_hom (transitivity Hle' Hle))).
    - intros.
      rewrite -comp_assoc -(cone_hom_commutes (proj_cone_hom Hle')) /=.
      rewrite -(cone_hom_commutes (proj_cone_hom Hle) (lift_in_lt_ds Hle' _)) /=.
      match goal with |- ?A ≡ ?B => assert (A = B) as ->; last done end.
      apply il_side_eq.
  Qed.
  Next Obligation.
  Proof.
    intros ?; rewrite /=.
    apply (hom_to_limit_unique _ _ _ (lo_map_il _)
             (cone_is_cone (proj_cone _ (cone_of_is_limit (lo_map_il _))))).
    - apply (cone_hom_commutes (proj_cone_hom (reflexivity _))).
    - intros δ; rewrite /= right_id.
      match goal with |- ?A ≡ ?B => assert (A = B) as ->; last done end.
      destruct δ; apply il_side_eq.
  Qed.
  Fail Next Obligation.

End later_func_gen.

Section later.
  Context {SI : indexT} {C : category} `{!HasTerm C} `{!Complete C}.

  Program Definition later_func_o_map_il (F : functor ((OrdCat SI)ᵒᵖ) C) α :
    {c : obj C & is_limit (lift_func (lt_dsp α) F) c} :=
    index_rec (λ α, {c : obj C & is_limit (lift_func (lt_dsp α) F) c})
      (existT _ (is_limit_at_zero F (term_is_terminal (term_of C))))
      (λ α _, existT _ (is_limit_at F α))
      (λ α _, existT _ (limiting_cone_is_limit (term_is_terminal (complete _))))
      α.
  Local Instance: ∀ {SI C} `{!Complete C} (F : functor ((OrdCat SI)ᵒᵖ) C),
      @index_rec_lim_ext
        SI (λ α, {c : obj C & is_limit (lift_func (lt_dsp α) F) c})
        (λ α _, existT _ (limiting_cone_is_limit (term_is_terminal (complete _)))).
  Proof. split; repeat intros ?; done. Qed.

  Definition later_func_o_map F α : obj C := projT1 (later_func_o_map_il F α).

  Lemma later_func_o_map_zero F : later_func_o_map F zero = (term (term_of C)).
  Proof. rewrite /later_func_o_map /later_func_o_map_il index_rec_zero //. Qed.

  Lemma later_func_o_map_succ F α : later_func_o_map F (succ α) = F ₒ α.
  Proof. rewrite /later_func_o_map /later_func_o_map_il index_rec_succ //. Qed.

  Lemma later_func_o_map_lim F (α : limit_idx SI) :
    later_func_o_map F α = vertex (term (complete (lift_func (lt_dsp α) F))).
  Proof. rewrite /later_func_o_map /later_func_o_map_il index_rec_lim //. Qed.

  Definition later_func_o_map_is_limit F α :
    is_limit (lift_func (lt_dsp α) F) (later_func_o_map F α) := projT2 (later_func_o_map_il F α).

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
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))).
      rewrite /= comp_assoc -(cone_hom_commutes (proj_cone_hom _ (later_func_o_map _) _ _)); done.
    - intros ?; rewrite /=.
      rewrite -comp_assoc -(cone_hom_commutes (proj_cone_hom _ (later_func_o_map _) _ _)) /=.
      apply (cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone η α)) (lift_in_lt_ds _ _)).
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
    - intros ?; rewrite /=.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))); done.
    - intros ?; rewrite /= -comp_assoc.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))).
      rewrite /= !comp_assoc.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))) //=.
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
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))).
      rewrite /= left_id //.
  Qed.

  Program Definition later : functor (FuncCat ((OrdCat SI)ᵒᵖ) C) (FuncCat ((OrdCat SI)ᵒᵖ) C) :=
    MkFunc later_func (λ _ _ η, later_h_map η) _ (λ _ _ _, later_h_map_comp) later_h_map_id.
  Next Obligation.
    intros F G η η' Heq α; rewrite /later_h_map /=.
    apply (hom_to_limit_unique _ _ _
      (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
      (cone_is_cone (later_h_map_cone _ _))).
    - intros ?; rewrite /=.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))); done.
    - intros ?; rewrite /=.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))) Heq; done.
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
          (bang (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _))
            (cone_down F (index_lt_le_subrel _ _ (index_succ_greater α))))) _) _.
  Next Obligation.
    intros ??? Hle; rewrite /=.
    eapply (hom_to_limit_unique _ _ _
             (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
             (cone_is_cone (cone_down _ (index_lt_le_subrel _ _ (index_le_lt_trans _ _ _ Hle (index_succ_greater _)))))).
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      rewrite -(cone_hom_commutes (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (cone_down _ _))) /=.
      rewrite -h_map_comp; f_equiv; done.
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      rewrite -(cone_hom_commutes (proj_cone_hom _ _ _ _)) /=.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (cone_down _ _)) (lift_in_lt_ds _ _)) /=.
      f_equiv; done.
  Qed.
  Next Obligation.
    intros F G η α; rewrite /=.
    apply (hom_to_limit_unique _ _ _
             (limiting_cone_is_limit (il_is_limiting_cone (lift_func _ _) _ (later_func_o_map_is_limit _ _)))
             (cone_is_cone (next_cone η (cone_down _ (index_lt_le_subrel _ _ (index_succ_greater _)))))).
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      rewrite -(cone_hom_commutes (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (cone_down _ _))) /=.
      rewrite naturality. f_equiv; done.
    - intros ?; rewrite /=.
      rewrite -comp_assoc.
      rewrite -(cone_hom_commutes (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (later_h_map_cone _ _))) /=.
      rewrite comp_assoc.
      rewrite -(cone_hom_commutes
        (bang (il_is_limiting_cone _ (later_func_o_map _ _) _) (cone_down _ _))) /=.
      f_equiv; done.
  Qed.

End later.

Section earlier.
  Context {SI : indexT} {C : category}.

  Program Definition earlier_func (F : functor ((OrdCat SI)ᵒᵖ) C) : functor ((OrdCat SI)ᵒᵖ) C :=
    MkFunc (λ α, F ₒ (succ α)) (λ _ _ Hle, F ₕ (index_le_succ_mono _ _ Hle)) _ _ _.
  Next Obligation. repeat intros ?; f_equiv; done. Qed.
  Next Obligation. repeat intros ?; rewrite/= -h_map_comp; f_equiv; done. Qed.
  Next Obligation. repeat intros ?; rewrite /= -h_map_id; f_equiv; done. Qed.
  Fail Next Obligation.

  Program Definition earlier_h_map {F G} (η : natural F G) : natural (earlier_func F) (earlier_func G) :=
    MkNat (λ α, η ₙ (succ α)) (λ _ _ Hle, naturality η (index_le_succ_mono _ _ Hle)).

  Program Definition earlier : functor (FuncCat ((OrdCat SI)ᵒᵖ) C) (FuncCat ((OrdCat SI)ᵒᵖ) C) :=
    MkFunc (λ F, earlier_func F) (λ _ _ η, earlier_h_map η) _ _ _.
  Next Obligation. repeat intros ?; rewrite /=; done.  Qed.
  Next Obligation. repeat intros ?; rewrite //=. Qed.
  Next Obligation. repeat intros ?; rewrite //=. Qed.
  Fail Next Obligation.

End earlier.
