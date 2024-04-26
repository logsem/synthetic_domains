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

(* useful tactics *)
Ltac rewrite_cone_hom_commutes_back :=
  match goal with
    |- context [il_side _ ?j ∘ cone_hom_map ?c] => rewrite -(cone_hom_commutes c j)
  | |- context [ic_side _ ?j ∘ cone_hom_map ?c] => rewrite -(cone_hom_commutes c j)
  end.

(* successor as a functor *)

Program Definition Succ SI : functor (OrdCat SI) (OrdCat SI) :=
  MkFunc (λ α, succ α) (λ _ _ h, index_le_succ_mono _ _ h) _ _ _.
Solve All Obligations with repeat intros ?; done.

Definition ord_pred {SI : indexT} := index_rec (λ _, SI) zero (λ α _, α) (λ α _, α).
Local Instance ord_pred_index_rec_lim_ext {SI} : @index_rec_lim_ext SI (λ _, SI) (λ α _, α).
Proof. done. Qed.

Lemma ord_pred_zero {SI} : @ord_pred SI zero = zero.
Proof. rewrite /ord_pred index_rec_zero //. Qed.

Lemma ord_pred_succ {SI} α : @ord_pred SI (succ α) = α.
Proof. rewrite /ord_pred index_rec_succ //. Qed.

Lemma ord_pred_lim {SI} (α : limit_idx SI) : ord_pred α = α.
Proof. rewrite /ord_pred index_rec_lim //. Qed.

Lemma ord_pred_mono {SI : indexT} {α β : SI} : α ⪯ β → ord_pred α ⪯ ord_pred β.
Proof.
  intros Hαβ.
  destruct (index_is_zero β) as [->|Hnz].
  { assert (α = zero) as ->; last by rewrite !ord_pred_zero.
    apply index_zero_is_unique; intros ??.
    eapply index_lt_zero_is_normal, index_lt_le_trans; eauto. }
  destruct (index_type_dec β) as [[->|[γ ->]]|Hlim].
  - apply index_lt_zero_is_normal in Hnz; done.
  - rewrite ord_pred_succ.
    destruct (index_is_zero α) as [->|Hnz'];
      first by rewrite ord_pred_zero; apply index_zero_minimum.
    destruct (index_dec_limit α) as [[δ ->]|Hlim].
    + rewrite ord_pred_succ; apply index_le_succ_inj; done.
    + rewrite (ord_pred_lim (mklimitidx α Hlim Hnz')) /=.
      pose proof (index_limit_not_succ α Hlim γ).
      apply index_le_eq_or_lt in Hαβ as [->|Hlt%index_succ_iff_proj_r2l]; done.
  - rewrite (ord_pred_lim (mklimitidx β Hlim Hnz)) /=.
    destruct (index_is_zero α) as [->|Hnz'];
      first by rewrite ord_pred_zero; apply index_zero_minimum.
    destruct (index_dec_limit α) as [[δ ->]|Hlim'].
    + rewrite ord_pred_succ. etrans; last done.
      apply index_lt_le_subrel, index_succ_greater.
    + rewrite (ord_pred_lim (mklimitidx α Hlim' Hnz')); done.
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

(** TODO: MOVE *)

Definition is_limit_trans {J C} {F : functor J C} {a b : obj C} (Heq : a = b) (il : is_limit F a) : is_limit F b :=
  match Heq in _ = Z return is_limit F Z with eq_refl => il end.

Lemma trans_side_of_is_limit_trans {J C} {F : functor J C} {a b : obj C}
  (Heq : a = b) (il : is_limit F a) :
  ∀ j, ic_side (il_is_cone (is_limit_trans Heq il)) j =
    hom_trans Heq eq_refl (ic_side (il_is_cone il) j).
Proof. destruct Heq; done. Qed.

Lemma bang_of_is_limit_trans {J C} {F : functor J C} {a b : obj C}
  (Heq : a = b) (il : is_limit F a) c :
  (cone_hom_map (bang (il_is_limiting_cone _ _ (is_limit_trans Heq il)) c)) =
    hom_trans eq_refl Heq (cone_hom_map (bang (il_is_limiting_cone _ _ il) c)).
Proof. destruct Heq; done. Qed.

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

  Definition later_func_o_map_is_limit F α : is_limit (lift_func (lt_dsp α) F) (later_func_o_map F α) :=
    projT2 (later_func_o_map_il F α).

  Lemma later_func_o_map_il_succ F α : later_func_o_map_il F (succ α) = existT _ (is_limit_at F α).
  Proof. rewrite /later_func_o_map_il /later_func_o_map_il index_rec_succ //. Qed.

  Lemma later_func_o_map_is_limit_succ F α :
    later_func_o_map_is_limit F (succ α) = is_limit_trans (eq_sym (later_func_o_map_succ F α)) (is_limit_at F α).
  Proof.
    pose proof (projT2_eq (later_func_o_map_il_succ F α)) as Heq; simpl in *.
    rewrite -Heq.
    replace (projT1_eq (later_func_o_map_il_succ F α)) with (later_func_o_map_succ F α) by apply ProofIrrelevance.
    destruct (later_func_o_map_succ F α); simpl; done.
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
          (bang (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _))
            (cone_down F (index_lt_le_subrel _ _ (index_succ_greater α))))) _) _.
  Next Obligation.
    intros ??? Hle; rewrite /=.
    apply (hom_to_limit_unique _ _ _
            (limiting_cone_is_limit (il_is_limiting_cone _ _ (later_func_o_map_is_limit _ _)))
            (cone_is_cone (cone_down _ (index_lt_le_subrel _ _ (index_le_lt_trans _ _ _ Hle (index_succ_greater _)))))).
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
             (limiting_cone_is_limit (il_is_limiting_cone (lift_func _ _) _ (later_func_o_map_is_limit _ _)))
             (cone_is_cone (next_cone η (cone_down _ (index_lt_le_subrel _ _ (index_succ_greater _)))))).
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
      with (eq_refl (G2 ₒ α)) by apply ProofIrrelevance.
    rewrite hom_trans_refl !comp_assoc.
    f_equiv.
    apply hom_trans_sym'.
    rewrite !hom_trans_compose !hom_trans_refl.
    rewrite -hom_trans_trans eq_trans_refl_r eq_trans_refl_l.
    match goal with |- hom_trans _ _ ?A ∘ _ ≡ _ => assert (A ≡ id _) as -> end.
    { rewrite -h_map_id; f_equiv; done. }
    replace (later_func_o_map_succ G1 α) with (func_eq_o_map (later_succ G1) α)
      by apply ProofIrrelevance.
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
    - intros [F G] η η' <- α; simpl in *.
      admit.
    - intros [F G] η η' <- α; simpl in *.
      admit.
  Admitted.

End Adjunction.
