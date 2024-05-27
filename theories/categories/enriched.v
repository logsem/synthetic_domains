From SynthDom Require Import prelude.
From SynthDom.categories Require Import category ord_cat.
From SynthDom Require Import stepindex.

Opaque later next earlier_later_nat_iso.

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
  MkLocContrFunc
    (λ a b, contr_func_h_map F (G ₒ a) (G ₒ b) ∘ (later ₕ (enr_func_h_map G a b))) _ _ _.
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
  epose proof (enr_func_h_map_comp G _ _ _) as Hcmp;
    simpl in Hcmp; rewrite Hcmp; clear Hcmp.
  epose proof (h_map_comp _ _ later _ _ _ _
    (enr_comp _ _ _) α _ _ (reflexivity _)) as Hlc;
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

(* α-isomorphism *)

Record iso_at
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (α : SI) := MkIsoAt
{
  inv_at : (enr_hom b a) ₒ α;
  inv_at_lr : (enr_comp a b a ₙ α) ((⌜f⌝ ₙ α) (), inv_at) ≡ (⌜id a⌝ ₙ α) ();
  inv_at_rl : (enr_comp b a b ₙ α) (inv_at, (⌜f⌝ ₙ α) ()) ≡ (⌜id b⌝ ₙ α) ();
}.
Global Arguments MkIsoAt {_ _ _ _ _ _ _} _ _ _.
Global Arguments inv_at {_ _ _ _ _ _ _} _.
Global Arguments inv_at_lr {_ _ _ _ _ _ _} _.
Global Arguments inv_at_rl {_ _ _ _ _ _ _} _.

Definition iso_upto {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (dsp : downset_pred SI) :=
  ∀ β : downset dsp, iso_at f β.

Definition iso_upto_glue {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (dsp : downset_pred SI)
  (isos : ∀ α, dsp α → iso_upto f (le_dsp α)) :
  iso_upto f dsp :=
  λ α, isos α (ds_in_dsp α) (MkDS (le_dsp α) (reflexivity _)).

Lemma iso_upto_natural {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (dsp : downset_pred SI)
  (iso : iso_upto f dsp) [α β : downset dsp] (Hle : β ⪯ α) :
  inv_at (iso β) ≡ (enr_hom b a ₕ Hle) (inv_at (iso α)).
Proof.
  eassert ((enr_comp b b a ₙ (β : SI))
             ((enr_comp b a b ₙ (β : SI))
                ((enr_hom b a ₕ Hle) (inv_at (iso α)),
                  (⌜ f ⌝ₙ (β : SI)) ()), (inv_at (iso β))) ≡
             inv_at (iso β)) as <-.
  { pose proof (@naturality _ _ _ _ (enr_comp b a b) _ _ Hle
         (inv_at (iso α), (⌜ f ⌝ₙ (α : SI)) ())
         _ (reflexivity _)) as Hn.
    simpl in Hn.
    pose proof (inv_at_rl (iso α)) as Hrl;
      simpl in Hrl; rewrite Hrl in Hn; clear Hrl.
    pose proof (naturality ⌜ id b ⌝ Hle () _ (reflexivity _)) as Hid;
      simpl in Hid; rewrite -Hid in Hn; clear Hid.
    pose proof (naturality ⌜ f ⌝ Hle () _ (reflexivity _)) as Hid;
      simpl in Hid; rewrite -Hid in Hn; clear Hid.
    rewrite Hn.
    epose proof
      (enr_right_id b a (β : SI) ((), inv_at (iso β))
         _ (reflexivity _)); done. }
  epose proof (enr_comp_assoc b a b a (β : SI)
    ((enr_hom b a ₕ Hle) (inv_at (iso α)),
      (⌜ f ⌝ₙ (β : SI)) (), inv_at (iso β)) _ (reflexivity _)) as Hass.
  rewrite /= in Hass; rewrite -Hass; clear Hass.
  pose proof (inv_at_lr (iso β)) as Hlr;
    simpl in Hlr; rewrite Hlr; clear Hlr.
  epose proof (enr_left_id b a (β : SI) (_, ()) _ (reflexivity _)) as Hlid;
    simpl in Hlid; rewrite Hlid; clear Hlid.
  done.
Qed.

Program Definition iso_upto_inv_embedded
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (dsp : downset_pred SI)
  (iso : iso_upto f dsp) :
  hom (PSh (OrdDSCat dsp))
    (lift_func dsp (1ₒ : PreSheaf _))
    (lift_func dsp (enr_hom b a)) :=
  MkNat (λ α, λset _, inv_at (iso α)) _.
Next Obligation. repeat intros ?; apply iso_upto_natural. Qed.

Definition iso_upto_total_inv_embedded
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (iso : iso_upto f (total_dsp SI)) :
  hom (1ₒ) (enr_hom b a) :=
  unlift_natural (iso_upto_inv_embedded f _ iso).

Definition iso_upto_total_inv
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (iso : iso_upto f (total_dsp SI)) :
  hom b a := ⌞iso_upto_total_inv_embedded f iso⌟.

Lemma iso_upto_total_isomorphism {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (iso : iso_upto f (total_dsp SI)) :
  isomorphism f (iso_upto_total_inv f iso).
Proof.
  split.
  - rewrite -{1}(enr_embed_project f).
    apply enr_embed_inj.
    intros α [] [] _.
    rewrite /iso_upto_total_inv /iso_upto_total_inv_embedded.
    rewrite enr_comp_comp /=.
    apply inv_at_lr.
  - rewrite -{2}(enr_embed_project f).
    apply enr_embed_inj.
    intros α [] [] _.
    rewrite /iso_upto_total_inv /iso_upto_total_inv_embedded.
    rewrite enr_comp_comp /=.
    apply inv_at_rl.
Qed.

Definition iso_upto_total {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  {a b : obj C} (f : hom a b) (iso : iso_upto f (total_dsp SI)) :
  isomorphic a b := MkIsoIc _ _ (iso_upto_total_isomorphism f iso).

Program Definition iso_at_func
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  (F : functor C C) `{!EnrichedFunctor F}
  {a b : obj C} (f : hom a b) {α} (iso : iso_at f α) :
  iso_at (F ₕ f) α :=
  MkIsoAt ((enr_func_h_map F b a ₙ α) (inv_at iso)) _ _.
Next Obligation.
  intros ??? F ? a b f α iso; simpl in *.
  rewrite -{1}(enr_embed_project f) enr_func_h_map_is_h_map /=.
  epose proof (enr_func_h_map_comp F _ _ _ α (_, _) _ (reflexivity _))
    as Hcmp; simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  rewrite inv_at_lr.
  epose proof (enr_func_h_map_id F _ α () _ (reflexivity _)); simpl in *; done.
Qed.
Next Obligation.
  intros ??? F ? a b f α iso; simpl in *.
  rewrite -{2}(enr_embed_project f) enr_func_h_map_is_h_map /=.
  epose proof (enr_func_h_map_comp F _ _ _ α (_, _) _ (reflexivity _))
    as Hcmp; simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  rewrite inv_at_rl.
  epose proof (enr_func_h_map_id F _ α () _ (reflexivity _)); simpl in *; done.
Qed.
Fail Next Obligation.

Definition iso_upto_func
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  (F : functor C C) `{!EnrichedFunctor F}
  {a b : obj C} (f : hom a b) {dsp} (iso : iso_upto f dsp) : iso_upto (F ₕ f) dsp :=
  λ α, iso_at_func F f (iso α).

(* TODO: MOVE *)
Lemma compose_along_iso_right_setoid {A B} (iso : A ≃@{Setoid} B) (x y : A) :
  forward iso x ≡ forward iso y → x ≡ y.
Proof.
  intros Heq.
  change x with (id A x); change y with (id A y).
  rewrite -(iso_lr (is_iso iso)) /= Heq //.
Qed.

Program Definition iso_upto_contr_func
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  (F : functor C C) `{!LocallyContractiveFunctor F}
  {a b : obj C} (f : hom a b) {dsp} (iso : iso_upto f dsp) α
  (Hdsp : ∀ β, β ≺ α → dsp β) : iso_at (F ₕ f) α :=
  MkIsoAt
    ((contr_func_h_map F b a ₙ α)
       (into_later_psh _
          (λ β (Hβ : β ≺ α), inv_at (iso (MkDS dsp (Hdsp _ Hβ)))) _))
    _ _.
Next Obligation.
  intros ???????? dsp ?? Hdsp β γ Hβ Hγ Hle; simpl in *.
  symmetry.
  apply (iso_upto_natural _ _ _
    (Hle : (MkDS dsp (Hdsp _ Hβ)) ⪯ (MkDS dsp (Hdsp _ Hγ)))).
Qed.
Next Obligation.
  intros ??? F ? a b f dsp iso α Hdsp; simpl in *.
  rewrite -{1}(enr_embed_project f) enr_func_h_map_is_h_map /=.
  rewrite -enr_func_h_map_id.
  rewrite !contr_func_h_map_is_h_map /=.
  epose proof (contr_func_h_map_comp F _ _ _ _ (_, _) _ (reflexivity _))
    as Hcmp; simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  f_equiv.
  apply equiv_of_into_later_psh.
  intros β Hβ.
  rewrite -(psh_naturality (next ₙ enr_hom _ _)) /=.
  epose proof (psh_naturality (⌜id _⌝)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (psh_naturality (later ₕ enr_comp _ _ _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (psh_naturality (backward (later_prod (enr_hom a b) (enr_hom b a))))
    as Hn; simpl in Hn; rewrite -Hn /=; clear Hn.
  rewrite -(psh_naturality (next ₙ enr_hom _ _)) /=.
  epose proof (psh_naturality (⌜f⌝)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  pose proof (side_of_later' (enr_hom b a) (MkDS (lt_dsp α) Hβ)) as Hsdl;
    simpl in Hsdl; rewrite Hsdl /=; clear Hsdl.
  rewrite into_later_side_psh /=.
  apply (compose_along_iso_right_setoid
           (natural_iso_proj
              (natural_iso_proj earlier_later_nat_iso (enr_hom a a)) β)); simpl.
  epose proof (naturality (forward (earlier_later_nat_iso (SI := SI) (C := Setoid)))
        (enr_comp a b a) β _ _ (reflexivity _)) as Hn;
    rewrite /= h_map_id /= in Hn; rewrite Hn; clear Hn.
  epose proof (earlier_later_earlier_later_prod (enr_hom a b) (enr_hom b a)
                 _ (_, _) _ (reflexivity _)) as Heq;
  rewrite /= !h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (iso_rl (is_iso (natural_iso_proj (earlier_later_nat_iso) (enr_hom b a)))
    _ _ _ (reflexivity _)) as Hfb; simpl in Hfb; rewrite Hfb; clear Hfb.
  epose proof (forward_earlier_later_nat_iso_next (C := Setoid) (enr_hom a a)
    _ _ _ (reflexivity _)) as Heq;
    rewrite /= h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (naturality ⌜ id _ ⌝ _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (forward_earlier_later_nat_iso_next (C := Setoid) (enr_hom a b)
    _ _ _ (reflexivity _)) as Heq;
    rewrite /= h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (naturality ⌜ f ⌝ _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  apply inv_at_lr.
Qed.
Next Obligation.
  intros ??? F ? a b f dsp iso α Hdsp; simpl in *.
  rewrite -{3}(enr_embed_project f) enr_func_h_map_is_h_map /=.
  rewrite -enr_func_h_map_id.
  rewrite !contr_func_h_map_is_h_map /=.
  epose proof (contr_func_h_map_comp F _ _ _ _ (_, _) _ (reflexivity _))
    as Hcmp; simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  f_equiv.
  apply equiv_of_into_later_psh.
  intros β Hβ.
  rewrite -(psh_naturality (next ₙ enr_hom _ _)) /=.
  epose proof (psh_naturality (⌜id _⌝)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (psh_naturality (later ₕ enr_comp _ _ _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (psh_naturality (backward (later_prod (enr_hom b a) (enr_hom a b))))
    as Hn; simpl in Hn; rewrite -Hn /=; clear Hn.
  rewrite -(psh_naturality (next ₙ enr_hom _ _)) /=.
  epose proof (psh_naturality (⌜f⌝)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  pose proof (side_of_later' (enr_hom b a) (MkDS (lt_dsp α) Hβ)) as Hsdl;
    simpl in Hsdl; rewrite Hsdl /=; clear Hsdl.
  rewrite into_later_side_psh /=.
  apply (compose_along_iso_right_setoid
           (natural_iso_proj
              (natural_iso_proj earlier_later_nat_iso (enr_hom b b)) β)); simpl.
  epose proof (naturality (forward (earlier_later_nat_iso (SI := SI) (C := Setoid)))
        (enr_comp b a b) β _ _ (reflexivity _)) as Hn;
    rewrite /= h_map_id /= in Hn; rewrite Hn; clear Hn.
  epose proof (earlier_later_earlier_later_prod (enr_hom b a) (enr_hom a b)
                 _ (_, _) _ (reflexivity _)) as Heq;
  rewrite /= !h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (iso_rl (is_iso (natural_iso_proj (earlier_later_nat_iso) (enr_hom b a)))
    _ _ _ (reflexivity _)) as Hfb; simpl in Hfb; rewrite Hfb; clear Hfb.
  epose proof (forward_earlier_later_nat_iso_next (C := Setoid) (enr_hom b b)
    _ _ _ (reflexivity _)) as Heq;
    rewrite /= h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (naturality ⌜ id _ ⌝ _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (forward_earlier_later_nat_iso_next (C := Setoid) (enr_hom a b)
    _ _ _ (reflexivity _)) as Heq;
    rewrite /= h_map_id /= in Heq; rewrite Heq; clear Heq.
  epose proof (naturality ⌜ f ⌝ _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  apply inv_at_rl.
Qed.
Fail Next Obligation.
