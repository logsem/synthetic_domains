From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category ord_cat.

Opaque later next later_prod.

Class ContractiveFunctor {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))}
  (F : functor C C) `{!EnrichedFunctor F} := MkContrFunc {
  contr_func_h_map : ∀ a b : obj C, hom (later ₒ (enr_hom a b)) (enr_hom (F ₒ a) (F ₒ b));
  contr_func_h_map_is_h_map :
  ∀ a b : obj C, enr_func_h_map F a b ≡ (contr_func_h_map a b) ∘ (next ₙ (enr_hom a b));
  contr_func_h_map_comp : ∀ a b c (f : hom a b) (g : hom b c),
    contr_func_h_map a c ∘
    (later ₕ (enr_comp a b c)) ∘
    (backward (later_prod (enr_hom a b) (enr_hom b c))) ∘
    (next ₙ (enr_hom a b) ×ₕ (next ₙ (enr_hom b c))) ∘ (⌜f⌝ ×ₕ ⌜g⌝)
    ≡
    (enr_comp (F ₒ a) (F ₒ b) (F ₒ c)) ∘
    ((contr_func_h_map a b) ×ₕ (contr_func_h_map b c)) ∘
    (next ₙ (enr_hom a b) ×ₕ (next ₙ (enr_hom b c))) ∘ (⌜f⌝ ×ₕ ⌜g⌝);
  contr_func_h_map_id : ∀ a,
  (contr_func_h_map a a) ∘ (later ₕ ⌜id a⌝) ∘ (next ₙ (1ₒ)) ≡ ⌜id (F ₒ a)⌝
}.
Global Arguments MkContrFunc {_ _ _ _ _} _ _ _ _.
Global Arguments contr_func_h_map {_ _ _} _ {_ _} _ _.
Global Arguments contr_func_h_map_is_h_map {_ _ _} _ {_ _} _ _.
Global Arguments contr_func_h_map_comp {_ _ _} _ {_ _} _ _ _.
Global Arguments contr_func_h_map_id {_ _ _} _ {_ _} _.

Global Program Instance ContractiveFunctor_comp_l
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))} (F G : functor C C)
  `{!EnrichedFunctor F} `{!ContractiveFunctor F} `{!EnrichedFunctor G} :
  ContractiveFunctor (functor_compose F G) :=
  MkContrFunc (λ a b, enr_func_h_map G (F ₒ a) (F ₒ b) ∘ contr_func_h_map F a b) _ _ _.
Next Obligation.
  intros ??? F G ??? a b α f g Heq; simpl in *.
  pose proof (contr_func_h_map_is_h_map F a b α f g Heq) as Heq'.
  simpl in Heq'; rewrite -Heq' //.
Qed.
Next Obligation.
  intros ??? F G ??? a b c f g α [[] []] [[] []] _; simpl in *.
  pose proof (contr_func_h_map_comp F a b c f g α ((), ()) _ (reflexivity _))
    as Hfg; simpl in Hfg; rewrite Hfg; clear Hfg.
  pose proof (contr_func_h_map_is_h_map F _ _ _ ((⌜f⌝ ₙ α) ()) _ (reflexivity _))
    as Hf; simpl in Hf; rewrite -!Hf; clear Hf.
  pose proof (contr_func_h_map_is_h_map F _ _ _ ((⌜g⌝ ₙ α) ()) _ (reflexivity _))
    as Hg; simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (enr_func_does_map F f α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite -!Hf; clear Hf.
  pose proof (enr_func_does_map F g α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (enr_func_does_map G (F ₕ f) α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite -!Hf; clear Hf.
  pose proof (enr_func_does_map G (F ₕ g) α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (enr_comp_comp (F ₕ f) (F ₕ g) α () _ (reflexivity _)) as Hcmp;
    simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  pose proof (enr_func_does_map G (F ₕ g ∘ (F ₕ f)) α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (enr_comp_comp (G ₕ (F ₕ f)) (G ₕ (F ₕ g)) α () _ (reflexivity _)) as Hcmp;
    simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  rewrite h_map_comp //.
Qed.
Next Obligation.
  intros ??? F G ??? a α [] [] _; simpl in *.
  pose proof (contr_func_h_map_id F a α () _ (reflexivity _)) as Hid;
    simpl in Hid; rewrite Hid; clear Hid.
  pose proof (enr_func_does_map G (id (F ₒ a)) α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  rewrite h_map_id //.
Qed.
Fail Next Obligation.

Global Program Instance ContractiveFunctor_comp_r
  {SI : indexT} {C : category} `{!Enriched C (PSh (OrdCat SI))} (F G : functor C C)
  `{!EnrichedFunctor F} `{!ContractiveFunctor F} `{!EnrichedFunctor G} :
  ContractiveFunctor (functor_compose G F) :=
  MkContrFunc (λ a b, contr_func_h_map F (G ₒ a) (G ₒ b) ∘ (later ₕ (enr_func_h_map G a b))) _ _ _.
Next Obligation.
  intros ??? F G ??? a b α f g <-; clear g; simpl in *.
  pose proof (contr_func_h_map_is_h_map
    F (G ₒ a) (G ₒ b) α ((enr_func_h_map G a b ₙ α) f) _ (reflexivity _))
    as Heq; simpl in Heq; rewrite Heq; clear Heq.
  f_equiv.
  pose proof (naturality next (enr_func_h_map G a b) α f _ (reflexivity _)); done.
Qed.
Next Obligation.
  intros ??? F G ??? a b c f g α [[] []] [[] []] _; simpl in *.
  pose proof (naturality next (enr_func_h_map G a b) α
    ((⌜f⌝ₙ α) ()) _ (reflexivity _)) as Hf; simpl in Hf; rewrite -Hf; clear Hf.
  pose proof (naturality next (enr_func_h_map G b c) α
    ((⌜g⌝ₙ α) ()) _ (reflexivity _)) as Hg; simpl in Hg; rewrite -Hg; clear Hg.
  pose proof (enr_func_does_map G f α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite -!Hf; clear Hf.
  pose proof (enr_func_does_map G g α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (contr_func_h_map_comp F _ _ _ (G ₕ f) (G ₕ g) α ((), ()) _ (reflexivity _))
    as Hfg; simpl in Hfg; rewrite -Hfg; clear Hfg.
  pose proof (enr_func_does_map G f α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite !Hf; clear Hf.
  pose proof (enr_func_does_map G g α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite !Hg; clear Hg.
  epose proof (later_prod_next _ _ _ (_, _) (_, _) (reflexivity _)) as Hlpn;
    simpl in Hlpn; rewrite Hlpn; clear Hlpn.
  epose proof (later_prod_next (natural_id _) (natural_id _) _ (_, _) (_, _) (reflexivity _)) as Hlpn;
    simpl in Hlpn; rewrite Hlpn; clear Hlpn.
  epose proof (naturality next (enr_comp _ _ _) _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (naturality next (enr_comp _ _ _) _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (naturality next (enr_func_h_map G _ _) _ _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  pose proof (enr_func_does_map G f α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite -!Hf; clear Hf.
  pose proof (enr_func_does_map G g α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  pose proof (enr_comp_comp (G ₕ f) (G ₕ g) α () _ (reflexivity _)) as Hcmp;
    simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  pose proof (enr_comp_comp f g α () _ (reflexivity _)) as Hcmp;
    simpl in Hcmp; rewrite -Hcmp; clear Hcmp.
  pose proof (enr_func_does_map G (g ∘ f) α () _ (reflexivity _)) as Hf;
    simpl in Hf; rewrite -!Hf; clear Hf.
  rewrite h_map_comp //.
Qed.
Next Obligation.
  intros ??? F G ??? a α [] [] _; simpl in *.
  pose proof (naturality next ⌜ id a ⌝ α () _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (naturality next (enr_func_h_map G a a) α _ _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite -Hn; clear Hn.
  epose proof (enr_func_does_map G _ α () _ (reflexivity _)) as Hg;
    simpl in Hg; rewrite -!Hg; clear Hg.
  rewrite h_map_id.
  pose proof (naturality next ⌜ id (G ₒ a) ⌝ α () _ (reflexivity _)) as Hn;
    simpl in Hn; rewrite Hn; clear Hn.
  pose proof (contr_func_h_map_id F (G ₒ a) α () _ (reflexivity _)) as Hid;
    simpl in Hid; rewrite Hid; done.
Qed.
Fail Next Obligation.
