From SynthDom Require Import prelude.
From SynthDom.categories Require Import category.
From SynthDom Require Import stepindex.

Open Scope category_scope.

Class Dist (SI: indexT) A := dist : SI → relation A.

Instance: Params (@dist) 4 := {}.
Notation "x ≡{ α }≡ y" := (dist α x y)
  (at level 70, α at next level, format "x  ≡{ α }≡  y").
Notation "x ≡{ α }@{ A }≡ y" := (dist (A:=A) α x y)
  (at level 70, α at next level, only parsing).

Hint Extern 0 (_ ≡{_}≡ _) => reflexivity : core.
Hint Extern 0 (_ ≡{_}≡ _) => symmetry; assumption : core.
Notation NonExpansive f := (∀ α, Proper (dist α ==> dist α) f).
Notation NonExpansive2 f := (∀ α, Proper (dist α ==> dist α ==> dist α) f).

(* Helper tactic. *)
Ltac solve_by_dist_rewrite :=
  by repeat match goal with Hd : context [dist _ _ _] |- _ => first [rewrite Hd| rewrite (Hd _)] end; eauto.


Class Distance A `{!Equiv A, !Dist SI A} := {
  dist_equiv : ∀ x y, (∀ α, x ≡{α}≡ y) ↔ x ≡ y;
  dist_equivalence :: ∀ α, Equivalence (dist α);
  dist_downwards : ∀ α β x y, x ≡{α}≡ y → β ⪯ α → x ≡{β}≡ y;
}.

Global Instance dist_ne `{!Equiv A, !Dist SI A, !Distance A} α : Proper (dist α ==> dist α ==> iff) (@dist SI A _ α).
Proof. intros ?? Heq ?? Heq'; rewrite Heq Heq'; done. Qed.

Global Instance dist_proper `{!Equiv A, !Dist SI A, !Distance A} α : Proper ((≡) ==> (≡) ==> iff) (@dist SI A _ α).
Proof. intros ?? Heq ?? Heq'. eapply dist_equiv in Heq, Heq'; rewrite Heq Heq'; done. Qed.
Global Instance dist_proper_2 `{!Equiv A, !Dist SI A, !Distance A} α x : Proper ((≡) ==> iff) (dist α x).
Proof. apply dist_proper, dist_equiv; done. Qed.

Lemma dist_le `{!Equiv A, !Dist SI A, !Distance A} α α' x y : x ≡{α}≡ y → α' ⪯ α → x ≡{α'}≡ y.
Proof. destruct 2; eauto using dist_downwards; congruence. Qed.
Lemma dist_le' `{!Equiv A, !Dist SI A, !Distance A} α α' x y : α' ⪯ α → x ≡{α}≡ y → x ≡{α'}≡ y.
Proof. intros; eauto using dist_le. Qed.
Global Instance ne_proper
  `{!Equiv A, !Dist SI A, !Distance A}
  `{!Equiv B, !Dist SI B, !Distance B} (f : A → B) `{!NonExpansive f} :
  Proper ((≡) ==> (≡)) f | 100.
Proof. by intros x1 x2; rewrite -!dist_equiv; intros Hx n; rewrite (Hx n). Qed.
Global Instance ne_proper_2
  `{!Equiv A, !Dist SI A, !Distance A}
  `{!Equiv B, !Dist SI B, !Distance B}
  `{!Equiv C, !Dist SI C, !Distance C} (f : A → B → C) `{!NonExpansive2 f} :
  Proper ((≡) ==> (≡) ==> (≡)) f | 100.
Proof.
  unfold Proper, respectful; setoid_rewrite <- dist_equiv.
  by intros x1 x2 Hx y1 y2 Hy n; rewrite (Hx n) (Hy n).
Qed.

Definition dist_later `{!Dist SI A} (α : SI) (x y : A) : Prop := ∀ β, β ≺ α → x ≡{β}≡ y.

Global Instance dist_later_equivalence `{!Dist SI A, !Equiv A} `{!Distance A} α : Equivalence (@dist_later SI A _ α).
Proof.
  split.
  - now intros ???.
  - unfold dist_later; intros ?? H ??; now rewrite H.
  - unfold dist_later; intros ??? H1 H2 ??; now rewrite H1 ?H2.
Qed.

Lemma dist_dist_later `{!Dist SI A, !Equiv A} `{!Distance A} α (x y : A) : dist α x y → dist_later α x y.
Proof. intros Heq ??; eapply dist_downwards; eauto. Qed.

Lemma dist_later_dist `{!Dist SI A, !Equiv A} `{!Distance A} α β (x y : A) : β ≺ α → dist_later α x y → dist β x y.
Proof. intros ? H; by apply H.  Qed.

Lemma dist_later_zero `{!Dist SI A, !Equiv A} `{!Distance A} (x y : A): dist_later zero x y.
Proof. intros ? [] % index_lt_zero_is_normal. Qed.

Global Instance ne_dist_later `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance B} (f : A → B) :
  NonExpansive f → ∀ α, Proper (dist_later α ==> dist_later α) f.
Proof. intros Hf ??????; by eapply Hf, H. Qed.

Global Instance ne2_dist_later_l
  `{!Dist SI A, !Equiv A} `{!Distance A}
  `{!Dist SI B, !Equiv B} `{!Distance B}
  `{!Dist SI C, !Equiv C} `{!Distance C} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist_later α ==> dist α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; eapply dist_downwards; eauto. Qed.
Global Instance ne2_dist_later_r
  `{!Dist SI A, !Equiv A} `{!Distance A}
  `{!Dist SI B, !Equiv B} `{!Distance B}
  `{!Dist SI C, !Equiv C} `{!Distance C} (f : A → B → C) :
  NonExpansive2 f → ∀ α, Proper (dist α ==> dist_later α ==> dist_later α) f.
Proof. intros H α a b H1 c d H2 β Hβ. apply H; eapply dist_downwards; eauto. Qed.

Notation Contractive f := (∀ α, Proper (dist_later α ==> dist α) f).

Global Instance const_contractive `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance A} (x : A) :
  Contractive (@const A B x).
Proof. by intros α y1 y2. Qed.

Section contractive.
  Local Set Default Proof Using "Type*".
  Context `{!Dist SI A, !Equiv A} `{!Distance A} `{!Dist SI B, !Equiv B} `{!Distance B} (f : A → B) `{!Contractive f}.
  Implicit Types x y : A.

  Lemma contractive_0 x y : f x ≡{zero}≡ f y.
  Proof. by apply (_ : Contractive f), dist_later_zero. Qed.
  Lemma contractive_mono α x y : dist_later α x y → f x ≡{α}≡ f y.
  Proof. by apply (_ : Contractive f). Qed.

  Global Instance contractive_ne : NonExpansive f | 100.
  Proof.
    intros n x y ?; eapply dist_downwards with (α := succ n).
    - eapply contractive_mono.
      intros ??. eapply dist_le; eauto.
    - apply index_lt_le_subrel, index_succ_greater.
  Qed.

  Global Instance contractive_proper : Proper ((≡) ==> (≡)) f | 100.
  Proof. intros ??; apply (ne_proper _). Qed.
End contractive.

(* Enriched categories and functors. *)

Polymorphic Class EnrichedCategory SI (C : category) := MkEnrCat {
  hom_dist :: ∀ a b, Dist SI (hom C a b);
  hom_dist_distance :: ∀ a b, Distance (hom C a b);
  comp_ne :: ∀ a b c, NonExpansive2 (@comp C a b c);
}.
Global Arguments MkEnrCat {_ _} _ _ _.

Polymorphic Class EnrichedFunctor `{!EnrichedCategory SI C, !EnrichedCategory SI D} (F : functor C D) := {
  h_map_ne :: ∀ a b, NonExpansive (@h_map _ _ F a b)
}.

Polymorphic Class LocallyContractiveFunctor `{!EnrichedCategory SI C, !EnrichedCategory SI D} (F : functor C D) := {
  h_map_contr :: ∀ a b, Contractive (@h_map _ _ F a b)
}.

Global Instance enriched_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : functor C D) `{!EnrichedFunctor F} (G : functor D E) `{!EnrichedFunctor G} : EnrichedFunctor (functor_compose F G).
Proof. constructor; intros ??????; rewrite /=; solve_by_dist_rewrite. Qed.

Global Instance enriched_locally_contractive_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : functor C D) `{!EnrichedFunctor F} (G : functor D E) `{!LocallyContractiveFunctor G} :
  LocallyContractiveFunctor (functor_compose F G).
Proof.
  constructor; intros ????? Hdist; rewrite /=.
  apply h_map_contr; intros ??; apply h_map_ne; apply Hdist; done.
Qed.

Global Instance locally_contractive_enriched_compose
  `{!EnrichedCategory SI C, !EnrichedCategory SI D, !EnrichedCategory SI E}
  (F : functor C D) `{!LocallyContractiveFunctor F} (G : functor D E) `{!EnrichedFunctor G} :
  LocallyContractiveFunctor (functor_compose F G).
Proof.
  constructor; intros ????? Hdist; rewrite /=.
  apply h_map_ne; apply h_map_contr; intros ??; apply Hdist; done.
Qed.

Global Program Instance SingletonCat_enriched {SI} : EnrichedCategory SI SingletonCat :=
  MkEnrCat (λ _ _ _ _ _, True) _ _.
Next Obligation. repeat intros ?; constructor; [done|apply _|done]. Qed.

Global Instance const_functor_locally_contractive `{!EnrichedCategory SI C} c : LocallyContractiveFunctor (const_functor c).
Proof. constructor; repeat intros ?; rewrite /=; done. Qed.

Global Instance id_functor_enriched `{!EnrichedCategory SI C} : EnrichedFunctor (id_functor C).
Proof. constructor; repeat intros ?; rewrite /=; done. Qed.

(* α-isomorphism *)

Record Aisomorphism `{!EnrichedCategory SI C} (α : SI) {a b} (f : hom C a b) (g : hom C b a) :=
MkAIso {
  Aiso_lr : g ∘ f ≡{α}≡ id _;
  Aiso_rl : f ∘ g ≡{α}≡ id _;
}.
Global Arguments MkAIso {_ _ _ _ _ _ _ _} _ _.
Global Arguments Aiso_lr {_ _ _ _ _ _ _ _} _.
Global Arguments Aiso_rl {_ _ _ _ _ _ _ _} _.

Record Aisomorphic `{!EnrichedCategory SI C} α a b := MkAIsoIc {
  Aforward : hom C a b;
  Abackward : hom C b a;
  Ais_iso : Aisomorphism α Aforward Abackward
}.
Global Arguments MkAIsoIc {_ _ _ _ _ _} _ _ _.
Global Arguments Aforward {_ _ _ _ _ _} _.
Global Arguments Abackward {_ _ _ _ _ _} _.
Global Arguments Ais_iso {_ _ _ _ _ _} _.

Infix "≃{ α }≃" := (Aisomorphic α) (at level 70, no associativity) : category_scope.
Infix "≃{ α }@{ C }≃" := (@Aisomorphic C _ α)
  (at level 70, only parsing, no associativity) : category_scope.

Hint Extern 1 (_ ≡{_}≡ _) => apply dist_equiv; assumption : core.

Lemma enr_func_iso_ne `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : functor C D) `{!EnrichedFunctor F}
  α {a b} {f : hom C a b} {g : hom C b a} (aiso : Aisomorphism α f g) :
  Aisomorphism α (F ₕ f) (F ₕ g).
Proof.
  split.
  - rewrite -h_map_comp (Aiso_lr aiso) h_map_id //.
  - rewrite -h_map_comp (Aiso_rl aiso) h_map_id //.
Qed.

Global Instance locally_contractive_enriched
  `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : functor C D) `{!LocallyContractiveFunctor F} : EnrichedFunctor F.
Proof.
  constructor; intros ??????.
  apply h_map_contr.
  intros ? ?; eapply dist_le; first eassumption.
  apply index_lt_le_subrel; done.
Qed.

Lemma contr_func_iso_contr
  `{!EnrichedCategory SI C, EnrichedCategory SI D} (F : functor C D) `{!LocallyContractiveFunctor F}
  α {a b} {f : hom C a b} {g : hom C b a} (aiso : ∀ β, β ≺ α → Aisomorphism β f g) :
  Aisomorphism α (F ₕ f) (F ₕ g).
Proof.
  split.
  - rewrite -h_map_comp -h_map_id.
    apply h_map_contr.
    intros β Hβ; apply (Aiso_lr (aiso β Hβ)).
  - rewrite -h_map_comp -h_map_id.
    apply h_map_contr.
    intros β Hβ; apply (Aiso_rl (aiso β Hβ)).
Qed.

Program Definition Aismorphism_id `{!EnrichedCategory SI C} α c :
  Aisomorphism α (@id C c) (@id C c) := MkAIso _ _.
Solve All Obligations with by repeat intros ?; rewrite left_id.
Fail Next Obligation.
Definition Aismorphism_swap
  `{!EnrichedCategory SI C} {α} {a b} {f : hom C a b} {g : hom C b a} (iso : Aisomorphism α f g) :
  Aisomorphism α g f :=
  MkAIso (Aiso_rl iso) (Aiso_lr iso).
Program Definition Aismorphism_compose `{!EnrichedCategory SI C} {α} {a b c}
  {f : hom C a b} {g : hom C b a} (iso : Aisomorphism α f g)
  {h : hom C b c} {i : hom C c b} (iso : Aisomorphism α h i) :
  Aisomorphism α (h ∘ f) (g ∘ i) := MkAIso _ _.
Next Obligation.
  intros ??????? f g isofg h i isohi.
  rewrite (comp_assoc _ _ g) -(comp_assoc _ _ i) (Aiso_lr isohi) left_id (Aiso_lr isofg) //.
Qed.
Next Obligation.
  intros ??????? f g isofg h i isohi.
  rewrite (comp_assoc _ _ h) -(comp_assoc _ _ f) (Aiso_rl isofg) left_id (Aiso_rl isohi) //.
Qed.
Fail Next Obligation.

Definition isomorphic_refl `{!EnrichedCategory SI C} α (c : obj C) : Aisomorphic α c c :=
  MkAIsoIc _ _ (Aismorphism_id _ _).
Definition isomorphic_symm
  `{!EnrichedCategory SI C} α (a b : obj C) : Aisomorphic α a b → Aisomorphic α b a :=
  λ iso, MkAIsoIc _ _ (Aismorphism_swap (Ais_iso iso)).
Definition isomorphic_trans `{!EnrichedCategory SI C} α (a b c : obj C) :
  Aisomorphic α a b → Aisomorphic α b c → Aisomorphic α a c :=
  λ iso1 iso2, MkAIsoIc _ _ (Aismorphism_compose (Ais_iso iso1) (Ais_iso iso2)).

Lemma iso_Aiso `{!EnrichedCategory SI C} {a b} (f : hom C a b) (g : hom C b a) :
  isomorphism f g ↔ ∀ α, Aisomorphism α f g.
Proof.
  split.
  - intros [Hf Hb] ?; split; rewrite ?Hf ?Hb; done.
  - intros Haiso; split; apply dist_equiv; intros ?; apply Haiso.
Qed.

Lemma iso_Aiso_1 `{!EnrichedCategory SI C} {a b} (f : hom C a b) (g : hom C b a) α :
  isomorphism f g → Aisomorphism α f g.
Proof. intros ?; apply iso_Aiso; done. Qed.

Lemma isoic_Aisoic_1 `{!EnrichedCategory SI C} (a b : obj C) :
  isomorphic a b → ∀ α, Aisomorphic α a b.
Proof.
  intros [f g Hiso] ?; exists f g; apply iso_Aiso; done.
Qed.

(* Lemma contr_func_unique_fixpoint *)
(*   `{!EnrichedCategory SI C} (F : functor C C) `{!LocallyContractiveFunctor F} : *)
(*   ∀ c d, c ≃ F ₒ c → d ≃ F ₒ d → c ≃ d. *)
(* Proof. *)
(*   intros c d cfx dfx. *)
  
