From SynthDom Require Import prelude.

Record category := MkCat {
  obj : Type;
  hom : obj → obj → Type;
  id : ∀ a, hom a a;
  comp : ∀ a b c, hom a b → hom b c → hom a c;
  hom_eq : ∀ a b, Equiv (hom a b);
  hom_eq_equiv : ∀ a b, Equivalence (hom_eq a b);
  comp_proper : ∀ a b c, Proper ((≡) ==> (≡) ==> (≡)) (comp a b c);
  comp_assoc : ∀ a b c d (f : hom a b) (g : hom b c) (h : hom c d),
    comp _ _ _ f (comp _ _ _ g h) ≡ comp _ _ _ (comp _ _ _ f g) h;
  left_id : ∀ a b (f : hom a b), comp _ _ _ f (id b) ≡ f;
  right_id : ∀ a b (f : hom a b), comp _ _ _ (id a) f ≡ f;
}.

Global Existing Instance hom_eq.
Global Existing Instance hom_eq_equiv.
Global Existing Instance comp_proper.

Global Arguments hom {C} a b, _ _ _: rename.
Global Arguments id {C} a: rename.
Global Arguments comp C {a b c} f g : rename.

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Notation "g ∘{ C } f" := (comp C f g) (at level 40, left associativity) : category_scope.
Notation "g ∘ f" := (comp _ f g) : category_scope.

Record functor C D := MkFunc {
  o_map : obj C → obj D;
  h_map : ∀ a b, hom a b → hom (o_map a) (o_map b);
  h_map_comp : ∀ a b c (f : hom a b) (g : hom b c), h_map _ _ (g ∘ f) ≡ h_map _ _ g ∘ h_map _ _ f;
  h_map_id : ∀ a, h_map _ _ (id a) ≡ (id _);
}.

Arguments MkFunc {_ _} _ _ _ _.
Arguments o_map {C D} F a : rename.
Arguments h_map {C D} F {a b} f : rename.

Notation "( F ₒ)" := (o_map F) : category_scope.
Notation "F 'ₒ' a" := (o_map F a) (at level 40, no associativity) : category_scope.
Notation "( F ₕ)" := (h_map F) : category_scope.
Notation "F 'ₕ' f" := (h_map F f) (at level 40, no associativity) : category_scope.

Record natural {C D} (F G : functor C D) := MkNat {
  nat_map : ∀ c, hom (F ₒ c) (G ₒ c);
  naturality : ∀ a b (f : hom a b), nat_map b ∘ (F ₕ f) ≡ (G ₕ f) ∘ nat_map a;
}.
Arguments MkNat {_ _ _ _} _ _.
Notation "'λnat' x .. y , t" := (MkNat (λ x .. y, t) _) (at level 10, x binder, y binder, t at level 200,
  format "'[ ' '[ ' 'λnat' x .. y ']' , '/' t ']'").

Arguments nat_map {C D F G} η c : rename.

Notation "( η ₙ)" := (nat_map η) : category_scope.
Notation "η 'ₙ' c" := (nat_map η c) (at level 40, no associativity) : category_scope.

Program Definition opposite C := MkCat (obj C) (λ a b, hom C b a) id (λ a b c, flip (comp C)) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by repeat intros ?; setoid_subst; rewrite /= ?comp_assoc ?left_id ?right_id.

Notation "C 'ᵒᵖ'" := (opposite C) (at level 75).

Record iso_morphism {C a b} (f : hom C a b) (g : hom C b a) := MkIso {
  iso_lr : g ∘ f ≡ id _;
  iso_rl : f ∘ g ≡ id _;
}.

(* Category of setoids (Set) *)

Record setoid := MkSetoid { setoid_set :> Type; setoid_eq : Equiv setoid_set; setoid_eq_equiv : Equivalence setoid_eq; }.
Global Existing Instance setoid_eq.
Global Existing Instance setoid_eq_equiv.
Record setoid_fun (A B : setoid) := MkSetoidMap {
  setoid_fun_map :> A → B;
  setoid_fun_map_proper : Proper ((≡) ==> (≡)) setoid_fun_map
}.
Global Existing Instance setoid_fun_map_proper.
Arguments MkSetoidMap {_ _} _ _.
Notation "'λset' x .. y , t" := (MkSetoidMap (λ x .. y, t) _) (at level 10, x binder, y binder, t at level 200,
  format "'[ ' '[ ' 'λset' x .. y ']' , '/' t ']'").
Global Instance setoid_fun_eq A B : Equiv (setoid_fun A B) := respectful (≡) (≡).
Global Instance setoid_fun_eq_equiv A B : Equivalence (setoid_fun_eq A B).
Proof.
  split; first by repeat intros ?; setoid_subst.
  - intros ?? Heq ?? ->; rewrite Heq; eauto.
  - intros ??? Heq1 ??? ->; rewrite Heq1; eauto.
Qed.
Global Instance setoid_fun_map_proper' : ∀ A B, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_fun_map A B).
Proof. intros ???? Heq ???; apply Heq; done. Qed.
Program Definition setoid_compose {A B C} (f : setoid_fun A B) (g : setoid_fun B C) : setoid_fun A C :=
  λset x, g (f x).
Solve All Obligations with by intros ????????; setoid_subst.
Global Instance setoid_compose_proper : ∀ A B C, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_compose A B C).
Proof. intros ????????????; setoid_subst; done. Qed.

Program Definition Setoid := MkCat setoid setoid_fun (λ _, λset x, x) (@setoid_compose) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by repeat intros ?; rewrite /=; setoid_subst.

(* Functor categories *)

Global Instance natural_eq {C D} {F G : functor C D} : Equiv (natural F G) := λ η ρ, ∀ a, η ₙ a ≡ ρ ₙ a.
Global Instance nat_map_proper : ∀ C D (F G : functor C D), Proper ((≡) ==>  forall_relation (λ _, (≡))) (@nat_map C D F G).
Proof. intros ?????? Heq ?; apply Heq. Qed.
Global Instance natural_eq_equiv {C D} {F G : functor C D} : Equivalence (≡@{natural F G}).
Proof.
  split; first by repeat intros?.
  - intros ?? Heq ?; rewrite Heq //.
  - intros ??? Heq ??; rewrite Heq //.
Qed.

Program Definition natural_id {C D} (F : functor C D) : natural F F := λnat x, id (F ₒ x).
Solve All Obligations with by intros ??????; rewrite /= left_id right_id.

Program Definition natural_comp {C D} {F G H : functor C D} (η : natural F G) (ρ : natural G H) : natural F H :=
  λnat c, (ρ ₙ c) ∘ (η ₙ c).
Solve All Obligations with by repeat intros ?; rewrite /= !comp_assoc naturality -!comp_assoc naturality.
Global Instance natural_comp_proper : ∀ {C D} {F G H : functor C D}, Proper ((≡) ==> (≡) ==> (≡)) (@natural_comp C D F G H).
Proof. repeat intros ?; setoid_subst; done. Qed.
Lemma natrual_comp_assoc : ∀ (C D : category) (F G H I : functor C D) (η : natural F G) (ρ : natural G H) (δ : natural H I),
    natural_comp η (natural_comp ρ δ) ≡ natural_comp (natural_comp η ρ) δ.
Proof. repeat intros ?; rewrite /= !comp_assoc //. Qed.
Lemma natrual_comp_left_id : ∀ (C D : category) (F G : functor C D) (η : natural F G), natural_comp η (natural_id _) ≡ η.
Proof. repeat intros ?; rewrite /= left_id //. Qed.
Lemma natrual_comp_right_id : ∀ (C D : category) (F G : functor C D) (η : natural F G), natural_comp (natural_id _) η ≡ η.
Proof. repeat intros ?; rewrite /= right_id //. Qed.


Program Definition FuncCat C D := MkCat (functor C D) natural natural_id (@natural_comp C D) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by auto using natrual_comp_assoc, natrual_comp_left_id, natrual_comp_right_id.

(* Presheaf categories *)

Definition PreSheaf C := functor (C ᵒᵖ) Setoid.

Definition PSh C := FuncCat (C ᵒᵖ) Setoid.
