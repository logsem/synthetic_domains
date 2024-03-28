From SynthDom Require Import prelude.

Polymorphic Record category := MkCat {
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
Global Arguments comp_assoc {C a b c d} f g h : rename.

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
Global Arguments MkNat {_ _ _ _} _ _.
Global Arguments nat_map {C D F G} η c : rename.
Global Arguments naturality {C D F G} η [a b] f : rename.

Notation "( η ₙ)" := (nat_map η) : category_scope.
Notation "η 'ₙ' c" := (nat_map η c) (at level 40, no associativity) : category_scope.

Program Definition opposite C := MkCat (obj C) (λ a b, hom C b a) id (λ a b c, flip (comp C)) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by repeat intros ?; setoid_subst; rewrite /= ?comp_assoc ?left_id ?right_id.
Fail Next Obligation.

Notation "C 'ᵒᵖ'" := (opposite C) (at level 75).

(* Isomorphisms *)

Record isomorphism {C a b} (f : hom C a b) (g : hom C b a) := MkIso {
  iso_lr : g ∘ f ≡ id _;
  iso_rl : f ∘ g ≡ id _;
}.
Global Arguments MkIso {_ _ _ _ _} _ _.
Global Arguments iso_lr {_ _ _ _ _} _.
Global Arguments iso_rl {_ _ _ _ _} _.

Record isomorphic {C} a b := MkIsoIc {forward : hom C a b; backward : hom C b a; is_iso : isomorphism forward backward}.
Global Arguments MkIsoIc {_ _ _} _ _ _.
Global Arguments forward {_ _ _} _.
Global Arguments backward {_ _ _} _.
Global Arguments is_iso {_ _ _} _.

Infix "≃" := isomorphic (at level 70, no associativity) : category_scope.
Infix "≃@{ C }" := (@isomorphic C) (at level 70, only parsing, no associativity) : category_scope.

Program Definition ismorphism_id {C} c : isomorphism (@id C c) (@id C c) := {|  iso_lr := _; iso_rl := _; |}.
Solve All Obligations with by repeat intros ?; rewrite left_id.
Fail Next Obligation.
Definition ismorphism_swap {C a b} {f : hom C a b} {g : hom C b a} (iso : isomorphism f g) : isomorphism g f :=
  MkIso (iso_rl iso) (iso_lr iso).
Program Definition ismorphism_compose {C a b c}
  {f : hom C a b} {g : hom C b a} (iso : isomorphism f g)
  {h : hom C b c} {i : hom C c b} (iso : isomorphism h i) : isomorphism (h ∘ f) (g ∘ i) := MkIso _ _.
Next Obligation.
  intros ???? f g isofg h i isohi; rewrite (comp_assoc _ _ g) -(comp_assoc _ _ i) (iso_lr isohi) left_id (iso_lr isofg) //.
Qed.
Next Obligation.
  intros ???? f g isofg h i isohi. rewrite (comp_assoc _ _ h) -(comp_assoc _ _ f) (iso_rl isofg) left_id (iso_rl isohi) //.
Qed.
Fail Next Obligation.

Definition isomorphic_refl {C} (c : obj C) : isomorphic c c := MkIsoIc _ _ (ismorphism_id _).
Definition isomorphic_symm {C} (a b : obj C) : isomorphic a b → isomorphic b a :=
  λ iso, MkIsoIc _ _ (ismorphism_swap (is_iso iso)).
Definition isomorphic_trans {C} (a b c : obj C) : isomorphic a b → isomorphic b c → isomorphic a c :=
  λ iso1 iso2, MkIsoIc _ _ (ismorphism_compose (is_iso iso1) (is_iso iso2)).

(* Helper tactic. *)
Ltac solve_by_equiv_rewrite :=
  by repeat match goal with Heq : context [equiv _ _] |- _ => first [rewrite Heq| rewrite (Heq _)] end; eauto.

(* Discrete categories *)

Program Definition Discr (A : Type) := MkCat A (=) (@eq_refl A) (@eq_trans A) (λ _ _ _ _, True) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

(* Category of setoids (Set) *)

Record setoid := MkSetoid { setoid_set :> Type; setoid_eq : Equiv setoid_set; setoid_eq_equiv : Equivalence setoid_eq; }.
Global Existing Instance setoid_eq.
Global Existing Instance setoid_eq_equiv.
Record setoid_fun (A B : setoid) := MkSetoidFun {
  setoid_fun_map :> A → B;
  setoid_fun_map_proper : Proper ((≡) ==> (≡)) setoid_fun_map
}.
Global Existing Instance setoid_fun_map_proper.
Arguments MkSetoidFun {_ _} _ _.
Notation "'λset' x .. y , t" := (MkSetoidFun (λ x .. y, t) _) (at level 10, x binder, y binder, t at level 200,
  format "'[ ' '[ ' 'λset' x .. y ']' , '/' t ']'").
Global Instance setoid_fun_eq A B : Equiv (setoid_fun A B) := respectful (≡) (≡).
Global Instance setoid_fun_eq_equiv A B : Equivalence (≡@{setoid_fun A B}).
Proof. split; repeat intros ?; solve_by_equiv_rewrite. Qed.

Global Instance setoid_fun_map_proper' : ∀ A B, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_fun_map A B).
Proof. intros ???? Heq ???; apply Heq; done. Qed.
Program Definition setoid_compose {A B C} (f : setoid_fun A B) (g : setoid_fun B C) : setoid_fun A C :=
  λset x, g (f x).
Solve All Obligations with by intros ????????; setoid_subst.
Fail Next Obligation.
Global Instance setoid_compose_proper : ∀ A B C, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_compose A B C).
Proof. intros ????????????; setoid_subst; done. Qed.

Program Definition Setoid := MkCat setoid setoid_fun (λ _, λset x, x) (@setoid_compose) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by repeat intros ?; rewrite /=; setoid_subst.
Fail Next Obligation.

(* Functor categories *)

Global Instance natural_eq {C D} {F G : functor C D} : Equiv (natural F G) := λ η ρ, ∀ a, η ₙ a ≡ ρ ₙ a.
Global Instance nat_map_proper : ∀ C D (F G : functor C D), Proper ((≡) ==>  forall_relation (λ _, (≡))) (@nat_map C D F G).
Proof. intros ?????? Heq ?; apply Heq. Qed.
Global Instance natural_eq_equiv {C D} {F G : functor C D} : Equivalence (≡@{natural F G}).
Proof. split; repeat intros ?; solve_by_equiv_rewrite. Qed.

Program Definition natural_id {C D} (F : functor C D) : natural F F := MkNat (λ x, id (F ₒ x)) _.
Solve All Obligations with by intros ??????; rewrite /= left_id right_id.
Fail Next Obligation.

Program Definition natural_comp {C D} {F G H : functor C D} (η : natural F G) (ρ : natural G H) : natural F H :=
  MkNat (λ c, (ρ ₙ c) ∘ (η ₙ c)) _.
Solve All Obligations with by repeat intros ?; rewrite /= !comp_assoc naturality -!comp_assoc naturality.
Fail Next Obligation.
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
Fail Next Obligation.

(* Presheaf categories *)

Definition PreSheaf C := functor (C ᵒᵖ) Setoid.

Definition PSh C := FuncCat (C ᵒᵖ) Setoid.

(* Terminal Object *)

Record is_terminal {C} (t : obj C) := MkIsTerm { bang : ∀ c, hom c t; bang_unique : ∀ c (f : hom c t), f ≡ bang c }.
Global Arguments MkIsTerm {_} _ _.
Global Arguments bang {_ _} _.
Global Arguments bang_unique {_ _} _ [_] _.

Record terminal C := MkTerm { term : obj C; term_is_terminal : is_terminal term; }.
Global Arguments MkTerm {_} _ _.
Global Arguments term {_} _.
Global Arguments term_is_terminal {_} _.

Program Definition is_term_unique {C} (t t' : obj C) : is_terminal t → is_terminal t' → isomorphic t t' :=
λ it it', MkIsoIc (bang it' t) (bang it t') _.
Next Obligation.
Proof.
  split.
  - rewrite ?(bang_unique it (id _)) ?(bang_unique it (_ ∘ _)) //.
  - rewrite ?(bang_unique it' (id _)) ?(bang_unique it' (_ ∘ _)) //.
Qed.
Fail Next Obligation.

(* Limits *)
Section Limit.
  Context {J C} (F : functor J C).

  Record cone := MkCone {
    vertex : obj C;
    side : ∀ j, hom vertex (F ₒ j);
    side_commutes : ∀ j j' f, side j' ≡ F ₕ f ∘ side j;
  }.

  Record cone_hom cn cn' := MkConeHom {
    cone_hom_map : hom (vertex cn) (vertex cn');
    cone_hom_commutes : ∀ j, side cn j ≡ side cn' j ∘ cone_hom_map;
  }.
  Arguments MkConeHom {_ _} _ _.
  Arguments cone_hom_map {_ _} _.

  Global Instance cone_hom_eq : ∀ cn cn', Equiv (cone_hom cn cn') := λ _ _ ch ch', cone_hom_map ch ≡ cone_hom_map ch'.
  Global Instance cone_hom_map_proper : ∀ cn cn', Proper ((≡) ==> (≡)) (@cone_hom_map cn cn').
  Proof. intros ???? Heq; exact Heq. Qed.
  Global Instance cone_hom_eq_equiv {cn cn'} : Equivalence (≡@{cone_hom cn cn'}).
  Proof. split; repeat intros []; rewrite /equiv /cone_hom_eq /=; repeat intros ?; solve_by_equiv_rewrite. Qed.

  Program Definition cone_hom_id cn : cone_hom cn cn := MkConeHom (id _) _.
  Solve All Obligations with by repeat intros ?; rewrite /= right_id.
  Fail Next Obligation.

  Program Definition cone_hom_comp {cn cn' cn''} (ch : cone_hom cn cn') (ch' : cone_hom cn' cn'') : cone_hom cn cn'' :=
  MkConeHom (cone_hom_map ch' ∘ cone_hom_map ch) _.
  Solve All Obligations with by repeat intros ?; rewrite -comp_assoc -!cone_hom_commutes.
  Fail Next Obligation.

  Global Instance cone_hom_comp_proper : ∀ cn cn' cn'', Proper ((≡) ==> (≡) ==> (≡)) (@cone_hom_comp cn cn' cn'').
  Proof. intros ??? [] [] Heq [] []; revert Heq; rewrite /= /equiv /cone_hom_eq /=; intros -> ->; done. Qed.
  Lemma cone_hom_comp_assoc : ∀ cn1 cn2 cn3 cn4 (ch1 : cone_hom cn1 cn2) (ch2 : cone_hom cn2 cn3) (ch3 : cone_hom cn3 cn4),
      cone_hom_comp ch1 (cone_hom_comp ch2 ch3) ≡ cone_hom_comp (cone_hom_comp ch1 ch2) ch3.
  Proof. intros ???? [] [] []; rewrite /= /equiv /cone_hom_eq /= comp_assoc; done. Qed.
  Lemma cone_hom_comp_left_id : ∀ cn cn' (ch : cone_hom cn cn'), cone_hom_comp ch (cone_hom_id _) ≡ ch.
  Proof. intros ?? []; rewrite /= /equiv /cone_hom_eq /= left_id; done. Qed.
  Lemma cone_hom_comp_right_id : ∀ cn cn' (ch : cone_hom cn cn'), cone_hom_comp (cone_hom_id _) ch ≡ ch.
  Proof. intros ?? []; rewrite /= /equiv /cone_hom_eq /= right_id; done. Qed.

  Program Definition ConeCat := MkCat cone cone_hom cone_hom_id (@cone_hom_comp) (λ _ _, (≡)) _ _ _ _ _.
  Solve All Obligations with by auto using cone_hom_comp_assoc, cone_hom_comp_left_id, cone_hom_comp_right_id.
  Fail Next Obligation.

  Definition is_limiting_cone cn := @is_terminal ConeCat cn.

  Definition limit := terminal ConeCat.

End Limit.
Global Arguments MkCone {_ _ _} _ _ _.
Global Arguments vertex {_ _ _} _.
Global Arguments side {_ _ _} _ _.
Global Arguments side_commutes {_ _ _} _ [_ _] _.
Global Arguments MkConeHom {_ _ _ _ _} _ _.
Global Arguments cone_hom {_ _ _} _ _.
Global Arguments cone_hom_map {_ _ _ _ _} _.
Global Arguments cone_hom_commutes {_ _ _ _ _} _ _.
Global Arguments is_limiting_cone {_ _ _} _.

Definition complete C := ∀ J (F : functor J C), limit F.

Global Instance sig_eq `{!Equiv A} (P : A → Prop) : Equiv (sig P) := λ x y, `x ≡ `y.
Global Instance sig_eq_equiv `{!Equiv A} (P : A → Prop) `{!Equivalence (≡@{A})} : Equivalence (≡@{sig P}).
Proof. split; repeat intros []; rewrite /equiv /sig_eq /=; try intros ->; eauto. Qed.
Global Instance proj1_sig_proper `{!Equiv A} (P : A → Prop) : Proper ((≡) ==> (≡)) (@proj1_sig _ P).
Proof. intros [] []; done. Qed.

Global Instance forall_eq `{!∀ a : A, Equiv (T a)} : Equiv (∀ a, T a) := forall_relation (λ x, (≡@{T x})).
Global Instance forall_eq_equiv `{!∀ a : A, Equiv (T a)} `{!∀ a, Equivalence (≡@{T a})} : Equivalence (≡@{∀ a, T a}).
Proof. split; repeat intros ?; solve_by_equiv_rewrite. Qed.

(* Completeness proofs *)

Section setoid_limit.
  Context {J} (F : functor J Setoid).

  Program Definition setoid_lim_obj :=
    MkSetoid { p : ∀ j, (F ₒ j) | ∀ j j' (f : hom J j j'), (F ₕ f) (p j) ≡ p j' } _ _.

  Program Definition setoid_lim_side : ∀ j, hom Setoid setoid_lim_obj (F ₒ j) :=
    λ j, λset x, proj1_sig x j.
  Solve All Obligations with intros ? [] [] ?; simpl in *; solve_by_equiv_rewrite.
  Fail Next Obligation.

  Program Definition setoid_lim_cone : cone F := MkCone setoid_lim_obj setoid_lim_side _.
  Solve All Obligations with by intros ????? ->; rewrite /setoid_lim_side /= -(proj2_sig y _ _ f).
  Fail Next Obligation.

  Program Definition setoid_fun_to_setoid_lim_cone (cn : cone F) :
    setoid_fun (vertex cn) (vertex setoid_lim_cone) :=
    λset x, exist _ (λ j, side cn j x) (λ _ _ f, symmetry (side_commutes cn f x x (reflexivity _))).
  Solve All Obligations with repeat intros ?; rewrite /=; solve_by_equiv_rewrite.
  Fail Next Obligation.

  Program Definition cone_hom_to_setoid_lim_cone cn : cone_hom cn setoid_lim_cone :=
    MkConeHom (setoid_fun_to_setoid_lim_cone cn) _.
  Solve All Obligations with by intros ???? ->.
  Fail Next Obligation.

  Program Definition setoid_lim_cone_is_limiting_cone : is_limiting_cone setoid_lim_cone :=
    MkIsTerm setoid_lim_cone cone_hom_to_setoid_lim_cone _.
  Next Obligation.
  Proof. intros cn [chm chmc] x y Heq j; pose proof (chmc j y x (symmetry Heq)) as Heq'; simpl in *; done. Qed.
  Fail Next Obligation.
End setoid_limit.

Program Definition setoid_complete : complete Setoid :=
  λ _ F, MkTerm (setoid_lim_cone F) (setoid_lim_cone_is_limiting_cone F).

Section psh_limit.
  Context {C} {J} (F : functor J (PSh C)).

  Program Definition pointwise_func : ∀ c : obj C, functor J Setoid :=
    λ c, MkFunc (λ j, (F ₒ j) ₒ c) (λ _ _ f, F ₕ f ₙ c) _ _.
  Solve All Obligations with repeat first [intros ->|intros ?]; rewrite /= ?h_map_comp ?h_map_id //=.
  Fail Next Obligation.

  Program Definition pointwise_cone (cn : cone F) c : cone (pointwise_func c) :=
    MkCone (vertex cn ₒ c) (λ j, side cn j ₙ c) (λ _ _ f, side_commutes cn f c).

  Program Definition psh_lim_func_hom a b (f : hom a b) :
    setoid_fun (setoid_lim_obj (pointwise_func b)) (setoid_lim_obj (pointwise_func a)) :=
    λset x, exist _ (λ j, (F ₒ j ₕ f) (`x j)) _.
  Next Obligation.
  Proof.
    intros ?? f x j ? g.
    rewrite -(proj2_sig x _ _ g).
    apply (naturality (F ₕ g) f (`x j) (`x j) (reflexivity _)).
  Qed.
  Next Obligation.
  Proof. intros ????? Heq z; rewrite /= (Heq z) //. Qed.
  Fail Next Obligation.

  Program Definition psh_lim_func : PreSheaf C :=
    MkFunc (λ c, setoid_lim_obj (pointwise_func c)) (λ a b f, psh_lim_func_hom b a f) _ _.
  Solve All Obligations with repeat first [intros ->| intros ?]; rewrite /= ?h_map_comp ?h_map_id //=.
  Fail Next Obligation.

  Program Definition psh_lim_side : ∀ j, hom (PSh C) psh_lim_func (F ₒ j) :=
    λ j, MkNat (λ c, MkSetoidFun (λ p, `p j) _) _.
  Solve All Obligations with repeat intros ?; solve_by_equiv_rewrite.
  Fail Next Obligation.

  Program Definition psh_lim_cone : cone F := MkCone psh_lim_func psh_lim_side _.
  Next Obligation. intros ????? z ->. rewrite /= (proj2_sig z _ _ f) //. Qed.
  Fail Next Obligation.

  Program Definition pointwise_cone_hom {cn : cone F} (h : cone_hom cn psh_lim_cone) c :
    cone_hom (pointwise_cone cn c) (setoid_lim_cone (pointwise_func c)) :=
    MkConeHom (cone_hom_map h ₙ c) _.
  Next Obligation. repeat intros ?; apply (cone_hom_commutes h); done. Qed.
  Fail Next Obligation.

  Program Definition natural_to_psh_lim_cone (cn : cone F) :
    natural (vertex cn) (vertex psh_lim_cone) :=
    MkNat (λ c, MkSetoidFun (λ x, setoid_fun_to_setoid_lim_cone (pointwise_func c) (pointwise_cone cn c) x) _) _.
  Next Obligation. repeat intros ?; solve_by_equiv_rewrite. Qed.
  Next Obligation. repeat intros ?; apply (naturality (side cn _)); done. Qed.
  Fail Next Obligation.

  Program Definition cone_hom_to_psh_lim_cone cn : cone_hom cn psh_lim_cone :=
    MkConeHom (natural_to_psh_lim_cone cn) _.
  Next Obligation. repeat intros ?; solve_by_equiv_rewrite. Qed.
  Fail Next Obligation.

  Program Definition psh_lim_cone_is_limiting_cone : is_limiting_cone psh_lim_cone :=
    MkIsTerm psh_lim_cone cone_hom_to_psh_lim_cone _.
  Next Obligation.
  Proof.
    intros ???????; simpl in *.
    apply (bang_unique (setoid_lim_cone_is_limiting_cone (pointwise_func _)) (pointwise_cone_hom f a)); done.
  Qed.

End psh_limit.

Program Definition presheaves_complete C : complete (PSh C) :=
  λ _ F, MkTerm (psh_lim_cone F) (psh_lim_cone_is_limiting_cone F).

