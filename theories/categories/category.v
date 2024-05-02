From SynthDom Require Import prelude.

(* Helper tactic. *)
Ltac solve_by_equiv_rewrite :=
  by repeat match goal with
         Heq : context [equiv _ _] |- _ => first [rewrite Heq| rewrite (Heq _)] end;
  eauto.

Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Inductive Empty@{i} : Type@{i} :=.

Global Hint Extern 0 => match goal with H : Empty |- _ => exfalso; inversion H end : core.

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
Global Arguments comp_assoc {C a b c d} f g h : rename.
Global Arguments left_id {C a b} f : rename.
Global Arguments right_id {C a b} f : rename.

Declare Scope category_scope.
Delimit Scope category_scope with category.

Local Open Scope category_scope.

Notation "g ∘{ C } f" := (comp C f g) (at level 40, left associativity) : category_scope.
Notation "g ∘ f" := (comp _ f g) : category_scope.

Program Definition SingletonCat : category :=
  MkCat unit (λ _ _, unit) (λ _, ()) (λ _ _ _ _ _, ()) (λ _ _ _ _, True) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

Record functor C D := MkFunc {
  o_map : obj C → obj D;
  h_map : ∀ a b, hom a b → hom (o_map a) (o_map b);
  h_map_proper : ∀ a b, Proper ((≡) ==> (≡)) (h_map a b);
  h_map_comp : ∀ a b c (f : hom a b) (g : hom b c), h_map _ _ (g ∘ f) ≡ h_map _ _ g ∘ h_map _ _ f;
  h_map_id : ∀ a, h_map _ _ (id a) ≡ (id _);
}.

Global Existing Instance h_map_proper.

Global Arguments MkFunc {_ _} _ _ _ _.
Global Arguments o_map {C D} F a : rename.
Global Arguments h_map {C D} F [a b] f : rename.

Notation "( F ₒ)" := (o_map F) (format "( F ₒ)") : category_scope.
Notation "F 'ₒ' a" := (o_map F a) (at level 40, no associativity, format "F ₒ  a") :
    category_scope.
Notation "( F ₕ)" := (h_map F) (format "( F ₕ)") : category_scope.
Notation "F 'ₕ' f" := (h_map F f) (at level 40, no associativity, format "F ₕ  f" ) :
    category_scope.

Program Definition id_functor C : functor C C := MkFunc (λ c, c) (λ _ _ f, f) _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

Program Definition functor_compose {C D E} (F : functor C D) (G : functor D E) : functor C E :=
MkFunc (λ c, G ₒ (F ₒ c)) (λ _ _ f, G ₕ (F ₕ f)) _ _ _.
Solve All Obligations with
  repeat intros ?; rewrite /= ?h_map_comp ?h_map_id; solve_by_equiv_rewrite.
Fail Next Obligation.

Definition hom_trans {C} {a b c d: obj C} (heq : a = c) (heq' : b = d) (f : hom a b) : hom c d :=
    match heq in _ = z return hom z _ with
      eq_refl =>
        match heq' in _ = w return hom _ w with
          eq_refl => f
        end
    end.

Lemma hom_trans_id {C a b} (Heq : a = b) : hom_trans Heq Heq (@id C a) ≡ id b.
Proof. destruct Heq; done. Qed.

Lemma hom_trans_refl {C a b} (f : hom C a b) : hom_trans eq_refl eq_refl f ≡ f.
Proof. done. Qed.

Lemma hom_trans_sym {C a b c d} heq heq' (f : hom C a b) (g : hom C c d) :
  hom_trans heq heq' f ≡ g → f ≡ hom_trans (eq_sym heq) (eq_sym heq') g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_sym' {C a b c d} heq heq' (f : hom C a b) (g : hom C c d) :
  hom_trans (eq_sym heq) (eq_sym heq') f ≡ g → f ≡ hom_trans heq heq' g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_trans {C a b c d c' d'}
  (heq1 : a = c) (heq1' : b = d) (heq2 : c = c') (heq2' : d = d') (f : hom C a b) :
  hom_trans (eq_trans heq1 heq2) (eq_trans heq1' heq2') f ≡
  hom_trans heq2 heq2' (hom_trans heq1 heq1' f).
Proof. destruct heq1; destruct heq1'; destruct heq2; destruct heq2'; done. Qed.

Lemma hom_trans_compose {C} {a b c d e : obj C} (heq : a = d) (heq' : c = e)
  (f : hom a b) (g : hom b c) :
  hom_trans heq heq' (g ∘ f) ≡ hom_trans eq_refl heq' g ∘ hom_trans heq eq_refl f.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_l {C} {a b c d e : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom d e) :
  g ∘ hom_trans heq heq' f ≡ hom_trans (eq_sym heq') eq_refl g ∘ hom_trans heq eq_refl f.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_r {C} {e a b c d : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom e c) :
  hom_trans heq heq' f ∘ g ≡ hom_trans eq_refl heq' f ∘ hom_trans eq_refl (eq_sym heq) g.
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_take_in_l {C} {a b c d e : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom d e) :
  g ∘ hom_trans heq heq' f ≡ hom_trans heq eq_refl (hom_trans (eq_sym heq') eq_refl g ∘ f).
Proof. destruct heq; destruct heq'; done. Qed.

Lemma hom_trans_compose_take_in_r {C} {e a b c d : obj C} (heq : a = c) (heq' : b = d)
  (f : hom a b) (g : hom e c) :
  hom_trans heq heq' f ∘ g ≡ hom_trans eq_refl heq' (f ∘ hom_trans eq_refl (eq_sym heq) g).
Proof. destruct heq; destruct heq'; done. Qed.

Global Arguments hom_trans : simpl never.

Global Instance hom_trans_proper {C} {a b c d : obj C} (heq : a = c) (heq' : b = d) :
  Proper ((≡) ==> (≡)) (hom_trans heq heq').
Proof. intros ???; destruct heq; destruct heq'; done. Qed.

Record functor_equiv {C D} (F G : functor C D) := MkFuncEq {
  func_eq_o_map : ∀ a, F ₒ a = G ₒ a;
  func_eq_h_map :
    ∀ a b (f : hom C a b), hom_trans (func_eq_o_map a) (func_eq_o_map b) (F ₕ f) ≡ G ₕ f;
}.
Global Arguments MkFuncEq {_ _ _ _} _ _, {_ _} _ _ _ _.
Global Arguments func_eq_o_map {_ _ _ _} _ _.
Global Arguments func_eq_h_map {_ _ _ _} _ [_ _] _.

Global Instance functor_equiv_instance C D : Equiv (functor C D) := functor_equiv.
Global Instance functor_equiv_equiv C D : Equivalence (≡@{functor C D}).
Proof.
  split.
  - intros F; refine (MkFuncEq (λ _, eq_refl) _); done.
  - intros F G [Hoeq Hheq].
    refine (MkFuncEq (λ _, eq_sym (Hoeq _)) _).
    intros.
    symmetry; apply hom_trans_sym; rewrite Hheq; done.
  - intros ??? [Hoeq Hheq] [Hoeq' Hheq'].
    refine (MkFuncEq (λ _, eq_trans (Hoeq _) (Hoeq' _)) _).
    intros ???; rewrite hom_trans_trans Hheq; done.
Qed.

Global Instance functor_compose_proepr C D E :
  Proper ((≡) ==> (≡) ==> (≡)) (@functor_compose C D E).
Proof.
  intros F G [Hoeq Hheq] F' G' [Hoeq' Hheq']; simpl in *.
  pose (λ a, match Hoeq a in _ = z return F' ₒ (F ₒ a) =
    G' ₒ z with eq_refl => Hoeq' (F ₒ _) end) as Hcoeq.
  refine (MkFuncEq (functor_compose F F') (functor_compose G G') (λ _, Hcoeq _) _).
  intros ???; simpl.
  transitivity (G' ₕ (hom_trans (Hoeq a) (Hoeq b) (F ₕ f))).
  - rewrite /Hcoeq. do 2 destruct Hoeq; rewrite /=; done.
  - f_equiv; done.
Qed.

Program Definition Cat : category :=
  MkCat category functor id_functor (λ _ _ _ F G, functor_compose F G) (λ _ _, (≡)) _ _ _ _ _.
Next Obligation.
  intros ???? F G H; rewrite /=.
  refine (MkFuncEq (functor_compose F (functor_compose G H))
    (functor_compose (functor_compose F G) H) (λ _, eq_refl) _); done.
Qed.
Next Obligation.
  intros ?? F; rewrite /=.
  refine (MkFuncEq (functor_compose F (id_functor _)) F (λ _, eq_refl) _); done.
Qed.
Next Obligation.
  intros ?? F; rewrite /=.
  refine (MkFuncEq (functor_compose (id_functor _) F) F (λ _, eq_refl) _); done.
Qed.

Program Definition cat_prod (C D : category) : category :=
  MkCat
    (obj C * obj D)
    (λ cd cd', hom C cd.1 cd'.1 * hom D cd.2 cd'.2)%type
    (λ cd, (id cd.1, id cd.2))
    (λ _ _ _ f g, (g.1 ∘ f.1, g.2 ∘ f.2))
    (λ _ _ f g, f.1 ≡ g.1 ∧ f.2 ≡ g.2)
    _ _ _ _ _.
Solve All Obligations with
  repeat first [intros []|intros ?]; simpl in *; try f_equiv; solve_by_equiv_rewrite.
Fail Next Obligation.

Program Definition cat_proj1 {C D} : functor (cat_prod C D) C :=
  MkFunc (λ cd, cd.1) (λ _ _ f, f.1) _ (λ _ _ _ _ _, reflexivity _) (λ _, reflexivity _).
Program Definition cat_proj2 {C D} : functor (cat_prod C D) D :=
  MkFunc (λ cd, cd.2) (λ _ _ f, f.2) _ (λ _ _ _ _ _, reflexivity _) (λ _, reflexivity _).

Program Definition functor_prod {C D C' D'} (F : functor C D) (G : functor C' D') :
  functor (cat_prod C C') (cat_prod D D') :=
  MkFunc (λ ab, (F ₒ ab.1, G ₒ ab.2)) (λ _ _ f, (F ₕ f.1, G ₕ f.2)) _ _ _.
Solve All Obligations with
  repeat intros ?; rewrite /=; f_equiv; rewrite ?h_map_comp ?h_map_id; solve_by_equiv_rewrite.
Fail Next Obligation.

Program Definition const_functor {C} (c : obj C) : functor SingletonCat C :=
  MkFunc (λ _, c) (λ _ _ _, id c) _ _ _.
Solve All Obligations with repeat intros ?; rewrite /= ?left_id //.
Fail Next Obligation.

Record natural {C D} (F G : functor C D) := MkNat {
  nat_map : ∀ c, hom (F ₒ c) (G ₒ c);
  naturality : ∀ a b (f : hom a b), nat_map b ∘ (F ₕ f) ≡ (G ₕ f) ∘ nat_map a;
}.
Global Arguments MkNat {_ _ _ _} _ _.
Global Arguments nat_map {C D F G} η c : rename.
Global Arguments naturality {C D F G} η [a b] f : rename.

Notation "( η ₙ)" := (nat_map η) (format "( η ₙ)") : category_scope.
Notation "η 'ₙ' c" := (nat_map η c) (at level 40, no associativity, format "η ₙ  c") :
    category_scope.

(* Functor categories *)

Global Instance natural_eq {C D} {F G : functor C D} : Equiv (natural F G) :=
  λ η ρ, ∀ a, η ₙ a ≡ ρ ₙ a.
Global Instance nat_map_proper :
  ∀ C D (F G : functor C D), Proper ((≡) ==>  forall_relation (λ _, (≡))) (@nat_map C D F G).
Proof. intros ?????? Heq ?; apply Heq. Qed.
Global Instance natural_eq_equiv {C D} {F G : functor C D} : Equivalence (≡@{natural F G}).
Proof. split; repeat intros ?; solve_by_equiv_rewrite. Qed.

Program Definition natural_id {C D} (F : functor C D) : natural F F := MkNat (λ x, id (F ₒ x)) _.
Solve All Obligations with by intros ??????; rewrite /= left_id right_id.
Fail Next Obligation.

Program Definition natural_comp {C D} {F G H : functor C D} (η : natural F G) (ρ : natural G H) :
  natural F H := MkNat (λ c, (ρ ₙ c) ∘ (η ₙ c)) _.
Solve All Obligations with
  by repeat intros ?; rewrite /= !comp_assoc naturality -!comp_assoc naturality.
Fail Next Obligation.
Global Instance natural_comp_proper :
  ∀ {C D} {F G H : functor C D}, Proper ((≡) ==> (≡) ==> (≡)) (@natural_comp C D F G H).
Proof. repeat intros ?; rewrite /=; solve_by_equiv_rewrite. Qed.
Lemma natrual_comp_assoc :
  ∀ (C D : category) (F G H I : functor C D) (η : natural F G) (ρ : natural G H) (δ : natural H I),
    natural_comp η (natural_comp ρ δ) ≡ natural_comp (natural_comp η ρ) δ.
Proof. repeat intros ?; rewrite /= !comp_assoc //. Qed.
Lemma natrual_comp_left_id :
  ∀ (C D : category) (F G : functor C D) (η : natural F G), natural_comp η (natural_id _) ≡ η.
Proof. repeat intros ?; rewrite /= left_id //. Qed.
Lemma natrual_comp_right_id :
  ∀ (C D : category) (F G : functor C D) (η : natural F G), natural_comp (natural_id _) η ≡ η.
Proof. repeat intros ?; rewrite /= right_id //. Qed.

Program Definition FuncCat C D :=
  MkCat (functor C D) natural natural_id (@natural_comp C D) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with
  by auto using natrual_comp_assoc, natrual_comp_left_id, natrual_comp_right_id.
Fail Next Obligation.

Program Definition hor_comp {C D E} {F G : functor C D} {F' G' : functor D E}
  (η : natural F G) (η' : natural F' G') : natural (functor_compose F F') (functor_compose G G') :=
  MkNat (λ a, (η' ₙ (G ₒ a)) ∘ (F' ₕ (η ₙ a))) _.
Next Obligation.
  repeat intros ?; rewrite /=.
  rewrite !naturality !comp_assoc !naturality -!comp_assoc -!h_map_comp !naturality //.
Qed.

Global Instance hor_comp_proper {C D E F G F' G'} :
  Proper ((≡) ==> (≡) ==> (≡)) (@hor_comp C D E F G F' G').
Proof. repeat intros ?; rewrite /=; solve_by_equiv_rewrite. Qed.

Program Definition functor_eq_natural {C D} {F G : functor C D} (Heq : F ≡ G) : natural F G :=
  MkNat (λ a, hom_trans eq_refl (func_eq_o_map Heq a) (id _)) _.
Next Obligation.
  repeat intros ?; simpl.
  rewrite hom_trans_compose_take_in_r left_id /= hom_trans_refl.
  rewrite hom_trans_compose_take_in_l right_id /= hom_trans_refl.
  change (eq_refl (G ₒ b)) with (eq_sym (eq_refl (G ₒ b))).
  apply hom_trans_sym.
  rewrite -hom_trans_trans /= eq_trans_refl_l.
  apply Heq.
Qed.

Definition opposite C :=
  MkCat (obj C) (λ a b, hom C b a) id (λ a b c, flip (comp C)) (λ _ _, (≡))
  (λ _ _, hom_eq_equiv C _ _)
  (λ _ _ _ _ _ Heq1 _ _ Heq2, comp_proper C _ _ _ _ _ Heq2 _ _ Heq1)
  (λ _ _ _ _ f g h, symmetry (comp_assoc h g f))
  (λ _ _ f, right_id f)
  (λ _ _ f, left_id f).

Notation "C 'ᵒᵖ'" := (opposite C) (at level 75, format "C ᵒᵖ").

Program Definition opposite_func {C D} (F : functor C D) : functor (C ᵒᵖ) (D ᵒᵖ) :=
  MkFunc (λ c : obj (C ᵒᵖ), F ₒ c) (λ _ _ f, F ₕ f) _ _ _.
Solve All Obligations
  with repeat intros ?; rewrite /= ?h_map_comp ?h_map_id; solve_by_equiv_rewrite.
Fail Next Obligation.

(* Isomorphisms *)

Record isomorphism {C a b} (f : hom C a b) (g : hom C b a) := MkIso {
  iso_lr : g ∘ f ≡ id _;
  iso_rl : f ∘ g ≡ id _;
}.
Global Arguments MkIso {_ _ _ _ _} _ _.
Global Arguments iso_lr {_ _ _ _ _} _.
Global Arguments iso_rl {_ _ _ _ _} _.

Record isomorphic {C} a b := MkIsoIc {
  forward : hom C a b;
  backward : hom C b a;
  is_iso : isomorphism forward backward
}.
Global Arguments MkIsoIc {_ _ _} _ _ _.
Global Arguments forward {_ _ _} _.
Global Arguments backward {_ _ _} _.
Global Arguments is_iso {_ _ _} _.

Infix "≃" := isomorphic (at level 70, no associativity) : category_scope.
Infix "≃@{ C }" := (@isomorphic C) (at level 70, only parsing, no associativity) : category_scope.

Program Definition ismorphism_id {C} c : isomorphism (@id C c) (@id C c) := MkIso _ _.
Solve All Obligations with by repeat intros ?; rewrite left_id.
Fail Next Obligation.
Definition ismorphism_swap {C a b} {f : hom C a b} {g : hom C b a} (iso : isomorphism f g) :
  isomorphism g f := MkIso (iso_rl iso) (iso_lr iso).
Program Definition ismorphism_compose {C a b c}
  {f : hom C a b} {g : hom C b a} (iso : isomorphism f g)
  {h : hom C b c} {i : hom C c b} (iso : isomorphism h i) :
  isomorphism (h ∘ f) (g ∘ i) := MkIso _ _.
Next Obligation.
  intros ???? f g isofg h i isohi.
  rewrite (comp_assoc _ _ g) -(comp_assoc _ _ i) (iso_lr isohi) left_id (iso_lr isofg) //.
Qed.
Next Obligation.
  intros ???? f g isofg h i isohi.
  rewrite (comp_assoc _ _ h) -(comp_assoc _ _ f) (iso_rl isofg) left_id (iso_rl isohi) //.
Qed.
Fail Next Obligation.

Definition isomorphic_refl {C} (c : obj C) : isomorphic c c := MkIsoIc _ _ (ismorphism_id _).
Definition isomorphic_symm {C} (a b : obj C) : isomorphic a b → isomorphic b a :=
  λ iso, MkIsoIc _ _ (ismorphism_swap (is_iso iso)).
Definition isomorphic_trans {C} (a b c : obj C) :
  isomorphic a b → isomorphic b c → isomorphic a c :=
  λ iso1 iso2, MkIsoIc _ _ (ismorphism_compose (is_iso iso1) (is_iso iso2)).

(* Discrete categories *)

Program Definition Discr (A : Type) :=
  MkCat A (=) (@eq_refl A) (@eq_trans A) (λ _ _ _ _, True) _ _ _ _ _.
Solve All Obligations with done.
Fail Next Obligation.

Definition EmpCat := Discr Empty.

Program Definition func_from_EmpCat C : functor EmpCat C :=
  MkFunc (λ a, Empty_rect _ a) (λ a _ _, Empty_rect (λ _, hom C _ _) a) _ _ _.
Solve All Obligations with by simpl.
Fail Next Obligation.

Definition UnitCat := Discr unit.

Program Definition func_to_UnitCat C : functor C UnitCat :=
  MkFunc (λ _, ()) (λ _ _ _, reflexivity _) _ _ _.
Solve All Obligations with by repeat intros ?.
Fail Next Obligation.

(* Category of setoids (Set) *)

Record setoid := MkSetoid {
  setoid_set :> Type;
  setoid_eq : Equiv setoid_set;
  setoid_eq_equiv : Equivalence setoid_eq;
}.
Global Existing Instance setoid_eq.
Global Existing Instance setoid_eq_equiv.
Record setoid_fun (A B : setoid) := MkSetoidFun {
  setoid_fun_map :> A → B;
  setoid_fun_map_proper : Proper ((≡) ==> (≡)) setoid_fun_map
}.
Global Existing Instance setoid_fun_map_proper.
Arguments MkSetoidFun {_ _} _ _.
Notation "'λset' x .. y , t" :=
  (MkSetoidFun (λ x .. y, t) _) (at level 10, x binder, y binder, t at level 200,
  format "'[ ' '[ ' 'λset' x .. y ']' , '/' t ']'").
Global Instance setoid_fun_eq A B : Equiv (setoid_fun A B) := respectful (≡) (≡).
Global Instance setoid_fun_eq_equiv A B : Equivalence (≡@{setoid_fun A B}).
Proof. split; repeat intros ?; solve_by_equiv_rewrite. Qed.

Global Instance setoid_fun_map_proper' :
  ∀ A B, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_fun_map A B).
Proof. intros ???? Heq ???; apply Heq; done. Qed.
Program Definition setoid_compose {A B C} (f : setoid_fun A B) (g : setoid_fun B C) :
  setoid_fun A C := λset x, g (f x).
Solve All Obligations with by intros ????????; setoid_subst.
Fail Next Obligation.
Global Instance setoid_compose_proper :
  ∀ A B C, Proper ((≡) ==> (≡) ==> (≡)) (@setoid_compose A B C).
Proof. intros ????????????; rewrite /=; solve_by_equiv_rewrite. Qed.

Program Definition Setoid :=
  MkCat setoid setoid_fun (λ _, λset x, x) (@setoid_compose) (λ _ _, (≡)) _ _ _ _ _.
Solve All Obligations with by repeat intros ?; rewrite /=; setoid_subst.
Fail Next Obligation.

Program Definition empty_setoid : setoid := MkSetoid False (λ _ _, False) _.
Next Obligation. split; repeat intros ?; done. Qed.
Fail Next Obligation.
Definition singleton_setoid : setoid := MkSetoid unit (≡) _.

(* Presheaf categories *)

Definition PreSheaf C := functor (C ᵒᵖ) Setoid.

Definition PSh C := FuncCat (C ᵒᵖ) Setoid.

(* hom functor *)

Definition hom_setoid C (a b : obj C) : setoid := MkSetoid (hom C a b) _ _.

Program Definition compose_as_hom_setoid_map C {a b c d} (f : hom C a b) (g : hom C c d) :
  setoid_fun (hom_setoid _ b c) (hom_setoid _ a d) := λset h, g ∘ h ∘ f.
Next Obligation. repeat intros ?; solve_by_equiv_rewrite. Qed.
Fail Next Obligation.

Global Instance compose_as_hom_setoid_map_proper C {a b c d} :
  Proper ((≡) ==> (≡) ==> (≡)) (@compose_as_hom_setoid_map C a b c d).
Proof. repeat intros ?; simpl; solve_by_equiv_rewrite. Qed.

Program Definition Hom C : functor (cat_prod (C ᵒᵖ) C) Setoid :=
  MkFunc (λ ab, hom_setoid C ab.1 ab.2) (λ _ _ f, compose_as_hom_setoid_map C f.1 f.2) _ _ _.
Solve All Obligations
  with repeat intros ?; rewrite /= ?comp_assoc ?left_id ?right_id; solve_by_equiv_rewrite.
Fail Next Obligation.

Definition adjunction {C D} (F : functor C D) (G : functor D C) : Type :=
  functor_compose (functor_prod (id_functor (C ᵒᵖ)) G) (Hom C)
  ≃@{FuncCat (cat_prod (C ᵒᵖ) D) Setoid}
  functor_compose (functor_prod (opposite_func F) (id_functor D)) (Hom D).

(* Terminal Object *)

Record is_terminal {C} (t : obj C) :=
  MkIsTerm { bang : ∀ c, hom c t; bang_unique : ∀ c (f : hom c t), f ≡ bang c }.
Global Arguments MkIsTerm {_} _ _.
Global Arguments bang {_ _} _.
Global Arguments bang_unique {_ _} _ [_] _.

Record terminal C := MkTerm { term : obj C; term_is_terminal : is_terminal term; }.
Global Arguments MkTerm {_} _ _.
Global Arguments term {_} _.
Global Arguments term_is_terminal {_} _.

Program Definition is_term_unique {C} (t t' : obj C) :
  is_terminal t → is_terminal t' → isomorphic t t' :=
  λ it it', MkIsoIc (bang it' t) (bang it t') _.
Next Obligation.
Proof.
  split.
  - rewrite ?(bang_unique it (id _)) ?(bang_unique it (_ ∘ _)) //.
  - rewrite ?(bang_unique it' (id _)) ?(bang_unique it' (_ ∘ _)) //.
Qed.
Fail Next Obligation.

Class HasTerm C := term_of : terminal C.
Global Arguments term_of _ {_}.

Record product {C} (a b : obj C) := MkProd {
  prd : obj C;
  prj1 : hom prd a;
  prj2 : hom prd b;
  prd_hom d (p1 : hom d a) (p2 : hom d b) : hom d prd;
  prd_hom_commutes1 d p1 p2 : p1 ≡ prj1 ∘ (prd_hom d p1 p2);
  prd_hom_commutes2 d p1 p2 : p2 ≡ prj2 ∘ (prd_hom d p1 p2);
  prd_hom_unique d p1 p2 (h : hom d prd) :
    p1 ≡ prj1 ∘ h → p2 ≡ prj2 ∘ h → h ≡ prd_hom d p1 p2;
}.

Global Arguments prd {_ _ _} _.
Global Arguments prj1 {_ _ _} _.
Global Arguments prj2 {_ _ _} _.
Global Arguments prd_hom {_ _ _} _ {_} _ _.
Global Arguments prd_hom_commutes1 {_ _ _} _ {_} _ _.
Global Arguments prd_hom_commutes2 {_ _ _} _ {_} _ _.
Global Arguments prd_hom_unique {_ _ _} _ {_} _ _ _.

Global Instance prd_hom_proper {C a b p d} :
  Proper ((≡) ==> (≡) ==> (≡)) (@prd_hom C a b p d).
Proof.
  intros ??????; apply prd_hom_unique;
    by rewrite -?prd_hom_commutes1 -?prd_hom_commutes2.
Qed.

Class HasProducts C := product_of (a b : obj C) : product a b.
Global Arguments product_of {_ _} _ _, _ {_} _ _.

Definition obj_prod `{!HasProducts C} a b : obj C := prd (product_of a b).

Definition hom_prod `{!HasProducts C} {a b c d} (f : hom a c) (g : hom b d) :
  hom (obj_prod a b) (obj_prod c d) := prd_hom _ (f ∘ prj1 _) (g ∘ prj2 _).

Infix "×ₒ@{ C }" := (obj_prod (C := C)) (at level 40, left associativity).
Infix "×ₒ" := obj_prod (at level 40, left associativity).
Infix "×ₕ@{ C }" := (hom_prod (C := C)) (at level 40, left associativity).
Infix "×ₕ" := hom_prod (at level 40, left associativity).

Global Instance hom_prod_proper `{!HasProducts C} {a b c d} :
  Proper ((≡) ==> (≡) ==> (≡)) (@hom_prod C _ a b c d).
Proof.
  repeat intros ?; apply prd_hom_unique; setoid_subst;
    by rewrite -?prd_hom_commutes1 -?prd_hom_commutes2.
Qed.

Lemma hom_prod_comp `{!HasProducts C} {a b c d e f}
  (g1 : hom a c) (g2 : hom c e) (h1 : hom b d) (h2 : hom d f) :
  (g2 ∘ g1) ×ₕ (h2 ∘ h1) ≡ (g2 ×ₕ h2) ∘ (g1 ×ₕ h1).
Proof.
  symmetry; apply prd_hom_unique.
  - rewrite -!comp_assoc -prd_hom_commutes1 !comp_assoc -prd_hom_commutes1 //.
  - rewrite -!comp_assoc -prd_hom_commutes2 !comp_assoc -prd_hom_commutes2 //.
Qed.
Lemma hom_prod_id `{!HasProducts C} {a b} : (id a) ×ₕ (id b) ≡ id (a ×ₒ b).
Proof. symmetry; apply prd_hom_unique; rewrite left_id right_id //. Qed.

Lemma hom_prod_split `{!HasProducts C} {a b c d} (f : hom a c) (g : hom b d) :
  f ×ₕ g ≡ id _ ×ₕ g ∘ (f ×ₕ id _).
Proof. rewrite -hom_prod_comp left_id right_id //. Qed.

Program Definition prod_func `{!HasProducts C} : functor (cat_prod C C) C :=
  MkFunc (λ ab, ab.1 ×ₒ ab.2) (λ _ _ h, h.1 ×ₕ h.2) _ _ _.
Next Obligation. intros ??; repeat intros []; simpl in *; setoid_subst; done. Qed.
Next Obligation. repeat intros ?; apply hom_prod_comp. Qed.
Next Obligation. repeat intros ?; apply hom_prod_id. Qed.
Fail Next Obligation.

Record exponential `{!HasTerm C, !HasProducts C} (a b : obj C) := MkExp {
  exp : obj C;
  eval : hom (a ×ₒ exp) b;
  exp_hom d (f : hom (a ×ₒ d) b) : hom d exp;
  exp_hom_commutes d f : f ≡ eval ∘ (id a ×ₕ exp_hom d f);
  exp_hom_unique d f h : f ≡ eval ∘ (id a ×ₕ h) → h ≡ exp_hom d f;
}.

Global Arguments exp {_ _ _ _ _} _.
Global Arguments eval {_ _ _ _ _} _.
Global Arguments exp_hom {_ _ _ _ _} _ {_} _.
Global Arguments exp_hom_commutes {_ _ _ _ _} _ {_} _.
Global Arguments exp_hom_unique {_ _ _ _ _} _ {_} _ _ _.

Global Instance exp_hom_proper `{!HasTerm C, !HasProducts C} {a b e d} :
  Proper ((≡) ==> (≡)) (@exp_hom C _ _ a b e d).
Proof. intros ???; apply exp_hom_unique; by rewrite -?exp_hom_commutes. Qed.

Lemma exp_hom_commutes_gen `{!HasTerm C, !HasProducts C} {a b c d}
  (e : exponential a b) (g : hom d a) f :
  eval e ∘ (g ×ₕ exp_hom e f) ≡ f ∘ (g ×ₕ id c).
Proof. rewrite hom_prod_split -comp_assoc -exp_hom_commutes //. Qed.

Class HasExponentials C `{!HasTerm C, !HasProducts C} :=
  exponential_of (a b : obj C) : exponential a b.
Global Arguments exponential_of {_ _ _ _} _ _, _ {_ _ _} _ _.

Definition obj_exp `{!HasTerm C, !HasProducts C, !HasExponentials C} a b : obj C :=
  exp (exponential_of a b).

Definition hom_exp `{!HasTerm C, !HasProducts C, !HasExponentials C} {a b c d}
  (f : hom a c) (g : hom b d) : hom (obj_exp c b) (obj_exp a d) :=
  exp_hom _ (eval (exponential_of c d) ∘ (f ×ₕ (exp_hom _ (g ∘ eval _)))).

Infix "↑ₒ@{ C }" := (obj_exp (C := C)) (at level 40, left associativity).
Infix "↑ₒ" := obj_exp (at level 40, left associativity).
Infix "↑ₕ@{ C }" := (hom_exp (C := C)) (at level 40, left associativity).
Infix "↑ₕ" := hom_exp (at level 40, left associativity).

Global Instance hom_exp_proper `{!HasTerm C, !HasProducts C, !HasExponentials C} {a b c d} :
  Proper ((≡) ==> (≡) ==> (≡)) (@hom_exp C _ _ _ a b c d).
Proof. by repeat intros ?; apply exp_hom_unique; setoid_subst; rewrite -exp_hom_commutes. Qed.

Lemma hom_exp_comp `{!HasTerm C, !HasProducts C, !HasExponentials C} {a b c d e f}
  (g1 : hom a c) (g2 : hom c e) (h1 : hom b d) (h2 : hom d f) :
  (g2 ∘ g1) ↑ₕ (h2 ∘ h1) ≡ (g1 ↑ₕ h2) ∘ (g2 ↑ₕ h1).
Proof.
  rewrite /hom_exp.
  symmetry; apply exp_hom_unique.
  rewrite !exp_hom_commutes_gen.
  rewrite -(left_id (id a)) hom_prod_comp -!comp_assoc -!exp_hom_commutes.
  rewrite !comp_assoc -hom_prod_comp right_id -{2}(left_id g1) hom_prod_comp.
  rewrite hom_prod_id left_id.
  rewrite !exp_hom_commutes_gen.
  rewrite !comp_assoc -hom_prod_comp left_id //.
Qed.
Lemma hom_exp_id `{!HasTerm C, !HasProducts C, !HasExponentials C} {a b} :
  (id a) ↑ₕ (id b) ≡ id (a ↑ₒ b).
Proof.
  symmetry; apply exp_hom_unique.
  rewrite -!exp_hom_commutes hom_prod_id left_id right_id //.
Qed.

Program Definition exp_func `{!HasTerm C, !HasProducts C, !HasExponentials C} :
  functor (cat_prod (C ᵒᵖ) C) C :=
  MkFunc (λ ab, ab.1 ↑ₒ@{C} ab.2) (λ _ _ h, h.1 ↑ₕ@{C} h.2) _ _ _.
Next Obligation. intros ????; repeat intros []; simpl in *; setoid_subst; done. Qed.
Next Obligation. repeat intros ?; simpl; apply hom_exp_comp. Qed.
Next Obligation. repeat intros ?; simpl; apply hom_exp_id. Qed.
Fail Next Obligation.

Class CCC C := MkCCC {
  CCC_HT :: HasTerm C;
  CCC_HP :: HasProducts C;
  CCC_HE :: HasExponentials C
}.

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

  Global Instance cone_hom_eq :
    ∀ cn cn', Equiv (cone_hom cn cn') := λ _ _ ch ch', cone_hom_map ch ≡ cone_hom_map ch'.
  Global Instance cone_hom_map_proper : ∀ cn cn', Proper ((≡) ==> (≡)) (@cone_hom_map cn cn').
  Proof. intros ???? Heq; exact Heq. Qed.
  Global Instance cone_hom_eq_equiv {cn cn'} : Equivalence (≡@{cone_hom cn cn'}).
  Proof.
    split; repeat intros []; rewrite /equiv /cone_hom_eq /=;
      repeat intros ?; solve_by_equiv_rewrite.
  Qed.

  Program Definition cone_hom_id cn : cone_hom cn cn := MkConeHom (id _) _.
  Solve All Obligations with by repeat intros ?; rewrite /= right_id.
  Fail Next Obligation.

  Program Definition cone_hom_comp {cn cn' cn''} (ch : cone_hom cn cn') (ch' : cone_hom cn' cn'') :
    cone_hom cn cn'' :=
  MkConeHom (cone_hom_map ch' ∘ cone_hom_map ch) _.
  Solve All Obligations with by repeat intros ?; rewrite -comp_assoc -!cone_hom_commutes.
  Fail Next Obligation.

  Global Instance cone_hom_comp_proper :
    ∀ cn cn' cn'', Proper ((≡) ==> (≡) ==> (≡)) (@cone_hom_comp cn cn' cn'').
  Proof.
    intros ??? [] [] Heq [] []; revert Heq; rewrite /= /equiv /cone_hom_eq /=; intros -> ->; done.
  Qed.
  Lemma cone_hom_comp_assoc :
    ∀ cn1 cn2 cn3 cn4 (ch1 : cone_hom cn1 cn2) (ch2 : cone_hom cn2 cn3) (ch3 : cone_hom cn3 cn4),
      cone_hom_comp ch1 (cone_hom_comp ch2 ch3) ≡ cone_hom_comp (cone_hom_comp ch1 ch2) ch3.
  Proof. intros ???? [] [] []; rewrite /= /equiv /cone_hom_eq /= comp_assoc; done. Qed.
  Lemma cone_hom_comp_left_id :
    ∀ cn cn' (ch : cone_hom cn cn'), cone_hom_comp ch (cone_hom_id _) ≡ ch.
  Proof. intros ?? []; rewrite /= /equiv /cone_hom_eq /= left_id; done. Qed.
  Lemma cone_hom_comp_right_id :
    ∀ cn cn' (ch : cone_hom cn cn'), cone_hom_comp (cone_hom_id _) ch ≡ ch.
  Proof. intros ?? []; rewrite /= /equiv /cone_hom_eq /= right_id; done. Qed.

  Program Definition ConeCat :=
    MkCat cone cone_hom cone_hom_id (@cone_hom_comp) (λ _ _, (≡)) _ _ _ _ _.
  Solve All Obligations with
    by auto using cone_hom_comp_assoc, cone_hom_comp_left_id, cone_hom_comp_right_id.
  Fail Next Obligation.

  Definition is_limiting_cone cn := @is_terminal ConeCat cn.

  Definition limit := terminal ConeCat.

  (* an alternative formulation *)

  Record is_cone c := MkIsCone {
    ic_side : ∀ j, hom c (F ₒ j);
    ic_side_commutes : ∀ j j' f, ic_side j' ≡ F ₕ f ∘ ic_side j;
  }.

  Definition cone_of_is_cone {c} (ic : is_cone c) : cone :=
    MkCone c (ic_side _ ic) (ic_side_commutes _ ic).

  Definition cone_is_cone cn : is_cone (vertex cn) :=
    MkIsCone _ (side cn) (side_commutes cn).

  Record is_limit c := MkIsLimit {
    il_is_cone : is_cone c;
    il_is_limiting_cone : is_limiting_cone (cone_of_is_cone il_is_cone);
  }.

  Definition il_side {c} il := ic_side c (il_is_cone _ il).
  Definition il_side_commutes {c} il := ic_side_commutes c (il_is_cone _ il).

  Definition cone_of_is_limit {c} (il : is_limit c) : cone :=
    cone_of_is_cone (il_is_cone _ il).

  Definition limiting_cone_is_limit cn :
    is_limiting_cone cn → is_limit (vertex cn) :=
    match cn as u return is_limiting_cone u → is_limit (vertex u) with
      (MkCone v s c) => MkIsLimit v (MkIsCone _ s c)
    end.

  Definition is_limit_limiting_cone {c} (il : is_limit c) :
    is_limiting_cone (cone_of_is_limit il) := il_is_limiting_cone _ il.

  (* useful lemma *)
  Lemma hom_to_limit_unique {c l} (f g : hom C c l) (il : is_limit l) :
    ∀ ic : is_cone c,
      (∀ j, ic_side _ ic j ≡ ic_side _ (il_is_cone _ il) j ∘ f) →
      (∀ j, ic_side _ ic j ≡ ic_side _ (il_is_cone _ il) j ∘ g) →
      f ≡ g.
  Proof.
    intros ic Hf Hg.
    pose (@MkConeHom (cone_of_is_cone ic) (cone_of_is_limit il) f Hf) as fc.
    change f with (cone_hom_map fc).
    pose (@MkConeHom (cone_of_is_cone ic) (cone_of_is_limit il) g Hg) as gc.
    change g with (cone_hom_map gc).
    rewrite (bang_unique (il_is_limiting_cone _ il) fc).
    rewrite (bang_unique (il_is_limiting_cone _ il) gc).
    done.
  Qed.

  (* extending cones *)

  Program Definition extend_cone {c cn} (f : hom C c (vertex cn)) : cone :=
    MkCone c (λ j, side cn j ∘ f) _.
  Next Obligation. intros ??????; rewrite /= -comp_assoc side_commutes //. Qed.
  Fail Next Obligation.

  Program Definition extend_cone_hom {c cn} (f : hom C c (vertex cn)) :
    cone_hom (extend_cone f) cn :=
    MkConeHom f _.
  Next Obligation. intros ????; rewrite //. Qed.
  Fail Next Obligation.

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
Global Arguments MkIsCone {_ _ _ _} _ _, {_ _ _} _ _ _.
Global Arguments is_cone {_ _} _ _.
Global Arguments ic_side {_ _ _ _} _ _.
Global Arguments ic_side_commutes {_ _ _ _} _ [_ _] _.
Global Arguments cone_of_is_cone {_ _ _ _} _.
Global Arguments cone_is_cone {_ _ _} _.
Global Arguments MkIsLimit {_ _ _ _} _ _, {_ _ _} _ _ _.
Global Arguments is_limit {_ _} _ _.
Global Arguments il_is_cone {_ _ _ _} _.
Global Arguments il_side {_ _ _ _} _ _.
Global Arguments il_side_commutes {_ _ _ _} _ [_ _] _.
Global Arguments cone_of_is_limit {_ _ _ _} _.
Global Arguments is_limit_limiting_cone {_ _ _ _} _.
Global Arguments limiting_cone_is_limit {_ _ _ _} _.
Global Arguments extend_cone {_ _ _ _} _ _, {_ _ _ _ _} _.
Global Arguments extend_cone_hom {_ _ _ _} _ _, {_ _ _ _ _} _.

Class Complete C := complete : ∀ J (F : functor J C), limit F.
Arguments complete {_ _ _} _, _ {_ _} _.

Section Complete_terminal.
  Context C `{!Complete C}.

  Program Definition make_cone_on_func_from_EmpCat c : cone (func_from_EmpCat C) :=
    MkCone c ((λ a, Empty_rect (λ _, hom C _ _) a)) _.
  Next Obligation. by simpl. Qed.

  Program Definition make_cone_hom_from_func_from_EmpCat
    {c} {cn : cone (func_from_EmpCat C)} (f : hom c (vertex cn)) :
    cone_hom (make_cone_on_func_from_EmpCat c) cn := MkConeHom f _.
  Next Obligation. by simpl. Qed.


  Program Definition compl_term : terminal C :=
    let t := (complete C (func_from_EmpCat C)) in
    MkTerm (vertex (term t))
      (MkIsTerm _ (λ c, cone_hom_map (bang (term_is_terminal t) (make_cone_on_func_from_EmpCat c))) _).
  Next Obligation.
  Proof.
    intros t ? f; simpl in *.
    apply (bang_unique (term_is_terminal t) (make_cone_hom_from_func_from_EmpCat f)).
  Qed.

End Complete_terminal.


Global Instance sig_eq `{!Equiv A} (P : A → Prop) : Equiv (sig P) := λ x y, `x ≡ `y.
Global Instance sig_eq_equiv
  `{!Equiv A} (P : A → Prop) `{!Equivalence (≡@{A})} : Equivalence (≡@{sig P}).
Proof. split; repeat intros []; rewrite /equiv /sig_eq /=; try intros ->; eauto. Qed.
Global Instance proj1_sig_proper `{!Equiv A} (P : A → Prop) : Proper ((≡) ==> (≡)) (@proj1_sig _ P).
Proof. intros [] []; done. Qed.

Global Instance forall_eq `{!∀ a : A, Equiv (T a)} : Equiv (∀ a, T a) :=
  forall_relation (λ x, (≡@{T x})).
Global Instance forall_eq_equiv
  `{!∀ a : A, Equiv (T a)} `{!∀ a, Equivalence (≡@{T a})} : Equivalence (≡@{∀ a, T a}).
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
    λset x, exist _ (λ j, side cn j x)
      (λ _ _ f, symmetry (side_commutes cn f x x (reflexivity _))).
  Solve All Obligations with repeat intros ?; rewrite /=; solve_by_equiv_rewrite.
  Fail Next Obligation.

  Program Definition cone_hom_to_setoid_lim_cone cn : cone_hom cn setoid_lim_cone :=
    MkConeHom (setoid_fun_to_setoid_lim_cone cn) _.
  Solve All Obligations with by intros ???? ->.
  Fail Next Obligation.

  Program Definition setoid_lim_cone_is_limiting_cone : is_limiting_cone setoid_lim_cone :=
    MkIsTerm setoid_lim_cone cone_hom_to_setoid_lim_cone _.
  Next Obligation.
  Proof.
    intros cn [chm chmc] x y Heq j; pose proof (chmc j y x (symmetry Heq)) as Heq';
      simpl in *; done.
  Qed.
  Fail Next Obligation.
End setoid_limit.

Program Instance setoid_complete : Complete Setoid :=
  λ _ F, MkTerm (setoid_lim_cone F) (setoid_lim_cone_is_limiting_cone F).

Section psh_limit.
  Context {C} {J} (F : functor J (PSh C)).

  Program Definition pointwise_func : ∀ c : obj C, functor J Setoid :=
    λ c, MkFunc (λ j, (F ₒ j) ₒ c) (λ _ _ f, F ₕ f ₙ c) _ _ _.
  Solve All Obligations with
    repeat first [intros ->|intros ?]; rewrite /= ?h_map_comp ?h_map_id //=.
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
    MkFunc (λ c, setoid_lim_obj (pointwise_func c)) (λ a b f, psh_lim_func_hom b a f) _ _ _.
  Solve All Obligations with
    repeat intros ?; rewrite /= ?h_map_comp ?h_map_id //=; solve_by_equiv_rewrite.
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
  Next Obligation. intros ? h ?????; apply: (cone_hom_commutes h); done. Qed.
  Fail Next Obligation.

  Program Definition natural_to_psh_lim_cone (cn : cone F) :
    natural (vertex cn) (vertex psh_lim_cone) :=
    MkNat (λ c,
        MkSetoidFun (λ x,
            setoid_fun_to_setoid_lim_cone (pointwise_func c) (pointwise_cone cn c) x) _) _.
  Next Obligation. repeat intros ?; solve_by_equiv_rewrite. Qed.
  Next Obligation. repeat intros ?; apply: (naturality (side cn _)); done. Qed.
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
    apply: (bang_unique
      (setoid_lim_cone_is_limiting_cone (pointwise_func _)) (pointwise_cone_hom f a)); done.
  Qed.

End psh_limit.

Program Instance presheaves_complete C : Complete (PSh C) :=
  λ _ F, MkTerm (psh_lim_cone F) (psh_lim_cone_is_limiting_cone F).
