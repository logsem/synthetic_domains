From SynthDom Require Import prelude.
From SynthDom Require Import stepindex.
From SynthDom.categories Require Import category.

Require Export Coq.Logic.PropExtensionality.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.ProofIrrelevance.

Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Open Scope category_scope.

Record SigmaEq {A B} (P : A → Prop) (Q : B → Prop) :=
  MkSigmaEq {
      sigma_proj1_eq : A = B;
      sigma_proj2_eq : ∀ x, P x <-> Q (castT sigma_proj1_eq x);
    }.
Arguments MkSigmaEq {_ _ _ _}.
Arguments sigma_proj1_eq {_ _ _ _}.
Arguments sigma_proj2_eq {_ _ _ _}.

Program Definition SigmaEqRefl {A} {P : A → Prop} : SigmaEq P P
  := MkSigmaEq eq_refl _.
Next Obligation.
  intros; simpl.
  reflexivity.
Qed.

Lemma SigmaEqUIP {A B} {P : A → Prop} {Q : B → Prop}
  (p q : SigmaEq P Q) : p = q.
Proof.
  apply proof_irrelevance.
Qed.

Lemma SigmaReflUnifyPred {A} {P Q : A → Prop} :
  SigmaEq P Q → P = Q.
Proof.
  intros [p1 p2].
  assert (p1 = eq_refl) as Hf.
  { apply proof_irrelevance. }
  rewrite Hf in p2.
  apply functional_extensionality.
  intros; apply propositional_extensionality, p2.
Qed.

Lemma SigmaEqUnpack {A B} {P : A → Prop} {Q : B → Prop}
  (p : SigmaEq P Q) : { a : A | P a } = { b : B | Q b }.
Proof.
  destruct (sigma_proj1_eq p).
  rewrite (SigmaReflUnifyPred p).
  reflexivity.
Qed.

Lemma SigmaEqCanon {A B : Type}
  (P : A → Prop) (Q : B → Prop)
  (G : SigmaEq P Q)
  (H : { a : A | P a } = { b : B | Q b }) : H = SigmaEqUnpack G.
Proof.
  apply proof_irrelevance.
Qed.

Lemma SigmaEqSymm {A B} {P : A → Prop} {Q : B → Prop}
  : SigmaEq P Q → SigmaEq Q P.
Proof.
  intros p.
  destruct (sigma_proj1_eq p).
  destruct (SigmaReflUnifyPred p).
  apply SigmaEqRefl.
Qed.

Lemma SigmaEqSymmRefl {A} {P : A → Prop}
  : SigmaEqSymm (P := P) SigmaEqRefl = SigmaEqRefl.
Proof. apply proof_irrelevance. Qed.

Lemma SigmaEqTrans {A B C} {P : A → Prop} {Q : B → Prop} {R : C → Prop}
  : SigmaEq P Q → SigmaEq Q R → SigmaEq P R.
Proof.
  intros p q.
  destruct (sigma_proj1_eq p).
  destruct (sigma_proj1_eq q).
  destruct (SigmaReflUnifyPred p).
  destruct (SigmaReflUnifyPred q).
  apply SigmaEqRefl.
Qed.

Lemma SigmaEqTransLeftRefl {A B} {P : A → Prop} {Q : B → Prop}
  : ∀ (p : SigmaEq P Q), SigmaEqTrans (P := P) SigmaEqRefl p = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma SigmaEqTransRightRefl {A B} {P : A → Prop} {Q : B → Prop}
  : ∀ (p : SigmaEq P Q), SigmaEqTrans (P := P) p SigmaEqRefl = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma SigmaEqTransportProj1 {A B} {P : A → Prop} {Q : B → Prop}
  (p : SigmaEq P Q)
  : ∀ (x : { a : A | P a }),
  (proj1_sig (castT (SigmaEqUnpack p) x)) = ((castT (sigma_proj1_eq p) (proj1_sig x))).
Proof.
  intros.
  destruct (sigma_proj1_eq p).
  destruct (SigmaReflUnifyPred p).
  rewrite (proof_irrelevance _ (SigmaEqUnpack p) eq_refl).
  reflexivity.
Qed.

Record PiEq {A B} (P : A → Type) (Q : B → Type) :=
  MkPiEq {
      pi_dom_eq : A = B;
      pi_range_eq : ∀ x, P x = Q (castT pi_dom_eq x)
    }.
Arguments MkPiEq {_ _ _ _}.
Arguments pi_dom_eq {_ _ _ _}.
Arguments pi_range_eq {_ _ _ _}.

Program Definition PiEqRefl {A} {P : A → Type} : PiEq P P
  := MkPiEq eq_refl _.
Next Obligation.
  intros; simpl.
  reflexivity.
Qed.

Lemma PiEqUIP {A B} {P : A → Type} {Q : B → Type}
  (p q : PiEq P Q) : p = q.
Proof.
  apply proof_irrelevance.
Qed.

Lemma PiReflUnifyFam {A} {P Q : A → Type} :
  PiEq P Q → P = Q.
Proof.
  intros [p1 p2].
  assert (p1 = eq_refl) as Hf.
  { apply proof_irrelevance. }
  rewrite Hf in p2.
  apply functional_extensionality.
  intros; apply p2.
Qed.

Lemma PiEqUnpack {A B} {P : A → Type} {Q : B → Type}
  (p : PiEq P Q) : (∀ (a : A), P a) = (∀ (b : B), Q b).
Proof.
  destruct (pi_dom_eq p).
  rewrite (PiReflUnifyFam p).
  reflexivity.
Qed.

Lemma PiEqCanon {A B : Type}
  (P : A → Type) (Q : B → Type)
  (G : PiEq P Q)
  (H : (∀ (a : A), P a) = (∀ (b : B), Q b)) : H = PiEqUnpack G.
Proof.
  apply proof_irrelevance.
Qed.

Lemma PiEqSymm {A B} {P : A → Type} {Q : B → Type}
  : PiEq P Q → PiEq Q P.
Proof.
  intros p.
  destruct (pi_dom_eq p).
  destruct (PiReflUnifyFam p).
  apply PiEqRefl.
Qed.

Lemma PiEqSymmRefl {A} {P : A → Type}
  : PiEqSymm (P := P) PiEqRefl = PiEqRefl.
Proof. apply proof_irrelevance. Qed.

Lemma PiEqTrans {A B C} {P : A → Type} {Q : B → Type} {R : C → Type}
  : PiEq P Q → PiEq Q R → PiEq P R.
Proof.
  intros p q.
  destruct (pi_dom_eq p).
  destruct (pi_dom_eq q).
  destruct (PiReflUnifyFam p).
  destruct (PiReflUnifyFam q).
  apply PiEqRefl.
Qed.

Lemma PiEqTransLeftRefl {A B} {P : A → Type} {Q : B → Type}
  : ∀ (p : PiEq P Q), PiEqTrans (P := P) PiEqRefl p = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma PiEqTransRightRefl {A B} {P : A → Type} {Q : B → Type}
  : ∀ (p : PiEq P Q), PiEqTrans (P := P) p PiEqRefl = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma PiEqTransportApp {J} {P Q : J → Type}
  (b : ∀ x : J, P x)
  (K : PiEq P Q)
  (H : ∀ a : J, (P a) = (Q a))
  : castT (PiEqUnpack K) b = λ x, castT (H x) (b x).
Proof.
  destruct (PiReflUnifyFam K).
  assert (H = λ _, eq_refl) as Hf.
  {
    intros; apply proof_irrelevance.
  }
  rewrite Hf; clear Hf.
  simpl.
  assert (PiEqUnpack K = eq_refl) as ->.
  { apply proof_irrelevance. }
  reflexivity.
Qed.

Record SetoidEq (s1 s2 : setoid) :=
  MkSetoidEq {
      setoid_carrier_eq : setoid_set s1 = setoid_set s2;
      setoid_rel_equiv : ∀ x y, setoid_eq s1 x y
                                <-> setoid_eq s2 (castT setoid_carrier_eq x)
                                    (castT setoid_carrier_eq y);
    }.
Arguments MkSetoidEq {_ _}.
Arguments setoid_carrier_eq {_ _}.
Arguments setoid_rel_equiv {_ _}.

Program Definition SetoidEqRefl {A} : SetoidEq A A
  := MkSetoidEq eq_refl _.
Next Obligation.
  intros; simpl.
  reflexivity.
Qed.

Lemma SetoidEqUIP {A B}
  (p q : SetoidEq A B) : p = q.
Proof.
  apply proof_irrelevance.
Qed.

Lemma SetoidEqUnpack {A B}
  (p : SetoidEq A B) : A = B.
Proof.
  destruct A as [A1 A2 A3];
    destruct B as [B1 B2 B3].
  destruct p as [p1 p2].
  simpl in *; destruct p1.
  assert (A2 = B2) as Hf.
  {
    apply functional_extensionality; intros x.
    apply functional_extensionality; intros y.
    apply propositional_extensionality.
    apply p2.
  }
  destruct Hf.
  assert (A3 = B3) as ->.
  { apply proof_irrelevance. }
  reflexivity.
Qed.

Lemma SetoidEqPack {A B}
  (p : A = B) : SetoidEq A B.
Proof.
  rewrite p.
  apply SetoidEqRefl.
Qed.

Lemma SetoidEqPackUnpack {A B}
  (p : A = B) : SetoidEqUnpack (SetoidEqPack p) = p.
Proof. apply proof_irrelevance. Qed.

Lemma SetoidEqUnpackPack {A B}
  (p : SetoidEq A B) : SetoidEqPack (SetoidEqUnpack p) = p.
Proof. apply proof_irrelevance. Qed.

Lemma SetoidEqCanon {A B}
  (G : SetoidEq A B)
  (H : A = B) : H = SetoidEqUnpack G.
Proof.
  apply proof_irrelevance.
Qed.

Lemma SetoidEqSymm {A B}
  : SetoidEq A B → SetoidEq B A.
Proof.
  intros p.
  apply SetoidEqPack.
  apply SetoidEqUnpack in p.
  destruct p.
  reflexivity.
Qed.

Lemma SetoidEqSymmRefl {A}
  : SetoidEqSymm (A := A) SetoidEqRefl = SetoidEqRefl.
Proof. apply proof_irrelevance. Qed.

Lemma SetoidEqTrans {A B C}
  : SetoidEq A B → SetoidEq B C → SetoidEq A C.
Proof.
  intros p q.
  apply SetoidEqPack.
  apply SetoidEqUnpack in p.
  apply SetoidEqUnpack in q.
  destruct p.
  apply q.
Qed.

Lemma SetoidEqTransLeftRefl {A B}
  : ∀ (p : SetoidEq A B), SetoidEqTrans (A := A) SetoidEqRefl p = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma SetoidEqTransRightRefl {A B}
  : ∀ (p : SetoidEq A B), SetoidEqTrans (A := A) p SetoidEqRefl = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma SetoidEqUnpackSymm {A B}
  {p : SetoidEq A B}
  : eq_sym (SetoidEqUnpack p) = SetoidEqUnpack (SetoidEqSymm p).
Proof. apply proof_irrelevance. Qed.

Lemma MkSetoidEqSymm {A B}
  (f : setoid_set A = setoid_set B)
  (g : ∀ x y, setoid_eq A x y
              <-> setoid_eq B (castT f x) (castT f y))
  (h : ∀ x y : B, setoid_eq B x y
                    ↔ setoid_eq A (castT (eq_sym f) x) (castT (eq_sym f) y))
  : SetoidEqSymm (MkSetoidEq f g) = MkSetoidEq (eq_sym f) h.
Proof. apply proof_irrelevance. Qed.

Lemma SetoidEqSetoidConv {A B}
  (p : SetoidEq A B)
  : setoid_conv (SetoidEqUnpack p) = castT (setoid_carrier_eq p).
Proof.
  apply functional_extensionality.
  intros; simpl.
  destruct p as [p1 p2].
  destruct A as [A1 A2 A3];
    destruct B as [B1 B2 B3].
  simpl in *.
  destruct p1.
  simpl in *.
  assert (A2 = B2) as Hf.
  {
    apply functional_extensionality; intros a.
    apply functional_extensionality; intros b.
    apply propositional_extensionality, p2.
  }
  destruct Hf.
  assert (A3 = B3) as Hf by apply proof_irrelevance.
  destruct Hf.
  match goal with
  | |- context G [SetoidEqUnpack ?a] =>
      set (S := a)
  end.
  rewrite -(SetoidEqCanon S eq_refl).
  done.
Qed.

Program Definition setoid_vert_eq_obj_packed {J : category}
  {I_obj I'_obj : obj J → setoid}
  {I_arr : ∀ a b : obj J, hom a b → setoid_fun (I_obj a) (I_obj b)}
  {I'_arr : ∀ a b : obj J, hom a b → setoid_fun (I'_obj a) (I'_obj b)}
  (equiv_obj : ∀ x, I_obj x = I'_obj x)
  (equiv_arr : ∀ a b (f : hom a b),
     hom_trans (equiv_obj a : @eq (obj Setoid) _ _) (equiv_obj b) (I_arr _ _ f)
       ≡ I'_arr _ _ f)
  : SigmaEq (λ (p : ∀ j : obj J, I_obj j),
        ∀ (j j' : obj J) (f : hom j j'), (I_arr _ _ f) (p j) ≡ p j')
      (λ (p : ∀ j : obj J, I'_obj j),
        ∀ (j j' : obj J) (f : hom j j'), (I'_arr _ _ f) (p j) ≡ p j')
  := MkSigmaEq
       (forall_extensionality
          (λ x, f_equal setoid_set (equiv_obj x)))
       _.
Next Obligation.
  intros J I_obj I'_obj I_arr I'_arr equiv_obj equiv_arr b; simpl.
  split; intros.
  - assert (I_obj = I'_obj) as Hf.
    {
      apply functional_extensionality.
      apply equiv_obj.
    }
    destruct Hf.
    assert (equiv_obj = λ _, eq_refl) as ->.
    { apply proof_irrelevance. }
    simpl.
    assert ((forall_extensionality (λ x : obj J, eq_refl))
            = eq_refl) as ->.
    { apply proof_irrelevance. }
    simpl.
    rewrite -(H j j' f).
    symmetry.
    by apply equiv_arr.
  - specialize (H j j' f).
    assert (I_obj = I'_obj) as Hf.
    {
      apply functional_extensionality.
      apply equiv_obj.
    }
    destruct Hf.
    assert (equiv_obj = λ _, eq_refl) as Hf.
    { apply proof_irrelevance. }
    rewrite Hf in H, equiv_arr; clear Hf.
    simpl in H.
    eassert ((forall_extensionality (C := λ j : obj J, I_obj j) (λ x : obj J, eq_refl))
            = eq_refl) as Hf.
    { apply proof_irrelevance. }
    Unshelve.
    rewrite Hf in H; clear Hf.
    simpl in H.
    rewrite -H.
    apply equiv_arr.
    reflexivity.
Qed.

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

Record FunctorEq {C D} (F G : functor C D) :=
  MkFunctorEq {
      func_eq_obj : ∀ x, F ₒ x = G ₒ x;
      func_eq_arr : ∀ {x y} (f : hom x y),
        G ₕ f = hom_trans (func_eq_obj x) (func_eq_obj y) (F ₕ f);
    }.
Arguments MkFunctorEq {_ _ _ _}.
Arguments func_eq_obj {_ _ _ _}.
Arguments func_eq_arr {_ _ _ _}.

Program Definition FunctorEqRefl {C D} {F : functor C D} : FunctorEq F F
  := MkFunctorEq (λ _, eq_refl) _.
Next Obligation.
  intros; simpl.
  reflexivity.
Qed.

Lemma FunctorEqUIP {C D} {F G : functor C D}
  (p q : FunctorEq F G) : p = q.
Proof.
  apply proof_irrelevance.
Qed.

Lemma FunctorEqUnpack {C D} {F G : functor C D}
  (p : FunctorEq F G) : F = G.
Proof.
  destruct F as [F1 F2 F3 F4 F5];
    destruct G as [G1 G2 G3 G4 G5].
  destruct p as [p1 p2].
  simpl in *.
  assert (F1 = G1) as Hf.
  { apply functional_extensionality, p1. }
  destruct Hf.
  assert (p1 = λ _, eq_refl).
  { apply proof_irrelevance. }
  subst p1.
  assert (F2 = G2) as Hf.
  {
    apply functional_extensionality_dep; intros x.
    apply functional_extensionality_dep; intros y.
    apply functional_extensionality; intros f.
    rewrite p2.
    reflexivity.
  }
  destruct Hf.
  assert (F3 = G3) as ->.
  { apply proof_irrelevance. }
  assert (F4 = G4) as ->.
  { apply proof_irrelevance. }
  assert (F5 = G5) as ->.
  { apply proof_irrelevance. }
  reflexivity.
Qed.

Lemma FunctorEqPack {C D} {F G : functor C D}
  (p : F = G) : FunctorEq F G.
Proof.
  rewrite p.
  apply FunctorEqRefl.
Qed.

Lemma FunctorEqPackUnpack {C D} {F G : functor C D}
  (p : F = G) : FunctorEqUnpack (FunctorEqPack p) = p.
Proof. apply proof_irrelevance. Qed.

Lemma FunctorEqUnpackPack {C D} {F G : functor C D}
  (p : FunctorEq F G) : FunctorEqPack (FunctorEqUnpack p) = p.
Proof. apply proof_irrelevance. Qed.

Lemma FunctorEqCanon {C D} {F G : functor C D}
  (J : FunctorEq F G)
  (H : F = G) : H = FunctorEqUnpack J.
Proof.
  apply proof_irrelevance.
Qed.

Lemma FunctorEqSymm {C D} {F G : functor C D}
  : FunctorEq F G → FunctorEq G F.
Proof.
  intros p.
  apply FunctorEqPack.
  apply FunctorEqUnpack in p.
  destruct p.
  reflexivity.
Qed.

Lemma FunctorEqSymmRefl {C D} {F : functor C D}
  : FunctorEqSymm (F := F) FunctorEqRefl = FunctorEqRefl.
Proof. apply proof_irrelevance. Qed.

Lemma FunctorEqTrans {C D} {F G H : functor C D}
  : FunctorEq F G → FunctorEq G H → FunctorEq F H.
Proof.
  intros p q.
  apply FunctorEqPack.
  apply FunctorEqUnpack in p.
  apply FunctorEqUnpack in q.
  destruct p.
  apply q.
Qed.

Lemma FunctorEqTransLeftRefl {C D} {F G : functor C D}
  : ∀ (p : FunctorEq F G), FunctorEqTrans (F := F) FunctorEqRefl p = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma FunctorEqTransRightRefl {C D} {F G : functor C D}
  : ∀ (p : FunctorEq F G), FunctorEqTrans (F := F) p FunctorEqRefl = p.
Proof. intros; apply proof_irrelevance. Qed.

Lemma FunctorEqUnpackSymm {C D} {F G : functor C D}
  {p : FunctorEq F G}
  : eq_sym (FunctorEqUnpack p) = FunctorEqUnpack (FunctorEqSymm p).
Proof. apply proof_irrelevance. Qed.

Lemma MkFunctorEqSymm {C D} {F G : functor C D}
  (t : ∀ x, o_map F x = o_map G x)
  (g : ∀ x y (f : hom x y),
     h_map G f = hom_trans (t x) (t y) (h_map F f))
  (h : ∀ x y (f : hom x y),
     h_map F f = hom_trans (eq_sym (t x)) (eq_sym (t y)) (h_map G f))
  : FunctorEqSymm (MkFunctorEq t g) = MkFunctorEq (λ x, eq_sym (t x)) h.
Proof. apply proof_irrelevance. Qed.

Lemma FunctorMapPI {C D} {A B : functor C D}
  (f g : natural A B) :
  (nat_map f = nat_map g)
  → f = g :> natural A B.
Proof.
  intros Hf.
  destruct f as [f1 f2]; destruct g as [g1 g2]; simpl in *.
  destruct Hf.
  assert (f2 = g2) as -> by apply proof_irrelevance.
  reflexivity.
Qed.

(* Record functor_equal_pack {C D} (F G : functor C D) : Prop := *)
(*   MkFuncEqPack { *)
(*       func_eq_pack_o_map : ∀ a, F ₒ a = G ₒ a; *)
(*       func_eq_pack_h_map : ∀ a b (f : hom C a b), *)
(*         hom_trans (func_eq_pack_o_map a) (func_eq_pack_o_map b) (F ₕ f) *)
(*         = G ₕ f; *)
(* }. *)
(* Global Arguments MkFuncEqPack {_ _ _ _} _ _, {_ _} _ _ _ _. *)
(* Global Arguments func_eq_pack_o_map {_ _ _ _} _ _. *)
(* Global Arguments func_eq_pack_h_map {_ _ _ _} _ [_ _] _. *)

(* Lemma functor_equal_pack_eq {C D} (F G : functor C D) : *)
(*   functor_equal_pack F G = (F = G). *)
(* Proof. *)
(*   apply propositional_extensionality. *)
(*   split. *)
(*   - intros H. *)
(*     destruct F as [om hm hmp hmc hmi]. *)
(*     destruct G as [om' hm' hmp' hmc' hmi']. *)
(*     assert (om = om') as ->. *)
(*     { *)
(*       apply functional_extensionality. *)
(*       apply (func_eq_pack_o_map H). *)
(*     } *)
(*     assert (hm = hm') as ->. *)
(*     { *)
(*       apply functional_extensionality_dep. *)
(*       intros a. *)
(*       apply functional_extensionality_dep. *)
(*       intros b. *)
(*       apply functional_extensionality. *)
(*       intros f. *)
(*       pose proof (func_eq_pack_h_map H f) as G. *)
(*       simpl in G; rewrite -G; clear G. *)
(*       assert (func_eq_pack_o_map H a = eq_refl) as -> by apply proof_irrelevance. *)
(*       assert (func_eq_pack_o_map H b = eq_refl) as -> by apply proof_irrelevance. *)
(*       by rewrite hom_trans_refl. *)
(*     } *)
(*     assert (hmp = hmp') as -> by apply proof_irrelevance. *)
(*     assert (hmc = hmc') as -> by apply proof_irrelevance. *)
(*     assert (hmi = hmi') as -> by apply proof_irrelevance. *)
(*     reflexivity. *)
(*   - intros ->. *)
(*     apply (MkFuncEqPack (λ a, eq_refl)). *)
(*     intros; simpl. *)
(*     by rewrite hom_trans_refl. *)
(* Qed. *)

(* Global Instance functor_equal_pack_equiv {C D} *)
(*   : Equivalence (@functor_equal_pack C D). *)
(* Proof. *)
(*   split. *)
(*   - intros F. *)
(*     apply (MkFuncEqPack (λ _, eq_refl)). *)
(*     by intros; rewrite hom_trans_refl. *)
(*   - intros F G H. *)
(*     apply (MkFuncEqPack (λ a, eq_sym (func_eq_pack_o_map H a))). *)
(*     intros; simpl. *)
(*     symmetry. *)
(*     apply hom_trans_sym_eq. *)
(*     apply (func_eq_pack_h_map H). *)
(*   - intros K L M H G. *)
(*     apply (MkFuncEqPack (λ a, eq_trans (func_eq_pack_o_map H a) (func_eq_pack_o_map G a))). *)
(*     intros; simpl. *)
(*     rewrite hom_trans_trans. *)
(*     rewrite (func_eq_pack_h_map H). *)
(*     apply (func_eq_pack_h_map G). *)
(* Qed. *)

Definition cone_trans {J C} {F F' : functor J C}
  (heq : F = F') (cn : cone F) : cone F' :=
  match heq in _ = F' return cone F' with
      eq_refl => cn
  end.

Definition cones_eq {J C} {F F' : functor J C}
  (Fequiv : F = F') (cn : cone F) (cn' : cone F') :=
  cn' = cone_trans Fequiv cn.

Record cones_equal_pack {J C} {F F' : functor J C}
  (Fequiv : FunctorEq F F') (cn : cone F) (cn' : cone F') :=
  MkConesEqPack {
      cones_eq_pack_vertexes : vertex cn = vertex cn';
      cones_eq_pack_sides :
      ∀ j, side cn' j
           = hom_trans cones_eq_pack_vertexes
               (func_eq_obj Fequiv j)
               (side cn j);
    }.
Arguments MkConesEqPack {_ _ _ _ _ _ _} _ _.
Arguments cones_eq_pack_vertexes {_ _ _ _ _ _ _} _.
Arguments cones_eq_pack_sides {_ _ _ _ _ _ _} _ _.

Lemma cones_equal_pack_eq {J C} {F F' : functor J C}
  (Fequiv : FunctorEq F F')
  (Fequiv' : F = F') (cn : cone F) (cn' : cone F')
  : cones_equal_pack Fequiv cn cn'
    = (cones_eq Fequiv' cn cn').
Proof.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct Fequiv'.
    rewrite /cones_eq /=.
    destruct cn as [v s p].
    destruct cn' as [v' s' p'].
    assert (v = v') as ->.
    { apply (cones_eq_pack_vertexes H). }
    assert (s = s') as ->.
    {
      apply functional_extensionality_dep.
      intros x.
      pose proof (cones_eq_pack_sides H x) as G.
      simpl in G.
      rewrite G.
      clear.
      assert (func_eq_obj Fequiv x = eq_refl) as -> by apply proof_irrelevance.
      assert (cones_eq_pack_vertexes H = eq_refl) as -> by apply proof_irrelevance.
      by rewrite hom_trans_refl.
    }
    assert (p = p') as -> by apply proof_irrelevance.
    reflexivity.
  - intros ->.
    destruct Fequiv'.
    apply (MkConesEqPack eq_refl).
    intros j; simpl.
    assert ((func_eq_obj Fequiv j) = eq_refl)
      as ->
         by apply proof_irrelevance.
    by rewrite hom_trans_refl.
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

Record alg_equal_pack {D} {T : functor D D}
  (a b : obj (Alg T)) :=
  MkAlgEqPack {
      car_equal_pack : car a = car b;
      cons_equal_pack :
      cons b =
        hom_trans (o_map_eq T car_equal_pack) car_equal_pack (cons a);
    }.
Arguments MkAlgEqPack {_ _} _ _.
Arguments car_equal_pack {_ _ _ _}.
Arguments cons_equal_pack {_ _ _ _}.

Lemma alg_equal_pack_eq {D} (T : functor D D) (a b : obj (Alg T)) :
  alg_equal_pack a b = (a = b).
Proof.
  apply propositional_extensionality.
  split.
  - intros H.
    destruct a as [car cons].
    destruct b as [car' cons'].
    assert (car = car') as ->.
    {
      apply (car_equal_pack H).
    }
    assert (cons = cons') as ->.
    {
      pose proof (cons_equal_pack H) as G.
      simpl in G; rewrite G; clear G.
      assert (car_equal_pack H = eq_refl) as -> by apply proof_irrelevance.
      assert (o_map_eq T eq_refl = eq_refl) as -> by apply proof_irrelevance.
      by rewrite hom_trans_refl.
    }
    reflexivity.
  - intros ->.
    apply (MkAlgEqPack _ _ eq_refl).
    reflexivity.
Qed.

Record cones_equiv {J C} {F F' : functor J C}
  (Fequiv : functor_equiv F F') (cn : cone F) (cn' : cone F') :=
  MkConesEq {
      cones_eq_vertexes : vertex cn = vertex cn';
      cones_eq_sides :
      ∀ j, side cn' j
           ≡ hom_trans cones_eq_vertexes (func_eq_o_map Fequiv j) (side cn j);
    }.
Arguments MkConesEq {_ _ _ _ _ _ _} _ _.
Arguments cones_eq_vertexes {_ _ _ _ _ _ _} _.
Arguments cones_eq_sides {_ _ _ _ _ _ _} _ _.
