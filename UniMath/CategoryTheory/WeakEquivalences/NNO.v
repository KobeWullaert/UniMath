(**
   In this file, we prove that an arbitrary weak equivalence F : C -> D creates, preserves, and reflects natural numbers objects (NNO's).
   Consequently, we prove that the universal property of the Rezk completion lifts to categories equipped with (a terminal object, and a) NNO.
 *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.

Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.WeakEquivalences.Terminal.

Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Require Import UniMath.CategoryTheory.Arithmetic.NNO.

Local Open Scope cat.

Section Aux.

  Lemma weak_equiv_lifts_preserves_terminal
    {C1 C2 C3 : category}
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    (Fpterm : preserves_terminal F)
    : preserves_terminal H.
  Proof.
    intros x2 x2_is_term.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ Gw x2)).
    { apply isaprop_isTerminal. }
    intros [x1 i] y3.
    use (iscontrweqb' (Y :=  (C3⟦y3, H(G x1)⟧))).
    + use (iscontrweqb' (Y := (C3⟦y3, F x1⟧))).
      * use (Fpterm _ _).
        use (weak_equiv_reflects_terminal _ Gw).
        exact (iso_to_Terminal (_,, x2_is_term) _ (z_iso_inv i)).
      * apply z_iso_comp_left_weq.
        exact (_ ,, pr2 α x1).
    + apply z_iso_comp_left_weq.
      apply functor_on_z_iso.
      exact (z_iso_inv i).
  Qed.

  Lemma weak_equiv_lifts_preserves_chosen_terminal
    {C1 C2 C3 : category}
    {F : C1 ⟶ C3}
    {G : C1 ⟶ C2}
    {H : C2 ⟶ C3}
    (α : nat_z_iso (G ∙ H) F)
    (Gw : is_weak_equiv G)
    {T1 : Terminal C1} (T2 : Terminal C2)
    (Fpterm : preserves_chosen_terminal T1 F)
    : preserves_chosen_terminal T2 H.
  Proof.
    apply (weak_equiv_lifts_preserves_terminal α Gw).
    - exact (preserves_terminal_if_preserves_chosen T1 _ Fpterm).
    - apply T2.
  Defined.

End Aux.

Section WeakEquivCreatesNNO₀.

  Context
    {C D : category} {F : functor C D}
    {T_C : Terminal C}
    (N : NNO T_C)
    (F_weq : is_weak_equiv F).

  Context {m : D}
    (z : D ⟦F T_C, m⟧)
    (s : D ⟦m, m⟧)
    {M : C} (im : z_iso (F M) m).

  Let Z : C⟦T_C , M⟧
      := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ (z · z_iso_inv im).
  Let S : C⟦M, M⟧
      := fully_faithful_inv_hom (ff_from_weak_equiv _ F_weq) _ _ (im · s · z_iso_inv im).

  Definition weak_equiv_creates_NNO_map
    : D⟦F N, m⟧
    := #F (NNO_mor _ _ Z S) · im.

  Lemma weak_equiv_creates_NNO_creates_zero
    : # F (zeroNNO T_C N) · weak_equiv_creates_NNO_map = z.
  Proof.
    unfold weak_equiv_creates_NNO_map.
    rewrite assoc.
    rewrite <- functor_comp.
    rewrite NNO_mor_Z.
    unfold Z.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    apply id_right.
  Qed.

  Lemma weak_equiv_creates_NNO_creates_succ
    : # F (sucNNO T_C N) · weak_equiv_creates_NNO_map = weak_equiv_creates_NNO_map · s.
  Proof.
    unfold weak_equiv_creates_NNO_map.
    rewrite assoc.
    rewrite <- functor_comp.
    rewrite NNO_mor_S.
    rewrite functor_comp.
    rewrite ! assoc'.
    apply maponpaths.
    unfold S.
    rewrite functor_on_fully_faithful_inv_hom.
    rewrite assoc'.
    rewrite z_iso_inv_after_z_iso.
    apply id_right.
  Qed.

  Lemma image_of_NNO_satisifes_UVP_uniqueness_zero
    (φ : ∑ u : D ⟦ F N, m ⟧, # F (zeroNNO T_C N) · u = z × # F (sucNNO T_C N) · u = u · s)
    : zeroNNO T_C N · invmap (weq_from_fully_faithful (ff_from_weak_equiv F F_weq) N M)
        (pr1 φ · z_iso_inv im) = Z.
  Proof.
    refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _).
    apply maponpaths.
    simpl.
    rewrite ! functor_comp.
    etrans. {
      apply maponpaths.
      apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _)).
    }
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      exact (pr12 φ).
    }
    unfold Z.
    now rewrite functor_on_fully_faithful_inv_hom.
  Qed.

  Lemma image_of_NNO_satisifes_UVP_uniqueness_succ
    (φ : ∑ u : D ⟦ F N, m ⟧, # F (zeroNNO T_C N) · u = z × # F (sucNNO T_C N) · u = u · s)
    : sucNNO T_C N · invmap (weq_from_fully_faithful (ff_from_weak_equiv F F_weq) N M) (pr1 φ · z_iso_inv im)
      = invmap (weq_from_fully_faithful (ff_from_weak_equiv F F_weq) N M) (pr1 φ · z_iso_inv im) · S.
  Proof.
    refine (! homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _).
    apply maponpaths.
    simpl.
    rewrite ! functor_comp.
    etrans. {
      apply maponpaths.
      apply (homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _)).
    }
    rewrite assoc.
    etrans. {
      apply maponpaths_2.
      exact (pr22 φ).
    }
    unfold S.
    rewrite functor_on_fully_faithful_inv_hom.
    apply pathsinv0.
    etrans. {
      apply maponpaths_2.
      apply functor_on_fully_faithful_inv_hom.
    }
    rewrite ! assoc.
    do 2 apply maponpaths_2.
    rewrite assoc'.
    rewrite z_iso_after_z_iso_inv.
    apply id_right.
  Qed.

  Lemma image_of_NNO_satisfies_UVP_uniqueness
    : isaprop (∑ u : D ⟦ F N, m ⟧, # F (zeroNNO T_C N) · u = z × # F (sucNNO T_C N) · u = u · s).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    use (cancel_z_iso (pr1 φ₁) (pr1 φ₂) (z_iso_inv im)).

    refine (! homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _ @ _).
    refine (_ @ homotweqinvweq (weq_from_fully_faithful (ff_from_weak_equiv _ F_weq) _ _) _).
    apply maponpaths.
    use (NNO_mor_unique T_C N Z S).
    - apply image_of_NNO_satisifes_UVP_uniqueness_zero.
    - apply image_of_NNO_satisifes_UVP_uniqueness_zero.
    - apply image_of_NNO_satisifes_UVP_uniqueness_succ.
    - apply image_of_NNO_satisifes_UVP_uniqueness_succ.
  Qed.

  Lemma image_of_NNO_satisfies_UVP
    : iscontr (∑ u : D ⟦ F N, m ⟧, # F (zeroNNO T_C N) · u = z × # F (sucNNO T_C N) · u = u · s).
  Proof.
    use iscontraprop1.
    - apply image_of_NNO_satisfies_UVP_uniqueness.
    - simple refine (_ ,, _ ,, _).
      + exact weak_equiv_creates_NNO_map.
      + exact weak_equiv_creates_NNO_creates_zero.
      + exact weak_equiv_creates_NNO_creates_succ.
  Defined.

End WeakEquivCreatesNNO₀.

Proposition weak_equiv_creates_NNO
  {C D : category}
  {F : functor C D}
  {T_C : Terminal C}
  (N : NNO T_C)
  (F_weq : is_weak_equiv F)
  : creates_NNO (weak_equiv_preserves_chosen_terminal _ F_weq T_C) N.
Proof.
  intros m z s.
  use (factor_through_squash (isapropiscontr _) _ (eso_from_weak_equiv _ F_weq m)).
  intros [M im].
  exact (image_of_NNO_satisfies_UVP N F_weq z s im).
Defined.

Proposition weak_equiv_preserves_NNO
  {C D : category}
  {F : functor C D}
  {T_C : Terminal C} {T_D : Terminal D}
  (N : NNO T_C) (M : NNO T_D)
  (F_weq : is_weak_equiv F)
  : preserves_NNO T_C T_D (weak_equiv_preserves_chosen_terminal _ F_weq T_C) N M.
Proof.
  set (M' := NNO_from_functor_creation (weak_equiv_creates_NNO N F_weq)).
  exact (pr2 (iso_between_NNO_mod_chosen_terminal M M')).
Defined.

Section WeakEquivReflectsNNO₀.

  Context {C D : category}
    {F : functor C D}
    {T_C : Terminal C} {T_D : Terminal D}
    {N : ob C} {z : C⟦T_C, N⟧} {s : C⟦N, N⟧}
    {F_weq : is_weak_equiv F}
    (p : isNNO T_D (F N) (iscontrpr1 (weak_equiv_preserves_chosen_terminal _ F_weq T_C _) · #F z) (#F s)).

  Let N_D := make_NNO _ _ _ _ p.

  Context {n : C} (z' : C⟦T_C, n⟧) (s' : C⟦n, n⟧).

  Lemma weak_equiv_reflects_uvp_uniqueness_of_NNO
    : isaprop (∑ u : C⟦N, n⟧, z · u = z' × s · u = u · s').
  Proof.
    use invproofirrelevance.
    intros ϕ₁ ϕ₂.
    use subtypePath.
    { intro. apply isapropdirprod ; apply homset_property. }

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _).

    apply maponpaths.
    cbn.
    use (NNO_mor_unique _ N_D (iscontrpr1 (weak_equiv_preserves_chosen_terminal F F_weq T_C T_D) · # F z') (#F s')) ; cbn.
    - rewrite assoc'.
      rewrite <- functor_comp.
      now rewrite (pr12 ϕ₁).
    - rewrite assoc'.
      rewrite <- functor_comp.
      now rewrite (pr12 ϕ₂).
    - do 2 rewrite <- functor_comp.
      now rewrite (pr22 ϕ₁).
    - do 2 rewrite <- functor_comp.
      now rewrite (pr22 ϕ₂).
  Qed.

  Let u : D⟦N_D, F n⟧
      := NNO_mor _ N_D
           (iscontrpr1 (weak_equiv_preserves_chosen_terminal F F_weq T_C T_D) · # F z')
           (#F s').
  Let v : C⟦N, n⟧ := fully_faithful_inv_hom (pr2 F_weq) N n u.

  Lemma reflection_of_NNO_along_weak_equiv_commutes_with_zero :  z · v = z'.
  Proof.
    unfold v, u.

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _).
    apply maponpaths.
    cbn.
    rewrite functor_comp.
    etrans. {
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    use (cancel_z_iso' (z_iso_Terminals T_D (make_Terminal _ (weak_equiv_preserves_chosen_terminal F F_weq T_C)))).

    set (q := NNO_mor_Z _ N_D  (iscontrpr1 (weak_equiv_preserves_chosen_terminal F F_weq T_C T_D) · # F z') (# F s')).
    refine (assoc _ _ _ @ q).
  Qed.

  Lemma reflection_of_NNO_along_weak_equiv_commutes_with_succ  :  s · v = v · s'.
  Proof.
    unfold v, u.

    refine (! homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _ @ _).
    refine (_ @ homotinvweqweq (weq_from_fully_faithful (pr2 F_weq) _ _) _).
    apply maponpaths.
    cbn.
    rewrite functor_comp.
    etrans. {
      apply maponpaths.
      apply functor_on_fully_faithful_inv_hom.
    }
    etrans. { apply (NNO_mor_S _ N_D). }
    apply pathsinv0.
    rewrite functor_comp.
    apply maponpaths_2.
    apply (functor_on_fully_faithful_inv_hom _ (pr2 F_weq)).
  Qed.

  Definition weak_equiv_reflects_uvp_existence_of_NNO
    : ∑ u : C ⟦ N, n ⟧, z · u = z' × s · u = u · s'.
  Proof.
    exists (fully_faithful_inv_hom (pr2 F_weq) _ _ u).
    split.
    - apply reflection_of_NNO_along_weak_equiv_commutes_with_zero.
    - apply reflection_of_NNO_along_weak_equiv_commutes_with_succ.
  Defined.

End WeakEquivReflectsNNO₀.

Lemma weak_equiv_reflects_NNO
  {C D : category}
  {F : functor C D}
  (T_C : Terminal C) (T_D : Terminal D)
  (N : ob C) (z : C⟦T_C, N⟧) (s : C⟦N, N⟧)
  (F_weq : is_weak_equiv F)
  : isNNO T_D (F N) (iscontrpr1 (weak_equiv_preserves_chosen_terminal _ F_weq T_C _) · #F z) (#F s)
    → isNNO T_C N z s.
Proof.
  intro F_pN.
  intros n z' s'.
  use iscontraprop1.
  - apply (weak_equiv_reflects_uvp_uniqueness_of_NNO F_pN).
  - apply (weak_equiv_reflects_uvp_existence_of_NNO F_pN).
Defined.

(* Corollary weak_equiv_lift_NNO_mor
  {C D E : category}
  {F : functor C E}
  {G : functor C D}
  {H : functor D E}
  {T_C : Terminal C} {T_D : Terminal D} {T_E : Terminal E}
  (N : NNO T_C) (M : NNO T_D) (O : NNO T_E)
  (F_pT : preserves_chosen_terminal T_C F)
  (G_weq : is_weak_equiv G)
  (α : nat_z_iso (functor_composite G H) F)
  : preserves_NNO T_C T_E F_pT N O
    → preserves_NNO T_D T_E (weak_equiv_lifts_preserves_chosen_terminal α G_weq T_D F_pT) M O.
Proof.
  intro F_pN.
  set (G_pN := weak_equiv_preserves_NNO N M G_weq).

  (* Check NNO_from_functor_creation.
  set (M' := NNO_from_functor_creation). *)

  (* use (factor_through_squash _ _ (eso_from_weak_equiv _ G_weq M)).
  { apply isaprop_is_z_isomorphism. }
  intros [m i]. *)

  (* The morphism is the unique one from O to H(M). *)
  (* O ≅ (F N) ≅ H(G(N)) ≅ H(M) *)
  set (i_O_FN := make_z_iso _ _ (pr2 F_pN)).
  set (i_FN_HGN := nat_z_iso_pointwise_z_iso (nat_z_iso_inv α) N).
  set (i_M_GN := make_z_iso _ _ (pr2 G_pN)).
  set (i_O_HM := z_iso_comp i_O_FN (z_iso_comp i_FN_HGN (functor_on_z_iso H (z_iso_inv i_M_GN)))).

  (* set (GN_isNNO := weak_equiv_reflects_NNO T_C T_D N (zeroNNO _ N) (sucNNO _ N) G_weq). *)

  use (is_z_isomorphism_path _ (pr2 i_O_HM)).
  use NNO_mor_unique'.
  - cbn.
    rewrite assoc.
    rewrite NNO_mor_Z.
    rewrite ! assoc.


Admitted. *)
