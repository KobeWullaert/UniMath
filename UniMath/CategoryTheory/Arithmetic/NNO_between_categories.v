Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.Preservation.
Require Import UniMath.CategoryTheory.Arithmetic.NNO.

Local Open Scope cat.

Proposition adj_equiv_of_cats_preserve_initial
  {C D : category} {F : functor C D} (F_aq : adj_equivalence_of_cats F)
  (I : Initial C)
  : Initial D.
Proof.
  exists (F I).
  exact (left_adjoint_preserves_initial _ (F_aq) I (pr2 I)).
Defined.

Section NaturalNumbersObject.

  Context {C : category} (T : Terminal C).

  Definition nno_triple : UU := ∑ N : ob C, C⟦T, N⟧ × C⟦N, N⟧.

  Definition nno_triple_to_ob (n : nno_triple) : ob C := pr1 n.
  Coercion nno_triple_to_ob : nno_triple >-> ob.
  Definition nno_triple_to_zero (n : nno_triple) : C⟦T, n⟧ := pr12 n.
  Definition nno_triple_to_succ (n : nno_triple) : C⟦n, n⟧ := pr22 n.

  Definition nno_triple_hom (n N : nno_triple) : UU
    := ∑ f : C⟦n, N⟧, nno_triple_to_zero n · f = nno_triple_to_zero N × nno_triple_to_succ n · f = f · nno_triple_to_succ N.

  Definition nno_triple_hom_to_mor {n N} (f : nno_triple_hom n N) : C⟦n, N⟧ := pr1 f.
  Coercion nno_triple_hom_to_mor : nno_triple_hom >-> precategory_morphisms.

  Definition nno_triple_cat_ob_mor : precategory_ob_mor.
  Proof.
    exists (nno_triple).
    exact (λ n N, nno_triple_hom n N).
  Defined.

  Lemma nno_triple_cat_id (n : nno_triple) : nno_triple_hom n n.
  Proof.
    exists (identity _).
    abstract (split ; [apply id_right | refine (id_right _ @ ! id_left _)]).
  Defined.

  Lemma nno_triple_cat_comp {n₁ n₂ n₃ : nno_triple}
    : nno_triple_hom n₁ n₂ → nno_triple_hom n₂ n₃ → nno_triple_hom n₁ n₃.
  Proof.
    intros [f [f₁ f₂]] [g [g₁ g₂]].
    exists (f · g).
    split.
    - refine (assoc _ _ _ @ _).
      etrans. { apply maponpaths_2. exact f₁. }
      exact g₁.
    - refine (assoc _ _ _ @ _).
      etrans. { apply maponpaths_2. exact f₂. }
      refine (assoc' _ _ _ @ _ @ assoc _ _ _).
      apply maponpaths.
      exact g₂.
  Defined.

  Definition nno_triple_cat_id_comp : precategory_id_comp nno_triple_cat_ob_mor.
  Proof.
    split.
    - exact nno_triple_cat_id.
    - intros ? ? ? f g.
      exact (nno_triple_cat_comp f g).
  Defined.

  Lemma nno_triple_mor_eq {n N : nno_triple} (f g : nno_triple_hom n N)
    : pr1 f = pr1 g → f = g.
  Proof.
    intro p.
    use subtypePath.
    { intro ; apply isapropdirprod ; apply homset_property. }
    exact p.
  Qed.

  Lemma nno_triple_mor_isaset (n N : nno_triple): isaset (nno_triple_hom n N).
  Proof.
    apply isaset_total2.
    - apply homset_property.
    - intro ; apply isasetaprop ; apply isapropdirprod ; apply homset_property.
  Qed.

  Definition nat_num_object_cat : category.
  Proof.
    simple refine (((_ ,, _) ,, _) ,, _).
    - exact nno_triple_cat_ob_mor.
    - exact nno_triple_cat_id_comp.
    - unfold is_precategory.
      repeat split ; intro ; intros ; apply nno_triple_mor_eq.
      + apply id_left.
      + apply id_right.
      + apply assoc.
      + apply assoc'.
    - intro ; intro.
      apply nno_triple_mor_isaset.
  Defined.

End NaturalNumbersObject.

Definition category_with_nno (C : category) (T : Terminal C) : UU
  := Initial (nat_num_object_cat T).

(* A routine check *)
Proposition category_with_nno_to_NNO {C : category} (T : Terminal C)
  : category_with_nno _ T → NNO T.
Proof.
  intros [n p].
  unfold nat_num_object_cat in n.
  cbn in n.
  use make_NNO.
  - exact n.
  - exact (nno_triple_to_zero _ n).
  - exact (nno_triple_to_succ _ n).
  - intros N Z S.
    exact (p (N ,, (Z ,, S))).
Defined.

Section NaturalNumbersObjectAndFunctors.

  Context {C₁ C₂ : category} (T₁ : Terminal C₁) (T₂ : Terminal C₂) (F : functor C₁ C₂)
    (F_pT : preserves_terminal F).

  Definition functor_to_nno_cat_on_ob : nat_num_object_cat T₁ → nat_num_object_cat T₂.
  Proof.
    intros [n [z s]].
    exists (F n).
    split.
    + refine (_ · #F z).
      apply F_pT, T₁.
    + exact (#F s).
  Defined.

  Definition functor_to_nno_cat_on_mor
    {n N : nat_num_object_cat T₁}
    (f : (nat_num_object_cat T₁)⟦n, N⟧)
    : (nat_num_object_cat T₂)⟦functor_to_nno_cat_on_ob n, functor_to_nno_cat_on_ob N⟧.
  Proof.
    induction n as [n [z s]].
    induction N as [N [Z S]].
    induction f as [f [fz fs]].
    exists (#F f).

    abstract (
        cbn in * ;
        split;
        [ rewrite <- fz ;
          rewrite functor_comp ;
          rewrite assoc ;
          apply idpath
        | do 2 rewrite <- functor_comp ;
          apply maponpaths ;
          exact fs ]).
  Defined.

  Definition functor_to_nno_cat_data
    : functor_data (nat_num_object_cat T₁) (nat_num_object_cat T₂).
  Proof.
    exists functor_to_nno_cat_on_ob.
    exact (λ n N f, functor_to_nno_cat_on_mor f).
  Defined.

  Lemma functor_to_nno_cat_properties
    : is_functor functor_to_nno_cat_data.
  Proof.
    split.
    - intro n.
      use nno_triple_mor_eq.
      apply functor_id.
    - intros n₁ n₂ n₃ f g.
      use nno_triple_mor_eq.
      apply functor_comp.
  Qed.

  Definition functor_to_nno_cat
    : functor (nat_num_object_cat T₁) (nat_num_object_cat T₂).
  Proof.
    exists functor_to_nno_cat_data.
    exact functor_to_nno_cat_properties.
  Defined.

End NaturalNumbersObjectAndFunctors.

Section NaturalNumbersObjectAndFunctorsModuloChosenTerminal.

  Context (C : category).

  Definition nno_modulo_chosen_terminal_unit
    (T T' : Terminal C)
    : functor_identity (nat_num_object_cat T)
        ⟹ functor_to_nno_cat T T' (functor_identity C) (identity_preserves_terminal C)
        ∙ functor_to_nno_cat T' T (functor_identity C) (identity_preserves_terminal C).
  Proof.
    use make_nat_trans.
    - intro n.
      simple refine (identity _ ,, (_ ,, _)) ; cbn.
      + unfold identity_preserves_terminal.
        refine (id_right _ @ _).
        rewrite assoc.
        refine (! id_left _ @ _).
        apply maponpaths_2.
        use proofirrelevance.
        apply isapropifcontr, T.
      + exact (id_right _ @ ! id_left _).
    - intros n N f.
      use nno_triple_mor_eq.
      exact (id_right _ @ ! id_left _).
  Defined.

  Lemma nno_modulo_chosen_terminal_unit_is_iso'
          (T T' : Terminal C) n
    : is_z_isomorphism (nno_modulo_chosen_terminal_unit T T' n).
  Proof.
    use make_is_z_isomorphism.
    - simple refine (identity _ ,, (_ ,, _)) ; cbn.
      + rewrite id_right.
        rewrite assoc.
        refine (_ @ id_left _).
        apply maponpaths_2.
        use proofirrelevance.
        apply isapropifcontr, T.
      + exact (id_right _ @ ! id_left _).
    - split ; use nno_triple_mor_eq ; cbn ; apply id_right.
  Defined.

  Lemma nno_modulo_chosen_terminal_unit_is_iso
    (T T' : Terminal C)
    : is_nat_z_iso (nno_modulo_chosen_terminal_unit T T').
  Proof.
    intro.
    apply nno_modulo_chosen_terminal_unit_is_iso'.
  Defined.

  Definition nno_modulo_chosen_terminal_iso_unit
    (T T' : Terminal C)
    : nat_z_iso _ _
    := make_nat_z_iso _ _ _ (nno_modulo_chosen_terminal_unit_is_iso T T').

  Proposition nno_modulo_chosen_terminal
    (T T' : Terminal C)
    : adj_equivalence_of_cats (functor_to_nno_cat T T' (functor_identity C) (identity_preserves_terminal C)).
  Proof.
    use make_adj_equivalence_of_cats'.
    - exact (functor_to_nno_cat T' T (functor_identity C) (identity_preserves_terminal C)).
    - apply nno_modulo_chosen_terminal_iso_unit.
    - apply nat_z_iso_to_trans_inv.
      apply nno_modulo_chosen_terminal_iso_unit.
    - abstract (split ; intro ; use nno_triple_mor_eq ; apply id_right).
    - intro ; apply nno_modulo_chosen_terminal_unit_is_iso'.
    - intro n.
      apply (pr2 (z_iso_inv (_ ,, nno_modulo_chosen_terminal_unit_is_iso' T T' _))).
  Defined.

  Corollary nno_modulo_chosen_terminal'
    (T T' : Terminal C)
    : category_with_nno C T → category_with_nno C T'.
  Proof.
    exact (λ N, adj_equiv_of_cats_preserve_initial (nno_modulo_chosen_terminal T T') N).
  Defined.

End NaturalNumbersObjectAndFunctorsModuloChosenTerminal.

Section CreationAndPreservationOfNNO.

  Context {C₁ C₂ : category}
    {F : functor C₁ C₂}
    {T₁ : Terminal C₁}
    (F_pT : preserves_terminal F)
    (N₁ : category_with_nno C₁ T₁).

  Definition functor_creates_NNO
    : UU
    := isInitial _ (functor_to_nno_cat T₁ (preserves_terminal_to_terminal F F_pT T₁) F F_pT (pr1 N₁)).

  Proposition functor_creates_NNO_to_NNO
    : functor_creates_NNO → category_with_nno C₂ (preserves_terminal_to_terminal F F_pT T₁).
  Proof.
    intro F_pN.
    exact (_ ,, F_pN).
  Defined.

  Definition functor_preserves_NNO {T₂ : Terminal C₂} (N₂ : category_with_nno C₂ T₂)
    : UU
    := is_z_isomorphism (InitialArrow N₂ (functor_to_nno_cat T₁ T₂ F F_pT (pr1 N₁))).

End CreationAndPreservationOfNNO.

Section CreationAndPreservationProperties.

  Context {C : category} {T : Terminal C} (N : category_with_nno _ T).

  Lemma identity_functor_creates_NNO
    : functor_creates_NNO (identity_preserves_terminal C) N.
  Proof.
    exact (pr2 (nno_modulo_chosen_terminal' _ T  (preserves_terminal_to_terminal (functor_identity C) (identity_preserves_terminal C) T) N)).
  Defined.

  (* Lemma identity_functor_create_NNO
    (C : category) (T : Terminal C) (N : NNO T)
    : functor_preserves_NNO (identity_preserves_terminal _ _ (pr2 T)) N.
Proof.
  exact (λ m z s, pr222 N m z s).
Qed. *)


  Lemma composite_preserves_terminal {D E : category} {F : functor C D} {G : functor D E}
    (F_pT : preserves_terminal F) (G_pT : preserves_terminal G)
    : preserves_terminal (functor_composite F G).
  Proof.
  Admitted.

  Lemma composite_functor_creates_NNO {D E : category} (T_D : Terminal D)
    (M : category_with_nno _ T_D)
    {F : functor C D} (F_pT : preserves_terminal F)
    {G : functor D E} (G_pT : preserves_terminal G)
    (F_pN : functor_creates_NNO F_pT N)
    (G_pN : functor_creates_NNO G_pT M)
    : functor_creates_NNO (composite_preserves_terminal F_pT G_pT) N.
  Proof.
    set (T_D' := (preserves_terminal_to_terminal _ G_pT T_D)).
    set (FG_pT := (composite_preserves_terminal F_pT G_pT)).
    set (T_E' := (preserves_terminal_to_terminal _ FG_pT T)).

    set (O := functor_creates_NNO_to_NNO _ _ G_pN).
    set (O' := (nno_modulo_chosen_terminal' E T_D' T_E' O)).

    apply (iso_to_Initial O').

    Check functor_to_nno_cat T T_E'  (F ∙ G) FG_pT.

    use make_z_iso.
    - cbn.
      unfold nno_triple_hom.
      cbn.







End CreationAndPreservationProperties.




(*

Definition preserves_NNO
  {C D : category} {F : functor C D}
  {T_C : Terminal C}
  {T_D : Terminal D}
  (F_pT : preserves_terminal F)
  (N_C : NNO T_C)
  (N_D : NNO T_D)
  : UU.
Proof.
  simple refine (is_z_isomorphism (NNO_mor _ N_D _ _)).
  - exact (F N_C).
  - exact (iscontrpr1 (F_pT _ (pr2 T_C) T_D)).
  - Check NNO_mor.
Defined. *)


(* Lemma composite_functor_preserves_NNO
  {C₁ C₂ C₃ : category} {F : functor C₁ C₂} {G : functor C₂ C₃}
  {T₁ : Terminal C₁} {T₂ : Terminal C₂}
  (N₁ : NNO T₁) (N₂ : NNO T₂)
  (F_pT : preserves_chosen_terminal T₁ F)
  (G_pT : preserves_chosen_terminal T₂ G)
  (F_pN : preserves_NNO F_pT N₁)
  (G_pN : preserves_NNO G_pT N₂)
  : preserves_NNO (composite_preserves_chosen_terminal) N₁. *)
