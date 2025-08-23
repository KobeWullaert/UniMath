(*
        Groupoids As Dagger Categories

        Any groupoid becomes a †-category by defining f^† := f^-1.
        Furthermore, a groupoid is dagger univalent if and only if it is univalent.
        Also, every functor between groupoids is dagger-preserving

        Contents.
        1. Groupoids are dagger categories
        2. Univalence for groupoidal dagger categories
        3. Functors between groupoids are dagger-preserving
        4. The core of a dagger category is a dagger category
        5. Weak equivalences between dagger categories are dagger weak equivalences
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.WeakEquivalences.Core.
Require Import UniMath.CategoryTheory.Core.Univalence.

Require Import UniMath.CategoryTheory.Groupoids.

Require Import UniMath.CategoryTheory.DaggerCategories.Categories.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.
Require Import UniMath.CategoryTheory.DaggerCategories.Unitary.
Require Import UniMath.CategoryTheory.DaggerCategories.Univalence.
Require Import UniMath.CategoryTheory.DaggerCategories.Functors.WeakEquivalences.

Local Open Scope cat.

(** * 1. Groupoids Are Dagger Categories *)
Section GroupoidsAsDaggers.

  Context (C : groupoid).

  Definition GRP_dagger_structure : dagger_structure C.
  Proof.
    intros x y f.
    exact (pr1 (z_iso_inv (_ ,, groupoid_is_pregroupoid C x y f))).
  Defined.

  Lemma GRP_dagger_laws : dagger_laws GRP_dagger_structure.
  Proof.
    repeat split ; intro ; intros ; use inverse_unique_precat.
    - exact (identity x).
    - apply groupoid_is_pregroupoid.
    - apply is_inverse_in_precat_identity.
    - exact (f · g).
    - apply groupoid_is_pregroupoid.
    - apply is_inverse_in_precat_comp ; apply groupoid_is_pregroupoid.
    - apply groupoid_is_pregroupoid ; exact f.
    - apply groupoid_is_pregroupoid.
    - apply is_inverse_in_precat_inv ; apply groupoid_is_pregroupoid.
  Qed.

  Definition GRP_dagger : dagger C
    := _ ,, GRP_dagger_laws.

End GroupoidsAsDaggers.

(** * 2. Univalence For Groupoidal Dagger Categories *)
Section UnivalenceOfGroupoids.

  Context (C : groupoid).

  Definition univalence_to_dagger_univalence
        {x y : C} (f : z_iso x y)
    : unitary (GRP_dagger C) x y.
  Proof.
    exists (morphism_from_z_iso _ _ f).
    apply groupoid_is_pregroupoid.
  Defined.

  Definition dagger_univalence_to_univalence
             {x y : C} (f : unitary (GRP_dagger C) x y)
    : z_iso x y
    := make_z_iso _ _ (pr2 f).

  Definition z_iso_is_unitary (x y : C)
    : z_iso x y ≃ unitary (GRP_dagger C) x y.
  Proof.
    use weq_iso.
    - exact (λ p, univalence_to_dagger_univalence p).
    - exact (λ p, dagger_univalence_to_univalence p).
    - intro ; apply z_iso_eq, idpath.
    - intro ; apply unitary_eq, idpath.
  Defined.

  Lemma idtodagger_as_idtoiso_pointwise {x y : C} (p : x = y)
    : idtodaggeriso (GRP_dagger C) x y p = z_iso_is_unitary x y (idtoiso p).
  Proof.
    apply (unitary_eq (idtodaggeriso (GRP_dagger C) x y p) (univalence_to_dagger_univalence (idtoiso p))).
    induction p ; apply idpath.
  Defined.

  Lemma idtoiso_as_idtodagger_pointwise {x y : C} (p : x = y)
    : idtoiso p = dagger_univalence_to_univalence (idtodaggeriso (GRP_dagger C) x y p).
  Proof.
    apply (z_iso_eq (idtoiso p) (dagger_univalence_to_univalence (idtodaggeriso (GRP_dagger C) x y p))).
    induction p ; apply idpath.
  Defined.

  Definition groupoid_univalence_equiv_dagger_univalence
    : is_univalent C ≃ is_univalent_dagger (GRP_dagger C).
  Proof.
    use weqimplimpl.
    - intros u x y.
      apply (isweqhomot' (λ p, z_iso_is_unitary x y (idtoiso p))).
      + apply (twooutof3c (idtoiso (a := x) (b := y)) (z_iso_is_unitary x y)).
        * apply u.
        * apply z_iso_is_unitary.
      + apply (λ p, ! idtodagger_as_idtoiso_pointwise p).
    - intros u x y.
      apply (isweqhomot' (λ p, invweq (z_iso_is_unitary x y) (idtodaggeriso (GRP_dagger C) _ _ p))).
      + apply (twooutof3c (idtodaggeriso (GRP_dagger C) x y) (invweq (z_iso_is_unitary x y))).
        * apply u.
        * apply (invweq (z_iso_is_unitary _ _)).
      + apply (λ p, ! idtoiso_as_idtodagger_pointwise p).
    - apply isaprop_is_univalent.
    - apply isaprop_is_univalent_dagger.
  Qed.

End UnivalenceOfGroupoids.

(** * 3. Functors Are Dagger Preserving *)
Section FunctorsBetweenGroupoidsAreDaggerPreserving.

  Context {C D : groupoid} (F : functor C D).

  Lemma functor_between_groupoids_is_dagger_functor
    : is_dagger_functor (GRP_dagger C) (GRP_dagger D) F.
  Proof.
    intros a b f.
    cbn.
    refine (functor_on_inv_from_z_iso F (f ,, groupoid_is_pregroupoid C a b f) @ _).
    apply maponpaths.
    use subtypePath.
    { intro ; apply isaprop_is_z_isomorphism. }
    apply idpath.
  Qed.

End FunctorsBetweenGroupoidsAreDaggerPreserving.

(** * 4. Core Of A Dagger Category *)
Section CoreOfDaggerCategory.

  Context {C : category} (d : dagger C).

  Definition core_of_dagger_cat_data : precategory_data.
  Proof.
    use make_precategory_data.
    - use tpair.
      + exact (ob C).
      + exact (unitary d).
    - apply unitary_id.
    - intros a b c.
      apply unitary_comp.
  Defined.

  Definition core_of_dagger_cat_ax : is_precategory core_of_dagger_cat_data.
  Proof.
    repeat split ; intro ; intros
    ; apply unitary_eq
    ; apply (pr21 C).
  Qed.

  Definition core_of_dagger_precat : precategory.
  Proof.
    use make_precategory.
    - exact core_of_dagger_cat_data.
    - exact core_of_dagger_cat_ax.
  Defined.

  Definition core_of_dagger_cat : category.
  Proof.
    use make_category.
    - exact core_of_dagger_precat.
    - intro ; intro ; apply isaset_unitary.
  Defined.

  Definition dagger_on_core_of_dagger_cat
    : dagger core_of_dagger_cat.
  Proof.
    use tpair.
    - intro ; intro ; apply unitary_inv.
    - abstract (repeat split ; intro ; intros
      ; use unitary_eq ; apply (pr2 d)).
  Defined.

  Definition core_dagger_cat_is_groupoid : groupoid.
  Proof.
    exists core_of_dagger_cat.
    intros a b f.
    set (i := make_z_iso _ _ (pr2 f)).
    use tpair.
    - exact (unitary_inv f).
    - split ; use unitary_eq.
      + exact (pr122 i).
      + exact (pr222 i).
  Defined.

  Lemma dagger_on_groupoid_core_is_groupoid_dagger
    : GRP_dagger core_dagger_cat_is_groupoid = dagger_on_core_of_dagger_cat.
  Proof.
    use subtypePath.
    { intro ; apply isaprop_dagger_laws. }
    do 3 (apply funextsec ; intro) ; apply idpath.
  Qed.

  Definition groupoid_inclusion_is_dagger_functor
    : dagger_functor dagger_on_core_of_dagger_cat d.
  Proof.
    use make_dagger_functor.
    - use make_functor.
      + use make_functor_data.
        * exact (λ x, x).
        * exact (λ _ _ f, pr1 f).
      + abstract (split ; intro ; intros ; apply idpath).
    - split.
  Defined.

  Lemma unitary_in_dagger_core (c c' : C)
    : unitary dagger_on_core_of_dagger_cat c c' ≃ unitary d c c'.
  Proof.
    use weq_iso.
    - exact pr1.
    - intro u.
      exists u.
      split ; apply unitary_eq ; apply (pr2 u).
    - intro ; apply unitary_eq, idpath.
    - intro ; apply unitary_eq, idpath.
  Defined.

  Lemma idtouiso_in_dagger_code (c c' : C)
    : idtodaggeriso d c c'
      = funcomp (idtodaggeriso dagger_on_core_of_dagger_cat c c') (unitary_in_dagger_core c c').
  Proof.
    apply funextsec ; intro p.
    induction p.
    apply idpath.
  Qed.

  Lemma univalence_of_dagger_core
    : is_univalent_dagger d ≃ is_univalent_dagger dagger_on_core_of_dagger_cat.
  Proof.
    use weqonsecfibers.
    intro c.
    use weqonsecfibers.
    intro c'.
    refine (_ ∘ weq_transportf isweq (idtouiso_in_dagger_code c c'))%weq.
    use weqimplimpl ; try (apply isapropisweq).
    - intro p.
      use (twooutof3a _ _ p).
      apply unitary_in_dagger_core.
    - intro p.
      use (twooutof3c _ _ p).
      apply unitary_in_dagger_core.
  Qed.

End CoreOfDaggerCategory.

(** * 5. Weak Equivalences *)
Section WeakEquivalences.

  Lemma weak_equiv_preserves_groupoidalness
    {C D : category} (F : weak_equiv C D)
    : is_pregroupoid C → is_pregroupoid D.
  Proof.
    intro Cg.
    intros d d' f.
    use (factor_through_squash _ _ (eso_from_weak_equiv _ (pr2 F) d)).
    { apply isaprop_is_z_isomorphism. }
    intros [c id].
    use (factor_through_squash _ _ (eso_from_weak_equiv _ (pr2 F) d')).
    { apply isaprop_is_z_isomorphism. }
    intros [c' id'].

    assert (pf : f = inv_from_z_iso id
                       · #(pr1 F) (fully_faithful_inv_hom (pr22 F) _ _ (id · f · inv_from_z_iso id'))
                       · id'
           ).
    {
      rewrite functor_on_fully_faithful_inv_hom.
      rewrite ! assoc.
      rewrite z_iso_after_z_iso_inv, id_left.
      now rewrite assoc', z_iso_after_z_iso_inv, id_right.
    }
    induction (! pf).
    repeat (use is_z_isomorphism_comp).
    - apply z_iso_inv.
    - apply functor_on_is_z_isomorphism.
      apply Cg.
    - apply id'.
  Qed.

  Lemma eso_between_groupoids_is_dagger_eso
    {C D : groupoid} {F : functor C D} (F_eso : essentially_surjective F)
    : is_unitarily_eso (functor_between_groupoids_is_dagger_functor F).
  Proof.
    intro d.
    use (factor_through_squash _ _ (F_eso d)).
    { apply isapropishinh. }
    intros [c i].
    apply hinhpr.
    exists c.
    apply univalence_to_dagger_univalence.
    exact i.
  Qed.

  Lemma dagger_weak_equivalences_between_groupoids
    {C D : groupoid} (F : functor C D)
    : is_weak_equiv F ≃ is_weak_dagger_equiv (functor_between_groupoids_is_dagger_functor F).
  Proof.
    use weqdirprodf.
    2: { apply idweq. }
    use weqimplimpl.
    - apply eso_between_groupoids_is_dagger_eso.
    - apply is_unitarily_eso_is_eso.
    - apply isaprop_essentially_surjective.
    - apply isaprop_is_unitarily_eso.
  Qed.

End WeakEquivalences.
