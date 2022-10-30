Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.PrecompEquivalence.

Require Import UniMath.CategoryTheory.ProductCategory.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.

Require Import UniMath.CategoryTheory.Monoidal.MonoidalCategories.
Require Import UniMath.CategoryTheory.Monoidal.MonoidalFunctorCategory.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Functors.

Local Open Scope cat.

Section TensorRezk.

  Context {C D E : category} {H : functor C D}
          (Duniv : is_univalent D)
          (Euniv : is_univalent E)
          (H_eso : essentially_surjective H)
          (H_ff : fully_faithful H).

  Context (TC : functor (C ⊠ C) C) (I : C)
          (lu : left_unitor TC I)
          (ru : right_unitor TC I)
          (α : associator TC)
          (tri : triangle_eq TC I lu ru α)
          (pent : pentagon_eq TC α).

   Context (TE : functor (E ⊠ E) E) (IE : E)
          (luE : left_unitor TE IE)
          (ruE : right_unitor TE IE)
          (αE : associator TE)
          (triE : triangle_eq TE IE luE ruE αE)
          (pentE : pentagon_eq TE αE).

  Local Notation HH := (pair_functor H H).
  Let HH_eso := pair_functor_eso H H H_eso H_eso.
  Let HH_ff := pair_functor_ff H H H_ff H_ff.

  Definition TransportedTensor
    : functor (D ⊠ D) D
    := lift_functor_along (_,,Duniv) HH HH_eso HH_ff (functor_composite TC H).

  Definition TransportedTensorComm
    : nat_z_iso (HH ∙ lift_functor_along (D,, Duniv) HH HH_eso HH_ff (functor_composite TC H))
                (functor_composite TC H)
    := lift_functor_along_comm (_,,Duniv) HH HH_eso HH_ff (functor_composite TC H).

  Let TD := TransportedTensor.

  Definition precompT_data
    : disp_functor_data (pre_composition_functor _ _ E H)
                   (functor_tensor_disp_cat TD TE)
                   (functor_tensor_disp_cat TC TE).
  Proof.
    exists (λ G GG, functor_tensor_composition (pr1 (TransportedTensorComm)) GG).
    intros G1 G2 GG1 GG2 β ββ.
    intros x y.
    simpl.
    rewrite assoc.
    etrans. { apply maponpaths_2 ; exact (ββ (H x) (H y)). }
    do 2 rewrite assoc'.
    apply maponpaths.
    exact (! pr2 β _ _ (pr1 (pr1 (TransportedTensorComm)) (x, y))).
  Defined.

  Definition HT
    : disp_functor (pre_composition_functor _ _ E H)
                   (functor_tensor_disp_cat TD TE)
                   (functor_tensor_disp_cat TC TE).
  Proof.
    exists precompT_data.
    abstract (split ; intro ; intros ; apply isaprop_nat_trans_tensor).
  Defined.

  Definition lifted_functor_tensor
             {G : D ⟶ E}
             (HGG : functor_tensor TC TE (functor_compose H G))
    : functor_tensor TD TE G.
  Proof.
    use (lift_nat_trans_along (_,,Euniv) _ HH_eso HH_ff).
    use (nat_trans_comp _ _ _ HGG _).
    exact (post_whisker (nat_z_iso_inv TransportedTensorComm) G).
  Defined.

  Definition HT_eso : disp_functor_disp_ess_split_surj HT.
  Proof.
    intros G HGG.
    exists (lifted_functor_tensor HGG).
    use Isos.make_z_iso_disp.
    - intros c1 c2.
      simpl.
      rewrite id_right.
      rewrite (functor_id TE).
      rewrite id_left.

      (* In order to use lift_nat_along_comm, we need β to be of type
         HH · _ -> HH · _, the domain of β is not definitially
         of this form, hence, I have to do a manual 'casting' *)
      set (β :=
             nat_trans_comp
               (functor_tensor_map_dom TE (functor_compose H G))
               (functor_tensor_map_codom TC (functor_compose H G))
               (HH ∙ functor_tensor_map_codom TD G) HGG
               (post_whisker
                  (nat_z_iso_inv TransportedTensorComm)
                  G
               )
             : (nat_trans
                                 (HH  ∙ ((pair_functor G G) ∙ TE))
                                 ( HH ∙ functor_tensor_map_codom TD G))
          ).

      set (p := toforallpaths _ _ _ (base_paths _ _
                                                (lift_nat_trans_along_comm (_,,Euniv) _ HH_eso HH_ff β)) (c1,c2)).
      etrans.
      2: {
        apply maponpaths_2.
        exact (! p).
      }
      clear p.
      unfold β.

      unfold nat_trans_comp.
      unfold pr1.
      rewrite assoc'.
      etrans.
      2: {
        apply maponpaths.
        apply (functor_comp G).
      }

      etrans.
      2: {
        do 2 apply maponpaths.
        apply (! pr22 (pr2 (TransportedTensorComm) (c1,c2))).
      }
      rewrite functor_id.
      apply (! id_right _).
    - use tpair.
      2: { split ; apply isaprop_nat_trans_tensor. }
      intros c1 c2.
      simpl.
      rewrite id_right.
      rewrite (functor_id TE).
      rewrite id_left.
      unfold lifted_functor_tensor.

      set (β :=
             nat_trans_comp
               (functor_tensor_map_dom TE (functor_compose H G))
               (functor_tensor_map_codom TC (functor_compose H G))
               (HH ∙ functor_tensor_map_codom TD G) HGG
               (post_whisker
                  (nat_z_iso_inv TransportedTensorComm)
                  G
               )
             : (nat_trans
                                 (HH  ∙ ((pair_functor G G) ∙ TE))
                                 ( HH ∙ functor_tensor_map_codom TD G))
          ).

      set (p := toforallpaths _ _ _ (base_paths _ _
                                                (lift_nat_trans_along_comm (_,,Euniv) _ HH_eso HH_ff β)) (c1,c2)).
      etrans. {
        apply maponpaths_2.
        exact p.
      }
      clear p.
      unfold β.

      unfold nat_trans_comp.
      unfold pr1.
      rewrite assoc'.
      etrans. {
        apply maponpaths.
        apply (! functor_comp G _ _).
      }

      etrans. {
        do 2 apply maponpaths.
        apply (pr22 (pr2 (TransportedTensorComm) (c1,c2))).
      }
      rewrite functor_id.
      apply id_right.
  Qed.

  Definition HT_is_faithful
             {G1 G2 : [D, E]}
             (GG1 : functor_tensor_disp_cat TD TE G1)
             (GG2 : functor_tensor_disp_cat TD TE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    : isincl (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff).
  Proof.
    do 3 intro.
    assert (p : isaset ( hfiber (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff) y)).
    {
      use isaset_hfiber ; use isasetaprop ; apply isaprop_nat_trans_tensor.
    }

    use tpair.
    + use total2_paths_f.
      { apply isaprop_nat_trans_tensor. }
      use proofirrelevance.
      use hlevelntosn.
      apply isaprop_nat_trans_tensor.
    + intro ; apply p.
  Qed.

  Definition HT_is_full
             {G1 G2 : [D, E]}
             (GG1 : functor_tensor_disp_cat TD TE G1)
             (GG2 : functor_tensor_disp_cat TD TE G2)
             (β : [D, E] ⟦ G1, G2 ⟧)
    :   issurjective (λ ff : GG1 -->[ β] GG2, (# HT)%mor_disp ff).
  Proof.
    intro βHH.
    apply hinhpr.
    use tpair.
    2: apply isaprop_nat_trans_tensor.
    simpl in βHH.

    use nat_trans_tensor_to_characterization.
    use (lift_nat_trans_eq_along (_,,Euniv) _ HH_eso HH_ff).
    use nat_trans_eq.
    { apply homset_property. }
    intro cc.

    set (t := βHH (pr1 cc) (pr2 cc)).
    simpl in t.
    simpl.


    (* intros d1 d2.
    use (factor_through_squash _ _ (H_eso d1)).
    { apply homset_property. }
    intro c1.
    use (factor_through_squash _ _ (H_eso d2)).
    { apply homset_property. }
    intro c2.

    set (t := βHH (pr1 c1) (pr1 c2)).
    simpl in t.

    induction (isotoid _ Duniv (pr2 c1)).
    induction (isotoid _ Duniv (pr2 c2)).

    set (s := pr2 β _ _ (pr1 H_ptensor (pr1 c1, pr1 c2))).
    simpl in s.

    rewrite !  assoc' in t.
    rewrite <- s in t.*)


  Admitted.

  Definition HT_ff : disp_functor_ff HT.
  Proof.
    intro ; intros.
    apply isweqinclandsurj.
    - apply HT_is_faithful.
    - apply HT_is_full.
  Qed.

End TensorRezk.
