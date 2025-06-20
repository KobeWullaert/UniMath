(**

This file contains a direct formalization of the lambda calculus ([LambdaCalculus]) as the initial
algebra of the lambda calculus functor. A better formalization where the lambda calculus and a
substitution monad is obtained from a binding signature can be found in
SubstitutionSystems/LamFromBindingSig.v.

Written by: Anders Mörtberg, 2016

*)

Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.NaturalNumbers.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Graphs.Limits.
Require Import UniMath.CategoryTheory.PrecategoryBinProduct.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Examples.
Require Import UniMath.CategoryTheory.Chains.All.
Require Import UniMath.CategoryTheory.Exponentials.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Local Notation "'chain'" := (diagram nat_graph).

Section lambdacalculus.

Local Notation "'HSET2'":= [HSET, HSET].

(*
Local Definition has_homsets_HSET2 : has_homsets HSET2.
Proof.
apply functor_category_has_homsets.
Defined.
 *)

Local Definition BinProductsHSET2 : BinProducts HSET2.
Proof.
apply (BinProducts_functor_precat _ _ BinProductsHSET).
Defined.

Local Definition BinCoproductsHSET2 : BinCoproducts HSET2.
Proof.
apply (BinCoproducts_functor_precat _ _ BinCoproductsHSET).
Defined.

Local Lemma Exponentials_HSET2 : Exponentials BinProductsHSET2.
Proof.
apply Exponentials_functor_HSET.
Defined.

Local Lemma InitialHSET2 : Initial HSET2.
Proof.
apply (Initial_functor_precat _ _ InitialHSET).
Defined.

Local Definition CCHSET : Colims_of_shape nat_graph HSET :=
  ColimsHSET_of_shape nat_graph.

Local Notation "' x" := (omega_cocont_constant_functor x)
                          (at level 10).

Local Notation "'Id'" := (omega_cocont_functor_identity _).

Local Notation "F * G" :=
  (omega_cocont_BinProduct_of_functors_alt BinProductsHSET2 _
     (is_omega_cocont_constprod_functor1 _ Exponentials_HSET2) F G).

Local Notation "F + G" :=
  (omega_cocont_BinCoproduct_of_functors BinCoproductsHSET2 F G).

Local Notation "'_' 'o' 'option'" :=
  (omega_cocont_pre_composition_functor
      (option_functor BinCoproductsHSET TerminalHSET)
      CCHSET) (at level 10).

(** The lambda calculus functor with one component for variables, one for application and one for
    abstraction/lambda *)
Definition lambdaOmegaFunctor : omega_cocont_functor HSET2 HSET2 :=
  omega_cocont_constant_functor (C:= [_,_]) (D:=[_,_])(functor_identity HSET) +
                                        (Id * Id + _ o option).


(*
Definition lambdaOmegaFunctor : omega_cocont_functor HSET2 HSET2 :=
  '(functor_identity HSET) + (Id * Id + _ o option).
 *)

Let lambdaFunctor : functor HSET2 HSET2 := pr1 lambdaOmegaFunctor.
Let is_omega_cocont_lambdaFunctor : is_omega_cocont lambdaFunctor :=
  pr2 lambdaOmegaFunctor.

Lemma lambdaFunctor_Initial :
  Initial (category_FunctorAlg lambdaFunctor).
Proof.
apply (colimAlgInitial InitialHSET2 is_omega_cocont_lambdaFunctor).
apply ColimsFunctorCategory_of_shape; apply ColimsHSET_of_shape.
Defined.

(** The lambda calculus *)
Definition LambdaCalculus : HSET2 :=
  alg_carrier _ (InitialObject lambdaFunctor_Initial).

Let LambdaCalculus_mor : HSET2⟦lambdaFunctor LambdaCalculus,LambdaCalculus⟧ :=
  alg_map _ (InitialObject lambdaFunctor_Initial).

Let LambdaCalculus_alg : algebra_ob lambdaFunctor :=
  InitialObject lambdaFunctor_Initial.

Definition var_map : HSET2⟦functor_identity HSET,LambdaCalculus⟧ :=
  BinCoproductIn1 (BinCoproductsHSET2 _ _) · LambdaCalculus_mor.

(* How to do this nicer? *)
Definition prod2 (x y : HSET2) : HSET2.
Proof.
apply BinProductsHSET2; [apply x | apply y].
Defined.

Definition app_map : HSET2⟦prod2 LambdaCalculus LambdaCalculus,LambdaCalculus⟧ :=
  BinCoproductIn1 (BinCoproductsHSET2 _ _) · BinCoproductIn2 (BinCoproductsHSET2 _ _) · LambdaCalculus_mor.

Definition app_map' (x : HSET) : HSET⟦(pr1 LambdaCalculus x × pr1 LambdaCalculus x)%set,pr1 LambdaCalculus x⟧.
Proof.
apply app_map.
Defined.

Let precomp_option X := (pre_composition_functor _ _ HSET
                          (option_functor BinCoproductsHSET TerminalHSET) X).

Definition lam_map : HSET2⟦precomp_option LambdaCalculus,LambdaCalculus⟧ :=
  BinCoproductIn2 (BinCoproductsHSET2 _ _) · BinCoproductIn2 (BinCoproductsHSET2 _ _) · LambdaCalculus_mor.

Definition make_lambdaAlgebra (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) : algebra_ob lambdaFunctor.
Proof.
apply (tpair _ X).
use (BinCoproductArrow _ fvar (BinCoproductArrow _ fapp flam)).
Defined.

Definition foldr_map (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  algebra_mor lambdaFunctor LambdaCalculus_alg (make_lambdaAlgebra X fvar fapp flam).
Proof.
apply (InitialArrow lambdaFunctor_Initial (make_lambdaAlgebra X fvar fapp flam)).
Defined.

Definition foldr_map' (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
   HSET2 ⟦ pr1 LambdaCalculus_alg, pr1 (make_lambdaAlgebra X fvar fapp flam) ⟧.
Proof.
apply (foldr_map X fvar fapp flam).
Defined.

Lemma foldr_var (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  var_map · foldr_map X fvar fapp flam = fvar.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 (BinCoproductsHSET2 _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0; [eapply cancel_postcomposition, BinCoproductOfArrowsIn1|].
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
apply id_left.
Defined.

Lemma foldr_app (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  app_map · foldr_map X fvar fapp flam =
  # (pr1 (Id * Id)) (foldr_map X fvar fapp flam) · fapp.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn1 (BinCoproductsHSET2 _ _) · BinCoproductIn2 (BinCoproductsHSET2 _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, cancel_postcomposition, BinCoproductOfArrowsIn1.
rewrite <- assoc.
eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|].
rewrite <- assoc.
now eapply pathscomp0; [eapply maponpaths, BinCoproductIn1Commutes|].
Defined.

Lemma foldr_lam (X : HSET2) (fvar : HSET2⟦functor_identity HSET,X⟧)
  (fapp : HSET2⟦prod2 X X,X⟧) (flam : HSET2⟦precomp_option X,X⟧) :
  lam_map · foldr_map X fvar fapp flam =
  # (pr1 (_ o option)) (foldr_map X fvar fapp flam) · flam.
Proof.
assert (F := maponpaths (λ x, BinCoproductIn2 (BinCoproductsHSET2 _ _) · BinCoproductIn2 (BinCoproductsHSET2 _ _) · x)
                        (algebra_mor_commutes _ _ _ (foldr_map X fvar fapp flam))).
rewrite assoc in F.
eapply pathscomp0; [apply F|].
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition.
  rewrite <- assoc.
  eapply maponpaths, BinCoproductOfArrowsIn2.
rewrite assoc.
eapply pathscomp0.
  eapply cancel_postcomposition, cancel_postcomposition, BinCoproductOfArrowsIn2.
rewrite <- assoc.
eapply pathscomp0.
  eapply maponpaths, BinCoproductIn2Commutes.
rewrite <- assoc.
now eapply pathscomp0; [eapply maponpaths, BinCoproductIn2Commutes|].
Defined.

End lambdacalculus.


(* Old version *)
(* Definition Lambda : functor HSET2 HSET2. *)
(* Proof. *)
(* eapply coproduct_of_functors. *)
(*   apply CoproductsHSET2. *)
(*   apply (constant_functor HSET2 HSET2 (functor_identity HSET)). *)
(* eapply coproduct_of_functors. *)
(*   apply CoproductsHSET2. *)
(*   (* app *) *)
(*   eapply functor_composite. *)
(*     apply delta_functor. *)
(*     apply binproduct_functor. *)
(*     apply ProductsHSET2. *)
(* (* lam *) *)
(* apply (pre_composition_functor _ _ _ has_homsets_HSET _ *)
(*          (option_functor _ CoproductsHSET TerminalHSET)). *)
(* Defined. *)

(* Lemma omega_cocont_LambdaFunctor : is_omega_cocont LambdaFunctor. *)
(* Proof. *)
(* apply is_omega_cocont_coproduct_of_functors. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply functor_category_has_homsets. *)
(* simpl. *)
(* apply is_omega_cocont_functor_identity. *)
(*   apply has_homsets_HSET2. *)
(* apply is_omega_cocont_coproduct_of_functors. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_functor_composite. *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_delta_functor. *)
(*   apply (Products_functor_precat _ _ ProductsHSET). *)
(*   apply functor_category_has_homsets. *)
(*   apply is_omega_cocont_binproduct_functor. *)
(*   apply functor_category_has_homsets. *)
(*   apply Exponentials_functor_HSET. *)
(*   apply has_homsets_HSET. *)
(* apply is_omega_cocont_pre_composition_functor. *)
(* apply LimsHSET. *)
(* Defined. *)
