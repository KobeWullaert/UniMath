(**

Definition natural number objects (NNO's)

This is related to the initial algebra definition in FunctorAlgebras.v

Written by: Anders Mörtberg, 2018
Extended by: Kobe Wullaert, 2025

*)
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.Preservation.

Local Open Scope cat.

Section nno.

Context {C : category} (TC : Terminal C).

Local Notation "1" := TC.

Definition isNNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧) : hProp.
Proof.
use tpair.
- exact (∏ (a : C) (q : C ⟦ 1, a ⟧) (f : C ⟦ a, a ⟧),
         ∃! u : C ⟦ n, a ⟧, (z · u = q) × (s · u = u · f)).
- abstract (repeat (apply impred_isaprop; intros); apply isapropiscontr).
Defined.

Definition NNO : UU :=
  ∑ (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧), isNNO n z s.

Definition NNObject (n : NNO) : C := pr1 n.
Coercion NNObject : NNO >-> ob.

Definition zeroNNO (n : NNO) : C ⟦1,n⟧ := pr1 (pr2 n).
Definition sucNNO (n : NNO) : C ⟦n,n⟧ := pr1 (pr2 (pr2 n)).

Lemma isNNO_NNO (n : NNO) : isNNO n (zeroNNO n) (sucNNO n).
Proof.
exact (pr2 (pr2 (pr2 n))).
Qed.

Section UniversalMappingProperty.
  Context (N : NNO)
          {x : C}
          (z : 1 --> x)
          (s : x --> x).

  Definition NNO_mor
    : N --> x
    := pr11 (isNNO_NNO N x z s).

  Proposition NNO_mor_Z
    : zeroNNO N · NNO_mor = z.
  Proof.
    exact (pr121 (isNNO_NNO N x z s)).
  Qed.

  Proposition NNO_mor_S
    : sucNNO N · NNO_mor = NNO_mor · s.
  Proof.
    exact (pr221 (isNNO_NNO N x z s)).
  Qed.

  Proposition NNO_mor_unique
              {f g : N --> x}
              (fz : zeroNNO N · f = z)
              (gz : zeroNNO N · g = z)
              (fs : sucNNO N · f = f · s)
              (gs : sucNNO N · g = g · s)
    : f = g.
  Proof.
    exact (base_paths
             _ _
             (proofirrelevance
                _
                (isapropifcontr (isNNO_NNO N x z s))
                (f ,, fz ,, fs)
                (g ,, gz ,, gs))).
  Qed.

  Corollary NNO_mor_unique'
    {f : N --> x}
    (fz : zeroNNO N · f = z)
    (fs : sucNNO N · f = f · s)
    : f = NNO_mor.
  Proof.
    use NNO_mor_unique.
    - exact fz.
    - exact NNO_mor_Z.
    - exact fs.
    - exact NNO_mor_S.
  Qed.

End UniversalMappingProperty.

Definition make_NNO (n : C) (z : C ⟦ 1, n ⟧) (s : C ⟦ n, n ⟧)
 (h : isNNO n z s) : NNO := (n,,z,,s,,h).

Definition hasNNO : hProp := ∥ NNO ∥.

End nno.

Section UniqueUpToIso.
  Context {C : category}
          {TC : Terminal C}.

  Definition mor_between_NNO
             (N₁ N₂ : NNO TC)
    : N₁ --> N₂.
  Proof.
    use NNO_mor.
    - exact (zeroNNO TC N₂).
    - exact (sucNNO TC N₂).
  Defined.

  Proposition mor_between_NNO_inv
              (N₁ N₂ : NNO TC)
    : mor_between_NNO N₁ N₂ · mor_between_NNO N₂ N₁
      =
      identity _.
  Proof.
    unfold mor_between_NNO.
    use NNO_mor_unique.
    - exact (zeroNNO TC N₁).
    - exact (sucNNO TC N₁).
    - rewrite !assoc.
      rewrite !NNO_mor_Z.
      apply idpath.
    - apply id_right.
    - rewrite !assoc.
      rewrite NNO_mor_S.
      rewrite !assoc'.
      rewrite NNO_mor_S.
      apply idpath.
    - rewrite id_left, id_right.
      apply idpath.
  Qed.

  Definition iso_between_NNO
             (N₁ N₂ : NNO TC)
    : z_iso N₁ N₂.
  Proof.
    use make_z_iso.
    - apply mor_between_NNO.
    - apply mor_between_NNO.
    - abstract
        (split ; apply mor_between_NNO_inv).
  Defined.
End UniqueUpToIso.

Section UniqueUpToIsoModChosenTerminal.

  Lemma terminal_arrow_from_itself {C : category} (T : Terminal C)
    : TerminalArrow T T = identity T.
  Proof.
    apply pathsinv0, TerminalArrowUnique.
  Qed.

  Lemma is_between_NNO_mod_chosen_terminal_is_inverse
    {C : category} {T T' : Terminal C}
    (N : NNO T) (N' : NNO T')
    : NNO_mor T N (z_iso_Terminals T T' · zeroNNO T' N') (sucNNO T' N')
        · NNO_mor T' N' (z_iso_Terminals T' T · zeroNNO T N) (sucNNO T N) = identity N.
  Proof.
    use NNO_mor_unique.
    - apply N.
    - apply N.
    - cbn.
      rewrite assoc.
      rewrite NNO_mor_Z.
      rewrite assoc'.
      rewrite NNO_mor_Z.
      rewrite assoc.
      etrans. {
        apply maponpaths_2, TerminalArrowUnique.
      }
      etrans. {
        apply maponpaths_2, terminal_arrow_from_itself.
      }
      apply id_left.
    - apply id_right.
    - cbn.
      rewrite assoc.
      rewrite NNO_mor_S.
      rewrite assoc'.
      rewrite NNO_mor_S.
      now rewrite assoc.
    - exact (id_right _ @ ! id_left _).
  Qed.

  Lemma iso_between_NNO_mod_chosen_terminal
    {C : category} {T T' : Terminal C}
    (N : NNO T) (N' : NNO T')
    : z_iso N N'.
  Proof.
    set (iT := z_iso_Terminals T T').

    use make_z_iso.
    - use NNO_mor.
      + exact (iT · zeroNNO _ N').
      + exact (sucNNO _ N').
    - use NNO_mor.
      + exact (z_iso_inv iT · zeroNNO _ N).
      + exact (sucNNO _ N).
    - split ; apply is_between_NNO_mod_chosen_terminal_is_inverse.
  Defined.

End UniqueUpToIsoModChosenTerminal.

Section HomomorphismOfNNOs.

  (* Image of NNO is again an NNO *)
  Definition creates_NNO
    {C D : category} {F : functor C D}
    {T_C : Terminal C}
    (F_pT : preserves_chosen_terminal T_C F)
    (N : NNO T_C) : UU
    := isNNO (make_Terminal _ F_pT) (F N) (#F (zeroNNO _ N)) (#F (sucNNO _ N)).

  Definition NNO_from_functor_creation
    {C D : category} {F : functor C D}
    {T_C : Terminal C}
    {F_pT : preserves_chosen_terminal T_C F}
    {N : NNO T_C}
    (F_cN : creates_NNO F_pT N)
    : NNO (make_Terminal _ F_pT)
    := make_NNO _ _ _ _ F_cN.

  (* The unique morphism out of an NNO in the codomain, to the image of the NNO in the domain is an iso *)
  Definition preserves_NNO
    {C D : category} {F : functor C D}
    (T_C : Terminal C) (T_D : Terminal D)
    (F_pT : preserves_chosen_terminal T_C F)
    (N_C : NNO T_C) (N_D : NNO T_D): UU
    := is_z_isomorphism
         (NNO_mor T_D N_D (iscontrpr1 (F_pT T_D) · #F (zeroNNO _ N_C)) (#F (sucNNO _ N_C))).

End HomomorphismOfNNOs.
