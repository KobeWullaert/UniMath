(**

  Sets With One and Two Binary Operations

  Contents
  1. Unary operations
  2. Binary operations
  2.1. General definitions
  2.2. Standard conditions on one binary operation on a set
  2.3. Elements with inverses
  2.4. Group operations
  2.5. Standard conditions on a pair of binary operations on a set
  3. Sets with one binary operation
  3.1. General definitions
  3.2. Functions compatible with a binary operation (homomorphism) and their properties
  3.3. Transport of properties of a binary operation
  3.4. Subobject
  3.5. Relations compatible with a binary operation and quotient objects
  3.6. Relations inversely compatible with a binary operation
  3.7. Homomorphisms and relations
  3.8. Quotient relations
  3.9. Direct products
  4. Sets with two binary operations
  4.1. General definitions
  4.2. Functions compatible with a pair of binary operation (homomorphisms) and their properties
  4.3. Transport of properties of a pair of binary operations
  4.4. Subobjects
  4.5. Quotient objects
  4.6. Direct products
  5. Infinitary operations

  Originally written by Vladimir Voevodsky, Aug. 2011.

 *)
Require Export UniMath.Foundations.Sets.
Require Export UniMath.MoreFoundations.Propositions.

(** * 1. Unary operations *)

Definition unop (X : UU) : UU := X → X.

(** * 2. Binary operations *)

(** * 2.1. General definitions *)

Definition islcancelable {X : UU} (opp : binop X) (x : X) : UU := isincl (λ x0 : X, opp x x0).

Definition lcancel {X : UU} {opp : binop X} {x : X} (H_x : islcancelable opp x) (y z : X) :
  opp x y = opp x z → y = z.
Proof.
  apply invmaponpathsincl, H_x.
Defined.

Definition isrcancelable {X : UU} (opp : binop X) (x : X) : UU := isincl (λ x0 : X, opp x0 x).

Definition rcancel {X : UU} {opp : binop X} {x : X} (H_x : isrcancelable opp x) (y z : X) :
  opp y x = opp z x → y = z.
Proof.
  apply (invmaponpathsincl (λ y, opp y x)), H_x.
Defined.

Definition iscancelable {X : UU} (opp : binop X) (x : X) : UU :=
  (islcancelable opp x) × (isrcancelable opp x).

Definition islinvertible {X : UU} (opp : binop X) (x : X) : UU := isweq (λ x0 : X, opp x x0).

Definition isrinvertible {X : UU} (opp : binop X) (x : X) : UU := isweq (λ x0 : X, opp x0 x).

Definition isinvertible {X : UU} (opp : binop X) (x : X) : UU :=
  (islinvertible opp x) × (isrinvertible opp x).

(** **** Transfer of binary operations relative to weak equivalences *)

Definition binop_weq_fwd {X Y : UU} (H : X ≃ Y) :
  binop X → binop Y :=
  λ (opp : binop X) (x y : Y), H (opp (invmap H x) (invmap H y)).

Definition binop_weq_bck {X Y : UU} (H : X ≃ Y) :
  binop Y → binop X :=
  λ (opp : binop Y) (x y : X), invmap H (opp (H x) (H y)).

(** * 2.2. Standard conditions on one binary operation on a set *)

Definition isassoc {X : UU} (opp : binop X) : UU :=
  ∏ x x' x'', opp (opp x x') x'' = opp x (opp x' x'').

Lemma isapropisassoc {X : hSet} (opp : binop X) : isaprop (isassoc opp).
Proof.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

(** Compare to [CategoryTheory.Categories.assoc4] *)
Lemma assoc4 {X : UU} (opp : binop X) (isa : isassoc opp) :
  ∏ w x y z : X, opp (opp (opp w x) y) z = opp (opp w (opp x y)) z.
Proof.
  intros.
  repeat rewrite isa; exact (idpath _).
Qed.

(** cancellativity *)

Definition isrcancellative {X : UU} (opp : binop X) : UU :=
  ∏ x:X, isrcancelable opp x.

Definition islcancellative {X : UU} (opp : binop X) : UU :=
  ∏ x:X, islcancelable opp x.

(** *)

Definition islunit {X : UU} (opp : binop X) (un0 : X) : UU := ∏ x : X, opp un0 x = x.

Lemma isapropislunit {X : hSet} (opp : binop X) (un0 : X) : isaprop (islunit opp un0).
Proof.
  apply impred. intro x.
  simpl. apply (setproperty X).
Defined.

Definition isrunit {X : UU} (opp : binop X) (un0 : X) : UU := ∏ x : X, opp x un0 = x.

Lemma isapropisrunit {X : hSet} (opp : binop X) (un0 : X) : isaprop (isrunit opp un0).
Proof.
  apply impred. intro x.
  simpl. apply (setproperty X).
Defined.

Definition isunit {X : UU} (opp : binop X) (un0 : X) : UU :=
  (islunit opp un0) × (isrunit opp un0).

Definition make_isunit {X : UU} {opp : binop X} {un0 : X} (H1 : islunit opp un0)
           (H2 : isrunit opp un0) : isunit opp un0 := H1 ,, H2.

Definition isunital {X : UU} (opp : binop X) : UU := ∑ (un0 : X), isunit opp un0.

Definition make_isunital {X : UU} {opp : binop X} (un0 : X) (is : isunit opp un0) :
  isunital opp := un0 ,, is.

Lemma isapropisunital {X : hSet} (opp : binop X) : isaprop (isunital opp).
Proof.
  apply (@isapropsubtype X (λ un0, hconj (make_hProp _ (isapropislunit opp un0))
                                              (make_hProp _ (isapropisrunit opp un0)))).
  intros u1 u2. intros ua1 ua2.
  apply (!(pr2 ua2 u1) @ (pr1 ua1 u2)).
Defined.

(** *)

Definition ismonoidop {X : UU} (opp : binop X) : UU := (isassoc opp) × (isunital opp).

Definition make_ismonoidop {X : UU} {opp : binop X} (H1 : isassoc opp) (H2 : isunital opp) :
  ismonoidop opp := H1 ,, H2.

Definition assocax_is {X : UU} {opp : binop X} : ismonoidop opp → isassoc opp := @pr1 _ _.

Definition unel_is {X : UU} {opp : binop X} (is : ismonoidop opp) : X := pr1 (pr2 is).

Definition lunax_is {X : UU} {opp : binop X} (is : ismonoidop opp) :
  islunit opp (pr1 (pr2 is)) := pr1 (pr2 (pr2 is)).

Definition runax_is {X : UU} {opp : binop X} (is : ismonoidop opp) :
  isrunit opp (pr1 (pr2 is)) := pr2 (pr2 (pr2 is)).

Definition unax_is {X : UU} {opp : binop X} (is : ismonoidop opp) :
  isunit opp (pr1 (pr2 is)) := lunax_is is ,, runax_is is.

Lemma isapropismonoidop {X : hSet} (opp : binop X) : isaprop (ismonoidop opp).
Proof.
  apply (isofhleveldirprod 1).
  apply isapropisassoc.
  apply isapropisunital.
Defined.

(** * 2.3. Elements with inverses *)

Section ElementsWithInverses.
  Context {X : UU} (opp : binop X) (is : ismonoidop opp).
  Local Notation "x * y" := (opp x y).
  Local Notation u := (unel_is is).

  (** Is this element x0 the left/right inverse of x? *)

  Definition islinvel (x : X) : X → UU := λ x0, x0 * x = u.
  Definition isrinvel (x : X) : X → UU := λ x0, x * x0 = u.
  Definition isinvel (x : X) : X → UU := λ x0, (islinvel x x0) × (isrinvel x x0).

  (** Is there some element x0 that is the left/right inverse of x? *)

  Definition haslinv (x : X) : UU := ∑ x0 : X, islinvel x x0.
  Definition hasrinv (x : X) : UU := ∑ x0 : X, isrinvel x x0.
  Definition hasinv (x : X) : UU := ∑ x0 : X, isinvel x x0.

  (** Accessor functions *)
  Definition haslinv_to_linvel {x : X} : haslinv x → X := pr1.
  Definition hasrinv_to_rinvel {x : X} : hasrinv x → X := pr1.
  Definition hasinv_to_invel {x : X} : hasinv x → X := pr1.

  Definition merely_haslinv (x : X) : hProp := ∥ haslinv x ∥.
  Definition merely_hasrinv (x : X) : hProp := ∥ hasrinv x ∥.
  Definition merely_hasinv (x : X) : hProp := ∥ hasinv x ∥.

  (** Lemmas for elements with inverses *)

  (** The inverse of an element's two-sided inverse is just that element *)
  Definition is_inv_inv : ∏ (x x0 : X), (isinvel x x0 → isinvel x0 x) :=
    λ x x0 isinv, pr2 isinv ,, pr1 isinv.

  (** If two elements have left inverses, so does their product. *)
  Lemma invop_l :
    ∏ (x y x' y' : X),
      (islinvel x x' → islinvel y y' → islinvel (x * y) (y' * x')).
  Proof.
    intros x y x' y' xinv yinv.
    unfold islinvel.
    pose (assoc := pr1 is).
    cbn; unfold islinvel.
    rewrite <- assoc.
    rewrite (assoc4 opp assoc), xinv.
    rewrite (runax_is is).
    exact yinv.
  Qed.

  (** If two elements have right inverses, so does their product. *)
  Lemma invop_r :
    ∏ (x y x' y' : X),
      (isrinvel x x' → isrinvel y y' → isrinvel (x * y) (y' * x')).
  Proof.
    intros x y x' y' xinv yinv.
    pose (assoc := pr1 is).
    cbn; unfold isrinvel.
    rewrite <- assoc.
    rewrite (assoc4 opp assoc), yinv.
    rewrite (runax_is is).
    exact xinv.
  Qed.

  (** This is a similar statement to [grinvop] *)
  Lemma invop :
    ∏ (x y x' y' : X),
      (isinvel x x' → isinvel y y' → isinvel (x * y) (y' * x')).
  Proof.
    intros x y x' y' xinv yinv.
    use make_dirprod.
    - apply invop_l.
      + exact (dirprod_pr1 xinv).
      + exact (dirprod_pr1 yinv).
    - apply invop_r.
      + exact (dirprod_pr2 xinv).
      + exact (dirprod_pr2 yinv).
  Defined.

  Lemma mere_invop :
    ∏ (x y : X), (merely_hasinv x → merely_hasinv y → merely_hasinv (x * y)).
  Proof.
    intros x y.
    apply hinhfun2.
    intros xinv yinv.
    exists ((hasinv_to_invel yinv) * (hasinv_to_invel xinv)).
    apply invop.
    - exact (pr2 xinv).
    - exact (pr2 yinv).
  Defined.

  (** If an element has both left and right inverses, they're equal. *)
  Lemma linv_eq_rinv (x lx rx : X) (lxlinv : islinvel x lx) (rxrinv : isrinvel x rx) :
    lx = rx.
  Proof.
    intros.
    refine (!runax_is is _ @ _).
    refine (!maponpaths (λ z, lx * z) rxrinv @ _).
    refine (!assocax_is is _ _ _ @ _).
    refine (maponpaths (λ z, z * rx) lxlinv @ _).
    apply lunax_is.
  Defined.

End ElementsWithInverses.

Section InverseOperations.
  Context {X : UU} (opp : binop X) (u : X) (inv : X → X).
  Local Notation "x * y" := (opp x y).

  Definition islinv : UU := ∏ x : X, (inv x) * x = u.
  Definition isrinv : UU := ∏ x : X, x * (inv x) = u.
  Definition isinv : UU := islinv × isrinv.
End InverseOperations.

Section ElementsWithInversesSet.
  (** When working with an hSet instead of a general type, many of the above
      statements become propositions *)

  Context {X : hSet} (opp : binop X) (is : ismonoidop opp).
  Local Notation "x * y" := (opp x y).

  Definition isapropislinvel (x x0 : X) : isaprop (islinvel opp is x x0) := setproperty X _ _.
  Definition isapropisrinvel (x x0 : X) : isaprop (isrinvel opp is x x0) := setproperty X _ _.
  Definition isapropisinvel (x x0 : X) : isaprop (isinvel opp is x x0) := isapropdirprod _ _ (isapropislinvel _ _) (isapropisrinvel _ _).

  (** If the operation is left cancellable, right inverses are unique. *)
  Definition isaprop_haslinv (x : X) (can : islcancelable opp x) :
    isaprop (hasrinv opp is x).
  Proof.
    apply isaproptotal2.
    - intro; apply isapropislinvel.
    - intros x' x'' islinvx' islinvx''.
      apply (Injectivity (λ x0 : X, x * x0)).
      + apply incl_injectivity; assumption.
      + exact (islinvx' @ !islinvx'').
  Defined.

  (** If the operation is right cancellable, left inverses are unique. *)
  Definition isaprop_hasrinv (x : X) (can : isrcancelable opp x) :
    isaprop (haslinv opp is x).
  Proof.
    apply isaproptotal2.
    - intro; apply isapropisrinvel.
    - intros x' x'' isrinvx' isrinvx''.
      apply (Injectivity (λ x0 : X, x0 * x)).
      + apply incl_injectivity; assumption.
      + exact (isrinvx' @ !isrinvx'').
  Defined.

  (** For the two-sided case, we can just reuse the argument from the
      left-cancellable case. *)
  Definition isaprop_hasinv (x : X) (can : iscancelable opp x) :
    isaprop (hasinv opp is x).
  Proof.
    apply isaproptotal2.
    - intro; apply isapropdirprod.
      + apply isapropislinvel.
      + apply isapropisrinvel.
    - intros x' x'' isinvx' isinvx''.
      apply (Injectivity (λ x0 : X, x * x0)).
      + apply incl_injectivity; apply (pr1 can).
      + exact (pr2 isinvx' @ !pr2 isinvx'').
  Defined.

  (** The subset of elements that have inverses *)

  Definition merely_invertible_elements : hsubtype X := merely_hasinv opp is.

  Definition invertible_elements (can : ∏ x, iscancelable opp x) : hsubtype X.
  Proof.
    intro x.
    use make_hProp.
    - exact (hasinv opp is x).
    - apply isaprop_hasinv, can.
  Defined.

  (** If an element has an inverse, then it is cancellable *)

  Definition lcanfromlinv (a b c : X) (c' : haslinv opp is c) :
    c * a = c * b → a = b.
  Proof.
    intros e.
    refine (!lunax_is is a @ _ @ lunax_is is b).
    refine (!maponpaths (λ z, z * _) (pr2 c') @ _ @
             maponpaths (λ z, z * _) (pr2 c')).
    refine (assocax_is is _ _ _ @ _ @ !assocax_is is _ _ _).
    apply maponpaths.
    assumption.
  Defined.

  Definition rcanfromrinv (a b c : X) (c' : hasrinv opp is c) :
    a * c = b * c → a = b.
  Proof.
    intros e.
    refine (!runax_is is a @ _ @ runax_is is b).
    refine (!maponpaths (λ z, _ * z) (pr2 c') @ _ @
             maponpaths (λ z, _ * z) (pr2 c')).
    refine (!assocax_is is _ _ _ @ _ @ assocax_is is _ _ _).
    apply (maponpaths (λ z, z * _)).
    assumption.
  Defined.
End ElementsWithInversesSet.

Section InversesSet.
  (** Similarly, these are propositions for hSets *)
  Context {X : hSet} (opp : binop X) (u : X) (inv : X → X).

  Lemma isapropislinv : isaprop (islinv opp u inv).
  Proof.
    intros; apply impred; intro; apply setproperty.
  Defined.

  Lemma isapropisrinv : isaprop (isrinv opp u inv).
  Proof.
    intros; apply impred; intro; apply setproperty.
  Defined.

  Lemma isapropisinv : isaprop (isinv opp u inv).
  Proof.
    exact (isofhleveldirprod 1 _ _ isapropislinv isapropisrinv).
  Defined.
End InversesSet.

Definition make_isinv {X : UU} {opp : binop X} {un0 : X} {inv0 : X → X} (H1 : islinv opp un0 inv0)
          (H2 : isrinv opp un0 inv0) : isinv opp un0 inv0 := H1 ,, H2.

Definition invstruct {X : UU} (opp : binop X) (is : ismonoidop opp) : UU :=
  ∑ (inv0 : X → X), isinv opp (unel_is is) inv0.

Definition make_invstruct {X : UU} {opp : binop X} {is : ismonoidop opp} (inv0 : X → X)
           (H : isinv opp (unel_is is) inv0) : invstruct opp is := inv0 ,, H.

(** * 2.4. Group operations *)

Definition isgrop {X : UU} (opp : binop X) : UU :=
  ∑ (is : ismonoidop opp), invstruct opp is.

Definition make_isgrop {X : UU} {opp : binop X} (is1 : ismonoidop opp) (is2 : invstruct opp is1) :
  isgrop opp := is1 ,, is2.

Definition pr1isgrop (X : UU) (opp : binop X) : isgrop opp → ismonoidop opp := @pr1 _ _.
Coercion pr1isgrop : isgrop >-> ismonoidop.

Definition grinv_is {X : UU} {opp : binop X} (is : isgrop opp) : X → X := pr1 (pr2 is).

Definition grlinvax_is {X : UU} {opp : binop X} (is : isgrop opp) :
  islinv opp (unel_is is) (pr1 (pr2 is)) := pr1 (pr2 (pr2 is)).

Definition grrinvax_is {X : UU} {opp : binop X} (is : isgrop opp) :
  isrinv opp (unel_is is) (pr1 (pr2 is)) := pr2 (pr2 (pr2 is)).

Lemma isweqrmultingr_is {X : UU} {opp : binop X} (is : isgrop opp) (x0 : X) :
  isrinvertible opp x0.
Proof.
  induction is as [ is istr ].
  set (f := λ x : X, opp x x0).
  set (g := λ x : X, opp x ((pr1 istr) x0)).
  induction is as [ assoc isun0 ].
  induction istr as [ inv0 axs ].
  induction isun0 as [ un0 unaxs ].
  simpl in * |-.
  assert (egf : ∏ x, g (f x) = x).
  {
    intro x. unfold f. unfold g.
    induction (!assoc x x0 (inv0 x0)).
    set (e := pr2 axs x0). simpl in e. rewrite e.
    apply (pr2 unaxs x).
  }
  assert (efg : ∏ x, f (g x) = x).
  {
    intro x. unfold f. unfold g.
    induction (!assoc x (inv0 x0) x0).
    set (e := pr1 axs x0). simpl in e. rewrite e.
    apply (pr2 unaxs x).
  }
  apply (isweq_iso _ _ egf efg).
Defined.

Lemma isweqlmultingr_is {X : UU} {opp : binop X} (is : isgrop opp) (x0 : X) :
  islinvertible opp x0.
Proof.
  induction is as [ is istr ].
  set (f := λ x : X, opp x0 x).
  set (g := λ x : X, opp ((pr1 istr) x0) x).
  induction is as [ assoc isun0 ].
  induction istr as [ inv0 axs ].
  induction isun0 as [ un0 unaxs ].
  simpl in * |-.
  assert (egf : ∏ x, g (f x) = x).
  {
    intro x. unfold f. unfold g.
    induction (assoc (inv0 x0) x0 x).
    set (e := pr1 axs x0). simpl in e. rewrite e.
    apply (pr1 unaxs x).
  }
  assert (efg : ∏ x, f (g x) = x).
  {
    intro x. unfold f. unfold g.
    induction (assoc x0 (inv0 x0) x).
    set (e := pr2 axs x0). simpl in e. rewrite e.
    apply (pr1 unaxs x).
  }
  apply (isweq_iso _ _ egf efg).
Defined.

Lemma isapropinvstruct {X : hSet} {opp : binop X} (is : ismonoidop opp) :
  isaprop (invstruct opp is).
Proof.
  apply isofhlevelsn. intro is0.
  set (un0 := pr1 (pr2 is)).
  assert (int : ∏ (i : X → X),
                isaprop ((∏ x : X, opp (i x) x = un0) ×
                         (∏ x : X, opp x (i x) = un0))).
  {
    intro i. apply (isofhleveldirprod 1).
    - apply impred. intro x. simpl. apply (setproperty X).
    - apply impred. intro x. simpl. apply (setproperty X).
  }
  apply (isapropsubtype (λ i, make_hProp _ (int i))).
  intros inv1 inv2. simpl. intro ax1. intro ax2. apply funextfun. intro x0.
  apply (invmaponpathsweq (make_weq _ (isweqrmultingr_is (is ,, is0) x0))).
  simpl. rewrite (pr1 ax1 x0). rewrite (pr1 ax2 x0). apply idpath.
Defined.

Lemma isapropisgrop {X : hSet} (opp : binop X) : isaprop (isgrop opp).
Proof.
  apply (isofhleveltotal2 1).
  - apply isapropismonoidop.
  - apply isapropinvstruct.
Defined.

(* (** Unitary monoid where all elements are invertible is a group *)

Definition allinvvertibleinv {X : hSet} {opp : binop X} (is : ismonoidop opp)
  (allinv : ∏ x : X, islinvertible opp x) : X → X
  := λ x : X, invmap (make_weq _ (allinv x)) (unel_is is).

*)

(** The following lemma is an analog of [Bourbaki, Alg. 1, ex. 2, p. 132] *)

Lemma isgropif {X : hSet} {opp : binop X} (is0 : ismonoidop opp)
      (is : ∏ x : X, merely_hasrinv opp is0 x) : isgrop opp.
Proof.
  exists is0.
  induction is0 as [ assoc isun0 ].
  induction isun0 as [ un0 unaxs0 ].
  simpl in is.
  simpl in unaxs0. simpl in un0.
  simpl in assoc. simpl in unaxs0.
  assert (l1 : ∏ x' : X, isincl (λ x0 : X, opp x0 x')).
  {
    intro x'.
    apply (@hinhuniv (∑ (x0 : X), opp x' x0 = un0)
                     (make_hProp _ (isapropisincl (λ x0 : X, opp x0 x')))).
    - intro int1. simpl. apply isinclbetweensets.
      + apply (pr2 X).
      + apply (pr2 X).
      + intros a b. intro e.
        rewrite <- (pr2 unaxs0 a). rewrite <- (pr2 unaxs0 b).
        induction int1 as [ invx' eq ].
        rewrite <- eq.
        induction (assoc a x' invx').
        induction (assoc b x' invx').
        rewrite e. apply idpath.
    -  apply (is x').
  }
  assert (is' : ∏ x : X, ∃ (x0 : X), opp x0 x = un0).
  {
    intro x. apply (λ f , hinhuniv f (is x)). intro s1.
    induction s1 as [ x' eq ]. apply hinhpr. exists x'. simpl.
    apply (invmaponpathsincl _ (l1 x')).
    rewrite (assoc x' x x'). rewrite eq. rewrite (pr1 unaxs0 x').
    unfold unel_is. simpl. rewrite (pr2 unaxs0 x'). apply idpath.
  }
  assert (l1' : ∏ x' : X, isincl (λ x0 : X, opp x' x0)).
  {
    intro x'.
    apply (@hinhuniv (∑ (x0 : X), opp x0 x' = un0)
                     (make_hProp _ (isapropisincl (λ x0 : X, opp x' x0)))).
    - intro int1. simpl. apply isinclbetweensets.
      + apply (pr2 X).
      + apply (pr2 X).
      + intros a b. intro e.
        rewrite <- (pr1 unaxs0 a). rewrite <- (pr1 unaxs0 b).
        induction int1 as [ invx' eq ]. rewrite <- eq.
        induction (!assoc invx' x' a).
        induction (!assoc invx' x' b).
        rewrite e. apply idpath.
    - apply (is' x').
  }
  assert (int : ∏ x : X, isaprop (∑ (x0 : X), opp x0 x = un0)%logic).
  {
    intro x. apply isapropsubtype. intros x1 x2. intros eq1 eq2.
    apply (invmaponpathsincl _ (l1 x)).
    rewrite eq1. rewrite eq2. apply idpath.
  }
  simpl.
  set (linv0 := λ x : X, hinhunivcor1 (make_hProp _ (int x)) (is' x)).
  simpl in linv0.
  set (inv0 := λ x : X, pr1 (linv0 x)). exists inv0. simpl.
  exists (λ x, pr2 (linv0 x)). intro x.
  apply (invmaponpathsincl _ (l1 x)).
  rewrite (assoc x (inv0 x) x). change (inv0 x) with (pr1 (linv0 x)).
  rewrite (pr2 (linv0 x)). unfold unel_is. simpl.
  rewrite (pr1 unaxs0 x). rewrite (pr2 unaxs0 x). apply idpath.
Defined.

(** *)

Definition iscomm {X : UU} (opp : binop X) : UU := ∏ x x' : X, opp x x' = opp x' x.

Lemma isapropiscomm {X : hSet} (opp : binop X) : isaprop (iscomm opp).
Proof.
  apply impred. intros x.
  apply impred. intro x'.
  simpl.
  apply (setproperty X).
Defined.

Definition isabmonoidop {X : UU} (opp : binop X) : UU := (ismonoidop opp) × (iscomm opp).

Definition make_isabmonoidop {X : UU} {opp : binop X} (H1 : ismonoidop opp) (H2 : iscomm opp) :
  isabmonoidop opp := H1 ,, H2.

Definition pr1isabmonoidop (X : UU) (opp : binop X) : isabmonoidop opp → ismonoidop opp :=
  @pr1 _ _.
Coercion pr1isabmonoidop : isabmonoidop >-> ismonoidop.

Definition commax_is {X : UU} {opp : binop X} (is : isabmonoidop opp) : iscomm opp := pr2 is.

Lemma isapropisabmonoidop {X : hSet} (opp : binop X) :
  isaprop (isabmonoidop opp).
Proof.
  apply (isofhleveldirprod 1).
  apply isapropismonoidop.
  apply isapropiscomm.
Defined.

Lemma abmonoidoprer {X : UU} {opp : binop X} (is : isabmonoidop opp) (a b c d : X) :
 opp (opp a b) (opp c d) = opp (opp a c) (opp b d).
Proof.
  induction is as [ is comm ]. induction is as [ assoc unital0 ].
  simpl in *.
  induction (assoc (opp a b) c d). induction (assoc (opp a c) b d).
  induction (!assoc a b c). induction (!assoc a c b).
  induction (comm b c). apply idpath.
Defined.

(** *)

Lemma weqlcancelablercancelable {X : UU} (opp : binop X) (is : iscomm opp) (x : X) :
  (islcancelable opp x) ≃ (isrcancelable opp x).
Proof.
  assert (f : (islcancelable opp x) → (isrcancelable opp x)).
  {
    unfold islcancelable. unfold isrcancelable.
    intro isl. apply (λ h, isinclhomot _ _ h isl).
    intro x0. apply is.
  }
  assert (g : (isrcancelable opp x) → (islcancelable opp x)).
  {
    unfold islcancelable. unfold isrcancelable. intro isr.
    apply (λ h, isinclhomot _ _ h isr). intro x0. apply is.
  }
  exists f.
  apply (isweqimplimpl f g (isapropisincl (λ x0 : X, opp x x0))
                       (isapropisincl (λ x0 : X, opp x0 x))).
Defined.

Lemma weqlinvertiblerinvertible {X : UU} (opp : binop X) (is : iscomm opp) (x : X) :
  (islinvertible opp x) ≃ (isrinvertible opp x).
Proof.
  assert (f : (islinvertible opp x) → (isrinvertible opp x)).
  {
    unfold islinvertible. unfold isrinvertible. intro isl.
    apply (isweqhomot (λ y, opp x y)).
    - intro z. apply is.
    - apply isl.
  }
  assert (g : (isrinvertible opp x) → (islinvertible opp x)).
  {
    unfold islinvertible. unfold isrinvertible. intro isr.
    apply (λ h, isweqhomot _ _ h isr).
    intro x0. apply is.
  }
  exists f.
  apply (isweqimplimpl f g (isapropisweq (λ x0 : X, opp x x0))
                       (isapropisweq (λ x0 : X, opp x0 x))).
Defined.

(* Lemma below currently requires X:hSet but should have a proof for X:UU *)

Lemma weqlunitrunit {X : hSet} (opp : binop X) (is : iscomm opp) (un0 : X) :
  (islunit opp un0) ≃ (isrunit opp un0).
Proof.
  assert (f : (islunit opp un0) → (isrunit opp un0)).
  {
    unfold islunit. unfold isrunit. intro isl. intro x.
    induction (is un0 x). apply (isl x).
  }
  assert (g : (isrunit opp un0) → (islunit opp un0)).
  {
    unfold islunit. unfold isrunit. intro isr. intro x.
    induction (is x un0). apply (isr x).
  }
  exists f.
  apply (isweqimplimpl f g (isapropislunit opp un0) (isapropisrunit opp un0)).
Defined.

(* Same for the following lemma *)

Lemma weqlinvrinv {X : hSet} (opp : binop X) (is : iscomm opp) (un0 : X) (inv0 : X → X) :
  (islinv opp un0 inv0) ≃ (isrinv opp un0 inv0).
Proof.
  assert (f : (islinv opp un0 inv0) → (isrinv opp un0 inv0)).
  {
    unfold islinv. unfold isrinv. intro isl. intro x.
    induction (is (inv0 x) x). apply (isl x).
  }
  assert (g : (isrinv opp un0 inv0) → (islinv opp un0 inv0)).
  {
    unfold islinv. unfold isrinv. intro isr. intro x.
    induction (is x (inv0 x)). apply (isr x).
  }
  exists f.
  apply (isweqimplimpl f g (isapropislinv opp un0 inv0) (isapropisrinv opp un0 inv0)).
Qed.

(** *)

Definition isabgrop {X : UU} (opp : binop X) : UU := (isgrop opp) × (iscomm opp).

Definition make_isabgrop {X : UU} {opp : binop X} (H1 : isgrop opp) (H2 : iscomm opp) :
  isabgrop opp := H1 ,, H2.

Definition pr1isabgrop (X : UU) (opp : binop X) : isabgrop opp → isgrop opp := @pr1 _ _.
Coercion pr1isabgrop : isabgrop >-> isgrop.

Definition isabgroptoisabmonoidop (X : UU) (opp : binop X) : isabgrop opp → isabmonoidop opp :=
  λ is, pr1 (pr1 is) ,, pr2 is.
Coercion isabgroptoisabmonoidop : isabgrop >-> isabmonoidop.

Lemma isapropisabgrop {X : hSet} (opp : binop X) : isaprop (isabgrop opp).
Proof.
  apply (isofhleveldirprod 1).
  apply isapropisgrop.
  apply isapropiscomm.
Defined.

(** * 2.5. Standard conditions on a pair of binary operations on a set *)

Definition isldistr {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x x' x'' : X, opp2 x'' (opp1 x x') = opp1 (opp2 x'' x) (opp2 x'' x').

Lemma isapropisldistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isldistr opp1 opp2).
Proof.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

Definition isrdistr {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x x' x'' : X, opp2 (opp1 x x') x'' = opp1 (opp2 x x'') (opp2 x' x'').

Lemma isapropisrdistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isrdistr opp1 opp2).
Proof.
  apply impred. intro x.
  apply impred. intro x'.
  apply impred. intro x''.
  simpl. apply (setproperty X).
Defined.

Definition isdistr {X : UU} (opp1 opp2 : binop X) : UU :=
  (isldistr opp1 opp2) × (isrdistr opp1 opp2).

Lemma isapropisdistr {X : hSet} (opp1 opp2 : binop X) : isaprop (isdistr opp1 opp2).
Proof.
  apply (isofhleveldirprod 1 _ _ (isapropisldistr _ _) (isapropisrdistr _ _)).
Defined.

(** *)

Lemma weqldistrrdistr {X : hSet} (opp1 opp2 : binop X) (is : iscomm opp2) :
  (isldistr opp1 opp2) ≃ (isrdistr opp1 opp2).
Proof.
  assert (f : (isldistr opp1 opp2) → (isrdistr opp1 opp2)).
  {
    unfold isldistr. unfold isrdistr. intro isl. intros x x' x''.
    induction (is x'' (opp1 x x')). induction (is x'' x). induction (is x'' x').
    apply (isl x x' x'').
  }
  assert (g : (isrdistr opp1 opp2) → (isldistr opp1 opp2)).
  {
    unfold isldistr. unfold isrdistr. intro isr. intros x x' x''.
    induction (is (opp1 x x') x''). induction (is x x''). induction (is x' x'').
    apply (isr x x' x'').
  }
  exists f.
  apply (isweqimplimpl f g (isapropisldistr opp1 opp2) (isapropisrdistr opp1 opp2)).
Defined.

(** *)

Definition isabsorb {X : UU} (opp1 opp2 : binop X) : UU :=
  ∏ x y : X, opp1 x (opp2 x y) = x.

Lemma isapropisabsorb {X : hSet} (opp1 opp2 : binop X) :
  isaprop (isabsorb opp1 opp2).
Proof.
  apply impred_isaprop ; intros x.
  apply impred_isaprop ; intros y.
  apply (setproperty X).
Defined.

(** *)

Definition isrigops {X : UU} (opp1 opp2 : binop X) : UU :=
  (∑ axs : (isabmonoidop opp1) × (ismonoidop opp2),
           (∏ x : X, opp2 (unel_is (pr1 axs)) x = unel_is (pr1 axs))
             × (∏ x : X, opp2 x (unel_is (pr1 axs)) = unel_is (pr1 axs)))
    × (isdistr opp1 opp2).

Definition make_isrigops {X : UU} {opp1 opp2 : binop X} (H1 : isabmonoidop opp1)
           (H2 : ismonoidop opp2) (H3 : ∏ x : X, (opp2 (unel_is H1) x) = (unel_is H1))
           (H4 : ∏ x : X, (opp2 x (unel_is H1)) = (unel_is H1))
           (H5 : isdistr opp1 opp2) : isrigops opp1 opp2 :=
  ((H1 ,, H2) ,, H3 ,, H4) ,, H5.

Definition rigop1axs_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 → isabmonoidop opp1 := λ is, pr1 (pr1 (pr1 is)).

Definition rigop2axs_is {X : UU} {opp1 opp2 : binop X} : isrigops opp1 opp2 → ismonoidop opp2 :=
  λ is, pr2 (pr1 (pr1 is)).

Definition rigdistraxs_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 → isdistr opp1 opp2 := λ is,  pr2 is.

Definition rigldistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 → isldistr opp1 opp2 := λ is, pr1 (pr2 is).

Definition rigrdistrax_is {X : UU} {opp1 opp2 : binop X} :
  isrigops opp1 opp2 → isrdistr opp1 opp2 := λ is, pr2 (pr2 is).

Definition rigunel1_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) : X :=
  pr1 (pr2 (pr1 (rigop1axs_is is))).

Definition rigunel2_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) : X :=
  (pr1 (pr2 (rigop2axs_is is))).

Definition rigmult0x_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) (x : X) :
  opp2 (rigunel1_is is) x = rigunel1_is is := pr1 (pr2 (pr1 is)) x.

Definition rigmultx0_is {X : UU} {opp1 opp2 : binop X} (is : isrigops opp1 opp2) (x : X) :
  opp2 x (rigunel1_is is) = rigunel1_is is := pr2 (pr2 (pr1 is)) x.

Lemma isapropisrigops {X : hSet} (opp1 opp2 : binop X) : isaprop (isrigops opp1 opp2).
Proof.
  apply (isofhleveldirprod 1).
  - apply (isofhleveltotal2 1).
    + apply (isofhleveldirprod 1).
      * apply isapropisabmonoidop.
      * apply isapropismonoidop.
    + intro x. apply (isofhleveldirprod 1).
      * apply impred. intro x'.
        apply (setproperty X).
      * apply impred. intro x'.
        apply (setproperty X).
  - apply isapropisdistr.
Defined.

(** *)

Definition isringops {X : UU} (opp1 opp2 : binop X) : UU :=
  (isabgrop opp1 × ismonoidop opp2) × isdistr opp1 opp2.

Definition make_isringops {X : UU} {opp1 opp2 : binop X} (H1 : isabgrop opp1) (H2 : ismonoidop opp2)
           (H3 : isdistr opp1 opp2) : isringops opp1 opp2 :=
  (H1 ,, H2) ,, H3.

Definition ringop1axs_is {X : UU} {opp1 opp2 : binop X} : isringops opp1 opp2 → isabgrop opp1 :=
  λ is, pr1 (pr1 is).

Definition ringop2axs_is {X : UU} {opp1 opp2 : binop X} : isringops opp1 opp2 → ismonoidop opp2 :=
  λ is, pr2 (pr1 is).

Definition ringdistraxs_is {X : UU} {opp1 opp2 : binop X} :
  isringops opp1 opp2 → isdistr opp1 opp2 := λ is, pr2 is.

Definition ringldistrax_is {X : UU} {opp1 opp2 : binop X} :
  isringops opp1 opp2 → isldistr opp1 opp2 := λ is, pr1 (pr2 is).

Definition ringrdistrax_is {X : UU} {opp1 opp2 : binop X} :
  isringops opp1 opp2 → isrdistr opp1 opp2 := λ is, pr2 (pr2 is).

Definition ringunel1_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) : X :=
  unel_is (pr1 (pr1 is)).

Definition ringunel2_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) : X :=
  unel_is (pr2 (pr1 is)).

Lemma isapropisringops {X : hSet} (opp1 opp2 : binop X) : isaprop (isringops opp1 opp2).
Proof.
  apply (isofhleveldirprod 1).
  - apply (isofhleveldirprod 1).
    + apply isapropisabgrop.
    + apply isapropismonoidop.
  - apply isapropisdistr.
Defined.

Lemma multx0_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) (x : X) : opp2 x (unel_is (pr1 is1)) = unel_is (pr1 is1).
Proof.
  induction is12 as [ ldistr0 rdistr0 ].
  induction is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ].
  simpl in *.
  apply (invmaponpathsweq (make_weq _ (isweqrmultingr_is is1 (opp2 x un2)))).
  simpl.
  induction is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ].
  unfold unel_is. simpl in *.
  rewrite (lun1 (opp2 x un2)). induction (ldistr0 un1 un2 x).
  rewrite (run2 x). rewrite (lun1 un2). rewrite (run2 x). apply idpath.
Defined.
Opaque multx0_is_l.

Lemma mult0x_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) (x : X) : opp2 (unel_is (pr1 is1)) x = unel_is (pr1 is1).
Proof.
  induction is12 as [ ldistr0 rdistr0 ].
  induction is2 as [ assoc2 [ un2 [ lun2 run2 ] ] ]. simpl in *.
  apply (invmaponpathsweq (make_weq _ (isweqrmultingr_is is1 (opp2 un2 x)))).
  simpl.
  induction is1 as [ [ assoc1 [ un1 [ lun1 run1 ] ] ] [ inv0 [ linv0 rinv0 ] ] ].
  unfold unel_is. simpl in *.
  rewrite (lun1 (opp2 un2 x)). induction (rdistr0 un1 un2 x).
  rewrite (lun2 x). rewrite (lun1 un2). rewrite (lun2 x). apply idpath.
Defined.
Opaque mult0x_is_l.

Definition minus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
           (is2 : ismonoidop opp2) := (grinv_is is1) (unel_is is2).

Lemma islinvmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X}
      (is1 : isgrop opp1) (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2)
      (x : X) : opp1 (opp2 (minus1_is_l is1 is2) x) x = unel_is (pr1 is1).
Proof.
  set (xinv := opp2 (minus1_is_l is1 is2) x).
  rewrite <- (lunax_is is2 x).
  unfold xinv.
  rewrite <- (pr2 is12 _ _ x).
  unfold minus1_is_l. unfold grinv_is.
  rewrite (grlinvax_is is1 _). apply mult0x_is_l.
  - apply is2.
  - apply is12.
Defined.
Opaque islinvmultwithminus1_is_l.

Lemma isrinvmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
      (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2) (x : X) :
  opp1 x (opp2 (minus1_is_l is1 is2) x) = unel_is (pr1 is1).
Proof.
  set (xinv := opp2 (minus1_is_l is1 is2) x).
  rewrite <- (lunax_is is2 x). unfold xinv.
  rewrite <- (pr2 is12 _ _ x). unfold minus1_is_l. unfold grinv_is.
  rewrite (grrinvax_is is1 _).
  apply mult0x_is_l. apply is2. apply is12.
Defined.
Opaque isrinvmultwithminus1_is_l.

Lemma isminusmultwithminus1_is_l {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1)
      (is2 : ismonoidop opp2) (is12 : isdistr opp1 opp2) (x : X) :
  opp2 (minus1_is_l is1 is2) x = grinv_is is1 x.
Proof.
  apply (invmaponpathsweq (make_weq _ (isweqrmultingr_is is1 x))).
  simpl. rewrite (islinvmultwithminus1_is_l is1 is2 is12 x).
  unfold grinv_is. rewrite (grlinvax_is is1 x). apply idpath.
Defined.
Opaque isminusmultwithminus1_is_l.

Lemma isringopsif {X : UU} {opp1 opp2 : binop X} (is1 : isgrop opp1) (is2 : ismonoidop opp2)
      (is12 : isdistr opp1 opp2) : isringops opp1 opp2.
Proof.
  set (assoc1 := pr1 (pr1 is1)).
  split.
  - split.
    + exists is1.
      intros x y.
      apply (invmaponpathsweq
               (make_weq _ (isweqrmultingr_is is1 (opp2 (minus1_is_l is1 is2) (opp1 x y))))).
      simpl. rewrite (isrinvmultwithminus1_is_l is1 is2 is12 (opp1 x y)).
      rewrite (pr1 is12 x y _).
      induction (assoc1 (opp1 y x) (opp2 (minus1_is_l is1 is2) x) (opp2 (minus1_is_l is1 is2) y)).
      rewrite (assoc1 y x _).
      induction (!isrinvmultwithminus1_is_l is1 is2 is12 x).
      unfold unel_is. rewrite (runax_is (pr1 is1) y).
      rewrite (isrinvmultwithminus1_is_l is1 is2 is12 y).
      apply idpath.
    + apply is2.
  - apply is12.
Defined.

Definition ringmultx0_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) :
  ∏ (x : X), opp2 x (unel_is (pr1 (ringop1axs_is is))) = unel_is (pr1 (ringop1axs_is is)) :=
  multx0_is_l (ringop1axs_is is) (ringop2axs_is is) (ringdistraxs_is is).

Definition ringmult0x_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) :
  ∏ (x : X), opp2 (unel_is (pr1 (ringop1axs_is is))) x = unel_is (pr1 (ringop1axs_is is)) :=
  mult0x_is_l (ringop1axs_is is) (ringop2axs_is is) (ringdistraxs_is is).

Definition ringminus1_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) : X :=
  minus1_is_l (ringop1axs_is is) (ringop2axs_is is).

Definition ringmultwithminus1_is {X : UU} {opp1 opp2 : binop X} (is : isringops opp1 opp2) :
  ∏ (x : X),
  opp2 (minus1_is_l (ringop1axs_is is) (ringop2axs_is is)) x = grinv_is (ringop1axs_is is) x :=
  isminusmultwithminus1_is_l (ringop1axs_is is) (ringop2axs_is is) (ringdistraxs_is is).

Definition isringopstoisrigops (X : UU) (opp1 opp2 : binop X) (is : isringops opp1 opp2) :
  isrigops opp1 opp2.
Proof.
  split.
  - exists (isabgroptoisabmonoidop _ _ (ringop1axs_is is) ,, ringop2axs_is is).
    split.
    + simpl. apply (ringmult0x_is).
    + simpl. apply (ringmultx0_is).
  - apply (ringdistraxs_is is).
Defined.
Coercion isringopstoisrigops : isringops >-> isrigops.

(** *)

Definition iscommrigops {X : UU} (opp1 opp2 : binop X) : UU :=
  (isrigops opp1 opp2) × (iscomm opp2).

Definition pr1iscommrigops (X : UU) (opp1 opp2 : binop X) :
  iscommrigops opp1 opp2 → isrigops opp1 opp2 := @pr1 _ _.
Coercion pr1iscommrigops : iscommrigops >-> isrigops.

Definition rigiscommop2_is {X : UU} {opp1 opp2 : binop X} (is : iscommrigops opp1 opp2) :
  iscomm opp2 := pr2 is.

Lemma isapropiscommrig {X : hSet} (opp1 opp2 : binop X) : isaprop (iscommrigops opp1 opp2).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropisrigops.
  - apply isapropiscomm.
Defined.

(** *)

Definition iscommringops {X : UU} (opp1 opp2 : binop X) : UU :=
  (isringops opp1 opp2) × (iscomm opp2).

Definition pr1iscommringops (X : UU) (opp1 opp2 : binop X) :
  iscommringops opp1 opp2 → isringops opp1 opp2 := @pr1 _ _.
Coercion pr1iscommringops : iscommringops >-> isringops.

Definition ringiscommop2_is {X : UU} {opp1 opp2 : binop X} (is : iscommringops opp1 opp2) :
  iscomm opp2 := pr2 is.

Lemma isapropiscommring {X : hSet} (opp1 opp2 : binop X) : isaprop (iscommringops opp1 opp2).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropisringops.
  - apply isapropiscomm.
Defined.

Definition iscommringopstoiscommrigops (X : UU) (opp1 opp2 : binop X)
           (is : iscommringops opp1 opp2) : iscommrigops opp1 opp2 :=
  isringopstoisrigops _ _ _ (pr1 is) ,, pr2 is.
Coercion iscommringopstoiscommrigops : iscommringops >-> iscommrigops.

(** **** Transfer properties of binary operations relative to weak equivalences *)

(** binop_weq_fwd *)

Lemma isassoc_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isassoc opp → isassoc (binop_weq_fwd H opp).
Proof.
  intros is x y z.
  apply (maponpaths H).
  refine (_ @ is _ _ _ @ _).
  - apply (maponpaths (λ x, opp x _)).
    apply homotinvweqweq.
  - apply maponpaths.
    apply homotinvweqweq0.
Defined.

Lemma islunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  islunit opp x0 → islunit (binop_weq_fwd H opp) (H x0).
Proof.
  intros is y.
  unfold binop_weq_fwd.
  refine (maponpaths _ _ @ _).
  - refine (maponpaths (λ x, opp x _) _ @ _).
    + apply homotinvweqweq.
    + apply is.
  - apply homotweqinvweq.
Defined.

Lemma isrunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  isrunit opp x0 → isrunit (binop_weq_fwd H opp) (H x0).
Proof.
  intros is y.
  unfold binop_weq_fwd.
  refine (maponpaths _ _ @ _).
  - refine (maponpaths (opp _) _ @ _).
    + apply homotinvweqweq.
    + apply is.
  - apply homotweqinvweq.
Defined.

Lemma isunit_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) :
  isunit opp x0 → isunit (binop_weq_fwd H opp) (H x0).
Proof.
  intro is.
  split.
  apply islunit_weq_fwd, (pr1 is).
  apply isrunit_weq_fwd, (pr2 is).
Defined.

Lemma isunital_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isunital opp → isunital (binop_weq_fwd H opp).
Proof.
  intro is.
  exists (H (pr1 is)).
  apply isunit_weq_fwd, (pr2 is).
Defined.

Lemma ismonoidop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  ismonoidop opp → ismonoidop (binop_weq_fwd H opp).
Proof.
  intro is.
  split.
  apply isassoc_weq_fwd, (pr1 is).
  apply isunital_weq_fwd, (pr2 is).
Defined.

Lemma islinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  islinv opp x0 inv → islinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intros is y.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (_ @ is _).
  apply (maponpaths (λ x, opp x _)).
  apply homotinvweqweq.
Defined.
Lemma isrinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  isrinv opp x0 inv → isrinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intros is y.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (_ @ is _).
  apply (maponpaths (opp _)).
  apply homotinvweqweq.
Defined.
Lemma isinv_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (x0 : X) (inv : X → X) :
  isinv opp x0 inv → isinv (binop_weq_fwd H opp) (H x0) (λ y : Y, H (inv (invmap H y))).
Proof.
  intro is.
  split.
  apply islinv_weq_fwd, (pr1 is).
  apply isrinv_weq_fwd, (pr2 is).
Defined.
Lemma invstruct_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) (is : ismonoidop opp) :
  invstruct opp is → invstruct (binop_weq_fwd H opp) (ismonoidop_weq_fwd H opp is).
Proof.
  intro inv.
  exists (λ y : Y, H (pr1 inv (invmap H y))).
  apply isinv_weq_fwd, (pr2 inv).
Defined.

Lemma isgrop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isgrop opp → isgrop (binop_weq_fwd H opp).
Proof.
  intro is.
  use tpair.
  - apply ismonoidop_weq_fwd, (pr1 is).
  - apply invstruct_weq_fwd, (pr2 is).
Defined.

Lemma iscomm_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  iscomm opp → iscomm (binop_weq_fwd H opp).
Proof.
  intros is x y.
  unfold binop_weq_fwd.
  apply maponpaths, is.
Defined.

Lemma isabmonoidop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isabmonoidop opp → isabmonoidop (binop_weq_fwd H opp).
Proof.
  intro is.
  split.
  apply ismonoidop_weq_fwd, (pr1 is).
  apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma isabgrop_weq_fwd {X Y : UU} (H : X ≃ Y) (opp : binop X) :
  isabgrop opp → isabgrop (binop_weq_fwd H opp).
Proof.
  intro is.
  split.
  apply isgrop_weq_fwd, (pr1 is).
  apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma isldistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isldistr op1 op2 → isldistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros is x y z.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (_ @ is _ _ _ @ _).
  - apply maponpaths.
    apply homotinvweqweq.
  - apply map_on_two_paths ; apply homotinvweqweq0.
Defined.
Lemma isrdistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isrdistr op1 op2 → isrdistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros is x y z.
  unfold binop_weq_fwd.
  apply maponpaths.
  refine (_ @ is _ _ _ @ _).
  - apply (maponpaths (λ x, op2 x _)).
    apply homotinvweqweq.
  - apply map_on_two_paths ; apply homotinvweqweq0.
Defined.

Lemma isdistr_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isdistr op1 op2 → isdistr (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intro is.
  split.
  apply isldistr_weq_fwd, (pr1 is).
  apply isrdistr_weq_fwd, (pr2 is).
Defined.

Lemma isabsorb_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isabsorb op1 op2 → isabsorb (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intros is x y.
  unfold binop_weq_fwd.
  refine (_ @ homotweqinvweq H _).
  apply maponpaths.
  refine (_ @ is _ _).
  apply maponpaths.
  apply (homotinvweqweq H).
Defined.

Lemma isrigops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isrigops op1 op2 → isrigops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intro is.
  split.
  - use tpair.
    + split.
      apply isabmonoidop_weq_fwd, (pr1 (pr1 (pr1 is))).
      apply ismonoidop_weq_fwd, (pr2 (pr1 (pr1 is))).
    + split ; simpl.
      * intros x.
        apply (maponpaths H).
        refine (_ @ pr1 (pr2 (pr1 is)) _).
        apply (maponpaths (λ x, op2 x _)).
        apply homotinvweqweq.
      * intros x.
        apply (maponpaths H).
        refine (_ @ pr2 (pr2 (pr1 is)) _).
        apply (maponpaths (op2 _)).
        apply homotinvweqweq.
  - apply isdistr_weq_fwd, (pr2 is).
Defined.

Lemma isringops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  isringops op1 op2 → isringops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intro is.
  split.
  - split.
    + apply isabgrop_weq_fwd, (pr1 (pr1 is)).
    + apply ismonoidop_weq_fwd, (pr2 (pr1 is)).
  - apply isdistr_weq_fwd, (pr2 is).
Defined.

Lemma iscommrigops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  iscommrigops op1 op2 → iscommrigops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intro is.
  split.
  - apply isrigops_weq_fwd, (pr1 is).
  - apply iscomm_weq_fwd, (pr2 is).
Defined.

Lemma iscommringops_weq_fwd {X Y : UU} (H : X ≃ Y) (op1 op2 : binop X) :
  iscommringops op1 op2 → iscommringops (binop_weq_fwd H op1) (binop_weq_fwd H op2).
Proof.
  intro is.
  split.
  - apply isringops_weq_fwd, (pr1 is).
  - apply iscomm_weq_fwd, (pr2 is).
Defined.

(** binop_weq_bck *)

Lemma isassoc_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isassoc opp → isassoc (binop_weq_bck H opp).
Proof.
  intros is x y z.
  apply (maponpaths (invmap H)).
  refine (_ @ is _ _ _ @ _).
  - apply (maponpaths (λ x, opp x _)).
    apply homotweqinvweq.
  - apply maponpaths.
    symmetry.
    apply homotweqinvweq.
Defined.
Lemma islunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  islunit opp x0 → islunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intros is y.
  unfold binop_weq_bck.
  refine (maponpaths _ _ @ _).
  - refine (maponpaths (λ x, opp x _) _ @ _).
    + apply homotweqinvweq.
    + apply is.
  - apply homotinvweqweq.
Defined.
Lemma isrunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  isrunit opp x0 → isrunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intros is y.
  unfold binop_weq_bck.
  refine (maponpaths _ _ @ _).
  - refine (maponpaths (opp _) _ @ _).
    + apply homotweqinvweq.
    + apply is.
  - apply homotinvweqweq.
Defined.
Lemma isunit_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) :
  isunit opp x0 → isunit (binop_weq_bck H opp) (invmap H x0).
Proof.
  intro is.
  split.
  apply islunit_weq_bck, (pr1 is).
  apply isrunit_weq_bck, (pr2 is).
Defined.

Lemma isunital_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isunital opp → isunital (binop_weq_bck H opp).
Proof.
  intro is.
  exists (invmap H (pr1 is)).
  apply isunit_weq_bck, (pr2 is).
Defined.

Lemma ismonoidop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  ismonoidop opp → ismonoidop (binop_weq_bck H opp).
Proof.
  intro is.
  split.
  apply isassoc_weq_bck, (pr1 is).
  apply isunital_weq_bck, (pr2 is).
Defined.

Lemma islinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  islinv opp x0 inv → islinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intros is y.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (_ @ is _).
  apply (maponpaths (λ x, opp x _)).
  apply homotweqinvweq.
Defined.
Lemma isrinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  isrinv opp x0 inv → isrinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intros is y.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (_ @ is _).
  apply (maponpaths (opp _)).
  apply homotweqinvweq.
Defined.
Lemma isinv_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (x0 : Y) (inv : Y → Y) :
  isinv opp x0 inv → isinv (binop_weq_bck H opp) (invmap H x0) (λ y : X, invmap H (inv (H y))).
Proof.
  intro is.
  split.
  apply islinv_weq_bck, (pr1 is).
  apply isrinv_weq_bck, (pr2 is).
Defined.
Lemma invstruct_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) (is : ismonoidop opp) :
  invstruct opp is → invstruct (binop_weq_bck H opp) (ismonoidop_weq_bck H opp is).
Proof.
  intro inv.
  exists (λ y : X, invmap H (pr1 inv (H y))).
  apply isinv_weq_bck, (pr2 inv).
Defined.

Lemma isgrop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isgrop opp → isgrop (binop_weq_bck H opp).
Proof.
  intro is.
  use tpair.
  apply ismonoidop_weq_bck, (pr1 is).
  apply invstruct_weq_bck, (pr2 is).
Defined.

Lemma iscomm_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  iscomm opp → iscomm (binop_weq_bck H opp).
Proof.
  intros is x y.
  unfold binop_weq_bck.
  apply maponpaths, is.
Defined.

Lemma isabmonoidop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isabmonoidop opp → isabmonoidop (binop_weq_bck H opp).
Proof.
  intro is.
  split.
  apply ismonoidop_weq_bck, (pr1 is).
  apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma isabgrop_weq_bck {X Y : UU} (H : X ≃ Y) (opp : binop Y) :
  isabgrop opp → isabgrop (binop_weq_bck H opp).
Proof.
  intro is.
  split.
  apply isgrop_weq_bck, (pr1 is).
  apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma isldistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isldistr op1 op2 → isldistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros is x y z.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (_ @ is _ _ _ @ _).
  - apply maponpaths.
    apply homotweqinvweq.
  - apply map_on_two_paths;
    exact (!homotweqinvweq _ _).
Defined.
Lemma isrdistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isrdistr op1 op2 → isrdistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros is x y z.
  unfold binop_weq_bck.
  apply maponpaths.
  refine (_ @ is _ _ _ @ _).
  - apply (maponpaths (λ x, op2 x _)).
    apply homotweqinvweq.
  - apply map_on_two_paths; exact (!homotweqinvweq _ _).
Defined.

Lemma isdistr_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isdistr op1 op2 → isdistr (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intro is.
  split.
  apply isldistr_weq_bck, (pr1 is).
  apply isrdistr_weq_bck, (pr2 is).
Defined.

Lemma isabsorb_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isabsorb op1 op2 → isabsorb (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intros is x y.
  unfold binop_weq_bck.
  refine (_ @ homotinvweqweq H _).
  apply maponpaths.
  refine (_ @ is _ _).
  apply maponpaths.
  apply (homotweqinvweq H).
Defined.

Lemma isrigops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isrigops op1 op2 → isrigops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intro is.
  split.
  - use tpair.
    + split.
      apply isabmonoidop_weq_bck, (pr1 (pr1 (pr1 is))).
      apply ismonoidop_weq_bck, (pr2 (pr1 (pr1 is))).
    + split ; simpl.
      * intros x.
        apply (maponpaths (invmap H)).
        refine (_ @ pr1 (pr2 (pr1 is)) _).
        apply (maponpaths (λ x, op2 x _)).
        apply homotweqinvweq.
      * intros x.
        apply (maponpaths (invmap H)).
        refine (_ @ pr2 (pr2 (pr1 is)) _).
        apply (maponpaths (op2 _)).
        apply homotweqinvweq.
  - apply isdistr_weq_bck, (pr2 is).
Defined.

Lemma isringops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  isringops op1 op2 → isringops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intro is.
  split.
  - split.
    + apply isabgrop_weq_bck, (pr1 (pr1 is)).
    + apply ismonoidop_weq_bck, (pr2 (pr1 is)).
  - apply isdistr_weq_bck, (pr2 is).
Defined.

Lemma iscommrigops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  iscommrigops op1 op2 → iscommrigops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intro is.
  split.
  - apply isrigops_weq_bck, (pr1 is).
  - apply iscomm_weq_bck, (pr2 is).
Defined.

Lemma iscommringops_weq_bck {X Y : UU} (H : X ≃ Y) (op1 op2 : binop Y) :
  iscommringops op1 op2 → iscommringops (binop_weq_bck H op1) (binop_weq_bck H op2).
Proof.
  intro is.
  split.
  - apply isringops_weq_bck, (pr1 is).
  - apply iscomm_weq_bck, (pr2 is).
Defined.


(** * 3. Sets with one binary operation *)

(** * 3.1. General definitions *)

Definition setwithbinop : UU := ∑ (X : hSet), binop X.

Definition make_setwithbinop (X : hSet) (opp : binop X) : setwithbinop := X ,, opp.

Definition pr1setwithbinop : setwithbinop → hSet := @pr1 _ (λ X : hSet, binop X).
Coercion pr1setwithbinop : setwithbinop >-> hSet.

Definition op {X : setwithbinop} : binop X := pr2 X.

Definition isasetbinoponhSet (X : hSet) : isaset (@binop X).
Proof.
  use impred_isaset. intros t1.
  use impred_isaset. intros t2.
  use setproperty.
Qed.

Declare Scope addoperation_scope.
Delimit Scope addoperation_scope with addoperation.
Notation "x + y" := (op x y) : addoperation_scope.
Declare Scope multoperation_scope.
Delimit Scope multoperation_scope with multoperation.
Notation "x * y" := (op x y) : multoperation_scope.

(* The reverse/opposite binary operation where the arguments are flipped. *)
Definition setwithbinop_rev (X : setwithbinop) : setwithbinop :=
  make_setwithbinop X (λ x y, op y x).

(** * 3.2. Functions compatible with a binary operation (homomorphism) and their properties *)

Definition isbinopfun {X Y : setwithbinop} (f : X → Y) : UU :=
  ∏ x x' : X, f (op x x') = op (f x) (f x').

Definition make_isbinopfun {X Y : setwithbinop} {f : X → Y}
           (H : ∏ x x' : X, f (op x x') = op (f x) (f x')) : isbinopfun f := H.

Lemma isapropisbinopfun {X Y : setwithbinop} (f : X → Y) : isaprop (isbinopfun f).
Proof.
  apply impred. intro x.
  apply impred. intro x'.
  apply (setproperty Y).
Defined.

Definition isbinopfun_twooutof3b {A B C : setwithbinop} (f : A → B) (g : B → C)
           (H : issurjective f) : isbinopfun (g ∘ f)%functions → isbinopfun f → isbinopfun g.
Proof.
  intros H1 H2.
  apply make_isbinopfun.
  intros b1 b2.
  apply (squash_to_prop (H b1) (@setproperty C _ _)). intros H1'.
  apply (squash_to_prop (H b2) (@setproperty C _ _)). intros H2'.
  rewrite <- (hfiberpr2 _ _ H1'). rewrite <- (hfiberpr2 _ _ H2').
  refine (!maponpaths g (H2 (hfiberpr1 _ _ H1') (hfiberpr1 _ _ H2')) @ _).
  apply H1.
Qed.

Definition binopfun (X Y : setwithbinop) : UU := ∑ (f : X → Y), isbinopfun f.

Definition make_binopfun {X Y : setwithbinop} (f : X → Y) (is : isbinopfun f) : binopfun X Y := f ,, is.

Definition pr1binopfun (X Y : setwithbinop) : binopfun X Y → (X → Y) := @pr1 _ _.
Coercion pr1binopfun : binopfun >-> Funclass.

Definition binopfunisbinopfun {X Y : setwithbinop} (f : binopfun X Y) : isbinopfun f := pr2 f.

Lemma isasetbinopfun  (X Y : setwithbinop) : isaset (binopfun X Y).
Proof.
  apply (isasetsubset (pr1binopfun X Y)).
  - change (isofhlevel 2 (X → Y)).
    apply impred. intro.
    apply (setproperty Y).
  - refine (isinclpr1 _ _). intro.
    apply isapropisbinopfun.
Defined.

Lemma binopfun_paths
  {X Y : setwithbinop}
  (f g : binopfun X Y)
  (H : (f : X → Y) = g)
  : f = g.
Proof.
  apply subtypePath.
  - exact isapropisbinopfun.
  - exact H.
Qed.

Definition binopfun_eq
  {X Y : setwithbinop}
  (f g : binopfun X Y)
  : (f = g) ≃ (∏ x, f x = g x).
Proof.
  use weqimplimpl.
  - intros e x.
    exact (maponpaths (λ (f : binopfun _ _), f x) e).
  - intro e.
    apply binopfun_paths.
    apply funextfun.
    exact e.
  - abstract apply isasetbinopfun.
  - abstract (
      apply impred_isaprop;
      intro;
      apply setproperty
    ).
Defined.

Lemma isbinopfuncomp {X Y Z : setwithbinop} (f : binopfun X Y) (g : binopfun Y Z) :
  isbinopfun (g ∘ f).
Proof.
  set (axf := binopfunisbinopfun f). set (axg := binopfunisbinopfun g).
  intros a b. simpl.
  rewrite (axf a b). rewrite (axg (f a) (f b)).
  apply idpath.
Qed.

Definition binopfuncomp {X Y Z : setwithbinop} (f : binopfun X Y) (g : binopfun Y Z) :
  binopfun X Z := make_binopfun (g ∘ f) (isbinopfuncomp f g).

Definition binopmono (X Y : setwithbinop) : UU := ∑ (f : incl X Y), isbinopfun (pr1 f).

Definition make_binopmono {X Y : setwithbinop} (f : incl X Y) (is : isbinopfun f) :
  binopmono X Y := f ,, is.

Definition pr1binopmono (X Y : setwithbinop) : binopmono X Y → incl X Y := @pr1 _ _.
Coercion pr1binopmono : binopmono >-> incl.

Definition binopincltobinopfun (X Y : setwithbinop) :
  binopmono X Y → binopfun X Y := λ f, make_binopfun (pr1 (pr1 f)) (pr2 f).
Coercion binopincltobinopfun : binopmono >-> binopfun.

Definition binopmonocomp {X Y Z : setwithbinop} (f : binopmono X Y) (g : binopmono Y Z) :
  binopmono X Z := make_binopmono (inclcomp (pr1 f) (pr1 g)) (isbinopfuncomp f g).

Definition binopiso (X Y : setwithbinop) : UU := ∑ (f : X ≃ Y), isbinopfun f.

Definition make_binopiso {X Y : setwithbinop} (f : X ≃ Y) (is : isbinopfun f) :
  binopiso X Y := f ,, is.

Definition pr1binopiso (X Y : setwithbinop) : binopiso X Y → X ≃ Y := @pr1 _ _.
Coercion pr1binopiso : binopiso >-> weq.

Lemma isasetbinopiso (X Y : setwithbinop) : isaset (binopiso X Y).
Proof.
  use isaset_total2.
  - use isaset_total2.
    + use impred_isaset. intros t. use setproperty.
    + intros x. use isasetaprop. use isapropisweq.
  - intros w. use isasetaprop. use isapropisbinopfun.
Qed.

Definition binopisotobinopmono (X Y : setwithbinop) :
  binopiso X Y → binopmono X Y := λ f, make_binopmono (weqtoincl (pr1 f)) (pr2 f).
Coercion binopisotobinopmono : binopiso >-> binopmono.

Definition binopisocomp {X Y Z : setwithbinop} (f : binopiso X Y) (g : binopiso Y Z) :
  binopiso X Z := make_binopiso (weqcomp (pr1 f) (pr1 g)) (isbinopfuncomp f g).

Lemma isbinopfuninvmap {X Y : setwithbinop} (f : binopiso X Y) : isbinopfun (invmap (pr1 f)).
Proof.
  set (axf := pr2 f). intros a b.
  apply (invmaponpathsweq (pr1 f)).
  rewrite (homotweqinvweq (pr1 f) (op a b)).
  rewrite (axf (invmap (pr1 f) a) (invmap (pr1 f) b)).
  rewrite (homotweqinvweq (pr1 f) a).
  rewrite (homotweqinvweq (pr1 f) b).
  apply idpath.
Qed.

Definition invbinopiso {X Y : setwithbinop} (f : binopiso X Y) :
  binopiso Y X := make_binopiso (invweq (pr1 f)) (isbinopfuninvmap f).

Definition idbinopiso (X : setwithbinop) : binopiso X X.
Proof.
  use make_binopiso.
  - exact (idweq X).
  - intros x1 x2. use idpath.
Defined.


(** **** (X = Y) ≃ (binopiso X Y)
   The idea is to use the composition (X = Y) ≃ (X ╝ Y) ≃ (binopiso X Y)
*)

Definition setwithbinop_univalence_weq1 (X Y : setwithbinop) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition setwithbinop_univalence_weq2 (X Y : setwithbinop) : (X ╝ Y) ≃ (binopiso X Y).
Proof.
  use weqbandf.
  - use hSet_univalence.
  - intros e. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    induction e. use weqimplimpl.
    + intros i.
      use funextfun. intros x1.
      use funextfun. intros x2.
      exact (i x1 x2).
    + intros e. cbn in e. intros x1 x2. induction e. use idpath.
    + use isapropisbinopfun.
    + use isasetbinoponhSet.
Defined.

Definition setwithbinop_univalence_map (X Y : setwithbinop) : X = Y → binopiso X Y.
Proof.
  intro e. induction e. exact (idbinopiso X).
Defined.

Lemma setwithbinop_univalence_isweq (X Y : setwithbinop) :
  isweq (setwithbinop_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (setwithbinop_univalence_weq1 X Y) (setwithbinop_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque setwithbinop_univalence_isweq.

Definition setwithbinop_univalence (X Y : setwithbinop) : (X = Y) ≃ (binopiso X Y)
  := make_weq
    (setwithbinop_univalence_map X Y)
    (setwithbinop_univalence_isweq X Y).


(** **** hfiber and binop*)
Local Lemma hfiberbinop_path {A B : setwithbinop} (f : binopfun A B) (b1 b2 : B)
      (hf1 : hfiber (pr1 f) b1) (hf2 : hfiber (pr1 f) b2) :
  pr1 f (@op A (pr1 hf1) (pr1 hf2)) = (@op B b1 b2).
Proof.
  refine (binopfunisbinopfun f _ _ @ _).
  rewrite <- (hfiberpr2 _ _ hf1). rewrite <- (hfiberpr2 _ _ hf2). use idpath.
Qed.

Definition hfiberbinop {A B : setwithbinop} (f : binopfun A B) (b1 b2 : B)
           (hf1 : hfiber (pr1 f) b1) (hf2 : hfiber (pr1 f) b2) :
  hfiber (pr1 f) (@op B b1 b2) :=
  make_hfiber (pr1 f) (@op A (pr1 hf1) (pr1 hf2)) (hfiberbinop_path f b1 b2 hf1 hf2).


(** * 3.3. Transport of properties of a binary operation *)

Lemma islcancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : islcancelable (@op Y) (f x)) : islcancelable (@op X) x.
Proof.
  unfold islcancelable.
  apply (isincltwooutof3a (λ x0 : X, op x x0) f (pr2 (pr1 f))).
  assert (h : homot ((λ y0 : Y, op (f x) y0) ∘ f) (f ∘ (λ x0 : X, op x x0))).
  {
    intro x0; simpl. apply (!(pr2 f) x x0).
  }
  apply (isinclhomot _ _ h).
  apply (isinclcomp f (make_incl _ is)).
Defined.

Lemma isrcancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : isrcancelable (@op Y) (f x)) : isrcancelable (@op X) x.
Proof.
  unfold islcancelable.
  apply (isincltwooutof3a (λ x0 : X, op x0 x) f (pr2 (pr1 f))).
  assert (h : homot ((λ y0 : Y, op y0 (f x)) ∘ f) (f ∘ (λ x0 : X, op x0 x))).
  {
    intro x0; simpl. apply (!(pr2 f) x0 x).
  }
  apply (isinclhomot _ _ h). apply (isinclcomp f (make_incl _ is)).
Defined.

Lemma iscancelablemonob {X Y : setwithbinop} (f : binopmono X Y) (x : X)
      (is : iscancelable (@op Y) (f x)) : iscancelable (@op X) x.
Proof.
  apply (islcancelablemonob f x (pr1 is) ,, isrcancelablemonob f x (pr2 is)).
Defined.

Notation islcancelableisob := islcancelablemonob.
Notation isrcancelableisob := isrcancelablemonob.
Notation iscancelableisob := iscancelablemonob.

Lemma islinvertibleisob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : islinvertible (@op Y) (f x)) : islinvertible (@op X) x.
Proof.
  unfold islinvertible. apply (twooutof3a (λ x0 : X, op x x0) f).
  - assert (h : homot ((λ y0 : Y, op (f x) y0) ∘ f) (f ∘ (λ x0 : X, op x x0))).
    {
      intro x0; simpl. apply (!(pr2 f) x x0).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp f (make_weq _ is))).
  - apply (pr2 (pr1 f)).
Defined.

Lemma isrinvertibleisob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isrinvertible (@op Y) (f x)) : isrinvertible (@op X) x.
Proof.
  unfold islinvertible. apply (twooutof3a (λ x0 : X, op x0 x) f).
  - assert (h : homot ((λ y0 : Y, op y0 (f x)) ∘ f) (f ∘ (λ x0 : X, op x0 x))).
    {
      intro x0; simpl. apply (!(pr2 f) x0 x).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp f (make_weq _ is))).
  - apply (pr2 (pr1 f)).
Defined.

Lemma isinvertiblemonob {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isinvertible (@op Y) (f x)) : isinvertible (@op X) x.
Proof.
  apply (islinvertibleisob f x (pr1 is) ,, isrinvertibleisob f x (pr2 is)).
Defined.

Definition islinvertibleisof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
           (is : islinvertible (@op X) x) : islinvertible (@op Y) (f x).
Proof.
  unfold islinvertible. apply (twooutof3b f).
  - apply (pr2 (pr1 f)).
  - assert (h : homot (f ∘ (λ x0 : X, op x x0)) (λ x0 : X, op (f x) (f x0))).
    {
      intro x0; simpl. apply (pr2 f x x0).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp (make_weq _ is) f)).
Defined.

Definition isrinvertibleisof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
           (is : isrinvertible (@op X) x) : isrinvertible (@op Y) (f x).
Proof.
  unfold isrinvertible. apply (twooutof3b f).
  - apply (pr2 (pr1 f)).
  - assert (h : homot (f ∘ (λ x0 : X, op x0 x)) (λ x0 : X, op (f x0) (f x))).
    {
      intro x0; simpl. apply (pr2 f x0 x).
    }
    apply (isweqhomot _ _ h). apply (pr2 (weqcomp (make_weq _ is) f)).
Defined.

Lemma isinvertiblemonof {X Y : setwithbinop} (f : binopiso X Y) (x : X)
      (is : isinvertible (@op X) x) : isinvertible (@op Y) (f x).
Proof.
  apply (islinvertibleisof f x (pr1 is) ,, isrinvertibleisof f x (pr2 is)).
Defined.

Lemma isassocmonob {X Y : setwithbinop} (f : binopmono X Y) (is : isassoc (@op Y)) :
  isassoc (@op X).
Proof.
  set (axf := pr2 f). simpl in axf. intros a b c.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  rewrite (axf (op a b) c). rewrite (axf a b).
  rewrite (axf a (op b c)). rewrite (axf b c). apply is.
Qed.

Lemma iscommmonob {X Y : setwithbinop} (f : binopmono X Y) (is : iscomm (@op Y)) : iscomm (@op X).
Proof.
  set (axf := pr2 f). simpl in axf. intros a b.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  rewrite (axf a b). rewrite (axf b a). apply is.
Qed.

Notation isassocisob := isassocmonob.
Notation iscommisob := iscommmonob.

Lemma isassocisof {X Y : setwithbinop} (f : binopiso X Y) (is : isassoc (@op X)) : isassoc (@op Y).
Proof.
  apply (isassocmonob (invbinopiso f) is).
Qed.

Lemma iscommisof {X Y : setwithbinop} (f : binopiso X Y) (is : iscomm (@op X)) : iscomm (@op Y).
Proof.
  apply (iscommmonob (invbinopiso f) is).
Qed.

Lemma isunitisof {X Y : setwithbinop} (f : binopiso X Y) (unx : X) (is : isunit (@op X) unx) :
  isunit (@op Y) (f unx).
Proof.
  set (axf := pr2 f). split.
  - intro a. change (f unx) with (pr1 f unx).
    apply (invmaponpathsweq (pr1 (invbinopiso f))).
    rewrite (pr2 (invbinopiso f) (pr1 f unx) a). simpl.
    rewrite (homotinvweqweq (pr1 f) unx). apply (pr1 is).
  - intro a. change (f unx) with (pr1 f unx).
    apply (invmaponpathsweq (pr1 (invbinopiso f))).
    rewrite (pr2 (invbinopiso f) a (pr1 f unx)). simpl.
    rewrite (homotinvweqweq (pr1 f) unx). apply (pr2 is).
Qed.

Definition isunitalisof {X Y : setwithbinop} (f : binopiso X Y) (is : isunital (@op X)) :
  isunital (@op Y) := make_isunital (f (pr1 is)) (isunitisof f (pr1 is) (pr2 is)).

Lemma isunitisob {X Y : setwithbinop} (f : binopiso X Y) (uny : Y) (is : isunit (@op Y) uny) :
  isunit (@op X) ((invmap f) uny).
Proof.
  set (int := isunitisof (invbinopiso f)). simpl. simpl in int.
  apply int. apply is.
Qed.

Definition isunitalisob {X Y : setwithbinop} (f : binopiso X Y) (is : isunital (@op Y)) :
  isunital (@op X) := make_isunital ((invmap f) (pr1 is)) (isunitisob f (pr1 is) (pr2 is)).

Definition ismonoidopisof {X Y : setwithbinop} (f : binopiso X Y) (is : ismonoidop (@op X)) :
  ismonoidop (@op Y) := isassocisof f (pr1 is) ,, isunitalisof f (pr2 is).

Definition ismonoidopisob {X Y : setwithbinop} (f : binopiso X Y) (is : ismonoidop (@op Y)) :
  ismonoidop (@op X) := isassocisob f (pr1 is) ,, isunitalisob f (pr2 is).

Lemma isinvisof {X Y : setwithbinop} (f : binopiso X Y) (unx : X) (invx : X → X)
      (is : isinv (@op X) unx invx) :
  isinv (@op Y) (pr1 f unx) ((pr1 f) ∘ invx ∘ invmap (pr1 f)).
Proof.
  set (axf := pr2 f). set (axinvf := pr2 (invbinopiso f)).
  simpl in axf, axinvf. split.
  - intro a. apply (invmaponpathsweq (pr1 (invbinopiso f))).
    simpl. rewrite (axinvf ((pr1 f) (invx (invmap (pr1 f) a))) a).
    rewrite (homotinvweqweq (pr1 f) unx).
    rewrite (homotinvweqweq (pr1 f) (invx (invmap (pr1 f) a))).
    apply (pr1 is).
  - intro a. apply (invmaponpathsweq (pr1 (invbinopiso f))).
    simpl. rewrite (axinvf a ((pr1 f) (invx (invmap (pr1 f) a)))).
    rewrite (homotinvweqweq (pr1 f) unx).
    rewrite (homotinvweqweq (pr1 f) (invx (invmap (pr1 f) a))).
    apply (pr2 is).
Qed.

Definition isgropisof {X Y : setwithbinop} (f : binopiso X Y) (is : isgrop (@op X)) :
  isgrop (@op Y) := ismonoidopisof f is ,,
                    (f ∘ grinv_is is ∘ invmap f) ,,
                    isinvisof f (unel_is is) (grinv_is is) (pr2 (pr2 is)).

Lemma isinvisob {X Y : setwithbinop} (f : binopiso X Y) (uny : Y) (invy : Y → Y)
      (is : isinv (@op Y) uny invy) : isinv (@op X) (invmap (pr1 f) uny)
                                            (invmap f ∘ invy ∘ f).
Proof.
  apply (isinvisof (invbinopiso f) uny invy is).
Qed.

Definition isgropisob {X Y : setwithbinop} (f : binopiso X Y) (is : isgrop (@op Y)) :
  isgrop (@op X) := ismonoidopisob f is ,,
                    invmap f ∘ grinv_is is ∘ f ,,
                    isinvisob f (unel_is is) (grinv_is is) (pr2 (pr2 is)).

Definition isabmonoidopisof {X Y : setwithbinop} (f : binopiso X Y) (is : isabmonoidop (@op X)) :
  isabmonoidop (@op Y) := ismonoidopisof f is ,, iscommisof f (commax_is is).

Definition isabmonoidopisob {X Y : setwithbinop} (f : binopiso X Y) (is : isabmonoidop (@op Y)) :
  isabmonoidop (@op X) := ismonoidopisob f is ,, iscommisob f (commax_is is).

Definition isabgropisof {X Y : setwithbinop} (f : binopiso X Y) (is : isabgrop (@op X)) :
  isabgrop (@op Y) := isgropisof f is ,, iscommisof f (commax_is is).

Definition isabgropisob {X Y : setwithbinop} (f : binopiso X Y) (is : isabgrop (@op Y)) :
  isabgrop (@op X) := isgropisob f is ,, iscommisob f (commax_is is).


(** * 3.4. Subobject *)

Definition issubsetwithbinop {X : hSet} (opp : binop X) (A : hsubtype X) : UU :=
  ∏ a a' : A, A (opp (pr1 a) (pr1 a')).

Lemma isapropissubsetwithbinop {X : hSet} (opp : binop X) (A : hsubtype X) :
  isaprop (issubsetwithbinop opp A).
Proof.
  apply impred. intro a.
  apply impred. intros a'.
  apply (pr2 (A (opp (pr1 a) (pr1 a')))).
Defined.

Definition subsetswithbinop (X : setwithbinop) : UU :=
  ∑ (A : hsubtype X), issubsetwithbinop (@op X) A.

Definition make_subsetswithbinop
  {X : setwithbinop}
  (t : hsubtype X)
  (H : issubsetwithbinop op t)
  : subsetswithbinop X
  := t ,, H.

Definition subsetswithbinopconstr {X : setwithbinop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwithbinop op A) t →
                       ∑ A : hsubtype X, issubsetwithbinop op A := @make_subsetswithbinop X.

Definition pr1subsetswithbinop (X : setwithbinop) : subsetswithbinop X → hsubtype X :=
  @pr1 _ (λ A : hsubtype X, issubsetwithbinop (@op X) A).
Coercion pr1subsetswithbinop : subsetswithbinop >-> hsubtype.

Definition pr2subsetswithbinop {X : setwithbinop} (Y : subsetswithbinop X) :
  issubsetwithbinop (@op X) (pr1subsetswithbinop X Y) := pr2 Y.

Definition totalsubsetwithbinop (X : setwithbinop) : subsetswithbinop X.
Proof.
  exists (λ x : X, htrue). intros x x'. apply tt.
Defined.

Definition carrierofasubsetwithbinop {X : setwithbinop} (A : subsetswithbinop X) : setwithbinop.
Proof.
  set (aset := (make_hSet (carrier A) (isasetsubset (pr1carrier A) (setproperty X)
                                                   (isinclpr1carrier A))) : hSet).
  exists aset.
  set (subopp := (λ a a' : A, make_carrier A (op (pr1carrier _ a) (pr1carrier _ a')) (pr2 A a a')) :
                   (A → A → A)).
  simpl. unfold binop. apply subopp.
Defined.
Coercion carrierofasubsetwithbinop : subsetswithbinop >-> setwithbinop.


(** * 3.5. Relations compatible with a binary operation and quotient objects *)

Definition isbinophrel {X : setwithbinop} (R : hrel X) : UU :=
  (∏ a b c : X, R a b → R (op c a) (op c b)) × (∏ a b c : X, R a b → R (op a c) (op b c)).

Definition make_isbinophrel {X : setwithbinop} {R : hrel X}
           (H1 : ∏ a b c : X, R a b → R (op c a) (op c b))
           (H2 : ∏ a b c : X, R a b → R (op a c) (op b c)) : isbinophrel R :=
  H1 ,, H2.

Definition isbinophrellogeqf {X : setwithbinop} {L R : hrel X}
           (lg : hrellogeq L R) (isl : isbinophrel L) : isbinophrel R.
Proof.
  split.
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ (pr2 (lg  _ _) rab)))).
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ (pr2 (lg  _ _) rab)))).
Defined.

Lemma isapropisbinophrel {X : setwithbinop} (R : hrel X) : isaprop (isbinophrel R).
Proof.
  apply isapropdirprod.
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
Defined.

Lemma isbinophrelif {X : setwithbinop} (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, R a b → R (op c a) (op c b)) : isbinophrel R.
Proof.
  exists isl. intros a b c rab.
  induction (is c a). induction (is c b). apply (isl _ _ _ rab).
Defined.

Lemma iscompbinoptransrel {X : setwithbinop} (R : hrel X) (ist : istrans R) (isb : isbinophrel R) :
  iscomprelrelfun2 R R (@op X).
Proof.
  intros a b c d. intros rab rcd.
  set (racbc := pr2 isb a b c rab). set (rbcbd := pr1 isb c d b rcd).
  apply (ist _ _ _ racbc rbcbd).
Defined.

Lemma isbinopreflrel {X : setwithbinop} (R : hrel X) (isr : isrefl R)
      (isb : iscomprelrelfun2 R R (@op X)) : isbinophrel R.
Proof.
  split.
  - intros a b c rab. apply (isb c c a b (isr c) rab).
  - intros a b c rab. apply (isb a b c c rab (isr c)).
Defined.

Definition binophrel (X : setwithbinop) : UU := ∑ (R : hrel X), isbinophrel R.

Definition make_binophrel {X : setwithbinop} (t : hrel X) (H : isbinophrel t)
  : binophrel X
  := t ,, H.

Definition pr1binophrel (X : setwithbinop) : binophrel X → hrel X :=
  @pr1 _ (λ R : hrel X, isbinophrel R).
Coercion pr1binophrel : binophrel >-> hrel.

Definition binophrel_resp_left {X : setwithbinop} (R : binophrel X)
           {a b : X} (c : X) (r : R a b) : R (op c a) (op c b) :=
  pr1 (pr2 R) a b c r.

Definition binophrel_resp_right {X : setwithbinop} (R : binophrel X)
           {a b : X} (c : X) (r : R a b) : R (op a c) (op b c) :=
  pr2 (pr2 R) a b c r.

Definition binoppo (X : setwithbinop) : UU := ∑ (R : po X), isbinophrel R.

Definition make_binoppo {X : setwithbinop} (t : po X) (H : isbinophrel t)
  : binoppo X
  := t ,, H.

Definition pr1binoppo (X : setwithbinop) : binoppo X → po X := @pr1 _ (λ R : po X, isbinophrel R).
Coercion pr1binoppo : binoppo >-> po.

Definition binopeqrel (X : setwithbinop) : UU := ∑ (R : eqrel X), isbinophrel R.

Definition make_binopeqrel {X : setwithbinop} (t : eqrel X) (H : isbinophrel t)
  : binopeqrel X
  := t ,, H.

Definition pr1binopeqrel (X : setwithbinop) : binopeqrel X → eqrel X :=
  @pr1 _ (λ R : eqrel X, isbinophrel R).
Coercion pr1binopeqrel : binopeqrel >-> eqrel.

Definition binopeqrel_resp_left {X : setwithbinop} (R : binopeqrel X)
           {a b : X} (c : X) (r : R a b) : R (op c a) (op c b) :=
  pr1 (pr2 R) a b c r.

Definition binopeqrel_resp_right {X : setwithbinop} (R : binopeqrel X)
           {a b : X} (c : X) (r : R a b) : R (op a c) (op b c) :=
  pr2 (pr2 R) a b c r.

Definition setwithbinopquot {X : setwithbinop} (R : binopeqrel X) : setwithbinop.
Proof.
  exists (setquotinset R).
  set (qt  := setquot R). set (qtset := setquotinset R).
  assert (iscomp : iscomprelrelfun2 R R op) by apply (iscompbinoptransrel R (eqreltrans R) (pr2 R)).
  set (qtmlt := setquotfun2 R R op iscomp).
  simpl. unfold binop. apply qtmlt.
Defined.

Definition ispartbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) : UU :=
  (∏ a b c : X, S c → R a b → R (op c a) (op c b)) ×
  (∏ a b c : X, S c → R a b → R (op a c) (op b c)).

Lemma isaprop_ispartbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) :
  isaprop (ispartbinophrel S R).
Proof.
  apply isapropdirprod ;
  apply impred_isaprop ; intros a ;
  apply impred_isaprop ; intros b ;
  apply impred_isaprop ; intros c ;
  apply isapropimpl, isapropimpl, propproperty.
Defined.

Definition isbinoptoispartbinop {X : setwithbinop} (S : hsubtype X) (L : hrel X)
           (d2 : isbinophrel L) : ispartbinophrel S L.
Proof.
  unfold isbinophrel in d2. unfold ispartbinophrel. split.
  - intros a b c is. apply (pr1 d2 a b c).
  - intros a b c is. apply (pr2 d2 a b c).
Defined.

Definition ispartbinophrellogeqf {X : setwithbinop} (S : hsubtype X) {L R : hrel X}
           (lg : hrellogeq L R) (isl : ispartbinophrel S L) : ispartbinophrel S R.
Proof.
  split.
  - intros a b c is rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ is (pr2 (lg _ _) rab)))).
  - intros a b c is rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ is (pr2 (lg  _ _) rab)))).
Defined.

Lemma ispartbinophrelif {X : setwithbinop} (S : hsubtype X) (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, S c → R a b → R (op c a) (op c b)) : ispartbinophrel S R.
Proof.
  exists isl.
  intros a b c s rab. induction (is c a). induction (is c b).
  apply (isl _ _ _ s rab).
Defined.

(* The binophrel generated by an arbitrary hrel *)
Local Notation "A ⇒ B" := (himpl A B).
Definition generated_binophrel_hrel {X : setwithbinop} (R : hrel X) : hrel X :=
  λ x x',  ∀(R' : binophrel X), (∏ x₁ x₂, R x₁ x₂ → R' x₁ x₂) ⇒ R' x x'.

Lemma isbinophrel_generated_binophrel {X : setwithbinop} (R : hrel X) :
  isbinophrel (generated_binophrel_hrel R).
Proof.
  split.
  - intros a b c H R' H2. apply binophrel_resp_left. exact (H R' H2).
  - intros a b c H R' H2. apply binophrel_resp_right. exact (H R' H2).
Defined.

Definition generated_binophrel {X : setwithbinop} (R : hrel X) : binophrel X :=
  make_binophrel (generated_binophrel_hrel R) (isbinophrel_generated_binophrel R).

Lemma generated_binophrel_intro {X : setwithbinop} {R : hrel X} {x x' : X}
      (r : R x x') : generated_binophrel R x x'.
Proof.
  intros R' H. exact (H x x' r).
Defined.

(* The binopeqrel generated by an arbitrary hrel *)
Definition generated_binopeqrel_hrel {X : setwithbinop} (R : hrel X) : hrel X :=
  λ x x',  ∀(R' : binopeqrel X), (∏ x₁ x₂, R x₁ x₂ → R' x₁ x₂) ⇒ R' x x'.

Lemma isbinophrel_generated_binopeqrel {X : setwithbinop} (R : hrel X) :
  isbinophrel (generated_binopeqrel_hrel R).
Proof.
  split.
  - intros a b c H R' H2. apply binopeqrel_resp_left. exact (H R' H2).
  - intros a b c H R' H2. apply binopeqrel_resp_right. exact (H R' H2).
Defined.

Lemma iseqrel_generated_binopeqrel {X : setwithbinop} (R : hrel X) :
  iseqrel (generated_binopeqrel_hrel R).
Proof.
  use iseqrelconstr.
  - intros x1 x2 x3 H1 H2 R' HR. eapply eqreltrans.
    + exact (H1 R' HR).
    + exact (H2 R' HR).
  - intros x R' HR. apply eqrelrefl.
  - intros x1 x2 H R' HR. apply eqrelsymm. exact (H R' HR).
Defined.

Definition generated_binopeqrel {X : setwithbinop} (R : hrel X) : binopeqrel X :=
  make_binopeqrel (make_eqrel (generated_binopeqrel_hrel R) (iseqrel_generated_binopeqrel R))
                 (isbinophrel_generated_binopeqrel R).

Lemma generated_binopeqrel_intro {X : setwithbinop} {R : hrel X} {x x' : X}
      (r : R x x') : generated_binopeqrel R x x'.
Proof.
  intros R' H. exact (H x x' r).
Defined.

(* A proof that homomorphisms preserve the generated relations if they preserve the original one *)
Definition pullback_binopeqrel {X Y : setwithbinop} (f : binopfun X Y) (R : binopeqrel Y) :
  binopeqrel X.
Proof.
  use make_binopeqrel.
  - use make_eqrel.
    + intros x x'. exact (R (f x) (f x')).
    + apply iseqrelconstr.
      * intros x1 x2 x3 r1 r2. exact (eqreltrans R _ _ _ r1 r2).
      * intro x. exact (eqrelrefl R _).
      * intros x x' r. exact (eqrelsymm R _ _ r).
  - apply make_isbinophrel; simpl; intros x1 x2 x3 r; rewrite !binopfunisbinopfun.
    + exact (binopeqrel_resp_left R _ r).
    + exact (binopeqrel_resp_right R _ r).
Defined.

Definition pullback_binopeqrel_rev {X Y : setwithbinop} (f : binopfun X (setwithbinop_rev Y))
           (R : binopeqrel Y) : binopeqrel X.
Proof.
  apply (pullback_binopeqrel f). use make_binopeqrel.
  - exact R.
  - apply make_isbinophrel; intros x1 x2 x3 r; apply (pr2 R); exact r.
Defined.

Definition binopeqrel_eq (X : setwithbinop) : binopeqrel X.
Proof.
  use make_binopeqrel.
  - use make_eqrel.
    + intros x x'. exact (make_hProp (x = x') (pr2 (pr1 X) _ _)).
    + apply iseqrelconstr.
      * intros x1 x2 x3 r1 r2. exact (r1 @ r2).
      * intro x. reflexivity.
      * intros x x' r. exact (!r).
  - apply make_isbinophrel; simpl; intros x1 x2 x3 r; rewrite r; reflexivity.
Defined.

Definition binopeqrel_of_binopfun {X Y : setwithbinop} (f : binopfun X Y) : binopeqrel X :=
  pullback_binopeqrel f (binopeqrel_eq Y).

Lemma iscomprelfun_generated_binopeqrel {X Y : setwithbinop} {R : hrel X} (f : binopfun X Y)
      (H : iscomprelfun R f) : iscomprelfun (generated_binopeqrel R) f.
Proof.
  intros x x' r. exact (r (binopeqrel_of_binopfun f) H).
Defined.

Lemma iscomprelrelfun_generated_binopeqrel {X Y : setwithbinop} {R : hrel X} {S : hrel Y}
      (f : binopfun X Y) (H : iscomprelrelfun R S f) :
  iscomprelrelfun (generated_binopeqrel R) (generated_binopeqrel S) f.
Proof.
  intros x x' r. apply (r (pullback_binopeqrel f (generated_binopeqrel S))).
  intros x1 x2 r' S' s. use s. apply H. exact r'.
Defined.

(* It is also true for "contravariant" homomorphisms, where f (x * y) = f y * f x *)
Lemma iscomprelrelfun_generated_binopeqrel_rev {X Y : setwithbinop} {R : hrel X} {S : hrel Y}
      (f : binopfun X (setwithbinop_rev Y)) (H : iscomprelrelfun R S f) :
  iscomprelrelfun (generated_binopeqrel R) (generated_binopeqrel S) f.
Proof.
  intros x x' r. apply (r (pullback_binopeqrel_rev f (generated_binopeqrel S))).
  intros x1 x2 r' S' s. use s. apply H. exact r'.
Defined.

(** * 3.6. Relations inversely compatible with a binary operation *)

Definition isinvbinophrel {X : setwithbinop} (R : hrel X) : UU :=
  (∏ a b c : X, R (op c a) (op c b) →  R a b) × (∏ a b c : X, R (op a c) (op b c) → R a b).

Definition isinvbinophrellogeqf {X : setwithbinop} {L R : hrel X} (lg : hrellogeq L R)
           (isl : isinvbinophrel L) : isinvbinophrel R.
Proof.
  split.
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ (pr2 (lg  _ _) rab)))).
  - intros a b c rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ (pr2 (lg  _ _) rab)))).
Defined.

Lemma isapropisinvbinophrel {X : setwithbinop} (R : hrel X) : isaprop (isinvbinophrel R).
Proof.
  apply isapropdirprod.
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
  - apply impred. intro a.
    apply impred. intro b.
    apply impred. intro c.
    apply impred. intro r.
    apply (pr2 (R _ _)).
Defined.

Lemma isinvbinophrelif {X : setwithbinop} (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X,  R (op c a) (op c b) → R a b) : isinvbinophrel R.
Proof.
  exists isl. intros a b c rab.
  induction (is c a). induction (is c b).
  apply (isl _ _ _ rab).
Defined.

Definition ispartinvbinophrel {X : setwithbinop} (S : hsubtype X) (R : hrel X) : UU :=
  (∏ a b c : X, S c → R (op c a) (op c b) → R a b) ×
  (∏ a b c : X, S c → R (op a c) (op b c) → R a b).

Definition isinvbinoptoispartinvbinop {X : setwithbinop} (S : hsubtype X) (L : hrel X)
           (d2 : isinvbinophrel L) : ispartinvbinophrel S L.
Proof.
  unfold isinvbinophrel in d2. unfold ispartinvbinophrel.
  split.
  - intros a b c s. apply (pr1 d2 a b c).
  - intros a b c s. apply (pr2 d2 a b c).
Defined.

Definition ispartinvbinophrellogeqf {X : setwithbinop} (S : hsubtype X) {L R : hrel X}
           (lg : hrellogeq L R) (isl : ispartinvbinophrel S L) : ispartinvbinophrel S R.
Proof.
  split.
  - intros a b c s rab.
    apply ((pr1 (lg _ _) ((pr1 isl) _ _ _ s (pr2 (lg  _ _) rab)))).
  - intros a b c s rab.
    apply ((pr1 (lg _ _) ((pr2 isl) _ _ _ s (pr2 (lg  _ _) rab)))).
Defined.

Lemma ispartinvbinophrelif {X : setwithbinop} (S : hsubtype X) (R : hrel X) (is : iscomm (@op X))
      (isl : ∏ a b c : X, S c → R (op c a) (op c b) → R a b) : ispartinvbinophrel S R.
Proof.
  exists isl. intros a b c s rab.
  induction (is c a). induction (is c b).
  apply (isl _ _ _ s rab).
Defined.


(** * 3.7. Homomorphisms and relations *)

Lemma binophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (R : hrel Y) (is : @isbinophrel Y R) :
  @isbinophrel X (λ x x', R (f x) (f x')).
Proof.
  set (ish := (pr2 f) : ∏ a0 b0, f (op a0 b0) = op (f a0) (f b0)).
  split.
  - intros a b c r. rewrite (ish _ _). rewrite (ish _ _).
    apply (pr1 is). apply r.
  - intros a b c r. rewrite (ish _ _). rewrite (ish _ _).
    apply (pr2 is). apply r.
Defined.

Lemma ispartbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (SX : hsubtype X)
      (SY : hsubtype Y) (iss : ∏ x : X, (SX x) → (SY (f x))) (R : hrel Y)
      (is : @ispartbinophrel Y SY R) : @ispartbinophrel X SX (λ x x', R (f x) (f x')).
Proof.
  set (ish := (pr2 f) : ∏ a0 b0, f (op a0 b0) = op (f a0) (f b0)).
  split.
  - intros a b c s r. rewrite (ish _ _). rewrite (ish _ _).
    apply ((pr1 is) _ _ _ (iss _ s) r).
  - intros a b c s r. rewrite (ish _ _). rewrite (ish _ _).
    apply ((pr2 is) _ _ _ (iss _ s) r).
Defined.

Lemma invbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (R : hrel Y)
      (is : @isinvbinophrel Y R) : @isinvbinophrel X (λ x x', R (f x) (f x')).
Proof.
  set (ish := (pr2 f) : ∏ a0 b0, f (op a0 b0) = op (f a0) (f b0)).
  split.
  - intros a b c r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr1 is) _ _ _ r).
  - intros a b c r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr2 is) _ _ _ r).
Defined.

Lemma ispartinvbinophrelandfun {X Y : setwithbinop} (f : binopfun X Y) (SX : hsubtype X)
      (SY : hsubtype Y) (iss : ∏ x : X, (SX x) → (SY (f x))) (R : hrel Y)
      (is : @ispartinvbinophrel Y SY R) : @ispartinvbinophrel X SX (λ x x', R (f x) (f x')).
Proof.
  set (ish := (pr2 f) : ∏ a0 b0, f (op a0 b0) = op (f a0) (f b0)).
  split.
  - intros a b c s r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr1 is) _ _ _ (iss _ s) r).
  - intros a b c s r. rewrite (ish _ _) in r. rewrite (ish _ _) in r.
    apply ((pr2 is) _ _ _ (iss _ s) r).
Defined.


(** * 3.8. Quotient relations *)

Lemma isbinopquotrel {X : setwithbinop} (R : binopeqrel X) {L : hrel X} (is : iscomprelrel R L)
      (isl : isbinophrel L) : @isbinophrel (setwithbinopquot R) (quotrel is).
Proof.
  unfold isbinophrel. split.
  - assert (int : ∏ (a b c : setwithbinopquot R),
                  isaprop (quotrel is a b → quotrel is (op c a) (op c b))).
    {
      intros a b c. apply impred. intro. apply (pr2 (quotrel is _ _)).
    }
    apply (setquotuniv3prop R (λ a b c, make_hProp _ (int a b c))).
    exact (pr1 isl).
  - assert (int : ∏ (a b c : setwithbinopquot R),
                  isaprop (quotrel is a b → quotrel is (op a c) (op b c))).
    {
      intros a b c. apply impred. intro. apply (pr2 (quotrel is _ _)).
    }
    apply (setquotuniv3prop R (λ a b c, make_hProp _ (int a b c))).
    exact (pr2 isl).
Defined.

Definition iscommsetquotfun2 {X: hSet} {R : eqrel X} (f : binop X) (is : iscomprelrelfun2 R R f) (p : iscomm f) : iscomm (setquotfun2 R R f is).
Proof.
  use (setquotuniv2prop _ (λ x y ,  @eqset (setquotinset _) ((setquotfun2 _ _ _ _) x y) ((setquotfun2 _ _ _ _) y x) )).
  intros.
  cbn.
  now rewrite p.
Defined.

Definition isassocsetquotfun2 {X : hSet} {R : eqrel X} (f : binop X) (is : iscomprelrelfun2 R R f) (p : isassoc f) : isassoc (setquotfun2 R R f is).
Proof.
  set (ff := setquotfun2 _ _ _ is).
  intros ? ? ?.
  use (setquotuniv3prop _ (λ x y z, @eqset (setquotinset _) (ff (ff z x) y) (ff z (ff x y)))).
  intros.
  cbn.
  now rewrite p.
Defined.

(** * 3.9. Direct products *)

Definition setwithbinopdirprod (X Y : setwithbinop) : setwithbinop.
Proof.
  exists (setdirprod X Y). unfold binop. simpl.
  (* ??? in 8.4-8.5-trunk the following apply generates an error message if the
     type of xy and xy' is left as _ despite the fact that the type of goal is
     X × Y → X × Y →.. *)
  apply (λ xy xy' : X × Y, op (pr1 xy) (pr1 xy') ,, op (pr2 xy) (pr2 xy')).
Defined.


(** * 4. Sets with two binary operations *)

(** * 4.1. General definitions *)

Definition setwith2binop : UU := ∑ (X : hSet), (binop X) × (binop X).

Definition make_setwith2binop (X : hSet) (opps : (binop X) × (binop X)) :
  setwith2binop := X ,, opps.

Definition pr1setwith2binop : setwith2binop → hSet :=
  @pr1 _ (λ X : hSet, (binop X) × (binop X)).
Coercion pr1setwith2binop : setwith2binop >-> hSet.

Definition op1 {X : setwith2binop} : binop X := pr1 (pr2 X).

Definition op2 {X : setwith2binop} : binop X := pr2 (pr2 X).

Definition setwithbinop1 (X : setwith2binop) : setwithbinop := make_setwithbinop (pr1 X) (@op1 X).

Definition setwithbinop2 (X : setwith2binop) : setwithbinop := make_setwithbinop (pr1 X) (@op2 X).

Declare Scope twobinops_scope.
Notation "x + y" := (op1 x y) : twobinops_scope.
Notation "x * y" := (op2 x y) : twobinops_scope.

Definition isasettwobinoponhSet (X : hSet) : isaset ((binop X) × (binop X)).
Proof.
  use isasetdirprod.
  - use isasetbinoponhSet.
  - use isasetbinoponhSet.
Qed.


(** * 4.2. Functions compatible with a pair of binary operation (homomorphisms) and their properties *)

Definition istwobinopfun {X Y : setwith2binop} (f : X → Y) : UU :=
  (∏ x x' : X, f (op1 x x') = op1 (f x) (f x')) ×
  (∏ x x' : X, f (op2 x x') = op2 (f x) (f x')).

Definition make_istwobinopfun {X Y : setwith2binop} (f : X → Y)
           (H1 : ∏ x x' : X, f (op1 x x') = op1 (f x) (f x'))
           (H2 : ∏ x x' : X, f (op2 x x') = op2 (f x) (f x')) :
  istwobinopfun f := H1 ,, H2.

Lemma isapropistwobinopfun {X Y : setwith2binop} (f : X → Y) : isaprop (istwobinopfun f).
Proof.
  apply isofhleveldirprod.
  - apply impred. intro x.
    apply impred. intro x'.
    apply (setproperty Y).
  - apply impred. intro x.
    apply impred. intro x'.
    apply (setproperty Y).
Defined.

Definition twobinopfun (X Y : setwith2binop) : UU := ∑ (f : X → Y), istwobinopfun f.

Definition make_twobinopfun {X Y : setwith2binop} (f : X → Y) (is : istwobinopfun f) :
  twobinopfun X Y := f ,, is.

Definition pr1twobinopfun (X Y : setwith2binop) : twobinopfun X Y → (X → Y) := @pr1 _ _.
Coercion pr1twobinopfun : twobinopfun >-> Funclass.

Definition binop1fun {X Y : setwith2binop} (f : twobinopfun X Y) :
  binopfun (setwithbinop1 X) (setwithbinop1 Y) :=
  @make_binopfun (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2fun {X Y : setwith2binop} (f : twobinopfun X Y) :
  binopfun (setwithbinop2 X) (setwithbinop2 Y) :=
  @make_binopfun (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopfun_paths {X Y : setwith2binop} (f g : twobinopfun X Y)
           (e : pr1 f = pr1 g) : f = g.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropistwobinopfun.
Qed.

Lemma isasettwobinopfun  (X Y : setwith2binop) : isaset (twobinopfun X Y).
Proof.
  apply (isasetsubset (pr1twobinopfun X Y)).
  - change (isofhlevel 2 (X → Y)).
    apply impred. intro. apply (setproperty Y).
  - refine (isinclpr1 _ _). intro. apply isapropistwobinopfun.
Qed.

Lemma istwobinopfuncomp {X Y Z : setwith2binop} (f : twobinopfun X Y) (g : twobinopfun Y Z) :
  istwobinopfun (pr1 g ∘ pr1 f).
Proof.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  set (ax1g := pr1 (pr2 g)). set (ax2g := pr2 (pr2 g)).
  split.
  - intros a b. simpl.
    rewrite (ax1f a b). rewrite (ax1g (pr1 f a) (pr1 f b)).
    apply idpath.
  - intros a b. simpl.
    rewrite (ax2f a b). rewrite (ax2g (pr1 f a) (pr1 f b)).
    apply idpath.
Qed.

Definition twobinopfuncomp {X Y Z : setwith2binop} (f : twobinopfun X Y) (g : twobinopfun Y Z) :
  twobinopfun X Z := make_twobinopfun (g ∘ f) (istwobinopfuncomp f g).

Definition twobinopmono (X Y : setwith2binop) : UU := ∑ (f : incl X Y), istwobinopfun f.

Definition make_twobinopmono {X Y : setwith2binop} (f : incl X Y) (is : istwobinopfun f) :
  twobinopmono X Y := f ,, is.

Definition pr1twobinopmono (X Y : setwith2binop) : twobinopmono X Y → incl X Y := @pr1 _ _.
Coercion pr1twobinopmono : twobinopmono >-> incl.

Definition twobinopincltotwobinopfun (X Y : setwith2binop) :
  twobinopmono X Y → twobinopfun X Y := λ f, make_twobinopfun (pr1 (pr1 f)) (pr2 f).
Coercion twobinopincltotwobinopfun : twobinopmono >-> twobinopfun.

Definition binop1mono {X Y : setwith2binop} (f : twobinopmono X Y) :
  binopmono (setwithbinop1 X) (setwithbinop1 Y) :=
  @make_binopmono (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2mono {X Y : setwith2binop} (f : twobinopmono X Y) :
  binopmono (setwithbinop2 X) (setwithbinop2 Y) :=
  @make_binopmono (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopmonocomp {X Y Z : setwith2binop} (f : twobinopmono X Y) (g : twobinopmono Y Z) :
  twobinopmono X Z := make_twobinopmono (inclcomp (pr1 f) (pr1 g)) (istwobinopfuncomp f g).

Definition twobinopiso (X Y : setwith2binop) : UU := ∑ (f : X ≃ Y), istwobinopfun f.

Definition make_twobinopiso {X Y : setwith2binop} (f : X ≃ Y) (is : istwobinopfun f) :
  twobinopiso X Y := f ,, is.

Definition pr1twobinopiso (X Y : setwith2binop) : twobinopiso X Y → X ≃ Y := @pr1 _ _.
Coercion pr1twobinopiso : twobinopiso >-> weq.

Definition twobinopisototwobinopmono (X Y : setwith2binop) :
  twobinopiso X Y → twobinopmono X Y := λ f, make_twobinopmono (weqtoincl (pr1 f)) (pr2 f).
Coercion twobinopisototwobinopmono : twobinopiso >-> twobinopmono.

Definition twobinopisototwobinopfun {X Y : setwith2binop} (f : twobinopiso X Y) :
  twobinopfun X Y := make_twobinopfun f (pr2 f).

Lemma twobinopiso_paths {X Y : setwith2binop} (f g : twobinopiso X Y) (e : pr1 f = pr1 g) : f = g.
Proof.
  use total2_paths_f.
  - exact e.
  - use proofirrelevance. use isapropistwobinopfun.
Qed.

Definition binop1iso {X Y : setwith2binop} (f : twobinopiso X Y) :
  binopiso (setwithbinop1 X) (setwithbinop1 Y) :=
  @make_binopiso (setwithbinop1 X) (setwithbinop1 Y) (pr1 f) (pr1 (pr2 f)).

Definition binop2iso {X Y : setwith2binop} (f : twobinopiso X Y) :
  binopiso (setwithbinop2 X) (setwithbinop2 Y) :=
  @make_binopiso (setwithbinop2 X) (setwithbinop2 Y) (pr1 f) (pr2 (pr2 f)).

Definition twobinopisocomp {X Y Z : setwith2binop} (f : twobinopiso X Y) (g : twobinopiso Y Z) :
  twobinopiso X Z := make_twobinopiso (weqcomp (pr1 f) (pr1 g)) (istwobinopfuncomp f g).

Lemma istwobinopfuninvmap {X Y : setwith2binop} (f : twobinopiso X Y) :
  istwobinopfun (invmap (pr1 f)).
Proof.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  split.
  - intros a b. apply (invmaponpathsweq (pr1 f)).
    rewrite (homotweqinvweq (pr1 f) (op1 a b)).
    rewrite (ax1f (invmap (pr1 f) a) (invmap (pr1 f) b)).
    rewrite (homotweqinvweq (pr1 f) a).
    rewrite (homotweqinvweq (pr1 f) b).
    apply idpath.
  - intros a b. apply (invmaponpathsweq (pr1 f)).
    rewrite (homotweqinvweq (pr1 f) (op2 a b)).
    rewrite (ax2f (invmap (pr1 f) a) (invmap (pr1 f) b)).
    rewrite (homotweqinvweq (pr1 f) a).
    rewrite (homotweqinvweq (pr1 f) b).
    apply idpath.
Qed.

Definition invtwobinopiso {X Y : setwith2binop} (f : twobinopiso X Y) :
  twobinopiso Y X := make_twobinopiso (invweq (pr1 f)) (istwobinopfuninvmap f).

Definition idtwobinopiso (X : setwith2binop) : twobinopiso X X.
Proof.
  use make_twobinopiso.
  - use (idweq X).
  - use make_istwobinopfun.
    + intros x x'. use idpath.
    + intros x x'. use idpath.
Defined.


(** **** X = Y ≃ (X ≃ Y)
   The idea is to use the composition X = Y ≃ X ╝ Y ≃ (twobinopiso X Y)
*)

Definition setwith2binop_univalence_weq1 (X Y : setwith2binop) : (X = Y) ≃ (X ╝ Y) :=
  total2_paths_equiv _ X Y.

Definition setwith2binop_univalence_weq2 (X Y : setwith2binop) : (X ╝ Y) ≃ (twobinopiso X Y).
Proof.
  use weqbandf.
  - use hSet_univalence.
  - intros e. use invweq. induction X as [X Xop]. induction Y as [Y Yop]. cbn in e.
    induction e. use weqimplimpl.
    + intros i.
      use dirprod_paths.
      * use funextfun. intros x1.
        use funextfun. intros x2.
        exact ((dirprod_pr1 i) x1 x2).
      * use funextfun. intros x1.
        use funextfun. intros x2.
        exact ((dirprod_pr2 i) x1 x2).
    + intros e. cbn in e.
      use make_istwobinopfun.
      * intros x1 x2. induction e. use idpath.
      * intros x1 x2. induction e. use idpath.
    + use isapropistwobinopfun.
    + use isasettwobinoponhSet.
Defined.
Opaque setwith2binop_univalence_weq2.

Definition setwith2binop_univalence_map (X Y : setwith2binop) : X = Y → twobinopiso X Y.
Proof.
  intro e. induction e. exact (idtwobinopiso X).
Defined.

Lemma setwith2binop_univalence_isweq (X Y : setwith2binop) :
  isweq (setwith2binop_univalence_map X Y).
Proof.
  use isweqhomot.
  - exact (weqcomp (setwith2binop_univalence_weq1 X Y) (setwith2binop_univalence_weq2 X Y)).
  - intros e. induction e. use weqcomp_to_funcomp_app.
  - use weqproperty.
Defined.
Opaque setwith2binop_univalence_isweq.

Definition setwith2binop_univalence (X Y : setwith2binop) : (X = Y) ≃ (twobinopiso X Y)
  := make_weq
    (setwith2binop_univalence_map X Y)
    (setwith2binop_univalence_isweq X Y).


(** * 4.3. Transport of properties of a pair of binary operations *)

Lemma isldistrmonob {X Y : setwith2binop} (f : twobinopmono X Y) (is : isldistr (@op1 Y) (@op2 Y)) :
  isldistr (@op1 X) (@op2 X).
Proof.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  intros a b c. apply (invmaponpathsincl _ (pr2 (pr1 f))).
  change ((pr1 f) (op2 c (op1 a b)) = (pr1 f) (op1 (op2 c a) (op2 c b))).
  rewrite (ax2f c (op1 a b)).
  rewrite (ax1f a b).
  rewrite (ax1f (op2 c a) (op2 c b)).
  rewrite (ax2f c a).
  rewrite (ax2f c b).
  apply is.
Qed.

Lemma isrdistrmonob {X Y : setwith2binop} (f : twobinopmono X Y)
      (is : isrdistr (@op1 Y) (@op2 Y)) : isrdistr (@op1 X) (@op2 X).
Proof.
  set (ax1f := pr1 (pr2 f)). set (ax2f := pr2 (pr2 f)).
  intros a b c.
  apply (invmaponpathsincl _ (pr2 (pr1 f))).
  change ((pr1 f) (op2 (op1 a b) c) = (pr1 f) (op1 (op2 a c) (op2 b c))).
  rewrite (ax2f (op1 a b) c).
  rewrite (ax1f a b).
  rewrite (ax1f (op2 a c) (op2 b c)).
  rewrite (ax2f a c).
  rewrite (ax2f b c).
  apply is.
Qed.

Definition isdistrmonob {X Y : setwith2binop} (f : twobinopmono X Y)
           (is : isdistr (@op1 Y) (@op2 Y)) :
  isdistr (@op1 X) (@op2 X) := isldistrmonob f (pr1 is) ,, isrdistrmonob f (pr2 is).

Notation isldistrisob := isldistrmonob.
Notation isrdistrisob := isrdistrmonob.
Notation isdistrisob := isdistrmonob.

Lemma isldistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isldistr (@op1 X) (@op2 X)) :
  isldistr (@op1 Y) (@op2 Y).
Proof.
  apply (isldistrisob (invtwobinopiso f) is).
Defined.

Lemma isrdistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isrdistr (@op1 X) (@op2 X)) :
  isrdistr (@op1 Y) (@op2 Y).
Proof.
  apply (isrdistrisob (invtwobinopiso f) is).
Defined.

Lemma isdistrisof {X Y : setwith2binop} (f : twobinopiso X Y) (is : isdistr (@op1 X) (@op2 X)) :
  isdistr (@op1 Y) (@op2 Y).
Proof.
  apply (isdistrisob (invtwobinopiso f) is).
Defined.

Definition isrigopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrigops (@op1 X) (@op2 X)) : isrigops (@op1 Y) (@op2 Y).
Proof.
  split.
  - exists (isabmonoidopisof (binop1iso f) (rigop1axs_is is) ,,
                            ismonoidopisof (binop2iso f) (rigop2axs_is is)).
    simpl.
    change (unel_is (ismonoidopisof (binop1iso f) (rigop1axs_is is)))
    with ((pr1 f) (rigunel1_is is)).
    split.
    + intro y.
      rewrite <- (homotweqinvweq f y).
      rewrite <- ((pr2 (pr2 f)) _ _).
      apply (maponpaths (pr1 f)). apply (rigmult0x_is is).
    + intro y.
      rewrite <- (homotweqinvweq f y).
      rewrite <- ((pr2 (pr2 f)) _ _).
      apply (maponpaths (pr1 f)).
      apply (rigmultx0_is is).
  - apply (isdistrisof f). apply (rigdistraxs_is is).
Defined.

Definition isrigopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isrigops (@op1 Y) (@op2 Y)) : isrigops (@op1 X) (@op2 X).
Proof.
  apply (isrigopsisof (invtwobinopiso f) is).
Defined.

Definition isringopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isringops (@op1 X) (@op2 X)) : isringops (@op1 Y) (@op2 Y) :=
    (isabgropisof (binop1iso f) (ringop1axs_is is) ,,
    ismonoidopisof (binop2iso f) (ringop2axs_is is)) ,,
    isdistrisof f (pr2 is).

Definition isringopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : isringops (@op1 Y) (@op2 Y)) : isringops (@op1 X) (@op2 X) :=
  (isabgropisob (binop1iso f) (ringop1axs_is is) ,,
  ismonoidopisob (binop2iso f) (ringop2axs_is is)) ,,
  isdistrisob f (pr2 is).

Definition iscommringopsisof {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : iscommringops (@op1 X) (@op2 X)) : iscommringops (@op1 Y) (@op2 Y) :=
  isringopsisof f is ,, iscommisof (binop2iso f) (pr2 is).

Definition iscommringopsisob {X Y : setwith2binop} (f : twobinopiso X Y)
           (is : iscommringops (@op1 Y) (@op2 Y)) : iscommringops (@op1 X) (@op2 X) :=
  isringopsisob f is ,, iscommisob (binop2iso f) (pr2 is).


(** * 4.4. Subobjects *)

Definition issubsetwith2binop {X : setwith2binop} (A : hsubtype X) : UU :=
  (∏ a a' : A, A (op1 (pr1 a) (pr1 a'))) × (∏ a a' : A, A (op2 (pr1 a) (pr1 a'))).

Lemma isapropissubsetwith2binop {X : setwith2binop} (A : hsubtype X) :
  isaprop (issubsetwith2binop A).
Proof.
  apply (isofhleveldirprod 1).
  - apply impred. intro a.
    apply impred. intros a'.
    apply (pr2 (A (op1 (pr1 a) (pr1 a')))).
  - apply impred. intro a.
    apply impred. intros a'.
    apply (pr2 (A (op2 (pr1 a) (pr1 a')))).
Defined.

Definition subsetswith2binop (X : setwith2binop) : UU :=
  ∑ (A : hsubtype X), issubsetwith2binop A.

Definition make_subsetswith2binop {X : setwith2binop} (t : hsubtype X) (H : issubsetwith2binop t)
  : subsetswith2binop X
  := t ,, H.

Definition subsetswith2binopconstr {X : setwith2binop} :
  ∏ (t : hsubtype X), (λ A : hsubtype X, issubsetwith2binop A) t →
                       ∑ A : hsubtype X, issubsetwith2binop A :=
  @make_subsetswith2binop X.

Definition pr1subsetswith2binop (X : setwith2binop) : subsetswith2binop X → hsubtype X :=
  @pr1 _ (λ A : hsubtype X, issubsetwith2binop A).
Coercion pr1subsetswith2binop : subsetswith2binop >-> hsubtype.

Definition totalsubsetwith2binop (X : setwith2binop) : subsetswith2binop X.
Proof.
  exists (λ x : X, htrue). split.
  - intros x x'. apply tt.
  - intros. apply tt.
Defined.

Definition carrierofsubsetwith2binop {X : setwith2binop} (A : subsetswith2binop X) : setwith2binop.
Proof.
  set (aset := (make_hSet (carrier A) (isasetsubset (pr1carrier A) (setproperty X)
                                                   (isinclpr1carrier A))) : hSet).
  exists aset.
  set (subopp1 := (λ a a' : A, make_carrier A (op1 (pr1carrier _ a) (pr1carrier _ a'))
                                            (pr1 (pr2 A) a a')) : (A → A → A)).
  set (subopp2 := (λ a a' : A, make_carrier A (op2 (pr1carrier _ a) (pr1carrier _ a'))
                                            (pr2 (pr2 A) a a')) : (A → A → A)).
  simpl. exact (subopp1 ,, subopp2).
Defined.
Coercion carrierofsubsetwith2binop : subsetswith2binop >-> setwith2binop.


(** * 4.5. Quotient objects *)

Definition is2binophrel {X : setwith2binop} (R : hrel X) : UU :=
  (@isbinophrel (setwithbinop1 X) R) × (@isbinophrel (setwithbinop2 X) R).

Lemma isapropis2binophrel {X : setwith2binop} (R : hrel X) : isaprop (is2binophrel R).
Proof.
  apply (isofhleveldirprod 1).
  - apply isapropisbinophrel.
  - apply isapropisbinophrel.
Defined.

Lemma iscomp2binoptransrel {X : setwith2binop} (R : hrel X) (is : istrans R)
      (isb : is2binophrel R) :
  (iscomprelrelfun2 R R (@op1 X)) × (iscomprelrelfun2 R R (@op2 X)).
Proof.
  split.
  - apply (@iscompbinoptransrel (setwithbinop1 X) R is (pr1 isb)).
  - apply (@iscompbinoptransrel (setwithbinop2 X) R is (pr2 isb)).
Defined.

Definition twobinophrel (X : setwith2binop) : UU := ∑ (R : hrel X), is2binophrel R.

Definition make_twobinophrel {X : setwith2binop} (t : hrel X) (H : is2binophrel t)
  : twobinophrel X
  := t ,, H.

Definition pr1twobinophrel (X : setwith2binop) : twobinophrel X → hrel X :=
  @pr1 _ (λ R : hrel X, is2binophrel R).
Coercion pr1twobinophrel : twobinophrel >-> hrel.

Definition twobinoppo (X : setwith2binop) : UU := ∑ (R : po X), is2binophrel R.

Definition make_twobinoppo {X : setwith2binop} (t : po X) (H : is2binophrel t)
  : twobinoppo X
  := t ,, H.

Definition pr1twobinoppo (X : setwith2binop) : twobinoppo X → po X :=
  @pr1 _ (λ R : po X, is2binophrel R).
Coercion pr1twobinoppo : twobinoppo >-> po.

Definition twobinopeqrel (X : setwith2binop) : UU := ∑ (R : eqrel X), is2binophrel R.

Definition make_twobinopeqrel {X : setwith2binop} (t : eqrel X) (H : is2binophrel t)
  : twobinopeqrel X
  := t ,, H.

Definition pr1twobinopeqrel (X : setwith2binop) : twobinopeqrel X → eqrel X :=
  @pr1 _ (λ R : eqrel X, is2binophrel R).
Coercion pr1twobinopeqrel : twobinopeqrel >-> eqrel.

Definition setwith2binopquot {X : setwith2binop} (R : twobinopeqrel X) : setwith2binop.
Proof.
  exists (setquotinset R).
  set (qt := setquot R). set (qtset := setquotinset R).
  assert (iscomp1 : iscomprelrelfun2 R R (@op1 X))
    by apply (pr1 (iscomp2binoptransrel (pr1 R) (eqreltrans _) (pr2 R))).
  set (qtop1 := setquotfun2 R R (@op1 X) iscomp1).
  assert (iscomp2 : iscomprelrelfun2 R R (@op2 X))
    by apply (pr2 (iscomp2binoptransrel (pr1 R) (eqreltrans _) (pr2 R))).
  set (qtop2 := setquotfun2 R R (@op2 X) iscomp2).
  simpl. exact (qtop1 ,, qtop2).
Defined.


(** * 4.6. Direct products *)

Definition setwith2binopdirprod (X Y : setwith2binop) : setwith2binop.
Proof.
  exists (setdirprod X Y). simpl.
  (* ??? same issue as with setwithbinopdirpro above *)
  exact (
    (λ xy xy', (op1 (pr1 xy) (pr1 xy')) ,, (op1 (pr2 xy) (pr2 xy'))) ,,
    (λ xy xy', (op2 (pr1 xy) (pr1 xy')) ,, (op2 (pr2 xy) (pr2 xy')))
  ).
Defined.


(** * 5. Infinitary operations *)

(** Limit a more general infinitary operation to a binary operation *)

Lemma infinitary_op_to_binop {X : hSet} (op : ∏ I : UU, (I → X) → X) : binop X.
Proof.
  intros x y; exact (op _ (bool_rect (λ _, X) x y)).
Defined.
