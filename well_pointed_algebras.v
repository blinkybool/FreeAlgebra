(*|
The transfinite construction of a free-algebra (from a well-pointed endofunctor
in a category with ℕ-filtered colimits)

References:

* `nLab: transfinite construction of free algebras <https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras>`_
* `Max Kelly, A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on <https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/unified-treatment-of-transfinite-constructions-for-free-algebras-free-monoids-colimits-associated-sheaves-and-so-on/FE2E25E4959E4D8B4DE721718E7F55EE>`_
|*)

(*|
.. coq:: none
|*)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Subcategory.Reflective.

Local Open Scope cat.

Tactic Notation "rw_left_comp" constr(e) :=
  apply (transportb (λ x, x · _ = _) ltac:(apply e)).
Tactic Notation "rw_left_comp'" constr(e) :=
  apply (transportf (λ x, x · _ = _) ltac:(apply e)).
Tactic Notation "rw_right_comp" constr(e) :=
  apply (transportb (λ x, _ · x = _) ltac:(apply e)).
Tactic Notation "rw_right_comp'" constr(e) :=
  apply (transportf (λ x, _ · x = _) ltac:(apply e)).
Tactic Notation "rw_left" constr(e) :=
  eapply pathscomp0; [apply e|].
Tactic Notation "rw_left'" constr(e) :=
  apply (pathscomp0 ltac:(apply pathsinv0; apply e)).

(*||*)


(*|==========================
Algebra for an endofunctor
==========================|*)
Section Algebra_def. (* .none *)

Context {C : category}.

(*| An algebra for an endofunctor consists of a structure map only |*)
Definition algebra (F : C ⟶ C) : UU := ∑ X : C, F X --> X.

Definition make_algebra (F : C ⟶ C) (X : C) (s : F X --> X) : algebra F := tpair (λ X, F X --> X) X s.

#[reversible=no] Coercion alg_carrier {F : C ⟶ C} (X : algebra F) : C := pr1 X.

Definition algebra_map {F : C ⟶ C} (X : algebra F) : F X --> X := pr2 X.

(*
Morphisms of algebras are morphisms of underlying objects which are compatible with structure maps
*)
Definition algebra_mor {F : C ⟶ C} (X Y : algebra F)
  : UU
  := ∑ f : X --> Y, algebra_map X · f = #F f · algebra_map Y.

Coercion mor_from_algebra_mor {F : C ⟶ C} {X Y : algebra F} (f : algebra_mor X Y)
  : X --> Y := pr1 f.

Definition algebra_mor_commutes {F : C ⟶ C} {X Y : algebra F} (f : algebra_mor X Y)
  : algebra_map X · f = #F f · algebra_map Y
  := pr2 f.

(*| Such morphisms come with identity, composition |*)

Definition algebra_mor_id {F : C ⟶ C} (X : algebra F) : algebra_mor X X.
Proof.
  exists (identity X).
  rewrite functor_id, id_right, id_left; apply idpath.
Defined.

Definition algebra_mor_comp {F : C ⟶ C} (X Y Z : algebra F) (f : algebra_mor X Y) (g : algebra_mor Y Z)
  : algebra_mor X Z.
Proof.
  exists (f · g).
  rewrite assoc.
  rewrite algebra_mor_commutes.
  rewrite <- assoc.
  rewrite algebra_mor_commutes.
  rewrite functor_comp, assoc.
  apply idpath.
Defined.

(* Identifying morphisms of algebras is equivalent to identifying the underlying morphisms *)
Definition algebra_mor_eq {F : C ⟶ C} {X Y : algebra F} {f g : algebra_mor X Y}
  : ((f : X --> Y) = g) ≃ f = g.
Proof.
  apply invweq.
  apply subtypeInjectivity.
  intro h.
  apply homset_property.
Defined.

Definition algebra_category (F : C ⟶ C) : category.
Proof.
  use makecategory.
  - exact (algebra F).
  - exact algebra_mor.
  - intros X Y.
    apply (isofhleveltotal2 2). { apply homset_property. }
    intros f. apply isasetaprop. apply homset_property.
  - exact algebra_mor_id.
  - exact algebra_mor_comp.
  - intros. apply algebra_mor_eq. apply id_left.
  - intros. apply algebra_mor_eq. apply id_right.
  - intros. apply algebra_mor_eq. apply assoc.
  - intros. apply algebra_mor_eq, pathsinv0. apply assoc.
Defined.

End Algebra_def.

(*|
A pointed endofunctor F comes with a natural transformation 1 ⟹ F
|*)
Definition pointed_endofunctor (C : category) : UU := ∑ F : C ⟶ C, functor_identity C ⟹ F.

#[reversible=no] Coercion pointed_endofunctor_endofunctor {C : category} (X : pointed_endofunctor C) : C ⟶ C := pr1 X.

Definition make_pointed_endofunctor {C : category} (F : C ⟶ C) (σ : functor_identity C ⟹ F) : pointed_endofunctor C := tpair _ F σ.

(*| 
The *point* of a pointed endofunctor.
Usually set σ := point F
|*)
Definition point {C : category} (F : pointed_endofunctor C) : functor_identity C ⟹ F := pr2 F.

Definition point_naturality {C : category} (F : pointed_endofunctor C) {x y : C} (f : x --> y)
  : (f · point F y = point F x · # F f).
Proof.
  apply (nat_trans_ax (point F)).
Defined.

(*| 
  A well-pointed functor satisfies Fσ = σF, i.e. for every c : C, the two
  ways of constructing a morphism F c --> F (F c) coincide.
  Can be seen as a way to simplify the component of σ at (F c).
|*)
Definition well_pointed {C : category} (F : pointed_endofunctor C) :=
  let σ := point F
  in ∏ c : C,σ (F c) =  #F (σ c).

Definition well_pointed_endofunctor (C : category) : UU := ∑ F : pointed_endofunctor C, well_pointed F.

#[reversible=no] Coercion well_pointed_endofunctor_pointed_endofunctor {C : category} (X : well_pointed_endofunctor C) : pointed_endofunctor C := pr1 X.

Definition well_pointed_endofunctor_ax {C : category} (F : well_pointed_endofunctor C) : well_pointed F := pr2 F.

(*| A pointed algebra for a pointed endofunctor is an algebra (a : F X --> X)
  for the endofunctor which is a retraction of the point map (σ_X · a = id_X)
|*)
Definition pointed_algebra {C : category} (F : pointed_endofunctor C) : UU :=
  let σ := point F
  in ∑ X : algebra F, (σ X) · (algebra_map X) = identity X.

Definition make_pointed_algebra {C : category} (F : pointed_endofunctor C) (X : C) (s : F X --> X) (retracts_point : (point F X) · s = identity X)
  : pointed_algebra F
  := (make_algebra F X s,, retracts_point).

Coercion algebra_from_pointed_algebra {C : category} (F : pointed_endofunctor C) (X : pointed_algebra F) : algebra F := pr1 X.

Definition pointed_algebra_ax {C : category} {F : pointed_endofunctor C} (X : pointed_algebra F) : (point F X) · (algebra_map X) = identity X := pr2 X.

(*| A monad algebra for a monad is an algebra equipped with unit and multiplication laws (cf. pointed_algebra) |*)
Definition monad_algebra {C : category} (T : Monad C) : UU := ∑ X : algebra T,
  identity X = (η T X) · (algebra_map X) ×
  μ T X · algebra_map X = #T (algebra_map X) · algebra_map X.

Coercion algebra_from_monad_algebra {C : category} (T : Monad C) (X : monad_algebra T) : algebra T := pr1 X.

Definition pointed_algebra_category {C : category} (F : pointed_endofunctor C) : category.
Proof.
  use makecategory.
  - exact (pointed_algebra F).
  - intros X Y. exact (algebra_mor X Y).
  - intros X Y.
    apply (isofhleveltotal2 2). { apply homset_property. }
    intros f. apply isasetaprop. apply homset_property.
  - intros. apply algebra_mor_id.
  - intros X Y Z. exact (algebra_mor_comp X Y Z).
  - intros. apply algebra_mor_eq. apply id_left.
  - intros. apply algebra_mor_eq. apply id_right.
  - intros. apply algebra_mor_eq. apply assoc.
  - intros. apply algebra_mor_eq. refine (!(_)). apply assoc.
Defined.

Definition monad_algebra_category {C : category} (T : Monad C) : category.
Proof.
  use makecategory.
  - exact (monad_algebra T).
  - intros X Y. exact (algebra_mor X Y).
  - intros X Y.
    apply (isofhleveltotal2 2). { apply homset_property. }
    intros f. apply isasetaprop. apply homset_property.
  - intros. apply algebra_mor_id.
  - intros X Y Z. exact (algebra_mor_comp X Y Z).
  - intros. apply algebra_mor_eq. apply id_left.
  - intros. apply algebra_mor_eq. apply id_right.
  - intros. apply algebra_mor_eq. apply assoc.
  - intros. apply algebra_mor_eq. refine (!(_)). apply assoc.
Defined.

Definition algebraically_free {C : category} (F : C ⟶ C) (T : Monad C)
  : UU
  := equivalence_of_cats (monad_algebra_category T) (algebra_category F).

(*|
======================================
Algebras for well-pointed endofunctors
======================================
The notion of algebra for a pointed endofunctor F involves adding
*structure* to a carrier object X : C, i.e. a map F X --> X which is a retraction
of the point at X, σ_X : X --> F X.
Here we discover that when F is well-pointed, such a map is also a section of
σ_X, and so this structure degenerates to a *property* of X, i.e. is σ_X iso?

In fact, this makes the category of pointed algebras for F into a reflective
subcategory of C. Moreover, any reflective subcategory induces a monad, for
which the underlying pointed endofunctor is well-pointed, giving us concrete
examples of well-pointed endofunctors.
|*)

Section AlgebrasWellPointed.

Context {C : category}.

(*
If X is a pointed algebra for F (well-pointed), then σ_X : X --> F X is iso.
σ_X ⋅ s = id_X is the axiom for pointed algebras
s · σ_X = id_{FX} follows from naturality and well-pointedness (with the pointed algebra axiom)
*)
Definition well_pointed_point_z_iso_at_algebra
  (F : well_pointed_endofunctor C) (X : pointed_algebra F)
  : z_iso X (F X).
Proof.
  use make_z_iso.
  - exact (point F X).
  - exact (algebra_map X).
  - split.
    + apply pointed_algebra_ax.
    + rewrite point_naturality.
      rewrite well_pointed_endofunctor_ax.
      refine (! functor_comp F _ _ @ _).
      rewrite <- functor_id.
      apply maponpaths.
      apply pointed_algebra_ax.
Defined.

(*|
There is at most one pointed algebra structure on a given X : C.
|*)
Corollary well_pointed_has_pointed_algebra_isaprop (F : well_pointed_endofunctor C)
  : ∏ A : C, isaprop (∑ a : F A --> A, (point F A) · a = identity A).
Proof.
  intros A.
  apply invproofirrelevance; red. intros [a ar] [b br].
  apply subtypeInjectivity; simpl. { intros f. apply homset_property. }
  set (point_X_iso := well_pointed_point_z_iso_at_algebra F (make_pointed_algebra F A a ar)).
  apply (pre_comp_with_z_iso_is_inj point_X_iso); simpl.
  exact (ar @ ! br).
Defined.

(*|Given pointed algebras X, Y, any f : X ⟶ Y in C is a morphism of pointed algebras|*)
Corollary mor_is_algebra_mor {F : well_pointed_endofunctor C}
  (X Y : pointed_algebra F) (f : C ⟦ X, Y ⟧)
  : algebra_map X · f = # F f · algebra_map Y.
Proof.
  set (point_X_iso := well_pointed_point_z_iso_at_algebra F X).
  apply (pre_comp_with_z_iso_is_inj point_X_iso); simpl.
  rewrite assoc, assoc.
  rw_left_comp (pointed_algebra_ax X). apply pathsinv0.
  rw_left_comp (! point_naturality F f).
  rewrite <- assoc.
  rw_right_comp (pointed_algebra_ax Y).
  rewrite id_left, id_right; apply idpath.
Defined.

(* The functor which forgets the structure map into the underlying object. *)
Definition forgetful (F : pointed_endofunctor C) : pointed_algebra_category F ⟶ C.
Proof.
  use make_functor.
  - use make_functor_data.
    + intro X. exact (alg_carrier (algebra_from_pointed_algebra F X)).
    + intros X Y f. exact (mor_from_algebra_mor f).
  - split; red; intros; apply idpath.
Defined.

(*|
For a well-pointed algebra F, its category of pointed algebras can be viewed as a subcategory
of C via the forgetful functor, because it is fully-faithful. 
|*)
Definition forgetul_fully_faithful (F : well_pointed_endofunctor C) : fully_faithful (forgetful F).
Proof.
  red. intros X Y.
  use isweq_iso; simpl.
  + exact (λ f, (f,,mor_is_algebra_mor X Y f)).
  + intros f; simpl. apply algebra_mor_eq; simpl. apply idpath.
  + intros f; simpl. apply idpath. 
Defined.

(*|
Being in the (strict) image of the forgetful functor is a proposition.
|*)
Lemma well_pointed_image_forgetful_isaprop (F : well_pointed_endofunctor C)
  : ∏ A : C, isaprop (∑ X : pointed_algebra F, forgetful F X = A).
Proof.
  intros A.
  (* We reduce to showing this proposition is equivalent to the previous one *)
  refine (isofhlevelweqf 1 _ (well_pointed_has_pointed_algebra_isaprop F A)).
  use make_weq; [|use isweq_iso].
  (* These constructions are almost definitionally inverse *)
  - intros [a ar].
    exists (make_pointed_algebra F A a ar).
    apply idpath.
  - intros [X h].
    induction h.
    exists (algebra_map X).
    apply pointed_algebra_ax.
  - intros [a p]; apply idpath.
  - intros [X h]; induction h; apply idpath.
Defined.

End AlgebrasWellPointed.

(*|
For F : C ⟶ C well-pointed, we have a fully-faithful inclusion of F-Alg into C.
We will show that F-Alg is actually reflective in C by constructing its left-adjoint,
the free pointed-algebra functor.

We handle only the Κ=ℕ case of the transfinite-construction, where C is assumed to
have Κ-filtered colimits that F preserves.
This is equivalent to C having colimits of ℕ-indexed diagrams
of the form X_0 --> X_1 --> X_2 --> ..., and F preserving them.
|*)

Section TransfiniteConstruction.

Context {C : category}.

(*| Assumptions of the transfinite-construction |*)
Context (F : well_pointed_endofunctor C).
Context (F_preserves_chain_colims : preserves_colimits_of_shape F nat_graph).
Context (has_chain_colimits : ∏ (c : chain C), ColimCocone c).

(* Let σ : functor_identity C ⟹ F := point F. *)

(*| The diagram A --> FA --> FFA --> ..., where the ith morphism is σ (F^i A) |*)
Definition F_chain (A : C) : chain C.
Proof.
  exists (λ n, iter_functor F n A).
  intros m n []. exact (point F (iter_functor F m A)).
Defined.

(*| F (F^n A) = F^n (F A) |*)
Definition iterF_commutes (A : C) (n : nat) : F (iter_functor F n A) = iter_functor F n (F A).
Proof.
  induction n. { apply idpath. }
  simpl. rewrite IHn. apply idpath.
Defined.

(*| 
  The chosen colimiting cocone of A -> FA -> FFA -> ...
  We refer to it's vertex as F^ω A
  |*)
Definition F_chain_CC (A : C) : ColimCocone (F_chain A) := has_chain_colimits _.

(*|
  F preserves ℕ-filtered colimits, so applying F gives us a new colimiting
  cocone of the mapped diagram F(A) -> F(FA) -> F(FFA) -> ...
  with vertex F(F^ω A).
|*)
Definition mapF_F_chain_CC (A : C) : ColimCocone (mapdiagram F (F_chain A)).
Proof.
  use make_ColimCocone.
  - exact (F (colim (F_chain_CC A))).
  - exact (mapcocone F (F_chain A) (colimCocone (F_chain_CC A))).
  - apply F_preserves_chain_colims. apply F_chain_CC.
Defined.

(* F^ω A refers to the (assumed) colimiting cocone of
A --> FA --> FFA --> ...
For the colimiting object, we use colim (F^ω A). *)
Notation "'F^ω'" := (F_chain_CC) (at level 0).

(* FF^ω A refers to the (assumed) colimiting cocone of
F(A) --> F(FA) --> F(FFA) --> ...
For the colimiting object, we use colim (FF^ω A). *)
Notation "'FF^ω'" := (mapF_F_chain_CC) (at level 0).

(* Note the definitional difference between F(colim (F^ω A)) and colim (FF^ω A) *)

(*|
  We want a structure map of the form F(F^ω A) --> F^ω A.
  Since F(F^ω A) is a colimit, it suffices to construct a cocone
    F(A) --> F^ω A
    F(FA) --> F^ω A
    F(FFA) --> F^ω A
    ...
  and the (1+i)th map of the colimiting cone for F^ω A has the correct form,
  since F(F^i(A)) = F^(1+i) A definitionally.

  Here we construct the cocone.
|*)
Definition transfinite_structure_map_cocone (A : C) : (cocone (mapdiagram F (F_chain A)) (colim (F^ω A))).
Proof.
  use make_cocone.
  - intros i. exact ((colimIn (F^ω A)) (S i)).
  - simpl. intros i _ []; simpl.
    rewrite <- (colimInCommutes (F^ω A) (S i) (S (S i)) (idpath _)).
    apply cancel_postcomposition.
    simpl.
    apply pathsinv0, well_pointed_endofunctor_ax.
Defined.

(*| The morphism induced by the cocone above |*)
Definition transfinite_structure_map (A : C) : F (colim (F^ω A)) --> colim (F^ω A)
  := colimArrow (FF^ω A) (colim (F^ω A)) (transfinite_structure_map_cocone A).

(*| The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A |*)
Lemma transfinite_structure_map_restricts (A : C) (i : vertex nat_graph)
  : colimIn (FF^ω A) i · transfinite_structure_map A = (colimIn (F^ω A)) (S i).
Proof.
  apply colimArrowCommutes.
Defined.

(*| The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A |*)
Lemma transfinite_structure_map_restricts' (A : C) (i : vertex nat_graph)
  : # F (colimIn (F^ω A) i) · transfinite_structure_map A = (colimIn (F^ω A)) (S i).
Proof.
  change (# F (colimIn (F^ω A) i)) with (colimIn (FF^ω A) i).
  apply transfinite_structure_map_restricts.
Defined.

(*|
  The structure map restricts to the identity via σ (F^ω A).
  Not surprising, since the structure map is a colimit of components of σ
|*)
Lemma transfinite_structure_map_retraction (A : C)
  : point F (colim (F^ω A)) · (transfinite_structure_map A)
    = identity (colim (F^ω A)).
Proof.
  set (s := transfinite_structure_map A).

  apply pathsinv0, colim_endo_is_identity.
  intro i.
  rewrite assoc.
  rewrite point_naturality.
  rewrite <- assoc.
  rewrite transfinite_structure_map_restricts'.
  apply (colimInCommutes (F^ω A) i (1+i) (idpath _)).
Defined.

(*|
  The primary object of construction - we will prove this is the free pointed-algebra.
|*)
Definition transfinite_pointed_algebra (A : C) : pointed_algebra F
  := make_pointed_algebra F
      (colim (F^ω A))
      (transfinite_structure_map A)
      (transfinite_structure_map_retraction A).

(*| 
  The free functor action on morphisms, given by the canonical map between the colimits
  NOTE: this is the underlying morphism in C, not in the category of algebras
  |*)
Definition free_pointed_algebra_mor {A B : C} (f : A --> B)
  : C ⟦ transfinite_pointed_algebra A, transfinite_pointed_algebra B ⟧.
Proof.
  apply colimOfArrows with (λ i, # (iter_functor F i) f).
  intros i _ []; simpl; apply pathsinv0; apply point_naturality.
Defined.

Lemma free_pointed_algebra_mor_restricts {A B : C} (f : A --> B) (i : nat)
  : colimIn (F^ω A) i · free_pointed_algebra_mor f
    = # (iter_functor F i) f · colimIn (F^ω B) i.
Proof.
  apply colimArrowCommutes.
Defined.

(*
  The data of the free functor C --> pointed_algebra_category F, i.e.
  - it's action on objects (transfinite_pointed_algebra)
  - it's action on morphisms (free_pointed_algebra_mor + compatibility with structure maps)
*)
Definition free_pointed_algebra_data : functor_data C (pointed_algebra_category F).
Proof.
  exists transfinite_pointed_algebra.
  intros A B f.
  (* set (f' := free_pointed_algebra_mor f). *)
  exists (free_pointed_algebra_mor f).

  apply (colim_mor_eq (FF^ω A)); simpl.
  intros i.
  rewrite assoc, assoc.
  rw_left_comp transfinite_structure_map_restricts.
  rw_left (free_pointed_algebra_mor_restricts f (S i)).
  change (colimIn (FF^ω A) i) with (# F (colimIn (F^ω A) i)).
  rewrite <- functor_comp.
  apply (transportb (λ x, _ = # F x · _) (free_pointed_algebra_mor_restricts f i)).
  simpl.
  rewrite functor_comp. rewrite <- assoc.
  apply cancel_precomposition.
  apply pathsinv0, transfinite_structure_map_restricts.
Defined.

(* The free functor *)
Definition free_pointed_algebra : C ⟶ pointed_algebra_category F.
Proof.
  apply (make_functor free_pointed_algebra_data).
  split.
  + intros A. apply algebra_mor_eq. simpl.
    apply pathsinv0, colim_endo_is_identity. intros i.
    refine (free_pointed_algebra_mor_restricts _ _ @ _).
    rewrite functor_id.
    apply id_left.
  + red. intros X Y Z f g. apply algebra_mor_eq; simpl.
    refine (_ @ ! precompWithColimOfArrows _ _ _ _ _ _ _ _).
    apply colimArrowUnique; simpl. intros i.
    refine (free_pointed_algebra_mor_restricts (f · g) i @ _).
    rewrite assoc. apply cancel_postcomposition.
    apply functor_comp.
Defined.

(*| We now prove that this is indeed the free functor, by constructing an adjunction |*)

Definition unit_FF_adjunction : functor_identity C ⟹ free_pointed_algebra ∙ forgetful F.
Proof.
  use make_nat_trans; red; simpl.
  - exact (λ A, colimIn (F^ω A) 0).
  - intros A B f; simpl.
    refine (_ @ ! free_pointed_algebra_mor_restricts f 0).
    apply idpath.
Defined.

Definition counit_FF_cocone_arrows (X : pointed_algebra F) : ∏ i : nat, C ⟦ iter_functor F i X, X ⟧.
Proof.
  induction i as [|i f].
  - exact (identity X).
  - exact (# F f · algebra_map X).
Defined.

Definition counit_FF_forms_cocone (X : pointed_algebra F)
  : forms_cocone (F_chain X) (counit_FF_cocone_arrows X).
Proof.
  red; intros i _ []; simpl.
  set (ɛ := counit_FF_cocone_arrows X).
  rewrite assoc.
  rw_left_comp' (point_naturality F (ɛ i)).
  rewrite <- assoc.
  rw_right_comp (pointed_algebra_ax X).
  apply id_right.
Defined.

(*| The counit has a component at the algebra X which is a morphism of algebras
  F^ω X --> X. This is the underlying morphism in C.
  (Be aware of the implicit coercion of X to it's underlying object in C)
|*)
Definition counit_FF_map (X : pointed_algebra F) : colim (F^ω X) --> X.
Proof.
  apply colimArrow. use make_cocone.
  + apply counit_FF_cocone_arrows.
  + apply counit_FF_forms_cocone.
Defined.

Definition counit_FF_map_restricts (X : pointed_algebra F) (i : nat)
  : colimIn (F^ω X) i · counit_FF_map X = counit_FF_cocone_arrows X i.
Proof.
  apply colimArrowCommutes.
Defined.

Definition counit_FF_mor (X : pointed_algebra F) : free_pointed_algebra X --> X.
Proof.
  exists (counit_FF_map X).
  apply (colim_mor_eq (FF^ω X)).
  intros i.
  rewrite assoc, assoc.
  rewrite transfinite_structure_map_restricts.
  rw_left (counit_FF_map_restricts X (S i)); simpl.
  apply cancel_postcomposition.
  change (colimIn (FF^ω X) i) with (# F (colimIn (F^ω X) i)).
  rewrite <- functor_comp.
  apply maponpaths, pathsinv0.
  apply counit_FF_map_restricts.
Defined.

Definition counit_FF_adjunction : forgetful F ∙ free_pointed_algebra ⟹ functor_identity (pointed_algebra_category F).
Proof.
  use make_nat_trans. { exact counit_FF_mor. }

  intros X Y f. apply algebra_mor_eq; simpl in *.
  refine (precompWithColimOfArrows _ _ _ _ _ _ _ _ @ _).
  apply colim_mor_eq; intros i; simpl.
  rw_left (colimArrowCommutes (F^ω X)); simpl.
  
  apply pathsinv0.
  rewrite assoc.
  rw_left_comp counit_FF_map_restricts.
  set (ɛ := counit_FF_cocone_arrows).

  induction i; simpl.
  + rewrite id_left, id_right. apply idpath.
  + rewrite assoc. rewrite <- functor_comp.
    rewrite <- IHi.
    rewrite <- assoc.
    rewrite functor_comp.
    rewrite <- (assoc _ _ (algebra_map Y)).
    apply cancel_precomposition.
    apply algebra_mor_commutes.
Defined.

(*| The adjunction witnessing that the free pointed-algebra functor is indeed free |*)
Definition free_forgetful_adjunction : adjunction C (pointed_algebra_category F).
Proof.
  use make_adjunction.
  - use make_adjunction_data.
    + exact free_pointed_algebra.
    + exact (forgetful F).
    + exact unit_FF_adjunction.
    + exact counit_FF_adjunction.
  - split.
    + red. intro A. apply algebra_mor_eq, pathsinv0; simpl.
      apply colim_endo_is_identity. intros i.
      rewrite assoc.
      rw_left_comp (free_pointed_algebra_mor_restricts (colimIn (F^ω A) 0) i).
      rewrite <- assoc.
      rw_right_comp (counit_FF_map_restricts (transfinite_pointed_algebra A) i).
      set (ɛ := counit_FF_cocone_arrows).
      induction i; simpl. { apply id_right. }
      rewrite assoc, <- functor_comp.
      apply (transportb (λ x, # F x · _ = _) IHi).
      apply transfinite_structure_map_restricts.
    + red. intro X; simpl. apply (counit_FF_map_restricts X 0).
Defined.

Corollary are_adjoints_FF : are_adjoints free_pointed_algebra (forgetful F).
Proof. exact free_forgetful_adjunction. Defined.

End TransfiniteConstruction.

(*|
Conversely, we can take *any* reflective
subcategory of C and extract a well-pointed endfunctor (in fact, an idempotent monad).

This converse provides a way to produce well-pointed functors.
|*)

Lemma counit_is_nat_iso_from_fully_faithful (C D : category) (adj : adjunction C D)
  : fully_faithful (right_functor adj) → is_nat_iso (adjcounit adj).
Proof.
  intros R_ff.
  destruct adj as [[L [R [η ɛ]]] [t1 t2]].
  intros d e.
  specialize (R_ff d e). red in t1, t2.
  unfold right_functor, adjcounit, adjunit in *; simpl in *.
  refine (isweqhomot _ _ _ (twooutof3c _ (λ f, # L f · ɛ e) R_ff _)).
  - intros f; unfold precomp_with; simpl.
    apply (nat_trans_ax ɛ).
  - apply isweq_iso with (λ f : L (R d) --> e, η _ · # R f); simpl.
    + intros f.
      rewrite functor_comp, assoc.
      eapply pathscomp0.
        { 
          apply cancel_postcomposition, pathsinv0.
          apply (nat_trans_ax η).
        }
      simpl. rewrite <- assoc.
      rewrite t2. apply id_right.
    + intros g.
      rewrite functor_comp, <- assoc.
      eapply pathscomp0.
        { apply cancel_precomposition. apply (nat_trans_ax ɛ). }
      simpl. rewrite assoc, t1. apply id_left.
Defined.

Theorem is_well_pointed_of_reflective_subcat
  (C D : category) (adj : adjunction C D)
  : let L := left_functor adj in
    let R := right_functor adj in
    let η := adjunit adj in
      (fully_faithful R) → ∏ X : C, η ((L∙R) X) = # (L∙R) (η X).
Proof.
  simpl. intro R_ff.
  set (counit_is_iso := counit_is_nat_iso_from_fully_faithful C D adj R_ff).
  destruct adj as [[L [R [η ɛ]]] [t1 t2]].
  red in t1, t2;
  unfold left_functor, right_functor, adjcounit, adjunit in *; simpl in *.
  set (R_counit_is_iso := λ d, functor_on_is_iso_is_iso R (counit_is_iso d)).
  intros A.
  specialize (R_counit_is_iso (L A)).
  apply (post_comp_with_iso_is_inj _ _ _ R_counit_is_iso).
  rewrite t2.
  rewrite <- functor_comp, <- functor_id.
  apply maponpaths, pathsinv0.
  apply t1.
Defined.

Definition reflection_well_pointed_endofunctor 
  (C D : category) (adj : adjunction C D)
  (R_ff : fully_faithful (right_functor adj))
  : well_pointed_endofunctor C.
Proof.
  set (T := (left_functor adj ∙ right_functor adj)).
  set (η := adjunit adj).
  exists (make_pointed_endofunctor T η).
  intros X; simpl.
  apply is_well_pointed_of_reflective_subcat.
  exact R_ff.
Defined.

(*
Something could be said about idempotent monads, but extracting the monad
from an adjunction exists only in UniMath.Bicategories, but we are using
adjunctions in the sense of UniMath.CategoryTheory.Adjunctions.Core
*)