(*|
The transfinite construction of a free-algebra (from a well-pointed endofunctor
in a category with ℕ-filtered colimits)

References:

* `nLab: transfinite construction of free algebras <https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras>`_
* `Max Kelly, A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on <https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/unified-treatment-of-transfinite-constructions-for-free-algebras-free-monoids-colimits-associated-sheaves-and-so-on/FE2E25E4959E4D8B4DE721718E7F55EE>`_
|*)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.OmegaCocontFunctors.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

(*
To rewrite x to x' in x · y = z, use
rw_left_comp h.
where h has conclusion x = x'.
*)
Tactic Notation "rw_left_comp" constr(e) :=
  apply (transportb (λ x, x · _ = _) ltac:(apply e)).
(* Similarly `rw_right_comp h` uses h to rewrite x to x' in y · x = z *)
Tactic Notation "rw_right_comp" constr(e) :=
  apply (transportb (λ x, _ · x = _) ltac:(apply e)).


(*|==========================
Algebra for an endofunctor
==========================|*)
Section Algebra_def.

Context {C : category}.

(* An algebra for an endofunctor consists of a structure map only *)
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

(* Such morphisms come with identity, composition *)

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

(* A pointed endofunctor F comes with a natural transformation 1 ⟹ F *)
Definition pointed_endofunctor (C : category) : UU := ∑ F : C ⟶ C, functor_identity C ⟹ F.

#[reversible=no] Coercion pointed_endofunctor_endofunctor {C : category} (X : pointed_endofunctor C) : C ⟶ C := pr1 X.

Definition make_pointed_endofunctor {C : category} (F : C ⟶ C) (σ : functor_identity C ⟹ F) : pointed_endofunctor C := tpair _ F σ.

(* The *point* of a pointed endofunctor *)
Definition point {C : category} (F : pointed_endofunctor C) : functor_identity C ⟹ F := pr2 F.

Definition point_naturality {C : category} (F : pointed_endofunctor C) {x y : C} (f : x --> y)
  : (f · point F y = point F x · # F f).
Proof.
  apply (nat_trans_ax (point F)).
Defined.

(*| 
  A well-pointed functor satisfies Fσ = σF, i.e. for every c : C, the two
  ways of constructing a morphism F c --> F (F c) coincide.
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

(* A monad algebra for a monad is an algebra equipped with unit and multiplication laws (cf. pointed_algebra) *)
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

(* There is at most one pointed algebra structure on a given X : C. *)
Corollary well_pointed_has_pointed_algebra_isaprop (F : well_pointed_endofunctor C)
  : ∏ A : C, isaprop (∑ a : F A --> A, (point F A) · a = identity A).
Proof.
  intros A.
  apply invproofirrelevance; red. intros [a ar] [b br].
  apply subtypeInjectivity; simpl. { intros f. apply homset_property. }
  set (point_A_iso := well_pointed_point_z_iso_at_algebra F (make_pointed_algebra F A a ar)).
  apply (pre_comp_with_z_iso_is_inj point_A_iso); simpl.
  exact (ar @ ! br).
Defined.

(* Given pointed algebras X, Y, any f : X ⟶ Y in C is a morphism of pointed algebras *)
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

(* For a well-pointed algebra F, its category of pointed algebras can be viewed as a subcategory
of C via the forgetful functor, because it is fully-faithful. *)
Definition forgetul_fully_faithful (F : well_pointed_endofunctor C) : fully_faithful (forgetful F).
Proof.
  red. intros X Y.
  use isweq_iso; simpl.
  + exact (λ f, (f,,mor_is_algebra_mor X Y f)).
  + intros f; simpl. apply algebra_mor_eq; simpl. apply idpath.
  + intros f; simpl. apply idpath. 
Defined.

(* Being in the (strict) image of the forgetful functor is a proposition. *)
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


(* post_whisker_unit σ F is σF, i.e. at A it is σ (G A) : G A --> F (G A)
  This is equal to post_whisker σ F, without the complica
 *)
Definition post_whisker_unit {D C : category} {F : C ⟶ C} (σ : functor_identity C ⟹ F) (G : D ⟶ C) : G ⟹ G∙F.
Proof.
  use make_nat_trans; red.
  + exact (λ A, σ (G A)).
  + intros A B f. apply (nat_trans_ax σ).
Defined.

(* pre_whisker_unit *)
Definition pre_whisker_unit {D C : category} {F : C ⟶ C} (G : C ⟶ D) (σ : functor_identity C ⟹ F) : G ⟹ F∙G.
Proof.
  use make_nat_trans; red.
  + exact (λ A, # G (σ A)).
  + intros A B f. simpl. do 2 rewrite <- functor_comp. apply maponpaths. apply (nat_trans_ax σ).
Defined.

Definition map_ColimCocone {C D : category} {g : graph} (d : diagram g C) {F : C ⟶ D}
  (H : preserves_colimits_of_shape F g) : ColimCocone d → ColimCocone (mapdiagram F d).
Proof.
  intros CC.
  use make_ColimCocone.
  - exact (F (colim CC)).
  - exact (mapcocone F d (colimCocone CC)).
  - apply H. apply CC.
Defined.

Local Notation "F '^' i" := (iter_functor F i).

Section IterChain.

Context {C : category}.
Context (F : pointed_endofunctor C).

Definition iter_chain_mor (i : nat)
  : F^i ⟹ F^(S i).
Proof.
  induction i as [|i IHi].
  - exact (point F).
  - exact (post_whisker IHi F).
Defined.

(* This property of the chain morphisms is definitional, but important conceptually. *)
Definition iter_chain_mor_shift (i : nat) (A : C)
  : iter_chain_mor (S i) A = # F (iter_chain_mor i A)
  := idpath _.

(* The diagram Id --> F --> FF --> ..., where the ith morphism is F^i σ(-) *)
Definition iter_chain : chain [C, C].
Proof.
  exists (λ i, F ^ i).
  intros i _ []. exact (iter_chain_mor i).
Defined.

Definition iter_chain_at (A : C) : chain C.
Proof. 
  exists (λ i, (F ^ i) A).
  intros i _ []. exact (iter_chain_mor i A).
Defined.

End IterChain.

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

(* Assumptions of the transfinite-construction *)
Context (chain_colimits : Chains C).
Context (F : pointed_endofunctor C).
Context (F_omega_cocont : is_omega_cocont F).

(* 
  Well-pointed is used in (essentially) one part of the argument that the
  free-algebra-map is a retract of the point - all other constructions
  and theorems just treat F as a pointed endofunctor.
  Dependency graph is:
  F_well_pointed
    => iter_chain_mor_is_point
    => shift_iter_map_retraction
    => transfinite_pointed_algebra
   *)
Context (F_well_pointed : well_pointed F). 

(* 
  The chosen colimiting cocone of A --> FA --> FFA --> ...
*)
Let CC : ∏ A : C, ColimCocone (iter_chain_at F A)
  := λ A, chain_colimits _.
Local Notation "'F^ω'" := (λ A, colim (CC A)) (at level 0).

(*
  F preserves ℕ-filtered colimits, so applying F gives us a new colimiting
  cocone of the mapped diagram F(A) -> F(FA) -> F(FFA) -> ...
  with vertex F(F^ω A).
*)
Let F_CC : ∏ A : C, ColimCocone (mapchain F (iter_chain_at F A))
  := λ A, map_ColimCocone _ F_omega_cocont (CC A).
Local Notation "'FF^ω'" := (λ A, colim (F_CC A)) (at level 0).

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

Definition shift_iter_cocone (A : C)
  : cocone (mapchain F (iter_chain_at F A)) (F^ω A).
Proof.
  exists (λ i, colimIn (CC A) (S i)).
  intros i _ []; simpl. exact (colimInCommutes (CC A) (S i) _ (idpath (S (S i)))).
Defined.

(* The morphism induced by the cocone above *)
Definition shift_iter_map (A : C) : F (F^ω A) --> (F^ω A)
  := colimArrow 
      (map_ColimCocone (iter_chain_at F A) F_omega_cocont (CC A))
      (F^ω A)
      (shift_iter_cocone A).

(* The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A *)
Lemma shift_iter_map_restricts (A : C) (i : nat)
  : colimIn (F_CC A) i · shift_iter_map A = (colimIn (CC A)) (S i).
Proof.
  apply colimArrowCommutes.
Defined.

(* The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A *)
Lemma shift_iter_map_restricts' (A : C) (i : nat)
  : # F (colimIn (CC A) i) · shift_iter_map A = (colimIn (CC A)) (S i).
Proof.
  change (# F (colimIn (CC A) i)) with (colimIn (F_CC A) i).
  apply shift_iter_map_restricts.
Defined.

Lemma iter_chain_mor_is_point (i : nat) (A : C) : iter_chain_mor F i A = point F ((F ^ i) A).
Proof.
  apply pathsinv0.
  induction i.
  - exact (idpath _).
  - exact (F_well_pointed ((F ^ i) A) @ maponpaths (#F) IHi).
Defined.

(*|
  The structure map restricts to the identity via σ (F^ω A).
  Not surprising, since the structure map is a colimit of components of σ
|*)
Lemma shift_iter_map_retraction (A : C)
  : point F (F^ω A) · (shift_iter_map A)
    = identity (F^ω A).
Proof.
  set (s := shift_iter_map A).

  apply pathsinv0, colim_endo_is_identity.
  intro i.
  rewrite assoc.
  (* α_A^i · σ_{F^ω A} · s = σ_{F^i A} · F (α_A^i) · s *)
  rewrite point_naturality.
  rewrite <- assoc.
  (* ... = σ_{F^i A} · α_A^(1+i) *)
  rewrite shift_iter_map_restricts'.
  simpl. rewrite <- iter_chain_mor_is_point. (* well-pointedness used here! *)
  (* ... = α_A^i *)
  apply (colimInCommutes (CC A) i (1+i) (idpath _)).
Defined.

(*
  The primary object of construction - we will prove this is the free pointed-algebra.
*)
Definition transfinite_pointed_algebra (A : C) : pointed_algebra F
  := make_pointed_algebra F
      (F^ω A)
      (shift_iter_map A)
      (shift_iter_map_retraction A).

(*
  The free functor action on morphisms, given by the canonical map between the colimits
  NOTE: this is the underlying morphism in C, not in the category of algebras
*)
Definition free_pointed_algebra_map {A B : C} (f : A --> B)
  : C ⟦ transfinite_pointed_algebra A, transfinite_pointed_algebra B ⟧.
Proof.
  apply colimOfArrows with (λ i, # (F ^ i) f).
  intros i _ []; simpl.
  induction i.
  + simpl. apply pathsinv0, point_naturality.
  + simpl. do 2 rewrite <- functor_comp. apply maponpaths. exact IHi.
Defined.

Lemma free_pointed_algebra_map_restricts {A B : C} (f : A --> B) (i : nat)
  : colimIn (CC A) i · free_pointed_algebra_map f
    = # (F ^ i) f · colimIn (CC B) i.
Proof.
  apply colimArrowCommutes.
Defined.

(*
  The data of the free functor C --> pointed_algebra_category F, i.e.
  - it's action on objects (transfinite_pointed_algebra)
  - it's action on morphisms (free_pointed_algebra_map + compatibility with structure maps)
*)
Definition free_pointed_algebra_data : functor_data C (pointed_algebra_category F).
Proof.
  exists transfinite_pointed_algebra.
  intros A B f.
  exists (free_pointed_algebra_map f).

  apply (colim_mor_eq (F_CC A)); simpl.
  intros i.
  rewrite assoc, assoc.
  rw_left_comp shift_iter_map_restricts.
  refine (free_pointed_algebra_map_restricts f (S i) @ _).
  change (colimIn (F_CC A) i) with (# F (colimIn (CC A) i)).
  rewrite <- functor_comp.
  apply (transportb (λ x, _ = # F x · _) (free_pointed_algebra_map_restricts f i)).
  simpl.
  rewrite functor_comp, <- assoc.
  apply cancel_precomposition.
  apply pathsinv0, shift_iter_map_restricts.
Defined.

(* The free functor *)
Definition free_pointed_algebra : C ⟶ pointed_algebra_category F.
Proof.
  apply (make_functor free_pointed_algebra_data).
  split.
  - intros A. apply algebra_mor_eq.
    apply pathsinv0, colim_endo_is_identity. intros i.
    refine (free_pointed_algebra_map_restricts _ _ @ _).
    rewrite functor_id.
    apply id_left.
  - red. intros X Y Z f g. apply pathsinv0, algebra_mor_eq; simpl.
    apply colimArrowUnique; simpl. intros i.
    rewrite assoc.
    rw_left_comp (free_pointed_algebra_map_restricts f i).
    rewrite <- assoc.
    rw_right_comp (free_pointed_algebra_map_restricts g i).
    rewrite assoc. apply cancel_postcomposition.
    apply pathsinv0, functor_comp.
Defined.

(*| We now prove that this is indeed the free functor, by constructing an adjunction |*)

Definition unit_FF_adjunction : functor_identity C ⟹ free_pointed_algebra ∙ forgetful F.
Proof.
  use make_nat_trans; red; simpl.
  - exact (λ A, colimIn (CC A) 0).
  - intros A B f; simpl.
    apply pathsinv0, (free_pointed_algebra_map_restricts f 0).
Defined.

Definition counit_FF_cocone_arrows (X : pointed_algebra F) : ∏ i : nat, C ⟦ (F ^ i) X, X ⟧.
Proof.
  induction i as [|i IH].
  - exact (identity X). (* Forced by triangle identities *)
  - exact (# F IH · algebra_map X). (* Necessary to make ɛ an morphism of algebras *)
Defined.

Definition counit_FF_forms_cocone (X : pointed_algebra F)
  : forms_cocone (iter_chain_at F X) (counit_FF_cocone_arrows X).
Proof.
  red; intros i _ []; simpl.
  set (ɛ := counit_FF_cocone_arrows).
  rewrite assoc.
  (* This could be done using iter_chain_mor_is_point, but it's not necessary! *)
  induction i.
  - simpl. rewrite functor_id, id_right. apply pointed_algebra_ax.
  - simpl. rewrite <- functor_comp, assoc.
    apply (maponpaths (λ x, # F x · _) IHi).
Defined.

(* The counit has a component at the algebra X which is a morphism of algebras
  F^ω X --> X. This is the underlying morphism in C.
  (Be aware of the implicit coercion of X to it's underlying object in C)
*)
Definition counit_FF_map (X : pointed_algebra F) : colim (CC X) --> X.
Proof.
  apply colimArrow. use make_cocone.
  + apply counit_FF_cocone_arrows.
  + apply counit_FF_forms_cocone.
Defined.

Definition counit_FF_map_restricts (X : pointed_algebra F) (i : nat)
  : colimIn (CC X) i · counit_FF_map X = counit_FF_cocone_arrows X i.
Proof.
  apply colimArrowCommutes.
Defined.

Definition counit_FF_mor (X : pointed_algebra F) : free_pointed_algebra X --> X.
Proof.
  exists (counit_FF_map X).
  apply (colim_mor_eq (F_CC X)).
  intros i.
  rewrite assoc, assoc.
  rewrite shift_iter_map_restricts.
  refine (counit_FF_map_restricts X (S i) @ _); simpl.
  apply cancel_postcomposition.
  change (colimIn (F_CC X) i) with (# F (colimIn (CC X) i)).
  rewrite <- functor_comp.
  apply maponpaths, pathsinv0.
  apply counit_FF_map_restricts.
Defined.

Definition counit_FF_adjunction : forgetful F ∙ free_pointed_algebra ⟹ functor_identity (pointed_algebra_category F).
Proof.
  use make_nat_trans. { exact counit_FF_mor. }

  intros X Y f. apply algebra_mor_eq; simpl in *.
  apply colim_mor_eq; intros i. do 2 rewrite assoc.
  rw_left_comp (free_pointed_algebra_map_restricts f i).
  rewrite <- assoc.
  rw_right_comp (counit_FF_map_restricts Y i).
  rewrite (counit_FF_map_restricts X i).
  set (ɛ := counit_FF_cocone_arrows).

  induction i; simpl. { rewrite id_left. apply id_right. }
  rewrite assoc. rewrite <- functor_comp.
  apply (transportb (λ x, # F x · _ = _) IHi).
  rewrite <- assoc.
  rewrite functor_comp.
  rewrite <- (assoc _ _ (algebra_map Y)).
  apply cancel_precomposition.
  apply pathsinv0, algebra_mor_commutes.
Defined.

(* The adjunction witnessing that the free pointed-algebra functor is indeed free *)
Definition free_forgetful_adjunction : adjunction C (pointed_algebra_category F).
Proof.
  use make_adjunction.
  - use make_adjunction_data.
    + exact free_pointed_algebra.
    + exact (forgetful F).
    + exact unit_FF_adjunction.
    + exact counit_FF_adjunction.
  - split; red.
    + intro A. apply algebra_mor_eq, pathsinv0; simpl.
      apply colim_endo_is_identity. intros i.
      rewrite assoc.
      rw_left_comp (free_pointed_algebra_map_restricts (colimIn (CC A) 0) i).
      rewrite <- assoc.
      rw_right_comp (counit_FF_map_restricts (transfinite_pointed_algebra A) i).
      set (ɛ := counit_FF_cocone_arrows).
      induction i; simpl. { apply id_right. }
      rewrite assoc, <- functor_comp.
      apply (transportb (λ x, # F x · _ = _) IHi).
      apply shift_iter_map_restricts.
    + intro X. simpl. apply (counit_FF_map_restricts X 0).
Defined.

Corollary are_adjoints_FF : are_adjoints free_pointed_algebra (forgetful F).
Proof. exact free_forgetful_adjunction. Defined.

End TransfiniteConstruction.

(*|
Conversely, we can take *any* reflective subcategory of C and extract a
well-pointed endfunctor on C (in fact, an idempotent monad).

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
      apply (transportf (λ x, x · _ = _) (nat_trans_ax η _ _ f)); simpl.
      rewrite <- assoc.
      rewrite t2. apply id_right.
    + intros g.
      rewrite functor_comp, <- assoc.
      apply (transportb (λ x, _ · x = _) (nat_trans_ax ɛ _ _ g)); simpl.
      rewrite assoc, t1. apply id_left.
Defined.

Theorem is_well_pointed_of_reflective_subcat
  {C D : category} (adj : adjunction C D)
  : let L := left_functor adj in
    let R := right_functor adj in
    let η := adjunit adj in
      (fully_faithful R) → ∏ X : C, η ((L∙R) X) = # (L∙R) (η X).
Proof.
  simpl. intro R_ff.
  assert (counit_is_iso := counit_is_nat_iso_from_fully_faithful C D adj R_ff).
  destruct adj as [[L [R [η ɛ]]] [t1 t2]].
  red in t1, t2; unfold left_functor, right_functor, adjcounit, adjunit in *; simpl in *.
  assert (R_counit_is_iso := λ d, functor_on_is_iso_is_iso R (counit_is_iso d)).
  intros A.
  (* The triangle identities imply that RLη and ηRL are sections of RɛLA, which is iso *)
  specialize (R_counit_is_iso (L A)).
  specialize (t2 (L A)).
  pose proof (t1' := maponpaths (#R) (t1 A)); clear t1; rename t1' into t1.
  rewrite functor_comp, functor_id in t1.
  apply (post_comp_with_iso_is_inj _ _ _ R_counit_is_iso).
  exact (t2 @ ! t1).
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
  exact (is_well_pointed_of_reflective_subcat adj R_ff X).
Defined.

(*
Something could be said about idempotent monads, but I'm not sure how to
go about this (seems to involve UniMath.Bicategories).
*)