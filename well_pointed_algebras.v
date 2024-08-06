(**
The transfinite construction of a free-algebra (from a well-pointed endofunctor
in a category with ℕ-filtered colimits)
References:
- https://ncatlab.org/nlab/show/transfinite+construction+of+free+algebras
- Max Kelly, A unified treatment of transfinite constructions for free algebras, free monoids, colimits, associated sheaves, and so on

TODO:
  - prove transfinite construction yields algebraically free monad for F
  - expand construction to other cases.
*)

Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Equivalences.Core.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Chains.Chains.

Local Open Scope cat.

(* Fix a category *)
Context {C : category}.

Section Algebra_def.

  (* Fix an endofunctor *)
  Context (F : C ⟶ C).

  (* An algebra for an endofunctor consists of a structure map only *)
  Definition algebra  : UU := ∑ X : C, F X --> X.

  Definition make_algebra (X : C) (s : F X --> X) : algebra := tpair (λ X, F X --> X) X s.

  #[reversible=no] Coercion alg_carrier (X : algebra) : C := pr1 X.

  Definition algebra_map (X : algebra) : F X --> X := pr2 X.

  (* Morphisms of algebras are morphisms of underlying objects
    which are compatible with structure maps
          F f
      F X ---> F Y
       \        \
    a  \        \ b
       v        v
       X -----> Y
           f
   *)
  Definition algebra_mor (X Y : algebra)
    : UU
    := ∑ f : X --> Y, algebra_map X · f = #F f · algebra_map Y.

  Coercion mor_from_algebra_mor {X Y : algebra} (f : algebra_mor X Y)
    : X --> Y := pr1 f.

  Definition algebra_mor_commutes {X Y : algebra} (f : algebra_mor X Y)
    : algebra_map X · f = #F f · algebra_map Y
    := pr2 f.

  (* Such morphisms come with identity, composition *)

  Definition algebra_mor_id (X : algebra) : algebra_mor X X.
  Proof.
    exists (identity X).
    abstract (rewrite functor_id, id_right, id_left;
              apply idpath).
  Defined.

  Definition algebra_mor_comp (X Y Z : algebra) (f : algebra_mor X Y) (g : algebra_mor Y Z)
    : algebra_mor X Z.
  Proof.
    exists (f · g).
    abstract (rewrite assoc;
              rewrite algebra_mor_commutes;
              rewrite <- assoc;
              rewrite algebra_mor_commutes;
              rewrite functor_comp, assoc;
              apply idpath).
  Defined.

  (* Identifying morphisms of algebras is equivalent to
    identifying the underlying morphisms *)
  Definition algebra_mor_eq {X Y : algebra} {f g : algebra_mor X Y}
    : ((f : X --> Y) = g) ≃ f = g.
  Proof.
    apply invweq.
    apply subtypeInjectivity.
    intro h.
    apply homset_property.
  Defined.

  Definition algebra_category : category.
  Proof.
    use makecategory.
    - exact algebra.
    - exact algebra_mor.
    - intros X Y.
      apply (isofhleveltotal2 2). { apply homset_property. }
      intros f. apply isasetaprop. apply homset_property.
    - exact algebra_mor_id.
    - exact algebra_mor_comp.
    - intros. apply algebra_mor_eq. apply id_left.
    - intros. apply algebra_mor_eq. apply id_right.
    - intros. apply algebra_mor_eq. apply assoc.
    - intros. apply algebra_mor_eq. refine (!(_)). apply assoc.
  Defined.

End Algebra_def.

(* A pointed endofunctor F comes with a natural transformation 1 ⟹ F *)
Definition pointed_endofunctor : UU := ∑ F : C ⟶ C, functor_identity C ⟹ F.

#[reversible=no] Coercion pointed_endofunctor_functor (X : pointed_endofunctor) : C ⟶ C := pr1 X.

(* 
  The *point* of a pointed endofunctor.
  Usually set σ := point F
*)
Definition point (F : pointed_endofunctor) : functor_identity C ⟹ F := pr2 F.

(* 
  A well-pointed functor satisfies Fσ = σF, i.e. for every c : C, the two
  ways of constructing a morphism F c --> F (F c) coincide.
  Can be seen as a way to simplify the component of σ at (F c).
 *)
Definition well_pointed (F : pointed_endofunctor) :=
  let σ := point F
  in ∏ c : C, #F (σ c) = σ (F c).

(* A pointed algebra for a pointed endofunctor is an algebra (a : F X --> X)
  for the endofunctor which obeys the unit-law (id_X = σ_X · a)
*)
Definition pointed_algebra (F : pointed_endofunctor) : UU :=
  let σ := point F
  in ∑ X : algebra F, identity X = (σ X) · (algebra_map F X).

Definition make_pointed_algebra (F : pointed_endofunctor) (X : C) (s : F X --> X) (unit_law : identity X = (point F X) · s)
  : pointed_algebra F
  := (make_algebra F X s,, unit_law).

Coercion algebra_from_pointed_algebra (F : pointed_endofunctor) (X : pointed_algebra F) : algebra F := pr1 X.

Definition pointed_algebra_ax {F : pointed_endofunctor} (X : pointed_algebra F) : identity X = (point F X) · (algebra_map F X) := pr2 X.

(* A monad algebra for a monad is an algebra equipped with unit and multiplication laws (cf. pointed_algebra) *)
Definition monad_algebra (T : Monad C) : UU := ∑ X : algebra T,
  identity X = (η T X) · (algebra_map T X) ×
  μ T X · algebra_map T X = #T (algebra_map T X) · algebra_map T X.

Coercion algebra_from_monad_algebra (T : Monad C) (X : monad_algebra T) : algebra T := pr1 X.

Definition pointed_algebra_category (F : pointed_endofunctor) : category.
Proof.
  use makecategory.
  - exact (pointed_algebra F).
  - intros X Y. exact (algebra_mor F X Y).
  - intros X Y.
    apply (isofhleveltotal2 2). { apply homset_property. }
    intros f. apply isasetaprop. apply homset_property.
  - intros. apply algebra_mor_id.
  - intros X Y Z. exact (algebra_mor_comp F X Y Z).
  - intros. apply algebra_mor_eq. apply id_left.
  - intros. apply algebra_mor_eq. apply id_right.
  - intros. apply algebra_mor_eq. apply assoc.
  - intros. apply algebra_mor_eq. refine (!(_)). apply assoc.
Defined.

Definition monad_algebra_category (T : Monad C) : category.
Proof.
  use makecategory.
  - exact (monad_algebra T).
  - intros X Y. exact (algebra_mor T X Y).
  - intros X Y.
    apply (isofhleveltotal2 2). { apply homset_property. }
    intros f. apply isasetaprop. apply homset_property.
  - intros. apply algebra_mor_id.
  - intros X Y Z. exact (algebra_mor_comp T X Y Z).
  - intros. apply algebra_mor_eq. apply id_left.
  - intros. apply algebra_mor_eq. apply id_right.
  - intros. apply algebra_mor_eq. apply assoc.
  - intros. apply algebra_mor_eq. refine (!(_)). apply assoc.
Defined.

Definition algebraically_free (F : C ⟶ C) (T : Monad C)
  : UU
  := equivalence_of_cats (monad_algebra_category T) (algebra_category F).

(* TODO: prove transfinite construction yields algebraically free monad for F *)

(* 
We handle only the Κ=ℕ case of the transfinite-construction, where C is assumed to
have Κ-filtered colimits that F preserves.
This is equivalent to C having colimits of ℕ-indexed diagrams
of the form X_0 --> X_1 --> X_2 --> ..., and F preserving them.
 *)
Definition chain_colims (D : category) : UU
  := ∏ (c : chain C), ColimCocone c.

Section WellPointedHasFree.

  (* Assumptions of the transfinite-construction *)
  Context (has : chain_colims C).
  Context (F : pointed_endofunctor).
  Context (preserves : preserves_colimits_of_shape F nat_graph).
  Context (wF : well_pointed F).

  Local Definition σ := point F : functor_identity C ⟹ F.

  Local Definition naturality_σ (x y : C) (f : x --> y)
    : (f · σ y = σ x · # F f)
    := pr2 σ x y f.

  (* The diagram A --> FA --> FFA --> ...
    the ith morphism is σ (F^i A) *)
  Definition F_chain (A : C) : chain C.
  Proof.
    exists (λ n, iter_functor F n A).
    intros m n Hmn. destruct Hmn. simpl.
    apply σ.
  Defined.

  (* F (F^n A) = F^n (F A) *)
  Definition iterF_commutes (A : C) (n : nat) : F (iter_functor F n A) = iter_functor F n (F A).
  Proof.
    induction n. { apply idpath. }
    simpl. rewrite IHn. apply idpath.
  Defined.

  (* 
    The chosen colimiting cocone of A -> FA -> FFA -> ...
    We refer to it's vertex as F^ω A
   *)
  Definition F_chain_CC (A : C) : ColimCocone (F_chain A) := has _.

  (*
    F preserves ℕ-filtered colimits, so applying F gives us a new colimiting
    cocone of the mapped diagram F(A) -> F(FA) -> F(FFA) -> ...
    with vertex F(F^ω A).
  *)
  Definition mapF_F_chain_CC (A : C) : ColimCocone (mapdiagram F (F_chain A)).
  Proof.
    use make_ColimCocone.
    - exact (F (colim (F_chain_CC A))).
    - exact (mapcocone F (F_chain A) (colimCocone (F_chain_CC A))).
    - apply preserves. apply F_chain_CC.
  Defined.

  (*
    We want a structure map of the form F(F^ω A) --> F^ω A.
    Since F(F^ω A) is a colimit, it suffices to construct a cocone
      F(A) --> F^ω A
      F(FA) --> F^ω A
      F(FFA) --> F^ω A
      ...
    and the (1+i)th map of the colimiting cone for F^ω A has the correct form,
    since F(F^i(A)) = F^(1+i) A definitionally.

    Here we construct the cocone.
  *)
  Definition transfinite_structure_map_cocone (A : C) : (cocone (mapdiagram F (F_chain A)) (colim (F_chain_CC A))).
  Proof.
    use tpair.
    - intros i. exact ((colimIn (F_chain_CC A)) (S i)).
    - abstract (simpl; intros i _ []; simpl;
      rewrite <- (colimInCommutes (F_chain_CC A) (S i) (S (S i)) (idpath _));
      apply cancel_postcomposition;
      simpl;
      apply wF).
  Defined.

  (* The morphism induced by the cocone above *)
  Definition transfinite_structure_map (A : C) : F (colim (F_chain_CC A)) --> colim (F_chain_CC A)
    := colimArrow (mapF_F_chain_CC A) (colim (F_chain_CC A)) (transfinite_structure_map_cocone A).
  
  (* The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A *)
  Lemma transfinite_structure_map_commutes (A : C) (i : vertex nat_graph)
    : colimIn (mapF_F_chain_CC A) i · transfinite_structure_map A = (colimIn (F_chain_CC A)) (S i).
    Proof.
      apply colimArrowCommutes.
    Defined.

  (* The structure map restricted to F(F^i A) is the inclusion F^(1+i) A --> F^ω A *)
  Lemma transfinite_structure_map_commutes' (A : C) (i : vertex nat_graph)
    : # F (colimIn (F_chain_CC A) i) · transfinite_structure_map A = (colimIn (F_chain_CC A)) (S i).
    Proof.
      assert (H : colimIn (mapF_F_chain_CC A) i = colimIn (mapF_F_chain_CC A) i).
      { apply idpath. }
      apply (transportb (λ x, x · _ = _) H).
      apply colimArrowCommutes.
    Defined.

  (*
    The structure map restricts to the identity via σ (F^ω A).
    Not surprising, since the structure map is a colimit of components of σ
  *)
  Lemma transfinite_pointed_algebra_unit_law (A : C)
    : identity (colim (F_chain_CC A)) 
      = σ (colim (F_chain_CC A)) · (transfinite_structure_map A).
    Proof.
      set (Fω := F_chain_CC).
      set (FFω := mapF_F_chain_CC).
      set (s := transfinite_structure_map A).

      apply colim_endo_is_identity.
      intro i.
      rewrite assoc.
      rewrite naturality_σ.
      rewrite <- assoc.
      rewrite transfinite_structure_map_commutes'.
      apply (colimInCommutes (Fω A) i (1+i) (idpath _)).
    Defined.

  (*
    The primary object of construction - we will prove this is the free pointed-algebra.
  *)
  Definition transfinite_pointed_algebra (A : C) : pointed_algebra F
    := make_pointed_algebra F
        (colim (F_chain_CC A))
        (transfinite_structure_map A)
        (transfinite_pointed_algebra_unit_law A).

  (* The functor which forgets the structure map into the underlying object *)
  Definition forgetful : pointed_algebra_category F ⟶ C.
  Proof.
    use make_functor.
    - use make_functor_data.
      + intro X. exact (alg_carrier F (algebra_from_pointed_algebra F X)).
      + intros X Y f. exact (pr1 f).
    - split; red; intros; apply idpath.
  Defined.

  (* 
    The free functor action on morphisms, given by the canonical map between the colimits
    NOTE: this is the underlying morphism in C, not in the category of algebras
   *)
  Definition free_pointed_algebra_mor {A B : C} (f : A --> B)
    : C ⟦ transfinite_pointed_algebra A, transfinite_pointed_algebra B ⟧.
  Proof.
      apply colimOfArrows with (λ i, # (iter_functor F i) f).
      abstract (intros i _ []; simpl; apply pathsinv0; apply naturality_σ).
  Defined.

  (* About colimOfArrows.
  Definition colimOfArrows_comp {g : graph}
  {d1 d2 d3 : diagram g C} (CC1 : ColimCocone d1) (CC2 : ColimCocone d2) (CC3 : ColimCocone d3)
  (f : ∏ u : vertex g, C ⟦ dob d1 u, dob d2 u ⟧) (h : ∏ u : vertex g, C ⟦ dob d2 u, dob d3 u ⟧)
  (p : ∏ (u v : vertex g) (e : edge u v), dmor d1 e · f v = f u · dmor d2 e)
  (q : ∏ (u v : vertex g) (e : edge u v), dmor d2 e · h v = h u · dmor d3 e)
  : colimOfArrows () *)

  (*
    The data of the free functor C --> pointed_algebra_category F, i.e.
    - it's action on objects (transfinite_pointed_algebra)
    - it's action on morphisms (free_pointed_algebra_mor + compatibility with structure maps)
  *)
  Definition free_pointed_algebra_data : functor_data C (pointed_algebra_category F).
  Proof.
    exists transfinite_pointed_algebra.
    intros A B f.
    set (f' := free_pointed_algebra_mor f).
    exists f'.

    apply (colim_mor_eq (mapF_F_chain_CC A)); simpl.
    intros i.
    rewrite assoc.
    apply (transportb (λ x, x · _ = _) (colimArrowCommutes (mapF_F_chain_CC A) _ _ i)). 
    eapply pathscomp0. { exact (colimArrowCommutes (F_chain_CC A) _ _ (S i)). }
    simpl. apply pathsinv0.
    unfold colimIn at 1. simpl. rewrite assoc. rewrite <- functor_comp.
    eapply pathscomp0.
      { apply cancel_postcomposition.
        eapply maponpaths. 
        apply (colimArrowCommutes (F_chain_CC A)). }
    simpl.
    rewrite functor_comp. rewrite <- assoc.
    apply cancel_precomposition.
    apply (colimArrowCommutes (mapF_F_chain_CC B)).
  Defined.

  (* The free functor *)
  Definition free_pointed_algebra : C ⟶ pointed_algebra_category F.
  Proof.
    apply (make_functor free_pointed_algebra_data).
    split.
    + intros A. apply algebra_mor_eq. simpl.
      apply pathsinv0, colim_endo_is_identity. intros i.
      apply (pathscomp0 ltac:(eapply colimArrowCommutes)); simpl.
      apply (transportb (λ f, f · _ = _) ltac:(eapply functor_id)).
      apply id_left.
    + intros X Y Z f g. apply algebra_mor_eq.
      apply pathsinv0, (pathscomp0 ltac:(eapply precompWithColimOfArrows)).
      apply (maponpaths (colimArrow _ _)).
      apply cocone_paths; simpl. intros i.
      rewrite assoc. apply cancel_postcomposition, pathsinv0.
      apply functor_comp.
  Defined.

  (* We now prove that this is indeed the free functor, by constructing an adjunction *)

  Definition unit_FF_adjunction : functor_identity C ⟹ free_pointed_algebra ∙ forgetful.
  Proof.
    use make_nat_trans; red; simpl.
    { exact (λ A, colimIn (F_chain_CC A) 0). }
    intros A B f.
    apply pathsinv0.
    apply (pathscomp0 ltac:(eapply (colimArrowCommutes (F_chain_CC A) _ _ 0))); simpl.
    apply idpath.
  Defined.

  Definition counit_FF_cocone_arrows (X : pointed_algebra F) : ∏ i : nat, C ⟦ iter_functor F i X, X ⟧.
  Proof.
    induction i as [|i f]. { exact (identity X). }
    exact (# F f · algebra_map F X).
  Defined.

  Lemma counit_FF_cocone_arrows_rec (X : pointed_algebra F) (i : nat)
    : # F (counit_FF_cocone_arrows X i) · algebra_map F X
      = counit_FF_cocone_arrows X (S i).
  Proof.
    apply idpath.
  Defined.

  Definition counit_FF_forms_cocone (X : pointed_algebra F)
    : forms_cocone (F_chain X) (counit_FF_cocone_arrows X).
  Proof.
    red. intros i _ []; simpl. induction i; simpl in *.
    - rewrite assoc.
      apply (transportf (λ f, f · _ = _) ltac:(apply naturality_σ)).
      rewrite id_left. apply pathsinv0.
      apply X.
    - rewrite <- IHi. rewrite assoc.
      apply (transportf (λ f, f · _ = _) ltac:(apply naturality_σ)).
      rewrite <- assoc.
      eapply (transportf (λ x, _ · x = _) (pointed_algebra_ax X)).
      rewrite id_right. apply idpath.
  Defined.

  (* The counit has a component at the algebra X which is a morphism of algebras
    F^ω X --> X. This is the underlying morphism in C.
    (Be aware of the implicit coercion of X to it's underlying object in C)
   *)
  Definition counit_FF_map (X : pointed_algebra F) : colim (F_chain_CC X) --> X.
  Proof.
    apply colimArrow. use make_cocone.
    apply counit_FF_cocone_arrows.
    apply counit_FF_forms_cocone.
  Defined.

  Definition counit_FF_map_restricts_base (X : pointed_algebra F)
    : colimIn (F_chain_CC X) 0 · counit_FF_map X = identity X.
  Proof.
    apply colimArrowCommutes.
  Defined.

  Definition counit_FF_map_restricts_ind (X : pointed_algebra F) (i : nat)
    : colimIn (F_chain_CC X) (S i) · counit_FF_map X
      = # F (colimIn (F_chain_CC X) i · counit_FF_map X) · algebra_map F X.
  Proof.
    eapply pathscomp0.
    apply colimArrowCommutes.
    apply cancel_postcomposition.
    apply maponpaths.
    unfold counit_FF_map.
    rewrite colimArrowCommutes.
    simpl.
    apply idpath.
  Defined.

  Definition counit_FF_map_restricts (X : pointed_algebra F) (i : nat)
    : colimIn (F_chain_CC X) i · counit_FF_map X = counit_FF_cocone_arrows X i.
  Proof.
    apply colimArrowCommutes.
  Defined.

  Definition counit_FF_mor (X : pointed_algebra F) : free_pointed_algebra X --> X.
  Proof.
    exists (counit_FF_map X).
    apply (colim_mor_eq (mapF_F_chain_CC X)).
    intros i.
    rewrite assoc, assoc.
    rewrite transfinite_structure_map_commutes.
    eapply pathscomp0. { apply counit_FF_map_restricts_ind. }
    apply cancel_postcomposition.
    rewrite functor_comp.
    apply idpath.
  Defined.

  Definition counit_FF_adjunction : forgetful ∙ free_pointed_algebra ⟹ functor_identity (pointed_algebra_category F).
  Proof.
    use make_nat_trans. { exact counit_FF_mor. }

    intros X Y f. apply algebra_mor_eq; simpl. unfold free_pointed_algebra_mor.
    apply colim_mor_eq. intros i. rewrite assoc, assoc.
    unfold colimOfArrows, counit_FF_map.
    rewrite colimArrowCommutes, colimArrowCommutes.
    unfold coconeIn, make_cocone, pr1. rewrite <- assoc.
    rewrite colimArrowCommutes; simpl.
    induction i; simpl.
    + rewrite id_left, id_right. apply idpath.
    + rewrite assoc. rewrite <- functor_comp. rewrite IHi.
      rewrite functor_comp, <- assoc, <-assoc.
      rewrite algebra_mor_commutes.
      apply idpath.
  Defined.

  (* The adjunction witnessing that the free pointed-algebra functor is indeed free *)
  Definition free_forgetful_adjunction : adjunction C (pointed_algebra_category F).
  Proof.
    use make_adjunction.
    - use make_adjunction_data.
      + exact free_pointed_algebra.
      + exact forgetful.
      + exact unit_FF_adjunction.
      + exact counit_FF_adjunction.
    - split.
      + intro A. apply algebra_mor_eq, pathsinv0; simpl.
        apply colim_endo_is_identity. intros i.
        rewrite (assoc (colimIn _ _)).
        unfold free_pointed_algebra_mor, colimOfArrows.
        rewrite colimArrowCommutes. simpl.
        rewrite <- assoc.
        apply (transportb (λ x, _ · x = _) (counit_FF_map_restricts (transfinite_pointed_algebra A) i)).
        induction i. { apply id_right. }
        simpl.
        rewrite assoc, <- functor_comp.
        apply (transportb (λ x, # F x · _ = _) IHi).
        apply transfinite_structure_map_commutes.

      + intro X. simpl. apply counit_FF_map_restricts_base.
  Defined.

  Corollary are_adjoints_FF : are_adjoints free_pointed_algebra forgetful.
  Proof. exact free_forgetful_adjunction. Defined.


End WellPointedHasFree.