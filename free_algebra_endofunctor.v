Require Import UniMath.Foundations.All.
Require Import UniMath.CategoryTheory.Core.Prelude.
Require Import UniMath.CategoryTheory.Monads.Monads.
Require Import UniMath.CategoryTheory.Limits.Graphs.Colimits.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.whiskering.

Local Open Scope cat.

Definition map_ColimCocone {C D : category} {g : graph} (d : diagram g C) {F : C ⟶ D}
  (H : preserves_colimits_of_shape F g) : ColimCocone d → ColimCocone (mapdiagram F d).
Proof.
  intros CC.
  use make_ColimCocone.
  - exact (F (colim CC)).
  - exact (mapcocone F d (colimCocone CC)).
  - apply H. apply CC.
Defined.

Section FreeAlgebraEndofunctor.

Context {C : category}.
Context (chain_colimits : Chains C).
Context (F : C ⟶ C).
Context (F_omega_cocont : is_omega_cocont F).
Context (bin : BinCoproducts C).


Definition expand_chain_fun (i : nat) : C ⟶ C.
Proof.
  induction i as [|i func].
  - exact (functor_identity C).
  - exact (BinCoproduct_of_functors C C bin (functor_identity C) (func ∙ F)).
Defined.

Definition expand_chain_ob (i : nat) (A : C) : C.
Proof.
  induction i as [|i ob].
  - exact A.
  - exact (bin A (F ob)).
Defined.

Definition expand_chain_mor (i : nat) (A : C) :
  expand_chain_fun i A --> expand_chain_fun (S i) A.
Proof.
  induction i as [|i mor].
  - apply BinCoproductIn1.
  - apply BinCoproductArrow.
    + apply BinCoproductIn1.
    + refine (# F mor · _). apply BinCoproductIn2.
Defined.

Definition expand_chain_trans (i : nat) : expand_chain_fun i ⟹ expand_chain_fun (S i).
Proof.
  induction i as [|i trans].
  - apply coproduct_nat_trans_in1.
  - change (expand_chain_fun (S i)) with (BinCoproduct_of_functors C C bin (functor_identity C) (expand_chain_fun i ∙ F)).
    change (expand_chain_fun (S (S i))) with (BinCoproduct_of_functors C C bin (functor_identity C) (expand_chain_fun (S i) ∙ F)).
    apply (coproduct_nat_trans C C).
    + apply coproduct_nat_trans_in1.
    + refine (nat_trans_comp _ _ _ _ (coproduct_nat_trans_in2 _ _ _ _ _)).
      exact (post_whisker trans F).
Defined.

Lemma expand_chain_trans_pointwise (i : nat) (A : C)
  : expand_chain_trans i A = expand_chain_mor i A.
Proof.
  induction i.
  - apply idpath.
  - simpl. unfold coproduct_nat_trans_data. simpl.
    apply BinCoproductArrowUnique.
    + apply BinCoproductIn1Commutes.
    + rewrite BinCoproductIn2Commutes.
      rewrite <- IHi.
      apply cancel_precomposition. apply idpath.
Defined.

Definition expand_chain : chain [C,C].
Proof.
  exists (expand_chain_fun).
  intros i _ []. exact (expand_chain_trans i).
Defined.

Let CC : ColimCocone (expand_chain)
  := ColimFunctorCocone expand_chain (λ _, chain_colimits _).

Let Fstar : C ⟶ C := colim CC.

Definition shift_expand_cocone_arrow (A : C) (i : nat) : F (expand_chain_fun i A) --> (Fstar A).
Proof.
  exact (BinCoproductIn2 (bin A (F (expand_chain_fun i A))) · (colimIn CC (S i) : _ ⟹ _) A).
Defined.

Lemma helpful (i : nat) (A : C)
  : expand_chain_mor i A · colimIn (chain_colimits (diagram_pointwise expand_chain A)) (S i)
    = colimIn (chain_colimits (diagram_pointwise expand_chain A)) i.
Proof.
  rewrite <- expand_chain_trans_pointwise.
  apply (colimInCommutes (chain_colimits (diagram_pointwise expand_chain A)) i (S i) (idpath (S i))).
Defined.

Definition shift_expand_arrow (A : C) : F (Fstar A) --> Fstar A.
Proof.
  apply (colimArrow (map_ColimCocone (diagram_pointwise expand_chain A) F_omega_cocont (chain_colimits _))).
  exists (shift_expand_cocone_arrow A).
  intros i _ []. unfold shift_expand_cocone_arrow. simpl.
  rewrite <- (helpful (S i)).
  do 2 rewrite assoc. apply cancel_postcomposition.
  simpl.
  rewrite <- expand_chain_trans_pointwise.
  apply pathsinv0, BinCoproductIn2Commutes.
Defined.

Definition multiplication : Fstar ∙ Fstar ⟹ Fstar.
Proof.
  use make_nat_trans; red.
  - intros A.
    apply colimArrow.
    use tpair.
    + intros i.
      change (dob (diagram_pointwise expand_chain (Fstar A)) i) with (expand_chain_fun i (Fstar A)).
      induction i.
      * exact (identity _).
      * change (expand_chain_fun (S i) (Fstar A)) with (bin (Fstar A) (F ((expand_chain_fun i) (Fstar A))) : C).
        apply (BinCoproductArrow _ (identity _)).
        refine (# F IHi · _).
        exact (shift_expand_arrow A).
    + intros i _ []; simpl.
      admit.
  - admit.
Admitted.

Definition free_monad : Monad C.
Proof.
  exists Fstar.
  use tpair; red.
  - split.
    + admit.
    + exact (colimIn CC 0).
  - admit.
Admitted.

End FreeAlgebraEndofunctor.