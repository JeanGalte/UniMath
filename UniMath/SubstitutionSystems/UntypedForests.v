Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.Vectors.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.FunctorAlgebras.
Require Import UniMath.CategoryTheory.FunctorCoalgebras.
Require Import UniMath.CategoryTheory.Categories.StandardCategories.
Require Import UniMath.CategoryTheory.Groupoids.
Require Import UniMath.CategoryTheory.Limits.Initial.
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.CategoryTheory.Limits.BinCoproducts.
Require Import UniMath.CategoryTheory.Limits.Coproducts.
Require Import UniMath.CategoryTheory.Limits.BinProducts.
Require Import UniMath.CategoryTheory.Chains.Chains.
Require Import UniMath.CategoryTheory.Chains.Cochains.
Require Import UniMath.CategoryTheory.Categories.HSET.Core.
Require Import UniMath.CategoryTheory.Categories.HSET.Colimits.
Require Import UniMath.CategoryTheory.Categories.HSET.Limits.
Require Import UniMath.CategoryTheory.Categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Categories.HSET.Univalence.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require UniMath.SubstitutionSystems.SortIndexing.
Require Import UniMath.SubstitutionSystems.MultiSortedBindingSig.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require UniMath.SubstitutionSystems.MultiSortedMonadConstruction_alt.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.

Local Open Scope cat.

Section Signature.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).

Definition sort : UU := stn 3.

(* À prouver *)
Local Definition  Hsort : isofhlevel 3 sort.
Proof.
Admitted.

(* Voir comment contracter ces définitions *)
Definition a : 0 < 3.
Proof.
  simpl.
  apply idpath.
Qed.

Definition b : 1 < 3.
Proof.
  simpl.
  apply idpath.
Qed.

Definition c : 2 < 3.
Proof.
  simpl.
  apply idpath.
Qed.

(* Sorte des variables *)
Definition sv : sort := make_stn 3 0 a.
(* Sorte des termes *)
Definition st : sort := make_stn 3 0 b.
(* Sorte des sommes, ou eliminations alternatives *)
Definition se : sort := make_stn 3 0 c.

Let sortToSet : category := SortIndexing.sortToSet sort Hsort.
Let sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Let sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.


Let projSortToSet : sort -> sortToSetSet := MultiSortedMonadConstruction_alt.projSortToSet sort Hsort.
Let projSortToSetvariable : (sort → sort) → sortToSet2 := projSortToCvariable sort Hsort HSET.
Let hat_functorSet : sort -> HSET ⟶ sortToSet := MultiSortedMonadConstruction_alt.hat_functorSet sort Hsort.
Let sorted_option_functorSet : sort → functor sortToSet sortToSet := MultiSortedMonadConstruction_alt.sorted_option_functorSet sort Hsort.

Local Definition BCsortToSet : BinCoproducts sortToSet := SortIndexing.BCsortToSet sort Hsort.
Local Definition BPsortToSet : BinProducts sortToSet := SortIndexing.BPsortToSet sort Hsort.

Local Definition TsortToSet : Terminal sortToSet := SortIndexing.TsortToSet sort Hsort.
Local Definition TsortToSet2 : Terminal sortToSet2 := SortIndexing.TsortToSet2 sort Hsort.

Local Definition BPsortToSetSet : BinProducts sortToSetSet := SortIndexing.BPsortToSetSet sort Hsort.

Local Lemma sortToSet2_comp_on_mor (F G : sortToSet2) {ξ ξ' : sortToSet} (f : sortToSet⟦ ξ, ξ' ⟧) (s : sort) (* (elem : pr1 (pr1 (pr1 (functor_compose F G) ξ) s)) *) :
  pr1 (# (pr1 (functor_compose F G)) f) s = pr1 (# (pr1 G) (# (pr1 F) f)) s.
Proof.
  apply idpath.
Qed.

Lemma postcomp_with_projSortToSet_on_mor (F : sortToSet2) (s: sort) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
  (arg : pr1 (pr1 (functor_compose F (projSortToSet s)) ξ))
  : # (pr1 (functor_compose F (projSortToSet s))) f arg = pr1 (# (pr1 F) f) s arg.
Proof.
  apply idpath.
Qed.

Definition app_list_noind (n : nat) : list(list sort × sort).
Proof.
    use tpair.
    - exact n.
    - apply weqvecfun.
      intro i. apply ( ([],,se) :: []).
  Defined.


Definition UntypedForest_Sig : MultiSortedSig (⟦3⟧%stn).
Proof.
  use (make_MultiSortedSig (stn 3)).
  - apply (( (unit,,isasetunit) + (nat,,isasetnat) )%set).
    - intros H. induction H  as [abs | app].
      + exact ((((sv :: []) ,,st) :: []),,st).
      + exact ( (app_list_noind  app) ,, st).
Defined.

(** The canonical functor associated with Untypedforest_Sig **)
Definition Forest_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET UntypedForest_Sig.


(** the functor of which the fixed points are considered *)
Definition Forest_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToSet BCsortToSet Forest_Functor_H.

(** the canonical strength associated with UntypedForest_Sig *)
Let θForest := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET UntypedForest_Sig.

Definition ctx_ext (ξ : sortToSet) (s : sort) : sortToSet
  := sorted_option_functorSet s ξ.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for Forests *)
Let σind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort UntypedForest_Sig.
Let σcoind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort UntypedForest_Sig.



End Signature.
