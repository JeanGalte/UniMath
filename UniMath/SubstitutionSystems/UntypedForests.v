Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.
Require Import UniMath.Combinatorics.StandardFiniteSets.

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

Local Open Scope cat.

Section Signature.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).

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

(* Sort des variables *)
Definition sv : ⟦3⟧%stn := make_stn 3 0 a.
(* Sort des termes *)
Definition st : ⟦3⟧%stn := make_stn 3 0 b.
(* Sort des sommes, ou eliminations alternatives *)
Definition se : ⟦3⟧%stn := make_stn 3 0 c.

Definition UntypedForestSig : MultiSortedSig (⟦3⟧%stn).
Proof.
  use (make_MultiSortedSig synclass).
  - apply (( (unit,,isasetunit) + (nat,,isasetnat) )%set).
    - intros H. induction H  as [abs | app].
      + exact ((((sv :: []) ,,st) :: []),,st).
      + induction app.
        * exact ((([] ,,sv ) :: nil),, se).
        *
End Signature.
