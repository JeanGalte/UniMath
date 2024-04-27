Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.PartB.
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
Require Import UniMath.SubstitutionSystems.SortIndexing.

Local Open Scope cat.

Section Signature.

(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).

Context (atom : hSet) (otype : hSet) (atotype : atom -> otype) (arr : otype → otype → otype) (plus : list otype -> otype).

Local Notation "s ⇒ t" := (arr s t).
Local Notation "0" := (plus nil).

(*
Coïncide avec les "sortes" pour la version non typée du calcul : variables, elimination alternatives, et termes
*)
Definition syntcat : UU := stn 3.

(* Sorte des variables *)
Definition sv : syntcat := make_stn 3 0 (idpath true : 0 < 3).
(* Sorte des termes *)
Definition st : syntcat := make_stn 3 0 (idpath true : 1 < 3).
(* Sorte des sommes, ou eliminations alternatives *)
Definition se : syntcat := make_stn 3 0 (idpath true : 2 < 3).

Definition sort : UU := otype × syntcat.

Local Definition Hotype : isofhlevel 3 otype := MultiSortedBindingSig.STLC_Hsort otype.

Local Definition Hsyntcat : isofhlevel 3 syntcat := isofhlevelssnset 1 syntcat (setproperty (stnset 3)).

Local Definition Hsort : isofhlevel 3 sort := isofhleveldirprod 3 otype syntcat Hotype Hsyntcat.

(* fin de la partie à regarder *)

Let sortToSet : category := SortIndexing.sortToSet sort Hsort.
Let sortToSetSet : category := SortIndexing.sortToSetSet sort Hsort.
Let sortToSet2 : category := SortIndexing.sortToSet2 sort Hsort.

Definition TsortToSetSet : Terminal sortToSetSet := TsortToCC _ Hsort HSET TerminalHSET.

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

Definition n_list_sorts (s : sort) (n : nat) : list(list sort × sort).
Proof.
    use tpair.
    - exact n.
    - apply weqvecfun.
      intro i. apply([],,s).
Defined.

Definition Forest_Sig : MultiSortedSig sort.
Proof.
  use (make_MultiSortedSig sort ).
  - apply ((((sort × sort) + (nat,,isasetnat)) + (nat,, isasetnat))%set).
    - intros H. induction H  as [term_construct | elim_construct].
      + induction term_construct as [abs|sum].
        * induction abs as [s t].
           exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,t).

        * exact ((n_list_sorts se sum) ,, st ).
      + exact ( (([],,sv) :: (n_list_sorts st elim_construct)),, se).
Defined.

(** The canonical functor associated with Forest_Sig **)
Definition Forest_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET Forest_Sig.


(** the functor of which the fixed points are considered *)
Definition Forest_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToSet BCsortToSet Forest_Functor_H.

(** the canonical strength associated with UntypedForest_Sig *)
Let θForest := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET Forest_Sig.

Definition ctx_ext (ξ : sortToSet) (s : sort) : sortToSet
  := sorted_option_functorSet s ξ.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for Forests *)
Let σind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort Forest_Sig.
Let σcoind : SigmaMonoid θForest := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort Forest_Sig.

Section IndAndCoind.

Context (σ : SigmaMonoid θForest).

Definition Forest_gen : sortToSet2 := SigmaMonoid_carrier θForest σ.

(** the type of terms in a context of a sort *)
Definition Forest_gen_ctx_sort (ξ : sortToSet) (s : sort) : UU
  := pr1 (pr1 (pr1 Forest_gen ξ) s).

(** variable inclusion for syntax for forests *)
Definition Forest_eta_gen : sortToSet2⟦Id,Forest_gen⟧ := SigmaMonoid_η θForest σ.

Definition Forest_eta_gen_natural (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
# Id f · pr1 Forest_eta_gen ξ' = pr1 Forest_eta_gen ξ · # (pr1 Forest_gen) f
:= nat_trans_ax (Forest_eta_gen) ξ ξ' f.

Lemma Forest_eta_gen_natural' (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) :
  f · pr1 Forest_eta_gen ξ' = pr1 Forest_eta_gen ξ · # (pr1 Forest_gen) f.
Proof.
  etrans.
  2: { apply Forest_eta_gen_natural. }
  apply idpath.
Qed.

Lemma Forest_eta_gen_natural'_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 f u · pr1 (pr1 Forest_eta_gen ξ') u = pr1 (pr1 Forest_eta_gen ξ) u · pr1 (# (pr1 Forest_gen) f) u.
Proof.
  apply (nat_trans_eq_weq HSET _ _ (Forest_eta_gen_natural' ξ ξ' f)).
Qed.

Lemma Forest_eta_gen_natural'_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort) (elem : pr1 (pr1 (pr1 ξ) u)) :
  pr1 (pr1 Forest_eta_gen ξ') u (pr1 f u elem) =  pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 Forest_eta_gen ξ) u elem).
Proof.
  apply (toforallpaths _ _ _ (Forest_eta_gen_natural'_pointwise ξ ξ' f u)).
Qed.

Definition Forest_tau_gen : Forest_Functor_H Forest_gen --> Forest_gen := SigmaMonoid_τ θForest σ.

Definition app_source_gen (n : nat) : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inr n)) Forest_gen.

Definition app_source_gen_newstyle_zero : sortToSet2 :=
  functor_compose Forest_gen (projSortToSet sv ∙ hat_functorSet st).


Definition app_source_gen_newstyle_nonzero_aux (n : nat) : sortToSet2 :=
   nat_rect (fun _ =>  sortToSet2)
     (functor_compose Forest_gen (projSortToSet se ∙ hat_functorSet st))
     (fun _ IHn => BinProduct_of_functors BPsortToSet
                  (functor_compose Forest_gen (projSortToSet se ∙
hat_functorSet st)) IHn) n.

Definition app_source_gen_newstyle_nonzero (n : nat) : sortToSet2 :=
      BinProduct_of_functors BPsortToSet
        (functor_compose Forest_gen (projSortToSet sv ∙ hat_functorSet st))
        (app_source_gen_newstyle_nonzero_aux n).


Lemma app_source_gen_nonzero_eq (n : nat):
   app_source_gen (S n) = BinProduct_of_functors BPsortToSet
     (functor_compose Forest_gen (projSortToSet sv ∙ hat_functorSet st))
(ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized
sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET
CoproductsHSET ((n_list_sorts st (S n),,se)) Forest_gen).
Proof.
   apply idpath.
Qed.

Lemma app_source_gen_newstyle_nonzero_aux_eq (n : nat):
   app_source_gen_newstyle_nonzero_aux n =
ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort
Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET
((n_list_sorts st (S n),,se)) Forest_gen.
Proof.
   induction n.
   - apply idpath.
   - change (app_source_gen_newstyle_nonzero_aux (S n)) with
       (BinProduct_of_functors BPsortToSet
       (functor_compose Forest_gen (projSortToSet se ∙ hat_functorSet st))
       (app_source_gen_newstyle_nonzero_aux n)).
     rewrite IHn.
     apply idpath.
Qed.


Lemma app_source_zero_gen_ok : app_source_gen_newstyle_zero = app_source_gen 0.
Proof.
  apply idpath.
Qed.

Lemma app_source_nonzero_gen_ok (n : nat) : app_source_gen_newstyle_nonzero n = app_source_gen (S n).
Proof.
   unfold app_source_gen_newstyle_nonzero.
   rewrite app_source_gen_newstyle_nonzero_aux_eq.
   apply idpath.
Qed.

Definition app_map_gen (n : nat) : sortToSet2⟦app_source_gen n,Forest_gen⟧.
  Proof.
    exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inr n) · Forest_tau_gen) .
  Defined.

Definition app_map_gen_natural (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (app_source_gen n)) f · pr1 (app_map_gen n) ξ' = pr1 (app_map_gen n) ξ · # (pr1 Forest_gen) f
    := nat_trans_ax (app_map_gen n) ξ ξ' f.

Lemma app_map_gen_natural_pointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet  ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 (# (pr1 (app_source_gen n)) f) u · pr1 (pr1 (app_map_gen n) ξ') u =
  pr1 (pr1 (app_map_gen n) ξ) u · pr1 (# (pr1 Forest_gen) f) u.
Proof.
   apply (nat_trans_eq_weq HSET _ _ (app_map_gen_natural n ξ ξ' f)).
Qed.

Lemma app_map_gen_natural_ppointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (app_source_gen n) ξ) u)) :
    pr1 (pr1 (app_map_gen n) ξ') u (pr1 (# (pr1 (app_source_gen n)) f) u elem) =
      pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 (app_map_gen n) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (app_map_gen_natural_pointwise n ξ ξ' f u)).
  Qed.

Definition lam_source_gen_newstyle :  sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functorSet sv)
         Forest_gen)
      (projSortToSet st ∙ hat_functorSet st).

Definition lam_source_gen : sortToSet2 :=
  ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inl (inl tt ))) Forest_gen.

Lemma lam_source_ok : lam_source_gen = lam_source_gen_newstyle.
Proof.
  apply idpath.
Qed.

Definition lam_map_gen : sortToSet2⟦lam_source_gen ,Forest_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (inl (inl tt)) · Forest_tau_gen.

Definition lam_map_gen_natural (ξ ξ' : sortToSet) (f :  sortToSet ⟦ ξ, ξ' ⟧)
  : # (pr1 lam_source_gen) f · pr1 lam_map_gen ξ' = (pr1 lam_map_gen ξ) · # (pr1 Forest_gen) f
  := nat_trans_ax lam_map_gen ξ ξ' f.

Lemma lam_map_gen_natural_pointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 lam_source_gen) f) u · pr1 (pr1 lam_map_gen ξ') u =
        pr1 (pr1 lam_map_gen ξ) u · pr1 (# (pr1 Forest_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (lam_map_gen_natural ξ ξ' f)).
  Qed.

Lemma lam_map_gen_natural_ppointwise (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 lam_source_gen ξ) u)) :
    pr1 (pr1 lam_map_gen ξ') u (pr1 (# (pr1 lam_source_gen) f) u elem) =
      pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 lam_map_gen ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (lam_map_gen_natural_pointwise ξ ξ' f u)).
Qed.

Definition sum_source_gen (n : nat) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort Forest_Sig (inl (inr n))) Forest_gen.

Definition sum_source_gen_newstyle_zero : sortToSet2 :=
  functor_compose TsortToSetSet (hat_functorSet st).

Definition sum_source_gen_newstyle_nonzero (n : nat) : sortToSet2 :=
  nat_rect (fun _ =>  sortToSet2)
  (functor_compose Forest_gen (projSortToSet se ∙ hat_functorSet st))
  (fun _ IHn => BinProduct_of_functors BPsortToSet
    (functor_compose Forest_gen (projSortToSet se ∙ hat_functorSet st)) IHn) n.

Lemma sum_source_zero_gen_ok : sum_source_gen_newstyle_zero = sum_source_gen 0.
Proof.
   apply idpath.
Qed.

Lemma sum_source_gen_nonzero_eq (n : nat) :
  sum_source_gen n = ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort
Hsort SET TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET
((n_list_sorts se n,,st)) Forest_gen.
Proof.
  induction n.
  -apply idpath.
  -change (sum_source_gen (S n)) with
     (BinProduct_of_functors BPsortToSet
        (functor_compose Forest_gen (projSortToSet se ∙ hat_functorSet st))
        (sum_source_gen_newstyle_nonzero n)).

   (*
     Le code bloque à cet endroit.
    *)


Lemma sum_source_nonzero_gen_ok (n : nat) : sum_source_gen_newstyle_nonzero n = sum_source_gen n.
Proof.
  unfold sum_source_gen_newstyle_nonzero.
  rewrite sum_source_gen_newstyle_aux

Definition sum_map_gen (n : nat) : sortToSet2⟦sum_source_gen n,Forest_gen⟧.
  Proof.
    exact (CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _ , _ )) (inl (inr n)) · Forest_tau_gen) .
  Defined.

Definition sum_map_gen_natural (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    : # (pr1 (sum_source_gen n)) f · pr1 (sum_map_gen n) ξ' = pr1 (sum_map_gen n) ξ · # (pr1 Forest_gen) f
    := nat_trans_ax (sum_map_gen n) ξ ξ' f.

Lemma sum_map_gen_natural_pointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet  ⟦ ξ, ξ' ⟧) (u : sort) :
  pr1 (# (pr1 (sum_source_gen n)) f) u · pr1 (pr1 (sum_map_gen n) ξ') u =
  pr1 (pr1 (sum_map_gen n) ξ) u · pr1 (# (pr1 Forest_gen) f) u.
Proof.
   apply (nat_trans_eq_weq HSET _ _ (sum_map_gen_natural n ξ ξ' f)).
Qed.

Lemma sum_map_gen_natural_ppointwise (n : nat) (ξ ξ' : sortToSet) (f : sortToSet ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (sum_source_gen n) ξ) u)) :
    pr1 (pr1 (sum_map_gen n) ξ') u (pr1 (# (pr1 (sum_source_gen n)) f) u elem) =
      pr1 (# (pr1 Forest_gen) f) u (pr1 (pr1 (sum_map_gen n) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (sum_map_gen_natural_pointwise n ξ ξ' f u)).
  Qed.


End IndAndCoind.

End Signature.
