 (**

Syntax of the mono typed lambda calculus as a
multisorted signature.

2024 (adapted from STLC_alt.v)

 *)
Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Sets.

Require Import UniMath.MoreFoundations.Tactics.

Require Import UniMath.Combinatorics.Lists.

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
Require Import UniMath.CategoryTheory.Limits.Terminal.
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.
Require Import UniMath.SubstitutionSystems.STLC_alt.

Local Open Scope cat.
Section A.
  Context (sort : hSet).
  Local Lemma Hsort : isofhlevel 3 sort.
  Proof.
    exact (isofhlevelssnset 1 sort (setproperty sort)).
  Defined.
  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Let BPsortToHSET : BinProducts sortToHSET := BinProducts_functor_precat _ _ BinProductsHSET.
  Let BCsortToHSET : BinCoproducts sortToHSET := BinCoproducts_functor_precat _ _ BinCoproductsHSET.
Let terminal_sortToHSET : Terminal sortToHSET := Terminal_functor_precat _ _ TerminalHSET.


  Local Lemma BinProd : BinProducts [sortToHSET,HSET].
  Proof.
    apply BinProducts_functor_precat, BinProductsHSET.
  Defined.
(** Some notations *)
Local Infix "::" := (@cons _).
Local Notation "[]" := (@nil _) (at level 0, format "[]").
Local Notation "a + b" := (setcoprod a b) : set.
Local Notation "'Id'" := (functor_identity _).
(*Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)). *)
(* Local Notation "'1'" := (TerminalObject TerminalSortToSet). *)
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

Let sortToSet2 := [sortToHSET,sortToHSET].

Let terminal_sortToSet2 : Terminal sortToSet2 := Terminal_functor_precat sortToHSET sortToHSET terminal_sortToHSET.

Lemma postcomp_with_projSortToC_on_mor (F : sortToSet2) (s: sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
  (arg : pr1 (pr1 (functor_compose F (projSortToC sort Hsort SET s)) ξ))
  : # (pr1 (functor_compose F (projSortToC sort Hsort SET s))) f arg = pr1 (# (pr1 F) f) s arg.
Proof.
  apply idpath.
Qed.

                                         (** The signature of the monotyped lambda calculus *)
Definition LC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply (sort + sort )%set.
- intros H; induction H as [s_app|s_abs].
  + exact ((([],,s_app) :: ([],,s_app) ::  nil),,s_app).
  + exact (((cons s_abs [],,s_abs) :: []),,s_abs).
Defined.
(** the canonical functor associated with LC_Sig *)
Definition LC_Functor_H : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET LC_Sig.
(** the functor of which the fixed points are considered *)
Definition LC_Functor_Id_H : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToHSET BCsortToHSET LC_Functor_H.
(** the canonical strength associated with LC_Sig *)
Let θLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET LC_Sig.
Definition ctx_ext (ξ : sortToHSET) (s : sort) : sortToHSET
  := pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) ξ.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for monotyped lambda calculus *)
Let σind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort LC_Sig.
Let σcoind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort LC_Sig.
Section IndAndCoind.
  Context (σ : SigmaMonoid θLC).
  (** the functor representing the syntax for STLC**)
  Definition LC_gen : sortToSet2 := SigmaMonoid_carrier θLC σ.
  (** the functor associated to lambda calculus terms without the context of a sort**)
  Definition LC_gen_ctx (ξ : sortToHSET) : sortToHSET := pr1 LC_gen ξ.
  (** the type of monotyped lambda calculus terms in a context of a sort *)
  Definition LC_gen_ctx_sort (ξ : sortToHSET) (s : sort) : UU
    := pr1 (pr1 (LC_gen_ctx ξ) s).
                                                                           (** variable inclusion for syntax for monotyped LC *)
  Definition LC_eta_gen : sortToSet2⟦Id,LC_gen⟧ := SigmaMonoid_η θLC σ.
                                                                      Definition LC_eta_gen_natural (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) :
    # Id f · pr1 LC_eta_gen ξ' = pr1 LC_eta_gen ξ · # (pr1 LC_gen) f
                                                                        := nat_trans_ax (LC_eta_gen) ξ ξ' f.

  Lemma LC_eta_gen_natural' (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) :
    f · pr1 LC_eta_gen ξ' = pr1 LC_eta_gen ξ · # (pr1 LC_gen) f.
  Proof.
    etrans.
    2: { apply LC_eta_gen_natural. }
    apply idpath.
  Qed.

  Lemma LC_eta_gen_natural'_pointwise (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) (u : sort) :
    pr1 f u · pr1 (pr1 LC_eta_gen ξ') u = pr1 (pr1 LC_eta_gen ξ) u · pr1 (# (pr1 LC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (LC_eta_gen_natural' ξ ξ' f)).
  Qed.


  Lemma LC_eta_gen_natural'_ppointwise (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) (u : sort) (elem : pr1 (pr1 (pr1 ξ) u)) :
    pr1 (pr1 LC_eta_gen ξ') u (pr1 f u elem) =  pr1 (# (pr1 LC_gen) f) u (pr1 (pr1 LC_eta_gen ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (LC_eta_gen_natural'_pointwise ξ ξ' f u)).
  Qed.
                                                                      (** the algebra maps (the "domain-specific constructors") for monotyped LC *)
  Definition LC_tau_gen : LC_Functor_H LC_gen --> LC_gen  := SigmaMonoid_τ θLC σ.
  Definition app_source_gen_newstyle (s : sort) : sortToSet2 :=
    BinProduct_of_functors BPsortToHSET
      (functor_compose LC_gen
         (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s))
      (functor_compose LC_gen
         (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s)).
Definition app_source_gen (s : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort LC_Sig (inl s)) LC_gen.

  Lemma app_source_gen_ok (s : sort) : app_source_gen s  = app_source_gen_newstyle s.
  Proof.
    apply idpath.
  Qed.

  Lemma app_source_gen_mor_pr1 (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    (u : sort) (arg : pr1 (pr1 (pr1 (app_source_gen s) ξ) u)) :
    pr1 (pr1 (# (pr1 (app_source_gen s)) f) u arg) =
      pr1 (# (pr1 (functor_compose LC_gen
                     (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s))) f) u (pr1 arg).
  Proof.
    apply idpath.
  Qed.

   Lemma app_source_gen_mor_pr2 (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    (u : sort) (arg : pr1 (pr1 (pr1 (app_source_gen s) ξ) u)) :
    pr2 (pr1 (# (pr1 (app_source_gen s)) f) u arg) =
      pr1 (# (pr1 (functor_compose LC_gen
                     (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s))) f) u (pr2 arg).
  Proof.
    apply idpath.
  Qed.

  (** The application constructor *)
  Definition app_map_gen (s : sort) : sortToSet2⟦app_source_gen s ,LC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 s) · LC_tau_gen.

  Definition app_map_gen_natural (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    : # (pr1 (app_source_gen s)) f · pr1 (app_map_gen s) ξ' = pr1 (app_map_gen s) ξ · # (pr1 LC_gen) f
    := nat_trans_ax (app_map_gen s) ξ ξ' f.

  Lemma app_map_gen_natural_pointwise (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (app_source_gen s)) f) u · pr1 (pr1 (app_map_gen s) ξ') u =
        pr1 (pr1 (app_map_gen s) ξ) u · pr1 (# (pr1 LC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (app_map_gen_natural s ξ ξ' f)).
  Qed.

  Lemma app_map_gen_natural_ppointwise (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (app_source_gen s) ξ) u)) :
    pr1 (pr1 (app_map_gen s) ξ') u (pr1 (# (pr1 (app_source_gen s)) f) u elem) =
      pr1 (# (pr1 LC_gen) f) u (pr1 (pr1 (app_map_gen s) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (app_map_gen_natural_pointwise s ξ ξ' f u)).
  Qed.

  Definition lam_source_gen_newstyle (s : sort) : sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
         LC_gen)
      (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s).

  Definition lam_source_gen (s : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort LC_Sig (inr s)) LC_gen.

  Lemma lam_source_gen_ok (s : sort) : lam_source_gen s = lam_source_gen_newstyle s.
  Proof.
    apply idpath.
  Qed.

  Lemma lam_source_gen_mor_pr2 (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    (u : sort) (pr : pr1 (pr1 (pr1 (lam_source_gen s) ξ) u))
    : pr2 (pr1 (# (pr1 (lam_source_gen s)) f) u pr) =
        # (pr1 (functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
         LC_gen)
      (projSortToC sort Hsort SET s))) f (pr2 pr).
  Proof.
    apply idpath.
  Qed.

 (**  lambda-abstraction constructor *)
  Definition lam_map_gen (s : sort) : sortToSet2⟦lam_source_gen s ,LC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 s) · LC_tau_gen.

   Definition lam_map_gen_natural (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    : # (pr1 (lam_source_gen s)) f · pr1 (lam_map_gen s) ξ' = pr1 (lam_map_gen s) ξ · # (pr1 LC_gen) f
    := nat_trans_ax (lam_map_gen s) ξ ξ' f.

  Lemma lam_map_gen_natural_pointwise (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) (u : sort)
    : pr1 (# (pr1 (lam_source_gen s)) f) u · pr1 (pr1 (lam_map_gen s) ξ') u =
        pr1 (pr1 (lam_map_gen s) ξ) u · pr1 (# (pr1 LC_gen) f) u.
  Proof.
    apply (nat_trans_eq_weq HSET _ _ (lam_map_gen_natural s ξ ξ' f)).
  Qed.

  Lemma lam_map_gen_natural_ppointwise (s : sort) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧)
    (u : sort) (elem : pr1 (pr1 (pr1 (lam_source_gen s) ξ) u)) :
    pr1 (pr1 (lam_map_gen s) ξ') u (pr1 (# (pr1 (lam_source_gen s)) f) u elem) =
      pr1 (# (pr1 LC_gen) f) u (pr1 (pr1 (lam_map_gen s) ξ) u elem).
  Proof.
    apply (toforallpaths _ _ _ (lam_map_gen_natural_pointwise s ξ ξ' f u)).
  Qed.

  Section Church.
    (** fix a sort, viewed as an atom *)
    Context (s : sort).
    Definition ChurchZero_gen (ξ : sortToHSET) : LC_gen_ctx_sort ξ s.
    Proof.
      (** abstract a first variable - forced to be of type s *)
      refine (pr1 (pr1 (lam_map_gen _) _) _ _).
      exists (idpath _).
      change (LC_gen_ctx_sort (ctx_ext ξ s) s).
      (** abstract a second variable - forced to be of type [s] *)
      refine (pr1 (pr1 (lam_map_gen _ ) _) _ _).
      exists (idpath _).
      change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s).
      (** take a variable *)
      simple refine (pr1 (pr1 LC_eta_gen _) _ _).
      cbn.
      (** the available variables are seen, pick the last added variable of type [s] *)
      apply ii1.
      exists (idpath _).
      exact tt.
    Defined.

    Definition ChurchOne_gen (ξ : sortToHSET) : LC_gen_ctx_sort ξ s.
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ ) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ ) _) _ _).
      exists (idpath _).
      (** do an application with argument type [s] - not giving this argument would slow down the further steps *)
      refine (pr1 (pr1 (app_map_gen s ) _) _ _).
      split; exists (idpath _).
      - change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s).
        simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        (** the available variables are seen, pick the first added variable of type s *)
        apply ii2.
        apply ii1.
        exists (idpath _).
        exact tt.
      - change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s).
        simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        (** pick the last added variable of type [s] *)
        apply ii1.
        exists (idpath _).
        exact tt.
    Defined.

    Definition Church_gen_body (n : nat) (ξ : sortToHSET) : LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s.
    Proof.
      induction n.
      - simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        apply ii1.
        exists (idpath _).
        exact tt.
      - refine (pr1 (pr1 (app_map_gen s) _) _ _).
        split; exists (idpath _).
        + change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s).
          simple refine (pr1 (pr1 LC_eta_gen _) _ _).
          cbn.
          apply ii2.
          apply ii1.
          exists (idpath _).
          exact tt.
        + exact IHn.
    Defined.

    Lemma Church_gen_body_rec_eq (n : nat) (ξ : sortToHSET) :
      Church_gen_body (S n) ξ =
        pr1 (pr1 (app_map_gen s) (ctx_ext (ctx_ext ξ s) s)) s
     ((idpath s,,
       pr1 (pr1 LC_eta_gen (ctx_ext (ctx_ext ξ s) s)) s
         (inr (inl (idpath s,, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ s) s)) s))),,
        idpath s,, Church_gen_body n ξ).
    Proof.
      apply idpath.
    Qed.

    Definition Church_gen_header (ξ : sortToHSET) :
      LC_gen_ctx_sort (ctx_ext (ctx_ext ξ s) s) s -> LC_gen_ctx_sort ξ s.
    Proof.
      intro body.
      refine (pr1 (pr1 (lam_map_gen _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _) _) _ _).
      exists (idpath _).
      exact body.
    Defined.

    Definition Church_gen (n : nat) (ξ : sortToHSET) : LC_gen_ctx_sort ξ s
       := Church_gen_header ξ (Church_gen_body n ξ).

  End Church.

  Section Church_functor.

   Definition Church_gen_body_target_data: functor_data sortToHSET sortToHSET.
    Proof.
      use make_functor_data.
      - intro ξ.
        apply (functor_path_pregroupoid Hsort).
        intro s.
        exact (pr1 (pr1 LC_gen (ctx_ext (ctx_ext ξ s) s)) s).
        (** this is the pointwise formula - with context and sort argument *)
      - intros ξ ξ' f.
        apply nat_trans_functor_path_pregroupoid.
        intro s.
        simpl.
        exact (pr1 (# (pr1 LC_gen)
                      (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
                         (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) f))) s).
    Defined.

    Lemma Church_gen_body_target_data_ok : is_functor Church_gen_body_target_data.
    Proof.
      split; red.
      - intro ξ.
        apply nat_trans_eq; try apply HSET.
        intro s.
        apply funextfun.
        intro elem.
        unfold functor_on_morphisms.
        unfold Church_gen_body_target_data.
        unfold pr2.
        unfold make_functor_data.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold pr1.
        do 2 rewrite functor_id.
        rewrite (functor_id LC_gen).
        apply idpath.
      - intros ξ1 ξ2 ξ3 f g.
        apply nat_trans_eq; try apply HSET.
        intro s.
        apply funextfun.
        intro elem.
        unfold functor_on_morphisms.
        unfold Church_gen_body_target_data.
        unfold make_functor_data.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        unfold pr2.
        unfold nat_trans_data_from_nat_trans_funclass.
        unfold pr1.
        do 2 rewrite functor_comp.
        rewrite (functor_comp LC_gen).
        apply idpath.
    Qed.

    Definition Church_gen_body_target : sortToSet2 := _,, Church_gen_body_target_data_ok.

    Definition Church_gen_body_sortToHSET_data (n : nat) (ξ : sortToHSET) : global_element terminal_sortToHSET (pr1 Church_gen_body_target ξ).
    Proof.
      use nat_trans_functor_path_pregroupoid.
      intros s _.
      exact (Church_gen_body s n ξ).
    Defined.

    Lemma Church_gen_body_sortToHSET_data_ok (n : nat) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧) :
      Church_gen_body_sortToHSET_data n ξ · # (pr1 Church_gen_body_target) f = Church_gen_body_sortToHSET_data n ξ'.
    Proof.
      induction n.
      - apply nat_trans_eq; try apply HSET.
        intros s. apply funextfun.
        intros one. cbn in one. induction one.
        etrans.
        2: { apply pathsinv0, (LC_eta_gen_natural'_ppointwise _ _
                                 (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
                                    (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) f))
                                 s (inl (idpath s,, tt))). }
        apply idpath.
      - apply nat_trans_eq; try apply HSET.
        intros s. apply funextfun.
        intros one. cbn in one. induction one.
        set (aux := (λ (s0 : path_pregroupoid sort Hsort) (_ : pr1 (pr1 (pr1 terminal_sortToHSET) s0)),
                      Church_gen_body s0 (S n) ξ) : ∏ x : path_pregroupoid sort Hsort,
                   SET ⟦ pr1 (pr1 terminal_sortToHSET) x, pr1 (pr1 Church_gen_body_target ξ) x ⟧).
        match goal with |[ |- _ = ?rhs] => set (therhs := rhs) end.
        change (pr1 (# (pr1 Church_gen_body_target) f) s (aux s tt) = therhs).
        change (pr1 (# (pr1 Church_gen_body_target) f) s (Church_gen_body s (S n) ξ) =
                  Church_gen_body s (S n) ξ').
        do 2 rewrite Church_gen_body_rec_eq.
        clear aux therhs.
        assert (IHnpointwise : pr1 (# (pr1 Church_gen_body_target) f) s (Church_gen_body s n ξ) =
                                 Church_gen_body s n ξ').
        { apply (toforallpaths _ _ _ (toforallpaths _ _ _ (maponpaths pr1 IHn) s) tt). }
        rewrite <- IHnpointwise.
        clear IHnpointwise.
        unfold Church_gen_body_target.
        unfold pr1.
        unfold Church_gen_body_target_data.
        unfold make_functor_data.
        unfold functor_on_morphisms at 4.
        unfold pr2.
        unfold nat_trans_functor_path_pregroupoid.
        unfold make_nat_trans.
        apply pathsinv0.
        unfold functor_on_morphisms at 7.
        unfold pr2.
        apply pathsinv0.
        (** now begins the naturality reasoning *)
        etrans.
        match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
        use (maponpaths (fun x : sortToHSET
                                 ⟦ pr1 LC_gen
                                     (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s
                                        (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s  ξ)),
                                   pr1 LC_gen
                                     (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s
                                        (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ξ')) ⟧
                         => pr1 x s thearg)).
        2: { apply functor_composite_on_morphisms. }
        rewrite <- app_map_gen_natural_ppointwise.
        apply maponpaths.
        use dirprodeq; [unfold pr1 | unfold pr2].
        + rewrite app_source_gen_mor_pr1.
          unfold pr1.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            2: { apply pathsinv0, (LC_eta_gen_natural'_ppointwise _ _
                                     (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
                                        (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) f))
                                     s (inr (inl (idpath s,, tt)))). }
            apply idpath.
        + apply app_source_gen_mor_pr2.
    Qed.

    Definition Church_gen_body_sortToHSET (n : nat) : global_element terminal_sortToSet2 Church_gen_body_target.
    Proof.
      use make_global_element_functor_precat.
      - exact (Church_gen_body_sortToHSET_data n).
      - exact (Church_gen_body_sortToHSET_data_ok n).
    Defined.

    Definition Church_gen_header_sortToHSET_data : nat_trans_data (pr1 Church_gen_body_target)
            (pr1 (functor_compose LC_gen (projSortToCvariable sort Hsort SET (λ s : sort, s)))).
    Proof.
      intro ξ.
      use nat_trans_functor_path_pregroupoid.
      intros s body.
      exact (Church_gen_header s ξ body).
    Defined.

    Lemma Church_gen_header_sortToHSET_data_ok : is_nat_trans _ _ Church_gen_header_sortToHSET_data.
      intros ξ ξ' f.
      apply nat_trans_eq; try apply HSET.
      intros s. apply funextfun.
      intro body.
      simpl. unfold compose. simpl.
      (** the following for better readability *)
      match goal with |[ |- Church_gen_header s ξ' (pr1 (# (pr1 LC_gen) ?uglyxi ) s body)= _] => set (theuglyxi := uglyxi) end.
      unfold Church_gen_header.
      rewrite <- lam_map_gen_natural_ppointwise.
      apply maponpaths.
      use dirprodeq.
      - apply idpath.
      - unfold pr2.
        etrans.
        2: { apply pathsinv0, lam_source_gen_mor_pr2. }
        unfold pr2.
        etrans.
        2: { apply pathsinv0, postcomp_with_projSortToC_on_mor. }
        unfold functor_compose.
        etrans.
        2: { match goal with |[ |- _= _ ?arg ] => set (thearg := arg) end.
             use (maponpaths (fun x :
               sortToHSET ⟦ pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen) ξ,
                            pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen) ξ' ⟧
                              =>  pr1 x s thearg)).
             2: { apply pathsinv0, functor_composite_on_morphisms. }
        }
        etrans.
        2: { apply lam_map_gen_natural_ppointwise. }
        apply maponpaths.
        use dirprodeq.
        + apply idpath.
        + unfold pr2.
          etrans.
          2: { apply pathsinv0, lam_source_gen_mor_pr2. }
          apply idpath.
    Qed.

    Definition Church_gen_header_sortToHSET : sortToSet2⟦Church_gen_body_target,
         functor_compose LC_gen (projSortToCvariable sort Hsort HSET (fun s => s))⟧
      := _,, Church_gen_header_sortToHSET_data_ok.

     Definition Church_gen_sortToHSET (n : nat) : global_element terminal_sortToSet2
           (functor_compose LC_gen (projSortToCvariable sort Hsort HSET (fun s => s)))
      := Church_gen_body_sortToHSET n · Church_gen_header_sortToHSET.


     (** this makes superfluous the lengthy definitions below that are kept for comparison *)

    Definition old_Church_gen_sortToHSET_data (n : nat) (ξ : sortToHSET):
      global_element terminal_sortToHSET
        (pr1 (functor_compose LC_gen
           (projSortToCvariable sort Hsort SET (λ s : sort, s))) ξ).
    Proof.
      use nat_trans_functor_path_pregroupoid.
      intros s _.
      change (LC_gen_ctx_sort ξ s).
      exact (Church_gen s n ξ).
    Defined.


    Lemma old_Church_gen_sortToHSET_data_ok (n : nat) (ξ ξ' : sortToHSET) (f : sortToHSET ⟦ ξ, ξ' ⟧):
      old_Church_gen_sortToHSET_data n ξ ·
        # (pr1 (functor_compose LC_gen (projSortToCvariable sort Hsort SET (λ s : sort, s)))) f =
        old_Church_gen_sortToHSET_data n ξ'.
    Proof.
      apply nat_trans_eq; try apply HSET.
      intros s. apply funextfun.
      intros one. cbn in one. induction one.
      simpl. unfold compose. simpl. induction n.
      - change (pr1 (# (pr1 LC_gen) f) s (ChurchZero_gen s ξ) = ChurchZero_gen s ξ').
        unfold ChurchZero_gen.
        rewrite <- lam_map_gen_natural_ppointwise.
        apply maponpaths.
        use dirprodeq.
        + apply idpath.
        + unfold pr2.
          etrans.
          { apply lam_source_gen_mor_pr2. }
          unfold pr2.
          etrans.
          { apply postcomp_with_projSortToC_on_mor. }
          unfold functor_compose.
          etrans.
          match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
          use (maponpaths (fun x : sortToHSET ⟦ pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen) ξ,
                                     pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen) ξ' ⟧
                           =>  pr1 x s thearg)).
          2: { apply functor_composite_on_morphisms. }
          etrans.
          { apply pathsinv0, lam_map_gen_natural_ppointwise. }
          apply maponpaths.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            { apply lam_source_gen_mor_pr2. }
            unfold pr2.
            etrans.
            { apply postcomp_with_projSortToC_on_mor. }
            etrans.
            match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
            use (maponpaths (fun x : sortToHSET
                                     ⟦ pr1 (functor_compose (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) LC_gen)
                                         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ξ),
                                       pr1 (functor_compose (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) LC_gen)
                                         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ξ') ⟧
                             => pr1 x s thearg)).
            2: { apply functor_composite_on_morphisms. }
            etrans.
            { apply pathsinv0, LC_eta_gen_natural'_ppointwise. }
            apply maponpaths.
            apply idpath.
      - (** the successor case - this will not go through since there is the common prefix with the two lambda abstractions *)
        induction n.
        + change (pr1 (# (pr1 LC_gen) f) s (ChurchOne_gen s ξ) = ChurchOne_gen s ξ').
          unfold ChurchOne_gen.
          rewrite <- lam_map_gen_natural_ppointwise.
          apply maponpaths.
          use dirprodeq.
          * apply idpath.
          * unfold pr2.
            etrans.
            { apply lam_source_gen_mor_pr2. }
            unfold pr2.
            etrans.
            { apply postcomp_with_projSortToC_on_mor. }
            unfold functor_compose.
            etrans.
            match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
            use (maponpaths (fun x : sortToHSET
                                     ⟦ pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen)
                                         ξ,
                                       pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen) ξ'
                                     ⟧
                             => pr1 x s thearg)).
            2: { apply functor_composite_on_morphisms. }
            rewrite <- lam_map_gen_natural_ppointwise.
            apply maponpaths.
            use dirprodeq.
            -- apply idpath.
            -- unfold pr2.
               etrans.
               { apply lam_source_gen_mor_pr2. }
               unfold pr2.
               etrans.
               { apply postcomp_with_projSortToC_on_mor. }
               unfold functor_compose.
               etrans.
               match goal with |[ |- _ ?arg = _] => set (thearg := arg) end.
               use (maponpaths (fun x : sortToHSET
                                        ⟦ pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen)
                                            (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ξ),
                                          pr1 (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ∙ LC_gen)
                                            (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s ξ') ⟧
                                => pr1 x s thearg)).
               2: { apply functor_composite_on_morphisms. }
               rewrite <- app_map_gen_natural_ppointwise.
               apply maponpaths.
               use dirprodeq; [unfold pr1 | unfold pr2].
               ++ rewrite app_source_gen_mor_pr1.
                  unfold pr1.
                  use dirprodeq.
                  --- apply idpath.
                  --- unfold pr2.
                      etrans.
                      2: { apply pathsinv0, (LC_eta_gen_natural'_ppointwise _ _
                                               (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
                                                  (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) f))
                                               s (inr (inl (idpath s,, tt)))). }
                      apply idpath.
               ++ rewrite app_source_gen_mor_pr2.
                  unfold pr2.
                  use dirprodeq.
                  --- apply idpath.
                  --- unfold pr2.
                      etrans.
                      2: { apply pathsinv0, (LC_eta_gen_natural'_ppointwise _ _
                                               (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
                                                  (# (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s) f))
                                               s (inl (idpath s,, tt))). }
                      apply idpath.
        + (** case of n>=2 *)
          admit.
    Abort.

(*    Definition old_Church_gen_sortToHSET (n : nat) : global_element terminal_sortToSet2
                                                 (functor_compose STLC_gen (projSortToCvariable sort Hsort HSET (fun s => (s ⇒ s) ⇒ (s ⇒ s)))).
    Proof.
      use make_global_element_functor_precat.
      - exact (old_Church_gen_sortToHSET_data n).
      - exact (old_Church_gen_sortToHSET_data_ok n).
    Defined.
*)

  End Church_functor.


End IndAndCoind.

Definition LC_ctx_sort_ind (ξ : sortToHSET) (s : sort) : UU
  := LC_gen_ctx_sort σind ξ s.
Definition LC_ctx_sort_coind (ξ : sortToHSET) (s : sort) : UU
  := LC_gen_ctx_sort σcoind ξ s.

Definition LC_ind : sortToSet2 := LC_gen σind.
Definition LC_coind : sortToSet2 := LC_gen σcoind.

Definition LC_eta_ind : sortToSet2⟦Id,LC_ind⟧ := LC_eta_gen σind.
Definition LC_eta_coind : sortToSet2⟦Id,LC_coind⟧ := LC_eta_gen σcoind.

Definition LC_tau_ind : LC_Functor_H LC_ind --> LC_ind  := SigmaMonoid_τ θLC σind.
Definition LC_tau_coind : LC_Functor_H LC_coind --> LC_coind  := SigmaMonoid_τ θLC σcoind.

Definition app_source_ind (s : sort) : sortToSet2 := app_source_gen σind s.
Definition app_map_ind (s : sort) : sortToSet2⟦app_source_ind s ,LC_ind⟧ := app_map_gen σind s.
Definition lam_source_ind (s : sort) : sortToSet2 := lam_source_gen σind s.
Definition lam_map_ind (s : sort) : sortToSet2⟦lam_source_ind s,LC_ind⟧ := lam_map_gen σind s.

Definition app_source_coind (s : sort) : sortToSet2 := app_source_gen σcoind s.
Definition app_map_coind (s : sort) : sortToSet2⟦app_source_coind s ,LC_coind⟧ := app_map_gen σcoind s.
Definition lam_source_coind (s : sort) : sortToSet2 := lam_source_gen σcoind s.
Definition lam_map_coind (s : sort) : sortToSet2⟦lam_source_coind s ,LC_coind⟧ := lam_map_gen σcoind s.


(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition LC_ind_IA : Initial (FunctorAlg LC_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort SET TerminalHSET InitialHSET BinProductsHSET
       BinCoproductsHSET ProductsHSET CoproductsHSET (expSortToHSET1 sort Hsort)
       (ColimsHSET_of_shape nat_graph) LC_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition LC_coind_FC : Terminal (CoAlg_category LC_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET LC_Sig is_univalent_HSET.

Section Church.


  Definition ChurchInfinity_body_sortToHSET : global_element terminal_sortToSet2 (Church_gen_body_target σcoind).
  Proof.
    (** has to use [STLC_coind_FC] in the right way *)
  Admitted.

  Definition ChurchInfinity_body (ξ : sortToHSET) (s: sort) : LC_gen_ctx_sort σcoind (ctx_ext (ctx_ext ξ s) s) s.
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_body_sortToHSET) ξ) s tt).
  Defined.

  Definition ChurchInfinity_body_sortToHSET_rec_eq_statement (ξ : sortToHSET) (s : sort) : UU :=
    ChurchInfinity_body ξ s =
      pr1 (pr1 (app_map_coind s) (ctx_ext (ctx_ext ξ s) s)) s
        ((idpath s,,
            pr1 (pr1 LC_eta_coind (ctx_ext (ctx_ext ξ s) s)) s
            (inr (inl (idpath s,, tt)) : pr1 (pr1 (Id (ctx_ext (ctx_ext ξ s) s)) s))),,
           idpath s,, ChurchInfinity_body ξ s).

  Lemma ChurchInfinity_body_sortToHSET_rec_eq (ξ : sortToHSET) (s : sort) : ChurchInfinity_body_sortToHSET_rec_eq_statement ξ s.
  Proof.
  Admitted.

  Definition ChurchInfinity_sortToHSET : global_element terminal_sortToSet2
           (functor_compose LC_coind (projSortToCvariable sort Hsort HSET (fun s => s)))
      := ChurchInfinity_body_sortToHSET · (Church_gen_header_sortToHSET σcoind).

  Definition ChurchInfinity (s : sort) (ξ : sortToHSET) : LC_ctx_sort_coind ξ s.
  Proof.
    exact (pr1 ((pr1 ChurchInfinity_sortToHSET) ξ) s tt).
  Defined.

End Church.

End A.
