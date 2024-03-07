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
Require Import UniMath.SubstitutionSystems.SigmaMonoids.
Require Import UniMath.SubstitutionSystems.MultiSorted_alt.
Require Import UniMath.SubstitutionSystems.MultiSorted_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_actegorical.
Require Import UniMath.SubstitutionSystems.MultiSortedMonadConstruction_coind_actegorical.
Require Import UniMath.SubstitutionSystems.ContinuitySignature.InstantiateHSET.
Require Import UniMath.SubstitutionSystems.MultiSortedEmbeddingIndCoindHSET.
Require UniMath.SubstitutionSystems.STLC_alt.


Local Open Scope cat.

Section A.

  Context (sort : hSet) (arr : sort → sort → sort).

  Local Lemma Hsort : isofhlevel 3 sort.
  Proof.
    exact (isofhlevelssnset 1 sort (setproperty sort)).
  Defined.

  Let sortToHSET : category := [path_pregroupoid sort Hsort, HSET].

  Let BPsortToHSET : BinProducts sortToHSET := BinProducts_functor_precat _ _ BinProductsHSET.
  Let BCsortToHSET : BinCoproducts sortToHSET := BinCoproducts_functor_precat _ _ BinCoproductsHSET.

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

Definition ctx_ext (xi : sortToHSET) (s : sort) : sortToHSET
  := pr1 (option_list sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET (s :: [])) xi.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for monotyped lambda calculus *)
Let σind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort LC_Sig.
Let σcoind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort LC_Sig.

Section IndAndCoind.

  Context (σ : SigmaMonoid θLC).

  (** the functor representing the syntax for STLC *)
  Definition LC_gen : sortToSet2 := SigmaMonoid_carrier θLC σ.

  (** the type of monotyped lambda calculus terms in a context of a sort *)
  Definition LC_gen_ctx_sort (ξ : sortToHSET) (s : sort) : UU
    := pr1 (pr1 (pr1 LC_gen ξ) s).

  (** variable inclusion for syntax for monotyped LC *)
  Definition LC_eta_gen : sortToSet2⟦Id,LC_gen⟧ := SigmaMonoid_η θLC σ.

  (** the algebra maps (the "domain-specific constructors") for monotyped LC *)
  Definition LC_tau_gen : LC_Functor_H LC_gen --> LC_gen  := SigmaMonoid_τ θLC σ.

  (** the individual sorted constructors for application and lambda-abstraction *)

  (**
     On ne se préoccupe pas du "oldstyle".

  Definition app_source_gen_oldstyle_abstracted (s : sort) : functor sortToSet2 sortToSet2 :=
    (post_comp_functor (projSortToC sort Hsort HSET s) ⊗ post_comp_functor (projSortToC sort Hsort HSET s))
      ∙ (post_comp_functor (hat_functor sort Hsort HSET CoproductsHSET s)).

  (** this old-style definition coincides with [STLC_alt.v] *)
  Lemma app_source_gen_oldstyle_abstracted_ok (s t : sort) :
    app_source_gen_oldstyle_abstracted s t = SubstitutionSystems.STLC_alt.app_source sort arr s t.
  Proof.
    apply idpath.
  Qed.

   **)

  Definition app_source_gen_newstyle (s : sort) : sortToSet2 :=
    BinProduct_of_functors BPsortToHSET
      (functor_compose (functor_compose Id LC_gen)
         (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s))
      (functor_compose (functor_compose Id LC_gen)
         (projSortToC sort Hsort SET s ∙ hat_functor sort Hsort SET CoproductsHSET s)).

Definition app_source_gen (s : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort LC_Sig (inl s)) LC_gen.

  Lemma app_source_gen_ok (s : sort) : app_source_gen s  = app_source_gen_newstyle s.
  Proof.
    apply idpath.
  Qed.

  (** The application constructor *)
  Definition app_map_gen (s : sort) : sortToSet2⟦app_source_gen s ,LC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 s) · LC_tau_gen.

(**
On ne se préoccupe pas du "oldstyle"
  Definition lam_source_gen_oldstyle_abstracted (s t : sort) : functor sortToSet2 sortToSet2 :=
    pre_comp_functor (sorted_option_functor sort Hsort HSET TerminalHSET BinCoproductsHSET CoproductsHSET s)
      ∙ post_comp_functor (projSortToC sort Hsort SET t)
      ∙ post_comp_functor (hat_functor sort Hsort SET CoproductsHSET (s ⇒ t)).

  (** this old-style definition coincides with [STLC_alt.v] *)
  Lemma lam_source_gen_oldstyle_abstracted_ok (s t : sort) :
    lam_source_gen_oldstyle_abstracted s t = SubstitutionSystems.STLC_alt.lam_source sort arr s t.
  Proof.
    apply idpath.
  Qed.

 **)

  Definition lam_source_gen_newstyle (s t : sort) : sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET s)
         STLC_gen)
      (projSortToC sort Hsort SET t ∙ hat_functor sort Hsort SET CoproductsHSET (s ⇒ t)).

  Definition lam_source_gen (s t : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort STLC_Sig (inr (s,, t))) STLC_gen.

  Lemma lam_source_gen_ok (s t : sort) : lam_source_gen s t  = lam_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  (** The lambda-abstraction constructor *)
  Definition lam_map_gen (s t : sort) : sortToSet2⟦lam_source_gen s t,STLC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 (s,,t)) · STLC_tau_gen.

  Section Church.

    (** fix a sort, viewed as an atom *)
    Context (s : sort).

    Definition ChurchZero_gen (ξ : sortToHSET) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      (** abstract a first variable - forced to be of type [s ⇒ s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (STLC_gen_ctx_sort (ctx_ext ξ (s ⇒ s)) (s ⇒ s)).
      (** abstract a second variable - forced to be of type [s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      (** take a variable *)
      simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
      cbn.
      (** the available variables are seen, pick the last added variable of type [s] *)
      apply ii1.
      exists (idpath _).
      exact tt.
    Defined.

    Definition ChurchOne_gen (ξ : sortToHSET) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      (** do an application with argument type [s] - not giving this argument would slow down the further steps *)
      refine (pr1 (pr1 (app_map_gen s _) _) _ _).
      split; exists (idpath _).
      - change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
        simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        (** the available variables are seen, pick the first added variable of type [s ⇒ s] *)
        apply ii2.
        apply ii1.
        exists (idpath _).
        exact tt.
      - change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
        simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        (** pick the last added variable of type [s] *)
        apply ii1.
        exists (idpath _).
        exact tt.
    Defined.

    Definition Church_gen (n : nat) (ξ : sortToHSET) : STLC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      induction n.
      - simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
        cbn.
        apply ii1.
        exists (idpath _).
        exact tt.
      - refine (pr1 (pr1 (app_map_gen s _) _) _ _).
        split; exists (idpath _).
        + change (STLC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
          simple refine (pr1 (pr1 STLC_eta_gen _) _ _).
          cbn.
          apply ii2.
          apply ii1.
          exists (idpath _).
          exact tt.
        + exact IHn.
    Defined.

  End Church.

End IndAndCoind.

Definition STLC_ctx_sort_ind (ξ : sortToHSET) (s : sort) : UU
  := STLC_gen_ctx_sort σind ξ s.
Definition STLC_ctx_sort_coind (ξ : sortToHSET) (s : sort) : UU
  := STLC_gen_ctx_sort σcoind ξ s.

Definition STLC_ind : sortToSet2 := STLC_gen σind.
Definition STLC_coind : sortToSet2 := STLC_gen σcoind.

Definition STLC_eta_ind : sortToSet2⟦Id,STLC_ind⟧ := STLC_eta_gen σind.
Definition STLC_eta_coind : sortToSet2⟦Id,STLC_coind⟧ := STLC_eta_gen σcoind.

Definition STLC_tau_ind : STLC_Functor_H STLC_ind --> STLC_ind  := SigmaMonoid_τ θSTLC σind.
Definition STLC_tau_coind : STLC_Functor_H STLC_coind --> STLC_coind  := SigmaMonoid_τ θSTLC σcoind.

Definition app_source_ind (s t : sort) : sortToSet2 := app_source_gen σind s t.
Definition app_map_ind (s t : sort) : sortToSet2⟦app_source_ind s t,STLC_ind⟧ := app_map_gen σind s t.
Definition lam_source_ind (s t : sort) : sortToSet2 := lam_source_gen σind s t.
Definition lam_map_ind (s t : sort) : sortToSet2⟦lam_source_ind s t,STLC_ind⟧ := lam_map_gen σind s t.

Definition app_source_coind (s t : sort) : sortToSet2 := app_source_gen σcoind s t.
Definition app_map_coind (s t : sort) : sortToSet2⟦app_source_coind s t,STLC_coind⟧ := app_map_gen σcoind s t.
Definition lam_source_coind (s t : sort) : sortToSet2 := lam_source_gen σcoind s t.
Definition lam_map_coind (s t : sort) : sortToSet2⟦lam_source_coind s t,STLC_coind⟧ := lam_map_gen σcoind s t.


(** get a handle on the recursion principles *)

(** the initial algebra *)
Definition STLC_ind_IA : Initial (FunctorAlg STLC_Functor_Id_H)
  := DatatypeOfMultisortedBindingSig_CAT sort Hsort SET TerminalHSET InitialHSET BinProductsHSET
       BinCoproductsHSET ProductsHSET CoproductsHSET (expSortToHSET1 sort Hsort)
       (ColimsHSET_of_shape nat_graph) STLC_Sig.
(** notice that this is only the initial algebra and not the initial sigma monoid *)

(** the final coalgebra *)
Definition STLC_coind_FC : Terminal (CoAlg_category STLC_Functor_Id_H)
  := coindCodatatypeOfMultisortedBindingSig_CAT sort Hsort HSET TerminalHSET
         BinProductsHSET BinCoproductsHSET CoproductsHSET (LimsHSET_of_shape conat_graph)
         I_coproduct_distribute_over_omega_limits_HSET STLC_Sig is_univalent_HSET.

Section Church.

  (** fix a sort, viewed as an atom *)
  Context (s : sort).

  Definition ChurchInfinity (ξ : sortToHSET) : STLC_ctx_sort_coind ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_coind _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_coind _ _) _) _ _).
      exists (idpath _).
      change (STLC_ctx_sort_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      (* TODO: coinduction has to come into play *)
    Abort.

End Church.

End A.
