(**

Syntax of the untyped (or "monotyped") lambda calculus as a
multisorted signature.

**)

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

  Context (sort : hSet) (arr : sort → sort → sort) (l : sort).

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
Local Notation "s ⇒ t" := (arr s t).
Local Notation "'Id'" := (functor_identity _).
(*Local Notation "a ⊕ b" := (BinCoproductObject (BinCoprodSortToSet a b)). *)
(* Local Notation "'1'" := (TerminalObject TerminalSortToSet). *)
Local Notation "F ⊗ G" := (BinProduct_of_functors BinProd F G).

Let sortToSet2 := [sortToHSET,sortToHSET].

(** The signature of the simply untyped (or "monotyped") lambda calculus *)
Definition LC_Sig : MultiSortedSig sort.
Proof.
use make_MultiSortedSig.
- apply ((sort × sort) + (sort × sort))%set.
- intros H; induction H as [st|st]; induction st as [s t].
  + exact ((([],,(s ⇒ t)) :: ([],,s) :: nil),,l).
  + exact (((cons s [],,t) :: []),,l).
Defined.

(** the canonical functor associated with LC_Sig *)
Definition LC_Functor_H  : functor sortToSet2 sortToSet2 :=
  MultiSorted_actegorical.MultiSortedSigToFunctor' sort Hsort SET
    TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET LC_Sig.

(** the functor of which the fixed points are considered *)
Definition LC_Functor_Id_H (l : sort) : functor sortToSet2 sortToSet2 :=
  SubstitutionSystems.Id_H sortToHSET BCsortToHSET LC_Functor_H.

(** the canonical strength associated with LC_Sig *)
Let θLC := MultiSortedMonadConstruction_actegorical.MultiSortedSigToStrength' sort Hsort SET
               TerminalHSET BinProductsHSET BinCoproductsHSET CoproductsHSET LC_Sig .

Definition ctx_ext (xi : sortToHSET) (s : sort) : sortToHSET
  := pr1 (option_list sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET (l :: [])) xi.

(** the sigma-monoids for wellfounded and non-wellfounded syntax for LC *)
Let σind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σind sort Hsort LC_Sig.
Let σcoind : SigmaMonoid θLC := MultiSortedEmbeddingIndCoindHSET.σcoind sort Hsort LC_Sig.

Section IndAndCoind.

  Context (σ : SigmaMonoid θLC).

  (** the functor representing the syntax for LC *)
  Definition LC_gen : sortToSet2 := SigmaMonoid_carrier θLC σ.

  (** the type of LC terms in a context of a sort *)
  Definition LC_gen_ctx_sort (ξ : sortToHSET) (s : sort): UU
    := pr1 (pr1 (pr1 LC_gen ξ) l).

  (** variable inclusion for syntax for LC *)
  Definition LC_eta_gen : sortToSet2⟦Id,LC_gen⟧ := SigmaMonoid_η θLC σ.

  (** the algebra maps (the "domain-specific constructors") for LC *)
  Definition LC_tau_gen : LC_Functor_H LC_gen --> LC_gen  := SigmaMonoid_τ θLC σ.


(*
   Je ne suis pas certain que cette partie soit pertinente : on peut construire les constructeurs en version "old style", même pour du ̨λ-calcul non typé, mais cela ne coïncidera pas avec la définition de LC_alt.v. De ce que j'ai compris, c'était le seul itnérêt d'écrire les constructeurs en version old style dans le fichier

  (** the individual "monosorted" constructors for application and lambda-abstraction *)


  Definition app_source_gen_oldstyle_abstracted (s t : sort) : functor sortToSet2 sortToSet2 :=
    (post_comp_functor (projSortToC sort Hsort HSET l) ⊗ post_comp_functor (projSortToC sort Hsort HSET s))
      ∙ (post_comp_functor (hat_functor sort Hsort HSET CoproductsHSET t)).

  (** this old-style definition coincides with [LC_alt.v] *)
  Lemma app_source_gen_oldstyle_abstracted_ok (s t : sort) :
    app_source_gen_oldstyle_abstracted s t = SubstitutionSystems.STLC_alt.app_source sort arr ) .
  Proof.
    apply idpath.
  Qed.


*)


  Definition app_source_gen_newstyle (s t : sort) : sortToSet2 :=
    BinProduct_of_functors BPsortToHSET
      (functor_compose (functor_compose Id LC_gen)
         (projSortToC sort Hsort SET (l ⇒ l) ∙ hat_functor sort Hsort SET CoproductsHSET l))
      (functor_compose (functor_compose Id LC_gen)
         (projSortToC sort Hsort SET l ∙ hat_functor sort Hsort SET CoproductsHSET l)).

 Check arity sort LC_Sig (inl (l,,l)).

  Definition app_source_gen (s t : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort LC_Sig (inl (l,,l))) LC_gen.

  Lemma app_source_gen_ok (s t : sort) : app_source_gen s t  = app_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  (** The application constructor *)
  Definition app_map_gen (s t : sort) : sortToSet2⟦app_source_gen s t,LC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii1 (l,,l)) · LC_tau_gen.

 (**
Idem : pas sûr que cette partie soit pertinente à rédiger.
  Definition lam_source_gen_oldstyle_abstracted (s t : sort) : functor sortToSet2 sortToSet2 :=
    pre_comp_functor (sorted_option_functor sort Hsort HSET TerminalHSET BinCoproductsHSET CoproductsHSET s)
      ∙ post_comp_functor (projSortToC sort Hsort SET t)
      ∙ post_comp_functor (hat_functor sort Hsort SET CoproductsHSET (s ⇒ t)).

  (** this old-style definition coincides with [LC_alt.v] *)
  Lemma lam_source_gen_oldstyle_abstracted_ok (s t : sort) :
    lam_source_gen_oldstyle_abstracted s t = SubstitutionSystems.LC_alt.lam_source sort arr s t.
  Proof.
    apply idpath.
  Qed.

**)
  Definition lam_source_gen_newstyle (s t : sort) : sortToSet2 :=
    functor_compose
      (functor_compose
         (sorted_option_functor sort Hsort SET TerminalHSET BinCoproductsHSET CoproductsHSET l)
         LC_gen)
      (projSortToC sort Hsort SET l ∙ hat_functor sort Hsort SET CoproductsHSET l).

  Definition lam_source_gen (s t : sort) : sortToSet2 :=
    ContinuityOfMultiSortedSigToFunctor.hat_exp_functor_list'_optimized sort Hsort SET TerminalHSET
      BinProductsHSET BinCoproductsHSET CoproductsHSET (arity sort LC_Sig (inr (l,, l))) LC_gen.

  Lemma lam_source_gen_ok (s t : sort) : lam_source_gen s t  = lam_source_gen_newstyle s t.
  Proof.
    apply idpath.
  Qed.

  (** The lambda-abstraction constructor *)
  Definition lam_map_gen (s t : sort) : sortToSet2⟦lam_source_gen s t,LC_gen⟧ :=
    CoproductIn _ _ (Coproducts_functor_precat _ _ _ _ (λ _, _)) (ii2 (l,,l)) · LC_tau_gen.

  Section Church.

    Definition ChurchZero_gen (ξ : sortToHSET) : LC_gen_ctx_sort ξ ((l ⇒ l) ⇒ (l ⇒ l)).
    Proof.
      (** abstract a first variable - forced to be of type [s ⇒ s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (LC_gen_ctx_sort (ctx_ext ξ (l ⇒ l)) (l ⇒ l)).
      (** abstract a second variable - forced to be of type [s] *)
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ (l ⇒ l)) l) l).
      (** take a variable *)
      simple refine (pr1 (pr1 LC_eta_gen _) _ _).
      cbn.
      (** the available variables are seen, pick the last added variable of type [s] *)
      apply ii2.
      apply ii1.
      exists (idpath _).
      exact tt.
    Defined.

    Definition ChurchOne_gen (ξ : sortToHSET) : LC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      (** do an application with argument type [s] - not giving this argument would slow down the further steps *)
      refine (pr1 (pr1 (app_map_gen s _) _) _ _).
      split; exists (idpath _).
      - change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
        simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        (** the available variables are seen, pick the first added variable of type [s ⇒ s] *)
        apply ii2.
        apply ii1.
        exists (idpath _).
        exact tt.
      - change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
        simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        (** pick the last added variable of type [s] *)
        apply ii1.
        exists (idpath _).
        exact tt.
    Defined.

    Definition Church_gen (n : nat) (ξ : sortToHSET) : LC_gen_ctx_sort ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_gen _ _) _) _ _).
      exists (idpath _).
      change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      induction n.
      - simple refine (pr1 (pr1 LC_eta_gen _) _ _).
        cbn.
        apply ii1.
        exists (idpath _).
        exact tt.
      - refine (pr1 (pr1 (app_map_gen s _) _) _ _).
        split; exists (idpath _).
        + change (LC_gen_ctx_sort (ctx_ext (ctx_ext ξ (s ⇒ s)) s) (s ⇒ s)).
          simple refine (pr1 (pr1 LC_eta_gen _) _ _).
          cbn.
          apply ii2.
          apply ii1.
          exists (idpath _).
          exact tt.
        + exact IHn.
    Defined.

  End Church.

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

Definition app_source_ind (s t : sort) : sortToSet2 := app_source_gen σind s t.
Definition app_map_ind (s t : sort) : sortToSet2⟦app_source_ind s t,LC_ind⟧ := app_map_gen σind s t.
Definition lam_source_ind (s t : sort) : sortToSet2 := lam_source_gen σind s t.
Definition lam_map_ind (s t : sort) : sortToSet2⟦lam_source_ind s t,LC_ind⟧ := lam_map_gen σind s t.

Definition app_source_coind (s t : sort) : sortToSet2 := app_source_gen σcoind s t.
Definition app_map_coind (s t : sort) : sortToSet2⟦app_source_coind s t,LC_coind⟧ := app_map_gen σcoind s t.
Definition lam_source_coind (s t : sort) : sortToSet2 := lam_source_gen σcoind s t.
Definition lam_map_coind (s t : sort) : sortToSet2⟦lam_source_coind s t,LC_coind⟧ := lam_map_gen σcoind s t.


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

  (** fix a sort, viewed as an atom *)
  Context (s : sort).

  Definition ChurchInfinity (ξ : sortToHSET) : LC_ctx_sort_coind ξ ((s ⇒ s) ⇒ (s ⇒ s)).
    Proof.
      refine (pr1 (pr1 (lam_map_coind _ _) _) _ _).
      exists (idpath _).
      refine (pr1 (pr1 (lam_map_coind _ _) _) _ _).
      exists (idpath _).
      change (LC_ctx_sort_coind (ctx_ext (ctx_ext ξ (s ⇒ s)) s) s).
      (* TODO: coinduction has to come into play *)
    Abort.

End Church.

End A.
