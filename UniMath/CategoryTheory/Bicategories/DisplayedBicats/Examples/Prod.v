(* ******************************************************************************* *)
(** * Bicategories
    Benedikt Ahrens, Marco Maggesi
    February 2018

 Various basic constructions of displayed and non displayed bicategories:
 - Unit displayed bicategory of a displayed 1-category.
 - Full subbicategory of a bicategory.
 - Direct product of bicategories.
 ********************************************************************************* *)

Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.PartA.
Require Import UniMath.CategoryTheory.Categories.
Require Import UniMath.CategoryTheory.DisplayedCats.Auxiliary.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Bicat. Import Bicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Initial.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Examples.Final.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispBicat. Import DispBicat.Notations.
Require Import UniMath.CategoryTheory.Bicategories.Bicategories.Univalence.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispInvertibles.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispAdjunctions.
Require Import UniMath.CategoryTheory.Bicategories.DisplayedBicats.DispUnivalence.

Local Open Scope cat.
Local Open Scope mor_disp_scope.

(* ----------------------------------------------------------------------------------- *)
(** ** Direct product of two displayed structures over a bicategory.                   *)
(* ----------------------------------------------------------------------------------- *)

Section Disp_PreDirprod.

  Context {C : bicat}.
  Variable (D1 D2 : disp_prebicat C).

  Definition disp_dirprod_prebicat_1_id_comp_cells : disp_prebicat_1_id_comp_cells C.
  Proof.
    exists (dirprod_disp_cat_data D1 D2).
    intros c c' f g x d d' f' g'.
    cbn in *.
    exact ( (pr1 f' ==>[ x ] pr1 g') × (pr2 f' ==>[ x ] pr2 g')).
  Defined.

  Definition disp_dirprod_prebicat_ops : disp_prebicat_ops disp_dirprod_prebicat_1_id_comp_cells.
  Proof.
    repeat (use tpair).
    - cbn. intros.
      apply (dirprodpair (disp_id2 _ ) (disp_id2  _)).
    - cbn. intros.
      apply (dirprodpair (disp_lunitor _ ) (disp_lunitor  _)).
    - cbn. intros.
      apply (dirprodpair (disp_runitor _ ) (disp_runitor  _)).
    - cbn. intros.
      apply (dirprodpair (disp_linvunitor _ ) (disp_linvunitor  _)).
    - cbn. intros.
      apply (dirprodpair (disp_rinvunitor _ ) (disp_rinvunitor  _)).
    - cbn. intros.
      apply (dirprodpair (disp_rassociator _ _ _ ) (disp_rassociator _ _ _)).
    - cbn. intros.
      apply (dirprodpair (disp_lassociator _ _ _ ) (disp_lassociator _ _ _)).
    - cbn. intros.
      apply (dirprodpair (disp_vcomp2 (pr1 X) (pr1 X0)) (disp_vcomp2 (pr2 X) (pr2 X0))).
    - cbn. intros.
      apply (dirprodpair (disp_lwhisker (pr1 ff) (pr1 X)) (disp_lwhisker (pr2 ff) (pr2 X))).
    - cbn. intros.
      apply (dirprodpair (disp_rwhisker (pr1 gg) (pr1 X)) (disp_rwhisker (pr2 gg) (pr2 X))).
  Defined.

  Definition disp_dirprod_prebicat_data : disp_prebicat_data C := _ ,, disp_dirprod_prebicat_ops.

  Definition disp_dirprod_brebicat_laws : disp_prebicat_laws disp_dirprod_prebicat_data.
  Proof.
    repeat split; intro.
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_left _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_right _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vassocr _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_id2 _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_id2_rwhisker _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_vcomp _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_vcomp _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_lunitor _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_runitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_lwhisker _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rwhisker_rwhisker _ _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_vcomp_whisker _ _  _ _ _ _ _ _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lunitor_linvunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_linvunitor_lunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_runitor_rinvunitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rinvunitor_runitor _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lassociator_rassociator _ _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_rassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_runitor_rwhisker _ _  @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
    - cbn. intros.
      apply dirprod_paths; cbn; use (disp_lassociator_lassociator _ _ _ _ @ _ ); apply pathsinv0.
      + exact (@pr1_transportf (_ ==> _) _ (λ a _ , _ ) _ _ _ _  ).
      + apply (@pr2_transportf (_ ==> _) (λ a, _ ==>[a]_ ) (λ a, _ ==>[a]_ ) ).
  Qed.

  Definition disp_dirprod_prebicat : disp_prebicat C := _ ,, disp_dirprod_brebicat_laws.
End Disp_PreDirprod.

Section Disp_Dirprod.
  Context {C : bicat}.
  Variable (D1 D2 : disp_bicat C).

  Definition disp_dirprod_bicat
    : disp_bicat C.
  Proof.
    refine (disp_dirprod_prebicat D1 D2 ,, _).
    intros a b f g x aa bb ff gg.
    apply isasetdirprod.
    - apply D1.
    - apply D2.
  Defined.

  Definition pair_is_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x (pr1 xx) × is_disp_invertible_2cell x (pr2 xx)
      →
      is_disp_invertible_2cell x xx.
  Proof.
    intros H.
    induction H as [H1 H2].
    use tpair.
    - split.
      + exact (disp_inv_cell (_ ,, H1)).
      + exact (disp_inv_cell (_ ,, H2)).
    - split.
      + cbn.
        pose (disp_vcomp_rinv (_ ,, H1)) as p.
        cbn in p.
        rewrite p ; clear p.
        pose (disp_vcomp_rinv (_ ,, H2)) as p.
        cbn in p.
        rewrite p ; clear p.
        refine (!(transportb_dirprod (f ==> f)
                                     (λ α, _ ==>[α] _)
                                     (λ α, _ ==>[α] _)
                                     (_ ,, (_ ,, _))
                                     (_ ,, (_ ,, _))
                                     (vcomp_rinv x)
               )).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
      + cbn.
        pose (disp_vcomp_linv (_ ,, H1)) as p.
        cbn in p.
        rewrite p ; clear p.
        pose (disp_vcomp_linv (_ ,, H2)) as p.
        cbn in p.
        rewrite p ; clear p.
        refine (!(transportb_dirprod (g ==> g)
                                     (λ α, _ ==>[α] _)
                                     (λ α, _ ==>[α] _)
                                     (_ ,, (_ ,, _))
                                     (_ ,, (_ ,, _))
                                     (vcomp_lid x)
               )).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
  Defined.

  Definition pair_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
    : disp_invertible_2cell x (pr1 ff) (pr1 gg) × disp_invertible_2cell x (pr2 ff) (pr2 gg)
      →
      disp_invertible_2cell x ff gg.
  Proof.
    intros H.
    use tpair.
    - split.
      + apply H.
      + apply H.
    - apply pair_is_disp_invertible_2cell.
      split.
      + exact (pr2 (pr1 H)).
      + exact (pr2 (pr2 H)).
  Defined.

  Definition pr1_is_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x xx
      →
      is_disp_invertible_2cell x (pr1 xx).
  Proof.
    intros H.
    use tpair.
    - exact (pr1 (pr1 H)).
    - split.
      + refine (maponpaths pr1
                           (@disp_vcomp_rinv C disp_dirprod_bicat
                                             a b f g
                                             aa bb
                                             x
                                             ff gg
                                             (_ ,, H))
                           @ _).
        cbn.
        refine (maponpaths pr1 ((transportb_dirprod
                                   (f ==> f)
                                   (λ α, _ ==>[α] _)
                                   (λ α, _ ==>[α] _)
                                   (_ ,, (_ ,, _))
                                   (_ ,, (_ ,, _))
                                   (vcomp_rinv x)
               ))).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
      + refine (maponpaths pr1
                           (@disp_vcomp_linv C disp_dirprod_bicat
                                             a b f g
                                             aa bb
                                             x
                                             ff gg
                                             (_ ,, H))
                           @ _).
        cbn.
        refine (maponpaths pr1
                           ((transportb_dirprod
                               (g ==> g)
                               (λ α, _ ==>[α] _)
                               (λ α, _ ==>[α] _)
                               (_ ,, (_ ,, _))
                               (_ ,, (_ ,, _))
                               (vcomp_lid x)
               ))).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
  Defined.

  Definition pr1_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
    : disp_invertible_2cell x ff gg
      →
      disp_invertible_2cell x (pr1 ff) (pr1 gg).
  Proof.
    intros H.
    use tpair.
    - apply H.
    - refine (pr1_is_disp_invertible_2cell _ _ _).
      apply H.
  Defined.

  Definition pr2_is_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             {ff : aa -->[ f ] bb}
             {gg : aa -->[ g ] bb}
             (xx : ff ==>[ x ] gg)
    : is_disp_invertible_2cell x xx → is_disp_invertible_2cell x (pr2 xx).
  Proof.
    intros H.
    use tpair.
    - exact (pr2 (pr1 H)).
    - split.
      + refine (maponpaths dirprod_pr2
                           (@disp_vcomp_rinv C disp_dirprod_bicat
                                             a b f g
                                             aa bb
                                             x
                                             ff gg
                                             (_ ,, H))
                           @ _).
        cbn.
        refine (maponpaths dirprod_pr2
                           ((transportb_dirprod
                               (f ==> f)
                               (λ α, _ ==>[α] _)
                               (λ α, _ ==>[α] _)
                               (_ ,, (_ ,, _))
                               (_ ,, (_ ,, _))
                               (vcomp_rinv x)
               ))).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_rinv _) (disp_id2 _)).
      + refine (maponpaths dirprod_pr2
                           (@disp_vcomp_linv C disp_dirprod_bicat
                                             a b f g
                                             aa bb
                                             x
                                             ff gg
                                             (_ ,, H))
                           @ _).
        cbn.
        refine (maponpaths dirprod_pr2
                           ((transportb_dirprod
                               (g ==> g)
                               (λ α, _ ==>[α] _)
                               (λ α, _ ==>[α] _)
                               (_ ,, (_ ,, _))
                               (_ ,, (_ ,, _))
                               (vcomp_lid x)
               ))).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
        * exact (transportb (λ z, _ ==>[z] _) (vcomp_lid _) (disp_id2 _)).
  Defined.

  Definition pr2_disp_invertible_2cell
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
    : disp_invertible_2cell x ff gg → disp_invertible_2cell x (pr2 ff) (pr2 gg).
  Proof.
    intros H.
    use tpair.
    - apply H.
    - refine (pr2_is_disp_invertible_2cell _ _ _).
      apply H.
  Defined.

  Definition pair_disp_invertible_2cell_weq
             {a b : C}
             {f : a --> b} {g : a --> b}
             (x : invertible_2cell f g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             (ff : aa -->[ f ] bb)
             (gg : aa -->[ g ] bb)
    : (disp_invertible_2cell x (pr1 ff) (pr1 gg) × disp_invertible_2cell x (pr2 ff) (pr2 gg))
        ≃
        disp_invertible_2cell x ff gg.
  Proof.
    use weqpair.
    - exact (pair_disp_invertible_2cell x).
    - use isweq_iso.
      + intros H.
        split.
        * apply pr1_disp_invertible_2cell.
          exact H.
        * apply pr2_disp_invertible_2cell.
          exact H.
      + intros H ; cbn.
        use total2_paths2.
        * use subtypeEquality.
          ** intro ; simpl.
             apply isaprop_is_disp_invertible_2cell.
          ** reflexivity.
        * use subtypeEquality.
          ** intro ; simpl.
             apply isaprop_is_disp_invertible_2cell.
          ** reflexivity.
      + intros H ; cbn.
        use subtypeEquality.
        * intro xx ; simpl.
          apply (@isaprop_is_disp_invertible_2cell C disp_dirprod_bicat).
        * reflexivity.
  Defined.

  Definition prod_idtoiso_2_1
             {a b : C}
             {f : a --> b} {g : a --> b}
             (p : f = g)
             {aa : disp_dirprod_bicat a}
             {bb : disp_dirprod_bicat b}
             (ff : aa -->[f] bb)
             (gg : aa -->[g] bb)
             (HD1 : disp_locally_univalent D1)
             (HD2 : disp_locally_univalent D2)
    : (transportf (λ z : C ⟦ a, b ⟧, aa -->[ z] bb) p ff = gg)
        ≃
        disp_invertible_2cell (idtoiso_2_1 f g p) ff gg.
  Proof.
    refine (pair_disp_invertible_2cell_weq (idtoiso_2_1 _ _ p) ff gg ∘ _)%weq.
    refine (weqdirprod
              (_ ,, HD1 a b f g p (pr1 aa) (pr1 bb) (pr1 ff) (pr1 gg))
              (_ ,, HD2 a b f g p (pr2 aa) (pr2 bb) (pr2 ff) (pr2 gg))
              ∘ _)%weq.
    induction p ; cbn ; unfold idfun.
    apply WeakEquivalences.pathsdirprodweq.
  Defined.

  Definition is_univalent_2_1_dirprod_bicat
             (HD1 : disp_locally_univalent D1)
             (HD2 : disp_locally_univalent D2)
    : disp_locally_univalent disp_dirprod_bicat.
  Proof.
    intros a b f g p aa bb ff gg.
    use weqhomot.
    - exact (prod_idtoiso_2_1 p ff gg HD1 HD2).
    - intros q.
      induction p, q.
      use subtypeEquality.
      + intro.
        apply (@isaprop_is_disp_invertible_2cell C disp_dirprod_bicat).
      + reflexivity.
  Defined.

  Definition is_univalent_2_0_dirprod_bicat
             (HD1 : disp_univalent_2_0 D1)
             (HD2 : disp_univalent_2_0 D2)
    : disp_univalent_2_0 disp_dirprod_bicat.
  Proof.
    intros a b p f g.
  Admitted.
End Disp_Dirprod.