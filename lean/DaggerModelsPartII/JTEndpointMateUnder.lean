import DaggerModelsPartII.JTEndpointHom
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The literal comparison of ordered endpoint cobases

The original full-index Gamma-to-Xi comparison induces a map between the
two endpoint-collapsed cosimplicial frames under the same literal boundary.
Precomposition with that map agrees with the existing strict ordered mate
under the actual pushout Hom identifications.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointMateUnder

open JTRelativeReedyFrame JTActualCosimplicialFrame
open JTZeroObjects JTOrderedFrameMate JTEndpointHom JTEndpointObjects

noncomputable section

private local instance : HomotopicalAlgebra.ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

private local instance : HasLimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasLimits

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The comparison on both copies of the actual outer-zero frame. -/
def comparisonSource : endpointSource Gamma ⟶ endpointSource XiCurried where
  app k := coprod.map ((comparison.app k).app zeroIndex)
    ((comparison.app k).app zeroIndex)
  naturality {j k} θ := by
    apply coprod.hom_ext
    · have h := congrArg (fun t ↦ t.app zeroIndex) (comparison.naturality θ)
      simpa only [endpointSource, NatTrans.comp_app, coprod.inl_map_assoc,
        coprod.inl_map, Category.assoc] using
        congrArg (fun t ↦ t ≫ coprod.inl) h
    · have h := congrArg (fun t ↦ t.app zeroIndex) (comparison.naturality θ)
      simpa only [endpointSource, NatTrans.comp_app, coprod.inr_map_assoc,
        coprod.inr_map, Category.assoc] using
        congrArg (fun t ↦ t ≫ coprod.inr) h

/-- The original comparison evaluated at the outer one-simplex. -/
def comparisonOne :
    Gamma ⋙ (evaluation ReverseSimplex Coefficient).obj oneIndex ⟶
      XiCurried ⋙ (evaluation ReverseSimplex Coefficient).obj oneIndex :=
  Functor.whiskerRight comparison ((evaluation ReverseSimplex Coefficient).obj oneIndex)

/-- The ordered two-face square commutes in the full cosimplicial diagram. -/
theorem comparison_faces :
    endpointFaces Gamma ≫ comparisonOne =
      comparisonSource ≫ endpointFaces XiCurried := by
  apply NatTrans.ext
  funext k
  apply coprod.hom_ext
  · change coprod.inl ≫ coprod.desc _ _ ≫ (comparison.app k).app oneIndex =
      coprod.inl ≫ coprod.map _ _ ≫ coprod.desc _ _
    simpa only [endpointFaces, comparisonSource, comparisonOne,
      NatTrans.comp_app, coprod.inl_desc_assoc, coprod.inl_map_assoc,
      coprod.inl_desc, coprod.inl_map, Category.assoc] using
        ((comparison.app k).naturality (vertex 0))
  · change coprod.inr ≫ coprod.desc _ _ ≫ (comparison.app k).app oneIndex =
      coprod.inr ≫ coprod.map _ _ ≫ coprod.desc _ _
    simpa only [endpointFaces, comparisonSource, comparisonOne,
      NatTrans.comp_app, coprod.inr_desc_assoc, coprod.inr_map_assoc,
      coprod.inr_desc, coprod.inr_map, Category.assoc] using
        ((comparison.app k).naturality (vertex 1))

/-- The two collapses agree because the actual Gamma augmentation factors
through the literal comparison and the Xi augmentation. -/
theorem comparison_collapse :
    endpointCollapse augmentation =
      comparisonSource ≫ endpointCollapse XiAugmentationCurried := by
  apply NatTrans.ext
  funext k
  apply coprod.hom_ext
  · simp only [endpointCollapse, comparisonSource, augmentation,
      NatTrans.comp_app, coprod.inl_map_assoc, coprod.inl_desc,
      Category.assoc]
  · simp only [endpointCollapse, comparisonSource, augmentation,
      NatTrans.comp_app, coprod.inr_map_assoc, coprod.inr_desc,
      Category.assoc]

/-- The comparison of the two actual pushouts fixes the same boundary `Bdagger`. -/
def collapsedComparison :
    collapsedFrame augmentation ⟶ collapsedFrame XiAugmentationCurried :=
  pushout.map (endpointCollapse augmentation) (endpointFaces Gamma)
    (endpointCollapse XiAugmentationCurried) (endpointFaces XiCurried)
    (𝟙 _) comparisonOne comparisonSource
    (by simpa only [Category.comp_id] using comparison_collapse)
    comparison_faces

/-- The pushout comparison fixes the literal boundary coprojection. -/
theorem boundary_collapsedComparison :
    JTEndpointCobase.endpointCobase_inl (endpointFaces Gamma) Bdagger
        (endpointCollapse augmentation) ≫ collapsedComparison =
      JTEndpointCobase.endpointCobase_inl (endpointFaces XiCurried) Bdagger
        (endpointCollapse XiAugmentationCurried) := by
  change pushout.inl _ _ ≫ collapsedComparison = pushout.inl _ _
  unfold collapsedComparison
  simp only [pushout.map, pushout.inl_desc, Category.id_comp]

/-- The other pushout coprojection records the actual outer-one comparison. -/
theorem frame_collapsedComparison :
    JTEndpointCobase.endpointCobase_inr (endpointFaces Gamma) Bdagger
        (endpointCollapse augmentation) ≫ collapsedComparison =
      comparisonOne ≫
        JTEndpointCobase.endpointCobase_inr (endpointFaces XiCurried) Bdagger
          (endpointCollapse XiAugmentationCurried) := by
  change pushout.inr _ _ ≫ collapsedComparison =
    comparisonOne ≫ pushout.inr _ _
  unfold collapsedComparison
  simp only [pushout.map, pushout.inr_desc]

/-- The actual comparison as a natural map in the undercategory of the
literal free dagger two-object boundary. -/
def collapsedUnderComparison :
    collapsedUnder augmentation ⟶ collapsedUnder XiAugmentationCurried where
  app k := Under.homMk (collapsedComparison.app k) (by
    simpa only [NatTrans.comp_app] using
      congrArg (fun t ↦ t.app k) boundary_collapsedComparison)
  naturality {j k} θ := by
    apply Under.UnderMorphism.ext
    exact collapsedComparison.naturality θ

/-- Precomposition on Hom simplicial sets by the actual undercategory map. -/
def underPrecomp (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    underHomSSet XiAugmentationCurried C x y ⟶
      underHomSSet augmentation C x y :=
  Functor.whiskerRight (NatTrans.op collapsedUnderComparison)
    (yoneda.obj (targetUnder C x y))

/-- The pushout-represented map agrees strictly with the original ordered
right mate at every simplex and every specified ordered pair. -/
theorem orderedMate_underPrecomp (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) :
    underPrecomp C x y ≫ (orderedHomSSetIso augmentation C x y).hom =
      (orderedHomSSetIso XiAugmentationCurried C x y).hom ≫
        orderedMate C x y := by
  apply NatTrans.ext
  funext k f
  apply Subtype.ext
  change (orderedHomEquiv augmentation C x y k.unop
      (collapsedUnderComparison.app k.unop ≫ f)).val =
    ((orderedMate C x y).app k
      (orderedHomEquiv XiAugmentationCurried C x y k.unop f)).val
  rw [orderedHomEquiv_val]
  change _ = (comparison.app k.unop).app oneIndex ≫
    (orderedHomEquiv XiAugmentationCurried C x y k.unop f).val
  rw [orderedHomEquiv_val]
  change _ ≫ (collapsedComparison.app k.unop ≫ f.right) =
    (comparison.app k.unop).app oneIndex ≫ (_ ≫ f.right)
  rw [← Category.assoc]
  have h := congrArg (fun t ↦ t.app k.unop) frame_collapsedComparison
  simpa only [NatTrans.comp_app, comparisonOne, Category.assoc] using
    (congrArg (fun t ↦ t ≫ f.right) h)

open scoped SSet.modelCategoryQuillen in
/-- Weakness of the raw undercategory precomposition is exactly weakness of
the already calibrated ordered mate. No Reedy replacement is asserted. -/
theorem underPrecomp_weak_iff_orderedMate (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) :
    weakEquivalences SSet.{0} (underPrecomp C x y) ↔
      weakEquivalences SSet.{0} (orderedMate C x y) := by
  let e : Arrow.mk (underPrecomp C x y) ≅ Arrow.mk (orderedMate C x y) :=
    Arrow.isoMk (orderedHomSSetIso XiAugmentationCurried C x y)
      (orderedHomSSetIso augmentation C x y)
      (orderedMate_underPrecomp C x y).symm
  exact (weakEquivalences SSet.{0}).arrow_mk_iso_iff e

end

end DaggerModels.PartII.JTEndpointMateUnder
