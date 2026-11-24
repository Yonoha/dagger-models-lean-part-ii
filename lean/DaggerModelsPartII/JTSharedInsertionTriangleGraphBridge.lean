import DaggerModelsPartII.JTSharedInsertionPhaseGraph

/-!
# Identify the common phase triangle graph with the checked actual triangle graph

The equality is proved at natural-transformation level through the ORIGINAL
Family parameter. It compares full all-lifts covers, without choosing a section
or manufacturing a corrected product Family. Both projection and trace are kept.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionTriangleGraphBridge

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

private def parameterIso {I : Type} [SmallCategory I] (X : I ⥤ SSet.{0})
    {k m : I ⥤ SimplexCategory} (p q : X ⟶ k ⋙ J) (α : m ⟶ k) (h : p = q) :
    JTPrismChainGraphCover.cover X p α ≅ JTPrismChainGraphCover.cover X q α :=
  eqToIso (congrArg (fun t ↦ JTPrismChainGraphCover.cover X t α) h)

private theorem parameterIso_projection {I : Type} [SmallCategory I] (X : I ⥤ SSet.{0})
    {k m : I ⥤ SimplexCategory} (p q : X ⟶ k ⋙ J) (α : m ⟶ k) (h : p = q) :
    (parameterIso X p q α h).hom ≫ JTPrismChainGraphCover.projection X q α =
      JTPrismChainGraphCover.projection X p α := by
  subst q
  simp [parameterIso]

private theorem parameterIso_parameter {I : Type} [SmallCategory I] (X : I ⥤ SSet.{0})
    {k m : I ⥤ SimplexCategory} (p q : X ⟶ k ⋙ J) (α : m ⟶ k) (h : p = q) :
    (parameterIso X p q α h).hom ≫ JTPrismChainGraphCover.parameter X q α =
      JTPrismChainGraphCover.parameter X p α := by
  subst q
  simp [parameterIso]

private theorem product_comp_reindex {I B : Type} [SmallCategory I] [SmallCategory B]
    (G : I ⥤ B) {N : I ⥤ NecklaceCode} {M P : B ⥤ NecklaceCode}
    (n : N ⟶ G ⋙ M) (m : M ⟶ P) (t : B ⥤ SimplexCategory) :
    JTSharedInsertionPhaseGraph.reindexedProductMap G n t ≫
        Functor.whiskerLeft G (JTSharedInsertionPhaseGraph.mapWithTime m t) =
      JTSharedInsertionPhaseGraph.mapWithTime (n ≫ Functor.whiskerLeft G m) (G ⋙ t) := by
  change JTSharedInsertionPhaseGraph.mapWithTime n (G ⋙ t) ≫
      JTSharedInsertionPhaseGraph.mapWithTime (Functor.whiskerLeft G m) (G ⋙ t) = _
  exact JTSharedInsertionPhaseGraph.mapWithTime_comp n (Functor.whiskerLeft G m) (G ⋙ t)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private abbrev I := JTSharedInsertionPhaseGraph.Index F j
private abbrev G := JTSharedInsertionPhaseGraph.base F j
private abbrev original := JTSharedInsertionSeamNative.original F j
private abbrev t := JTSharedInsertionPhaseGraph.oldTime F j
private abbrev u := JTSharedInsertionPhaseGraph.triangleToCollapsed F j
private abbrev MT {C : Type} [SmallCategory C] {N M : C ⥤ NecklaceCode}
    (n : N ⟶ M) (t : C ⥤ SimplexCategory) := JTSharedInsertionPhaseGraph.mapWithTime n t

private def originalParameter :
    JTGraphCoveredProductInterface.product (original F j ⋙ codes L) (t F j) ⟶
      JTSharedInsertionNormalizedSeam.oldDegrees F j ⋙ J where
  app p := F.parameter ((original F j).obj p)
  naturality _ _ f := F.parameter_map ((original F j).map f)

private abbrev oldCodes := G F j ⋙ codes (JTSharedInsertionOldGraph.oldFamily F j).labels
private abbrev originalCodes := original F j ⋙ codes L

private def oldAssemblyFinal : oldCodes F j ⟶ originalCodes F j :=
  Functor.whiskerLeft (G F j) (JTSharedInsertionSeamNative.oldAssembly F j)

private def oldTimeMap : G F j ⋙ JTSharedInsertionOldGraph.X F j ⟶
    JTGraphCoveredProductInterface.product (originalCodes F j) (t F j) :=
  Functor.whiskerLeft (G F j) (JTSharedInsertionOldGraph.nativeTimeMap F j)

private def collapsedTimeMap :
    JTSharedInsertionPhaseGraph.X F j (JTSharedInsertionPhaseGraph.collapsedCodes F j) ⟶
      JTGraphCoveredProductInterface.product (originalCodes F j) (t F j) :=
  MT (JTSharedInsertionSeamNative.collapsedNative F j) (t F j)

private def triangleTimeMap : JTSharedInsertionSeamGraph.X F j ⟶
    JTGraphCoveredProductInterface.product (originalCodes F j) (t F j) :=
  MT (JTSharedInsertionSeamNative.wholeNative F j) (t F j)

set_option maxHeartbeats 850000 in
private theorem old_coarse_factor :
    Functor.whiskerLeft (G F j) (JTSharedInsertionOldGraph.coarseParameter F j) =
      oldTimeMap F j ≫ originalParameter F j := rfl

private theorem old_native_time : JTSharedInsertionOldGraph.nativeTimeMap F j =
    MT (JTSharedInsertionSeamNative.oldAssembly F j)
      (JTSharedInsertionOldGraph.oldTime F j) := rfl

set_option maxHeartbeats 850000 in
private theorem old_product_factor :
    JTSharedInsertionPhaseGraph.oldProductMap F j ≫
        oldTimeMap F j = collapsedTimeMap F j := by
  change JTSharedInsertionPhaseGraph.reindexedProductMap (G F j)
      (JTSharedInsertionPhaseGraph.nativeToOld F j) (JTSharedInsertionOldGraph.oldTime F j) ≫
    Functor.whiskerLeft (G F j) (JTSharedInsertionOldGraph.nativeTimeMap F j) = _
  rw [old_native_time, product_comp_reindex]
  rfl

private theorem legacy_coarse_factor : JTSharedInsertionSeamGraph.coarseParameter F j =
    triangleTimeMap F j ≫ originalParameter F j := rfl

set_option maxHeartbeats 850000 in
/-- The common phase triangle uses EXACTLY the original actual triangle coarse parameter. -/
theorem coarseParameter_eq : JTSharedInsertionPhaseGraph.coarseParameter F j (u F j) =
    JTSharedInsertionSeamGraph.coarseParameter F j := by
  calc
    _ = MT (u F j) (t F j) ≫
        (JTSharedInsertionPhaseGraph.oldProductMap F j ≫
          (oldTimeMap F j ≫ originalParameter F j)) := by
      rw [JTSharedInsertionPhaseGraph.coarseParameter,
        JTSharedInsertionPhaseGraph.collapsedParameter, old_coarse_factor]
    _ = MT (u F j) (t F j) ≫
        (collapsedTimeMap F j ≫
          originalParameter F j) := by
      rw [← Category.assoc (JTSharedInsertionPhaseGraph.oldProductMap F j), old_product_factor]
    _ = triangleTimeMap F j ≫
        originalParameter F j := by
      change MT (u F j) (t F j) ≫
        (MT (JTSharedInsertionSeamNative.collapsedNative F j) (t F j) ≫
          originalParameter F j) = _
      rw [← Category.assoc, JTSharedInsertionPhaseGraph.mapWithTime_comp]
      rfl
    _ = _ := (legacy_coarse_factor F j).symm

/-- Canonically identify the two complete all-lifts triangle graphs. -/
def iso : JTSharedInsertionPhaseGraph.triangleGraph F j ≅
    JTSharedInsertionSeamGraph.graph F j :=
  parameterIso (JTSharedInsertionPhaseGraph.X F j (codes
    (JTSharedInsertionNormalizedSeam.seamFamily F j).triangle.labels))
    (JTSharedInsertionPhaseGraph.coarseParameter F j (u F j))
    (JTSharedInsertionSeamGraph.coarseParameter F j)
    (JTSharedInsertionNormalizedSeam.coefficientProjection F j) (coarseParameter_eq F j)

/-- The canonical graph identification preserves the whole original native/time projection. -/
theorem iso_projection : (iso F j).hom ≫ JTSharedInsertionSeamGraph.projection F j =
    JTSharedInsertionPhaseGraph.projection F j (u F j) :=
  parameterIso_projection _ _ _ _ _

/-- It also preserves the full final lifted coefficient parameter. -/
theorem iso_parameter : (iso F j).hom ≫ JTSharedInsertionSeamGraph.parameter F j =
    JTSharedInsertionPhaseGraph.parameter F j (u F j) :=
  parameterIso_parameter _ _ _ _ _

end
end DaggerModels.PartII.JTSharedInsertionTriangleGraphBridge
