import DaggerModelsPartII.JTGraphCoveredLabelEvaluation
import DaggerModelsPartII.FullInverseImagePrism

/-! Weakness of full inverse-image presentations for any graph-covered label. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra DaggerModels DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphCoveredPresentationWeak

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (codes)
open JTNecklaceEndpointCylinder (cylinder)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)

private abbrev D := Over.lift (codes L) c
private abbrev T (p : I) := ((D Q L c).obj p).left
private abbrev X := JTJointRelativeParameters.withTime Q.map J time
  (D Q L c) (JTTargetIntervalOverMapping.whole Q.code)
private abbrev Y := JTDecoratedIntervalCylinder.reduced Q (D Q L c) time
private abbrev d := JTGraphCoveredLabelEvaluation.boundary Q L time c
private abbrev e := Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection

variable {G : I ⥤ SSet.{0}} (π : G ⟶ X Q L time c)
variable (hπ : ∀ p, trivialFibrations SSet.{0} (π.app p))

/-- The entire covered internal-necklace presentation maps to the original
native cylinder presentation. -/
abbrev presentationProjection :
    BoundaryNecklaceComma.Presentation
      (JTGraphCoveredLabelEvaluation.reduced Q L time c π) ⥤
      BoundaryNecklaceComma.Presentation (Y Q L time c) :=
  JTBoundaryNecklacePresentationCone.mapPresentation (Y Q L time c)
    (JTGraphCoveredLabelEvaluation.reduced Q L time c π) (𝟭 I)
    (JTGraphCoveredLabelEvaluation.projection Q L time c π)

private def cylinderLeg : X Q L time c ⟶ Y Q L time c ⋙ Under.forget B where
  app p := (cylinder (T Q L c p)).app (time.obj p)
  naturality _ _ f :=
    (JTDecoratedIntervalCylinder.reduced_map_cylinder Q (D Q L c) time f).symm

private theorem old_boundary :
    d Q L time c ≫ cylinderLeg Q L time c =
      e time ≫ JTEndpointReducedCover.boundary (Y Q L time c) := by
  apply NatTrans.ext
  funext p
  exact (JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)).w

private theorem cylinderHom_point_GW (S : NecklaceCode) (n : SimplexCategory) :
    DaggerSSetGluing.GW (pointMap (NecklaceCylinderHomSpan.cylinderHom S n)) := by
  letI := NecklaceCylinderHomSpan.leftMap_weak S n
  letI : WeakEquivalence (C := SSet.{0})
      (pointMap (NecklaceCylinderHomSpan.necklaceHom S)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DecoratedNecklaceHomBar.necklaceHom_point_GW S)
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← DaggerOriginalProductGadget.pointIsTerminal.hom_ext
    (NecklaceCylinderHomSpan.leftMap S n ≫ pointMap _) (pointMap _)]
  infer_instance

include hπ in
/-- Every actual fiber of the covered native presentation has weakly
contractible nerve, before any reindexing of the presentation. -/
theorem fiber_point_GW (a : I) :
    DaggerSSetGluing.GW (pointMap (nerve
      ((BoundaryNecklaceComma.fiberDiagram
        (JTGraphCoveredLabelEvaluation.reduced Q L time c π)).obj a))) := by
  apply FullInverseImagePrism.diagram_fiber_point_GW
    π (d Q L time c) (e time) (Y Q L time c)
    (cylinderLeg Q L time c) (old_boundary Q L time c) a
  · exact JTNecklaceEndpointCylinder.isPushout (T Q L c a) (time.obj a)
  · exact hπ a
  · rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T Q L c a) (time.obj a)

include hπ in
/-- The covered presentation projects weakly to the old native presentation,
for all target lengths and without any decorated raw equation. -/
theorem presentationProjection_weak :
    WeakEquivalence (nerveMap (presentationProjection Q L time c π)) := by
  apply FullInverseImagePrism.diagram_presentationProjection_weak
    π (d Q L time c) (e time) (Y Q L time c)
    (cylinderLeg Q L time c) (old_boundary Q L time c)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)
  · exact hπ
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T Q L c p) (time.obj p)
  · exact JTParametrizedTargetFamilies.projection_weak

include hπ in
/-- The entire covered internal-necklace presentation has the weak homotopy
type of its arbitrary base index, without a contractibility assumption on I. -/
theorem forget_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget
      (BoundaryNecklaceComma.fiberDiagram
        (JTGraphCoveredLabelEvaluation.reduced Q L time c π)))) := by
  apply FullInverseImagePrism.diagram_forget_weak
    π (d Q L time c) (e time) (Y Q L time c)
    (cylinderLeg Q L time c) (old_boundary Q L time c)
  · intro p
    exact JTNecklaceEndpointCylinder.isPushout (T Q L c p) (time.obj p)
  · exact hπ
  · intro p
    rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.last_eq]
    exact cylinderHom_point_GW (T Q L c p) (time.obj p)

end
end DaggerModels.PartII.JTGraphCoveredPresentationWeak

