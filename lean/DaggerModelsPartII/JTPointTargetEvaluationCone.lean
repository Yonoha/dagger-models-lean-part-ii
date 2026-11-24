import DaggerModelsPartII.JTConstantOrderedLabel
import DaggerModelsPartII.JTParametrizedTargetFamilies
import NativeOverNerveWeakContractibility

/-! A single decorated point cone contracts the entire fixed-point evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerOriginalProductGadget DaggerSSetGluing

namespace DaggerModels.PartII.JTPointTargetEvaluationCone

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family evaluate cylinders liftNatural)
open JTNecklaceEndpointCylinder (endpointInclusion under)
open NecklaceCylinderAugmentation (augmentation)
open BoundaryNecklaceComma (necklaceUnder)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev T := NecklaceCode.point
private abbrev pt := necklaceUnder.obj T
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def terminalUnder (Z : Under B) (h : IsTerminal Z.right) : IsTerminal Z :=
  IsTerminal.ofUniqueHom (fun X ↦ Under.homMk (h.from X.right) (h.hom_ext _ _))
    (fun _ f ↦ Under.UnderMorphism.ext (h.hom_ext f.right _))

private def pointTerminal : IsTerminal pt :=
  terminalUnder pt SSet.stdSimplex.isTerminalObj₀

private abbrev sectionMap : T.toSSet ⟶ B := SSet.boundary₁.ι₀

private theorem section_fac : sectionMap ≫ endpointInclusion T = 𝟙 T.toSSet :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem point_maps_eq {Z : Under B} (f g : pt ⟶ Z) : f = g := by
  apply Under.UnderMorphism.ext
  change f.right = g.right
  have hf : endpointInclusion T ≫ f.right = Z.hom := Under.w f
  have hg : endpointInclusion T ≫ g.right = Z.hom := Under.w g
  calc
    _ = (sectionMap ≫ endpointInclusion T) ≫ f.right := by
      rw [section_fac, Category.id_comp]
    _ = sectionMap ≫ Z.hom := by rw [Category.assoc, hf]
    _ = (sectionMap ≫ endpointInclusion T) ≫ g.right := by
      rw [Category.assoc, hg]
    _ = _ := by rw [section_fac, Category.id_comp]

private def cylinderTerminal (k : SimplexCategory) : IsTerminal ((under T).obj k) := by
  haveI : IsIso (augmentation T k) :=
    ReducedGroupoidCylinderAugmentation.augmentation_isIso_of_split_epi
      (endpointInclusion T) k sectionMap section_fac
  exact terminalUnder _ (SSet.stdSimplex.isTerminalObj₀.ofIso (asIso (augmentation T k)).symm)

variable (W : Source) (z : Vertex W)

/-- The actual native point in the unchanged raw realization. -/
abbrev pointTarget := NecklacesOver.point (rawVertex W z)

/-- The degree-zero decorated point with the same original endpoints. -/
abbrev pointLabel := JTConstantOrderedLabel.constantIndex W z T ⦋0⦌

private abbrev E := JTTargetCommaPullback.diagram W z z (pointTarget W z)
private abbrev q := JTTargetCommaPullback.targetMap W z z (pointTarget W z)
private abbrev ρ := (underCocone W z z).app (pointLabel W z)

private def centerLeg : pt ⟶ (E W z).obj (pointLabel W z) :=
  pullback.lift ((cylinderTerminal ⦋0⦌).from pt) (𝟙 pt) (point_maps_eq _ _)

private def pointPullbackTerminal : IsTerminal ((E W z).obj (pointLabel W z)) := by
  apply IsTerminal.ofUniqueHom (fun A ↦ pointTerminal.from A ≫ centerLeg W z)
  intro A f
  apply pullback.hom_ext (f := ρ W z) (g := q W z)
  · exact (cylinderTerminal ⦋0⦌).hom_ext _ _
  · exact pointTerminal.hom_ext _ _

/-- The chosen object of the actual pullback presentation has internal necklace the point. -/
def centerPresentation : JTTargetCommaPullback.Presentation W z z (pointTarget W z) :=
  ⟨pointLabel W z, CostructuredArrow.mk (Y := T) (centerLeg W z)⟩

/-- The corresponding object in the original fixed-target comma. -/
def center : TargetComma (pointTarget W z) :=
  (JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)).obj
    (centerPresentation W z)

variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W z z} {time : A ⥤ SimplexCategory}
variable (F : Family (pointTarget W z) L time)
variable (r : L ⟶ (Functor.const A).obj (pointLabel W z))

private def nativeCone :
    cylinders (L := L) (time := time) ⟶ (Functor.const A).obj pt where
  app _ := pointTerminal.from _
  naturality _ _ _ := pointTerminal.hom_ext _ _

set_option maxHeartbeats 850000 in
/-- Compatible arrows of the labels to the actual decorated point give a
cone on the original evaluation of every internal necklace. -/
def evaluation_toPoint :
    evaluate F ⟶ (Functor.const _).obj (center W z) := by
  let H := JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)
  let e := JTBoundaryNecklacePresentationCone.coneFromVariableDiagram
    (E W z) (centerPresentation W z) (cylinders (L := L) (time := time)) L
      (liftNatural F) r (nativeCone (W := W) (z := z) (L := L) (time := time))
      (fun _ ↦ (pointPullbackTerminal W z).hom_ext _ _)
  exact Functor.whiskerRight e H ≫ (Functor.constComp _ (centerPresentation W z) H).hom

include r in
/-- The original evaluation factors through a weakly contractible slice
with all of its native and decorated operators preserved. -/
theorem exists_contractible_factor :
    ∃ (C : Cat.{0, 0}) (u : JTParametrizedTargetFamilies.Presentation (L := L) (time := time) ⥤ C)
      (v : C ⥤ TargetComma (pointTarget W z)),
      GW (pointMap (nerve C)) ∧ evaluate F = u ⋙ v := by
  refine ⟨Cat.of (Over (center W z)), Over.lift (evaluate F) (evaluation_toPoint W z F r),
    Over.forget (center W z), DaggerNativeOverNerveWeakContractibility.point_GW _, rfl⟩

section AnyPresentation

variable {J : Type} [SmallCategory J]
variable (Y : J ⥤ Under B)
variable (M : J ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (ρ : Y ⟶ M ⋙ E W z)
variable (σ : M ⟶ (Functor.const J).obj (pointLabel W z))

private def nativeConeAny : Y ⟶ (Functor.const J).obj pt where
  app _ := pointTerminal.from _
  naturality _ _ _ := pointTerminal.hom_ext _ _

/-- Any whole internal-necklace presentation over the literal point target
contracts to the existing center when its decorated labels have a natural
point cone. The native and time traversals are retained in the source. -/
def evaluation_toPointOfLabelCone :
    (JTBoundaryNecklacePresentationCone.mapPresentation (E W z) Y M ρ ⋙
      JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)) ⟶
        (Functor.const _).obj (center W z) := by
  let H := JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)
  let e := JTBoundaryNecklacePresentationCone.coneFromVariableDiagram
    (E W z) (centerPresentation W z) Y M ρ σ (nativeConeAny Y)
      (fun _ ↦ (pointPullbackTerminal W z).hom_ext _ _)
  exact Functor.whiskerRight e H ≫ (Functor.constComp _ (centerPresentation W z) H).hom

/-- Restrict an arbitrary complete presentation along an index functor, then
contract it using a point cone on the restricted decorated labels. -/
def evaluation_toPointAfterReindex {K : Type} [SmallCategory K] (G : K ⥤ J)
    (τ : G ⋙ M ⟶ (Functor.const K).obj (pointLabel W z)) :
    Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram Y) G ⋙
      (JTBoundaryNecklacePresentationCone.mapPresentation (E W z) Y M ρ ⋙
        JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)) ⟶
      (Functor.const (BoundaryNecklaceComma.Presentation (G ⋙ Y))).obj
        (center W z) := by
  let H := JTTargetCommaExactEvaluation.fromPresentation W z z (pointTarget W z)
  let e := JTBoundaryNecklacePresentationCone.coneFromReindexedVariableDiagram
    (E W z) (centerPresentation W z) Y M ρ G τ (nativeConeAny (G ⋙ Y))
    (fun _ ↦ (pointPullbackTerminal W z).hom_ext _ _)
  exact Functor.whiskerRight e H ≫
    (Functor.constComp _ (centerPresentation W z) H).hom

end AnyPresentation

end
end DaggerModels.PartII.JTPointTargetEvaluationCone
