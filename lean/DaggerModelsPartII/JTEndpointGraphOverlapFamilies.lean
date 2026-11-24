import DaggerModelsPartII.JTEndpointGraphOverlapChoices
import DaggerModelsPartII.JTEndpointGraphCoefficientFamilies
import DaggerModelsPartII.JTFiniteCoefficientBridgeExtensionFamilies
import DaggerModelsPartII.JTFiniteCoefficientBridgeRaw

/-! Realization of the full bridge families over the original fixed bead. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTEndpointGraphOverlapFamilies

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientOverlap JTEndpointGraphOverlapChoices
open JTEndpointNormalizationLifts JTMixedGraphRawRefinement JTMixedGraphVerticalArrow
open JTChangingCoefficientBridgeFamilies (leftBase rightBase identityAt)
open JTEndpointRowGraphNormalization (vertexAt)
open JTFiniteCoefficientBridgeExtension (Extension)
open JTFiniteCoefficientBridgeExtensionFamilies

noncomputable section

private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (k : SimplexCategory) := std.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

variable (U : Index P parents refineTo hx hy)

abbrev overlapAt := ((projection P parents refineTo hx hy).obj U).1
abbrev child := (toCommon P parents refineTo).obj (overlapAt P parents refineTo hx hy U)
abbrev childGraph := (child P parents refineTo hx hy U).left.unop
abbrev dim := (horizontalDegree (childGraph P parents refineTo hx hy U)).len
abbrev param := (graph (childGraph P parents refineTo hx hy U)).obj.parameter
abbrev c := side (overlapAt P parents refineTo hx hy U)
abbrev u := final (overlapAt P parents refineTo hx hy U)
abbrev n := timeAt P parents refineTo ((projection P parents refineTo hx hy).obj U)
abbrev rowAt : Δ (coefficientDegree.obj P) ⟶ row W ⦋dim P parents refineTo hx hy U⦌ :=
  parentRow P (child P parents refineTo hx hy U)

private abbrev leftBase_eq :
    JTEndpointGraphCoefficientChoices.leftBase P x = leftBase (rowAt P parents refineTo hx hy U) x :=
  JTEndpointGraphCoefficientFamilies.leftBase_eq P (child P parents refineTo hx hy U)

private abbrev rightBase_eq :
    JTEndpointGraphCoefficientChoices.rightBase P y = rightBase (rowAt P parents refineTo hx hy U) y :=
  JTEndpointGraphCoefficientFamilies.rightBase_eq P (child P parents refineTo hx hy U)

private def leftSq :
    CommSq (identityAt x) (vertexAt (childGraph P parents refineTo hx hy U) 0)
      (endpointArrow W) (std.map (u P parents refineTo hx hy U) ≫
        leftBase (rowAt P parents refineTo hx hy U) x) := by
  rw [← leftBase_eq P parents refineTo hx hy U]
  exact leftAt P parents refineTo hx ((projection P parents refineTo hx hy).obj U)

private def rightSq :
    CommSq (identityAt y) (vertexAt (childGraph P parents refineTo hx hy U)
      (Fin.last (dim P parents refineTo hx hy U)))
      (endpointArrow W) (std.map (u P parents refineTo hx hy U) ≫
        rightBase (rowAt P parents refineTo hx hy U) y) := by
  rw [← rightBase_eq P parents refineTo hx hy U]
  exact rightAt P parents refineTo hy ((projection P parents refineTo hx hy).obj U)

private def leftExtension :
    Extension (c P parents refineTo hx hy U) (u P parents refineTo hx hy U)
      (leftSq P parents refineTo hx hy U) (n P parents refineTo hx hy U) where
  map := U.unop.snd.1.map
  stationary := U.unop.snd.1.stationary
  over := U.unop.snd.1.over.trans (congrArg
    (std.map (JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
      (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)) ≫ ·)
    (leftBase_eq P parents refineTo hx hy U))

private def rightExtension :
    Extension (c P parents refineTo hx hy U) (u P parents refineTo hx hy U)
      (rightSq P parents refineTo hx hy U) (n P parents refineTo hx hy U) where
  map := U.unop.snd.2.map
  stationary := U.unop.snd.2.stationary
  over := U.unop.snd.2.over.trans (congrArg
    (std.map (JTFiniteCoefficientBridgeOrder.base (c P parents refineTo hx hy U)
      (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)) ≫ ·)
    (rightBase_eq P parents refineTo hx hy U))

abbrev families := choiceFamilies (d := dim P parents refineTo hx hy U)
  (c P parents refineTo hx hy U) (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
  (rowAt P parents refineTo hx hy U) (param P parents refineTo hx hy U) x y
  (leftExtension P parents refineTo hx hy U) (rightExtension P parents refineTo hx hy U)

abbrev toFixedBead : single (dim P parents refineTo hx hy U) ⟶ single d :=
  bead.map ((horizontal.obj (child P parents refineTo hx hy U).left).hom)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy

theorem raw_eq :
    nativeRawGraph W (dim P parents refineTo hx hy U)
      (graph (childGraph P parents refineTo hx hy U)).obj.degree
      (std.map (u P parents refineTo hx hy U) ≫ rowAt P parents refineTo hx hy U)
      (param P parents refineTo hx hy U) =
    (toFixedBead P parents refineTo hx hy U).map ≫ (Q hx hy).map := by
  let A := childGraph P parents refineTo hx hy U
  have hf := coefficient_factor P (child P parents refineTo hx hy U)
  change std.map (u P parents refineTo hx hy U) ≫ rowAt P parents refineTo hx hy U =
    graphCoefficient A at hf
  rw [hf]
  have h := JTRowGraphNormalizationDiagram.raw_eq (d := dim P parents refineTo hx hy U) (graph A)
  change (singleIso (dim P parents refineTo hx hy U)).hom ≫
    rawGraph W ⦋dim P parents refineTo hx hy U⦌ (graph A).obj.degree (graphCoefficient A)
      (graph A).obj.parameter = _
  rw [h]
  change (singleIso (dim P parents refineTo hx hy U)).hom ≫ (std.map A.base.unop.hom.1 ≫ q) =
    ((singleIso (dim P parents refineTo hx hy U)).hom ≫ std.map A.base.unop.hom.1 ≫ (singleIso d).inv) ≫
      ((singleIso d).hom ≫ q)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The complete bridge realizes to the fixed bead through the original horizontal map. -/
theorem whole_raw :
    JTFiniteCoefficientBridgeCylinder.cylinderMap (c P parents refineTo hx hy U)
        (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
        (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (nativeGraphParameter (d := dim P parents refineTo hx hy U) (param P parents refineTo hx hy U)) ≫
      JTNecklaceEndpointCylinder.descend W x y
        (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (JTFiniteCoefficientBridgeOrder.bridge (graph (childGraph P parents refineTo hx hy U)).obj.degree
          (n P parents refineTo hx hy U) m)
        (JTMixedGraphOrderedLabel.orderedPoint (families P parents refineTo hx hy U)) =
    NecklaceCylinderAugmentation.augmentation (MixedGraphCylinderTraversal.code (dim P parents refineTo hx hy U))
        (JTFiniteCoefficientBridgeTime.time m (n P parents refineTo hx hy U)) ≫
      (MixedGraphCylinderTraversal.collapseOuter (dim P parents refineTo hx hy U)).map ≫
      (toFixedBead P parents refineTo hx hy U).map ≫ (Q hx hy).map := by
  let T := toFixedBead P parents refineTo hx hy U
  have qx : (T.map ≫ (Q hx hy).map).app (op ⦋0⦌)
      (single (dim P parents refineTo hx hy U)).first = rawVertex W x := by
    change (Q hx hy).map.app _ (T.map.app _ _) = _
    rw [T.first]
    exact (Q hx hy).first
  have qy : (T.map ≫ (Q hx hy).map).app (op ⦋0⦌)
      (single (dim P parents refineTo hx hy U)).last = rawVertex W y := by
    change (Q hx hy).map.app _ (T.map.app _ _) = _
    rw [T.last]
    exact (Q hx hy).last
  exact JTFiniteCoefficientBridgeRaw.whole_raw (c P parents refineTo hx hy U)
    (u P parents refineTo hx hy U) (n P parents refineTo hx hy U)
    (rowAt P parents refineTo hx hy U) (param P parents refineTo hx hy U)
    (families P parents refineTo hx hy U) (raw_eq P parents refineTo hx hy U) qx qy
    (choiceFamilies_left_vertical _ _ _ _ _ _ _ _ _)
    (choiceFamilies_right_vertical _ _ _ _ _ _ _ _ _)

end
end DaggerModels.PartII.JTEndpointGraphOverlapFamilies
