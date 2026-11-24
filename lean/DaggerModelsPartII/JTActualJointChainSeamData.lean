import DaggerModelsPartII.JTActualJointChainInverseFace
import DaggerModelsPartII.JTOrdinalInverseFaceDiagram
import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.JTJointSubcomplexRelativeLift

/-!
The actual higher-choice chain edges and their natural full inverse-image support.
All data come from the original Family and its exact-cut higher choices. This is
input for relative seam triangles; it does not identify the exact-cut source with
the weak marked source or assert that its projection to the original base is weak.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChainSeamData

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev I := JTActualJointChoiceChainGraph.Index F j
private abbrev K := JTActualJointChoiceChainGraph.ordinals F j
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- The actual exact cut, with its entire higher edge choice and full chain. -/
abbrev marked : I F j ⥤ JTExactlyMarkedSourceDiagram.Index F j :=
  JTActualJointChoiceChainGraph.base F j ⋙ JTActualJointChoiceCover.projection F j

/-- The original used face on the actual selected cut. -/
abbrev oldSupport := marked F j ⋙ JTExactlyMarkedSourceDiagram.supports F j

private abbrev oldDegree := marked F j ⋙ JTExactlyMarkedSourceDiagram.degrees F j
private abbrev α := JTActualJointChoiceChainGraph.toOriginal F j

/-- The original full-time support inclusion, pulled to the actual chains. -/
abbrev oldIncl : oldSupport F j ⟶ oldDegree F j :=
  Functor.whiskerLeft (marked F j) (JTExactlyMarkedSourceDiagram.incl F j)

private theorem oldIncl_mono (p : I F j) : Mono ((oldIncl F j).app p) :=
  JTExactlyMarkedSourceDiagram.incl_mono F j ((marked F j).obj p)

/-- Every chain vertex above the original used face, with all induced operators. -/
abbrev support : I F j ⥤ SimplexCategory :=
  JTOrdinalInverseFaceDiagram.supportDiagram (oldSupport F j) (oldDegree F j)
    (K F j) (oldIncl F j) (α F j) (oldIncl_mono F j)
    (JTActualJointChoiceChainGraph.toOriginal_surjective F j)

/-- Natural inclusion of the whole inverse-image face in the unchanged chain. -/
abbrev incl : support F j ⟶ K F j :=
  JTOrdinalInverseFaceDiagram.inclNat _ _ _ (oldIncl F j) (α F j)
    (oldIncl_mono F j) (JTActualJointChoiceChainGraph.toOriginal_surjective F j)

/-- The exact natural coordinate in the original full-time support. -/
abbrev toOldSupport : support F j ⟶ oldSupport F j :=
  JTOrdinalInverseFaceDiagram.toFaceNat _ _ _ (oldIncl F j) (α F j)
    (oldIncl_mono F j) (JTActualJointChoiceChainGraph.toOriginal_surjective F j)

/-- The full inverse-image square commutes along every actual chain operator. -/
theorem natural_square :
    toOldSupport F j ≫ oldIncl F j = incl F j ≫ α F j :=
  JTOrdinalInverseFaceDiagram.natural_square _ _ _ (oldIncl F j) (α F j)
    (oldIncl_mono F j) (JTActualJointChoiceChainGraph.toOriginal_surjective F j)

/-- Each new component is the existing pointwise full inverse-image inclusion. -/
theorem incl_app (p : I F j) :
    (incl F j).app p = JTActualJointChainInverseFace.incl F j p := rfl

/-- Every full inverse-image face includes monomorphically. -/
theorem incl_mono (p : I F j) : Mono ((incl F j).app p) :=
  JTOrdinalInverseFaceDiagram.incl_mono _ _ _ (oldIncl F j) (α F j)
    (oldIncl_mono F j) (JTActualJointChoiceChainGraph.toOriginal_surjective F j) p

/-- The actual natural support as a diagram of simplicial sets. -/
abbrev supportSSet : I F j ⥤ SSet.{0} := support F j ⋙ std

/-- The whole natural simplicial inclusion used in the relative seam problem. -/
abbrev supportIncl : supportSSet F j ⟶ K F j ⋙ std :=
  Functor.whiskerRight (incl F j) std

/-- Each simplicial support inclusion is monic. -/
theorem supportIncl_mono (p : I F j) : Mono ((supportIncl F j).app p) := by
  haveI := incl_mono F j p
  exact JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _

/-- Each entire support face includes by a Kan weak equivalence. -/
theorem supportIncl_weak (p : I F j) : WeakEquivalence ((supportIncl F j).app p) :=
  JTInterleavedParameter.standardMap_weak _

/-- The actual old cut row, at the exact common-chain coefficient degree. -/
def endpointRows : K F j ⋙ std ⟶ (Functor.const (I F j)).obj (row W ⦋0⦌) :=
  Functor.whiskerRight (α F j) std ≫
    Functor.whiskerLeft (marked F j) (JTExactlyMarkedSourceDiagram.endpointRows F j)

/-- The whole inverse-image support is literally the fixed joint row. -/
theorem supported_endpoint (p : I F j) :
    (supportIncl F j).app p ≫ (endpointRows F j).app p =
      term ((supportSSet F j).obj p) ≫ vertexPoint W (z j) := by
  have h := congrArg (fun η : support F j ⟶ oldDegree F j ↦ η.app p)
    (natural_square F j)
  change (toOldSupport F j).app p ≫ (oldIncl F j).app p =
    (incl F j).app p ≫ (α F j).app p at h
  change std.map ((incl F j).app p) ≫
    (std.map ((α F j).app p) ≫
      (JTExactlyMarkedSourceDiagram.endpointRows F j).app ((marked F j).obj p)) = _
  rw [← Category.assoc, ← std.map_comp, ← h, std.map_comp, Category.assoc]
  change std.map ((toOldSupport F j).app p) ≫
    (std.map ((JTExactlyMarkedSourceDiagram.incl F j).app ((marked F j).obj p)) ≫
      (JTExactlyMarkedSourceDiagram.endpointRows F j).app ((marked F j).obj p)) = _
  rw [JTExactlyMarkedSourceDiagram.supported_endpoint, ← Category.assoc]
  congr 1

/-- The actual ending edge has the prescribed varying-to-fixed boundary. -/
theorem ending_boundary (p : I F j) :
    (JTActualJointChoiceChainGraph.chainEnding F j).app p ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.boundaryPair W ((endpointRows F j).app p) (z j) :=
  JTActualJointChainSideLabels.ending_pair F j p

/-- The actual starting edge has the prescribed fixed-to-varying boundary. -/
theorem starting_boundary (p : I F j) :
    (JTActualJointChoiceChainGraph.chainStarting F j).app p ≫ endpointArrow W =
      JTJointSubcomplexRelativeLift.reverseBoundaryPair W
        ((endpointRows F j).app p) (z j) :=
  JTActualJointChainSideLabels.starting_pair F j p

/-- The entire ending edge is the identity on its natural full support. -/
theorem ending_supported (p : I F j) :
    (supportIncl F j).app p ≫ (JTActualJointChoiceChainGraph.chainEnding F j).app p =
      JTJointSubcomplexRelativeLift.identityOnU W (z j) := by
  have h := JTActualJointChainInverseFace.ending_face F j p
  change (supportIncl F j).app p ≫ (JTActualJointChoiceChainGraph.chainEnding F j).app p =
    (term ((supportSSet F j).obj p) ≫ vertexPoint W (z j)) ≫
      JTEndpointNormalizationLifts.identityFamily W at h
  simpa only [JTJointSubcomplexRelativeLift.identityOnU, Category.assoc] using h

/-- The entire starting edge is the identity on the same natural full support. -/
theorem starting_supported (p : I F j) :
    (supportIncl F j).app p ≫ (JTActualJointChoiceChainGraph.chainStarting F j).app p =
      JTJointSubcomplexRelativeLift.identityOnU W (z j) := by
  have h := JTActualJointChainInverseFace.starting_face F j p
  change (supportIncl F j).app p ≫ (JTActualJointChoiceChainGraph.chainStarting F j).app p =
    (term ((supportSSet F j).obj p) ≫ vertexPoint W (z j)) ≫
      JTEndpointNormalizationLifts.identityFamily W at h
  simpa only [JTJointSubcomplexRelativeLift.identityOnU, Category.assoc] using h

end
end DaggerModels.PartII.JTActualJointChainSeamData
