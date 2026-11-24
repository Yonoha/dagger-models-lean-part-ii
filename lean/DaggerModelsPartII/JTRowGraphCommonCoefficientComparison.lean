import DaggerModelsPartII.JTCommonCoefficientFinalComma
import DaggerModelsPartII.JTRowGraphNormalizationDiagram

/-!
# The comparison on the original coefficient arrows of row graphs
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTRowGraphCommonCoefficientComparison

open JTHigherInterleavedParameter (common)
open JTRowGraphFiber JTProjectiveOrderedFiberComparison
open JTMixedGraphRawRefinement OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open JTCommonCoefficientFinalPullback JTCommonCoefficientFinalComma
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{0}.obj a
private abbrev code := MixedGraphCylinderTraversal.code

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {r : ℕ}
variable {q : simplex ⦋r⦌ ⟶ Raw W} {G H : Fiber q}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (u : G ⟶ H) (n : SimplexCategory)

private abbrev opOf : G.obj.degree ⟶ H.obj.degree := u.hom.operator
private abbrev s := nativeGraphParameter G.obj.parameter

theorem nativeGraphParameter_arrow :
    s (G := G) ≫ J.map (opOf u) = nativeGraphParameter H.obj.parameter := by
  rw [nativeGraphParameter_map, u.hom.parameter]

variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code r))).obj
  (op (common H.obj.degree n)))
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q

variable (U : (under (code r)).obj n ⟶ (D Q).obj (finalIndex n z))
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n z) =
  JTHigherMixedGraphTargetLift.toDecorated r H.obj.parameter n)

include hU in
/-- The common-coefficient comparison uses the original graph's
parameter equation and the original final cylinder leg. -/
theorem final_leg :
    U ≫ JTTargetCommaPullback.fst W x y Q (finalIndex n z) =
      finalCylinder (opOf u) n z (s (G := G)) := by
  rw [hU]
  apply Under.UnderMorphism.ext
  change JTHigherGraphPrismCylinder.cylinderMap (code r) (nativeGraphParameter H.obj.parameter) n =
    JTHigherGraphPrismCylinder.cylinderMap (code r) (s (G := G) ≫ J.map (opOf u)) n
  rw [nativeGraphParameter_arrow u]

/-- An arbitrary original graph coefficient arrow transports the
comparison in the actual target comma, naturally in the original
internal necklaces. -/
def compareGraphArrow :
    pulledComma (opOf u) n z (s (G := G)) Q U (final_leg u n z Q U hU) ⟶
      finalComma n z Q U :=
  compareComma (opOf u) n z (s (G := G)) Q U (final_leg u n z Q U hU)

end

end DaggerModels.PartII.JTRowGraphCommonCoefficientComparison
