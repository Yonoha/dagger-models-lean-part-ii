import DaggerModelsPartII.JTGraphNormalizedFactoredPresentation
import DaggerModelsPartII.JTNativeFactorVertexFibers

/-!
# Comparison of transported lifts through the same normalized traversal
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphNormalizedOverlap

open JTProjectiveOrderedFiberComparison (row)
open JTGraphLiftTransport
open JTGraphRestrictionRaw (predecessor)
open JTGraphTransportRaw (commaTransport)
open JTGraphBeadBoundaryReflection (graph_eq_of_reflectsBeadBoundary)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphNormalizedFactoredPresentation
  (normalizedCode quotient traversal traversal_factor objectOfFactor reflectsBeadBoundary_of_factor
    targetFactor targetFactor_factor object)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {V : TargetComma Q} {S : NecklaceCode}

variable (c : S ⟶ V.left.fiber.left)

/-- Transport a lift and then compare it to the prescribed normalized graph. -/
def comparisonOfFactor (r : normalizedCode c ⟶ Q.code)
    (hr : quotient c ≫ r = c ≫ V.hom.hom)
    {U : TargetComma Q} (a : U ⟶ V) (D : GraphLift U.left S)
    (E : GraphLift (objectOfFactor c r hr).left (normalizedCode c))
    (hD : (D.transport a.left).collapse = c) (hE : E.collapse = 𝟙 _) :
    predecessor (U := U) D ⟶ predecessor (U := objectOfFactor c r hr) E :=
  commaTransport D a ≫ JTGraphFactoredComparison.compare c (quotient c) (traversal c) r
    (traversal_factor c) hr (D.transport a.left) E hD hE
    (graph_eq_of_reflectsBeadBoundary (quotient c) _ (reflectsBeadBoundary_of_factor c r hr)
      (degree V.left))

/-- The comparison retains exactly the normalization map of the shared source. -/
theorem comparisonOfFactor_code (r : normalizedCode c ⟶ Q.code)
    (hr : quotient c ≫ r = c ≫ V.hom.hom)
    {U : TargetComma Q} (a : U ⟶ V) (D : GraphLift U.left S)
    (E : GraphLift (objectOfFactor c r hr).left (normalizedCode c))
    (hD : (D.transport a.left).collapse = c) (hE : E.collapse = 𝟙 _) :
    (comparisonOfFactor c r hr a D E hD hE).left.fiber.left = quotient c := by
  let F := CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)
  change F.map (comparisonOfFactor c r hr a D E hD hE) = _
  rw [comparisonOfFactor, F.map_comp]
  change 𝟙 S ≫ quotient c = quotient c
  exact Category.id_comp _

/-- All lifts that transport to the prescribed collapse admit a common
normalized comparison, even if their original presentations differ. -/
theorem exists_common_over_factor (r : normalizedCode c ⟶ Q.code)
    (hr : quotient c ≫ r = c ≫ V.hom.hom) :
    ∃ E : GraphLift (objectOfFactor c r hr).left (normalizedCode c), E.collapse = 𝟙 _ ∧
      ∀ {U : TargetComma Q} (a : U ⟶ V) (D : GraphLift U.left S),
        (D.transport a.left).collapse = c →
          Nonempty (predecessor (U := U) D ⟶ predecessor (U := objectOfFactor c r hr) E) := by
  obtain ⟨E, hE⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift (objectOfFactor c r hr).left
  exact ⟨E, hE, fun a D hD ↦ ⟨comparisonOfFactor c r hr a D E hD hE⟩⟩

/-- When the fixed target is monic, the same normalized comparison is
available for all transports to the prescribed collapse. -/
theorem exists_common_over_monic [Mono Q.map] :
    ∃ E : GraphLift (object c).left (normalizedCode c), E.collapse = 𝟙 _ ∧
      ∀ {U : TargetComma Q} (a : U ⟶ V) (D : GraphLift U.left S),
        (D.transport a.left).collapse = c →
          Nonempty (predecessor (U := U) D ⟶ predecessor (U := object c) E) :=
  exists_common_over_factor c (targetFactor c) (targetFactor_factor c)

/-- For arbitrary raw targets, the required factor exists exactly when
the native target map is constant on the vertex fibers of the quotient. -/
theorem exists_common_over_vertex_fibers
    (h : ∀ i j : Fin (S.len + 1),
      NecklaceCode.orderMap (quotient c).map i = NecklaceCode.orderMap (quotient c).map j →
        NecklaceCode.orderMap (c ≫ V.hom.hom).map i =
          NecklaceCode.orderMap (c ≫ V.hom.hom).map j) :
    ∃ (r : normalizedCode c ⟶ Q.code) (hr : quotient c ≫ r = c ≫ V.hom.hom),
      ∃ E : GraphLift (objectOfFactor c r hr).left (normalizedCode c), E.collapse = 𝟙 _ ∧
        ∀ {U : TargetComma Q} (a : U ⟶ V) (D : GraphLift U.left S),
          (D.transport a.left).collapse = c →
            Nonempty (predecessor (U := U) D ⟶ predecessor (U := objectOfFactor c r hr) E) := by
  obtain ⟨r, hr⟩ := (JTNativeFactorVertexFibers.factor_iff_vertex_fibers
    (quotient c) (c ≫ V.hom.hom)).mpr h
  exact ⟨r, hr, exists_common_over_factor c r hr⟩

end

end DaggerModels.PartII.JTGraphNormalizedOverlap
