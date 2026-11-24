import DaggerModelsPartII.JTEndpointGraphCoefficientOverlap
import DaggerModelsPartII.JTFiniteCoefficientBridgeMixedCylinder
import DaggerModelsPartII.JTCommonCoefficientHorizontalCylinder

/-! Natural comparison of all original cylinders with the finite bridge on graph overlaps. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped Prod

namespace DaggerModels.PartII.JTEndpointGraphOverlapCylinder

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTEndpointSimplexSlice JTEndpointRowGraphOperators JTEndpointGraphCoefficientSlice
open JTEndpointGraphCoefficientOverlap
open JTNecklaceEndpointCylinder
open NecklaceCylinderJointDiagram (cylinderUnder)
open JTFiniteCoefficientBridgeCylinder
open JTMixedGraphRawRefinement (nativeGraphParameter)
open JTHigherMixedGraphTargetLift (commonToDecorated)

noncomputable section

private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev Boundary := JTXiEndpointCollapse.boundary

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)

private abbrev I := ParameterIndex P parents refineTo

/-- The actual padded source of the common child. -/
abbrev nativeCodes : I P parents refineTo ⥤ NecklaceCode :=
  CategoryTheory.Prod.fst _ _ ⋙ source P parents refineTo ⋙ horizontal ⋙ paddedSource d

abbrev cylinders (F : I P parents refineTo ⥤ SimplexCategory) : I P parents refineTo ⥤ Under Boundary :=
  ((nativeCodes P parents refineTo).prod' F) ⋙ cylinderUnder

private abbrev childGraph (U : I P parents refineTo) := U.1.pt.unop
private abbrev dim (U : I P parents refineTo) := (horizontalDegree (childGraph P parents refineTo U)).len
private abbrev param (U : I P parents refineTo) := (graph (childGraph P parents refineTo U)).obj.parameter

private abbrev parameter (U : I P parents refineTo) :=
  nativeGraphParameter (d := dim P parents refineTo U) (param P parents refineTo U)

/-- The full bridge joining map in the actual reduced-cylinder category. -/
def join : cylinders P parents refineTo (joinedTime P parents refineTo) ⟶
    cylinders P parents refineTo (bridgeParameter P parents refineTo) where
  app U := Under.homMk
    (cylinderMap (side U.1) (final U.1) (timeAt P parents refineTo U)
      ((nativeCodes P parents refineTo).obj U) (parameter P parents refineTo U))
    (cylinderMap_boundary _ _ _ _ _)
  naturality {U V} f := by
    let S := (nativeCodes P parents refineTo).obj U
    let T := (nativeCodes P parents refineTo).obj V
    let v : S ⟶ T := (nativeCodes P parents refineTo).map f
    let k := (degree P parents refineTo).map f.1
    let j := (joinedTime P parents refineTo).map f
    let a := (bridgeParameter P parents refineTo).map f
    let h := f.1.hom.unop.base.unop.left
    have hp : parameter P parents refineTo U ≫ J.map k =
        v.map ≫ parameter P parents refineTo V :=
      JTMixedGraphHorizontalTraversal.parameter_mixed
        (d := dim P parents refineTo U) (e := dim P parents refineTo V)
        h.1 h.2.1 h.2.2 k f.1.hom.unop.fiber.unop.hom.parameter
    have hc := JTFiniteCoefficientBridgeMixedCylinder.cylinderMap_mixed
      (side U.1) (final U.1) (timeAt P parents refineTo U)
      (side V.1) (final V.1) (timeAt P parents refineTo V) v k
      (parameter P parents refineTo U) (parameter P parents refineTo V)
      hp j a (paired_natural f)
    apply Under.UnderMorphism.ext
    change (nativeMap v ((joinedTime P parents refineTo).obj U) ≫ (value T).map j) ≫
        cylinderMap (side V.1) (final V.1) (timeAt P parents refineTo V) T
          (parameter P parents refineTo V) =
      cylinderMap (side U.1) (final U.1) (timeAt P parents refineTo U) S
          (parameter P parents refineTo U) ≫
        (nativeMap v ((bridgeParameter P parents refineTo).obj U) ≫ (value T).map a)
    have hj := nativeMap_parameter_natural v j
    have ha := nativeMap_parameter_natural v a
    rw [← hj, ← ha, Category.assoc]
    exact hc.symm

/-- Select one copy's horizontal coefficient cylinder and retain the entire time face. -/
theorem join_side (e : Fin (m + 1)) (U : I P parents refineTo) :
    (under ((nativeCodes P parents refineTo).obj U)).map ((timeToJoined P parents refineTo e).app U) ≫
        (join P parents refineTo).app U =
      commonToDecorated (d := dim P parents refineTo U) (n := timeAt P parents refineTo U)
          (side U.1 e) (param P parents refineTo U) ≫
        (under ((nativeCodes P parents refineTo).obj U)).map
          ((sideToBridge P parents refineTo e).app U) := by
  apply Under.UnderMorphism.ext
  exact cylinderMap_side (side U.1) (final U.1) (timeAt P parents refineTo U)
    (fun r ↦ coefficientDegree.map (refineTo r)) (side_final U.1)
    ((nativeCodes P parents refineTo).obj U) (parameter P parents refineTo U) e

end
end DaggerModels.PartII.JTEndpointGraphOverlapCylinder
