import DaggerModelsPartII.JTGraphCoveredLabelEvaluation

/-! Public cylinder equations for complete graph-covered decorated evaluations. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredCylinderEquations

open JTParametrizedTargetFamilies (codes)
open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceEndpointCylinder (cylinder)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (time : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)

private abbrev productDiagram := JTJointRelativeParameters.withTime Q.map J time
  (Over.lift (codes L) c) (JTTargetIntervalOverMapping.whole Q.code)

variable {Y : I ⥤ SSet.{0}} (π : Y ⟶ productDiagram Q L time c)

private abbrev d := JTGraphCoveredLabelEvaluation.boundary Q L time c
private abbrev e := Functor.whiskerLeft time JTXiEndpointCollapse.cylinderProjection
private abbrev u := JTEndpointReducedPullbackCover.boundaryInclusion π (d Q L time c)
private abbrev ec := JTEndpointReducedPullbackCover.collapse π (d Q L time c) (e time)

/-- The entire graph-domain summand of the endpoint quotient. -/
abbrev inc := pushout.inl (u Q L time c π) (ec Q L time c π)

/-- The native cylinder projection retains the whole original time. -/
theorem projection_cylinder (a : I) :
    (inc Q L time c π).app a ≫
        ((JTGraphCoveredLabelEvaluation.projection Q L time c π).app a).right =
      π.app a ≫ (cylinder ((codes L).obj a)).app (time.obj a) := by
  exact JTEndpointReducedPullbackCover.projection_cylinder _ _ _ _ _ _ a

/-- The complete decorated leg on the cylinder summand is the specified
native coordinate paired with the full coefficient parameter. -/
theorem decorated_cylinder
    (θ : Y ⟶ JTParametrizedTargetFamilyComparison.degrees L ⋙ J) (a : I) :
    (inc Q L time c π).app a ≫
        ((JTGraphCoveredLabelEvaluation.decorated Q L time c π θ).app a).right =
      lift (π.app a ≫ fst ((codes L).obj a).toSSet (J.obj (time.obj a))) (θ.app a) ≫
        (cylinder ((codes L).obj a)).app
          ((JTParametrizedTargetFamilyComparison.degrees L).obj a) := by
  exact JTEndpointReducedCover.descend_cylinder _ _ _ _ _ a

/-- Changing the coefficient ordinal acts on the complete paired graph map. -/
theorem coefficient_cylinder_map {X : SSet.{0}} (T : NecklaceCode)
    {k l : SimplexCategory} (α : k ⟶ l) (h : X ⟶ T.toSSet) (θ : X ⟶ J.obj k) :
    (lift h θ ≫ (cylinder T).app k) ≫ (JTNecklaceEndpointCylinder.value T).map α =
      lift h (θ ≫ J.map α) ≫ (cylinder T).app l := by
  have ht : lift h θ ≫ (𝟙 T.toSSet ⊗ₘ J.map α) = lift h (θ ≫ J.map α) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst, Category.comp_id]
    · simp only [Category.assoc, tensorHom_snd, lift_snd, lift_snd_assoc]
  rw [Category.assoc, ← (cylinder T).naturality α]
  change lift h θ ≫ ((𝟙 T.toSSet ⊗ₘ J.map α) ≫ (cylinder T).app l) = _
  rw [← Category.assoc, ht]

end

end DaggerModels.PartII.JTGraphCoveredCylinderEquations
