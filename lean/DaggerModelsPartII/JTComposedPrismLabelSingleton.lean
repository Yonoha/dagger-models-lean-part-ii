import DaggerModelsPartII.JTComposedPrismLabels

/-! The actual internal-necklace evaluation of a single completed two-piece prism. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTComposedPrismLabelSingleton

open JTParametrizedTargetFamilies (Family)
open JTComposedPrismLabels (Coefficients index rawProduct coefficient orderedPoint
  orderedPoint_coefficient reduced_raw)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev one := Discrete PUnit

variable {W : Source} {x y : Vertex W} {T U : NecklaceCode} {k n : SimplexCategory}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (C : Coefficients W T U k x y)
variable (f : wedge T U ⟶ Q.code)
variable (p : (wedge T U).toSSet ⊗ J.obj n ⟶ J.obj k)
variable (h : rawProduct W p (coefficient C) =
  CartesianMonoidalCategory.fst (wedge T U).toSSet (J.obj n) ≫ f.map ≫ Q.map)

set_option maxHeartbeats 1000000 in
/-- Turn an exact full product into an actual family retaining all internal necklaces. -/
def family :
    Family Q ((Functor.const one).obj (index C)) ((Functor.const one).obj n) where
  collapse := {
    app := fun _ ↦ f
    naturality := by
      intro a b g
      have hab : a = b := Subsingleton.elim _ _
      subst b
      have hg : g = 𝟙 a := Subsingleton.elim _ _
      subst g
      simp }
  parameter _ := p
  parameter_map := by
    intro a b g
    have hab : a = b := Subsingleton.elim _ _
    subst b
    have hg : g = 𝟙 a := Subsingleton.elim _ _
    subst g
    simp
    change 𝟙 (wedge T U).toSSet ▷ J.obj n ≫ p = p
    rw [id_whiskerRight, Category.id_comp]
  raw _ := by
    have hp : JTBinaryPrismRealization.realizeProduct W k p
        (JTRealizedLabelEndpoints.orderedLabel W x y (wedge T U) k (orderedPoint C)) =
        CartesianMonoidalCategory.fst (wedge T U).toSSet (J.obj n) ≫ f.map ≫ Q.map := by
      rw [orderedPoint_coefficient]
      exact h
    exact reduced_raw (orderedPoint C) Q f p hp

end
end DaggerModels.PartII.JTComposedPrismLabelSingleton
