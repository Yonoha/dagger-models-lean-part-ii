import DaggerModelsPartII.JTJointRelativeEdgePrism
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Full relative choices for two different endpoint rows with one common support. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTwoEndpointChoiceCover

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTJointRelativeEdgeChoiceDiagram (leftChoices rightChoices)
open GrothendieckTotalElements (totalDiagram)
open DaggerOriginalProductGadget (pointMap pointIsTerminal pointMap_tensor_GW)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev Ord := SimplexCategoryᵒᵖ

variable {I : Type} [SmallCategory I] (W : Source)
variable (s k : I ⥤ SimplexCategory) (u : s ⟶ k)
variable (f₀ f₁ : k ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (z : (row W ⦋0⦌).obj (op ⦋0⦌))
variable (h₀ : ∀ i, std.map (u.app i) ≫ f₀.app i =
  term (std.obj (s.obj i)) ≫ vertexPoint W z)
variable (h₁ : ∀ i, std.map (u.app i) ≫ f₁.app i =
  term (std.obj (s.obj i)) ≫ vertexPoint W z)

/-- The first correcting edge runs from the joint to the variable first row. -/
abbrev frontSpaces := rightChoices W s k u f₀ z h₀

/-- The last correcting edge runs from the variable last row to the joint. -/
abbrev backSpaces := leftChoices W s k u f₁ z h₁

/-- The two distinct endpoint choices share every higher simplex degree. -/
abbrev spaces : Iᵒᵖ ⥤ SSet.{0} :=
  Functor.diag Iᵒᵖ ⋙ (frontSpaces W s k u f₀ z h₀).prod
    (backSpaces W s k u f₁ z h₁) ⋙ MonoidalCategory.tensor SSet.{0}

/-- The first component keeps the entire front-edge simplex. -/
def frontProjection : spaces W s k u f₀ f₁ z h₀ h₁ ⟶ frontSpaces W s k u f₀ z h₀ where
  app _ := fst _ _
  naturality _ _ _ := tensorHom_fst _ _

/-- The second component keeps the entire back-edge simplex. -/
def backProjection : spaces W s k u f₀ f₁ z h₀ h₁ ⟶ backSpaces W s k u f₁ z h₁ where
  app _ := snd _ _
  naturality _ _ _ := tensorHom_snd _ _

/-- All higher paired choices over the ORIGINAL chart category. -/
abbrev Cover := (totalDiagram (spaces W s k u f₀ f₁ z h₀ h₁)).Elementsᵒᵖ

/-- The original chart and every original arrow are retained. -/
abbrev projection : Cover W s k u f₀ f₁ z h₀ h₁ ⥤ I :=
  (CategoryOfElements.π (totalDiagram (spaces W s k u f₀ f₁ z h₀ h₁)) ⋙
    CategoryTheory.Prod.fst Iᵒᵖ Ord).leftOp

/-- The common higher-choice time is independent of the original family time. -/
abbrev choiceTime : Cover W s k u f₀ f₁ z h₀ h₁ ⥤ SimplexCategory :=
  SynchronizedSimplicialParameters.time (spaces W s k u f₀ f₁ z h₀ h₁)

/-- Original coefficient degrees on the entire full choice cover. -/
abbrev coefficient := projection W s k u f₀ f₁ z h₀ h₁ ⋙ k

private theorem point_GW_of_terminal_weak (X : SSet.{0})
    [WeakEquivalence (term X)] : GW (pointMap X) := by
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  haveI : WeakEquivalence (pointMap X) := by
    rw [← pointIsTerminal.hom_ext (term X ≫ e.hom) (pointMap X)]
    infer_instance
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- Each full fiber of the two different endpoint choices is weakly contractible. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hu : ∀ i, Mono (u.app i)) (i : Iᵒᵖ) :
    GW (pointMap ((spaces W s k u f₀ f₁ z h₀ h₁).obj i)) := by
  haveI : Mono (u.app i.unop) := hu i.unop
  have hF : GW (pointMap ((frontSpaces W s k u f₀ z h₀).obj i)) := by
    haveI : WeakEquivalence (term ((frontSpaces W s k u f₀ z h₀).obj i)) :=
      JTJointEndpointRelativeLift.reverseLiftSpace_toPoint_weak W
      (u.app i.unop) (f₀.app i.unop) z (h₀ i.unop) hW
    exact point_GW_of_terminal_weak _
  have hB : GW (pointMap ((backSpaces W s k u f₁ z h₁).obj i)) := by
    haveI : WeakEquivalence (term ((backSpaces W s k u f₁ z h₁).obj i)) :=
      JTJointEndpointRelativeLift.liftSpace_toPoint_weak W
      (u.app i.unop) (f₁.app i.unop) z (h₁ i.unop) hW
    exact point_GW_of_terminal_weak _
  exact pointMap_tensor_GW hF hB

/-- The full higher choices give a nerve weak cover of the entire original diagram. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hu : ∀ i, Mono (u.app i)) :
    WeakEquivalence (nerveMap (projection W s k u f₀ f₁ z h₀ h₁)) := by
  let E := (totalDiagram (spaces W s k u f₀ f₁ z h₀ h₁)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff _).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (totalDiagram (spaces W s k u f₀ f₁ z h₀ h₁)) ⋙
      CategoryTheory.Prod.fst Iᵒᵖ Ord))
  exact SynchronizedSimplicialParameters.projection_weak _
    (spaces_point_GW W s k u f₀ f₁ z h₀ h₁ hW hu)

end
end DaggerModels.PartII.JTTwoEndpointChoiceCover
