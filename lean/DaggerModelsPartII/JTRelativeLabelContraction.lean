import DaggerModelsPartII.JTRelativeEndpointPrism
import DaggerModelsPartII.JTOrderedNecklaceLabelFibrancy
import DaggerModelsPartII.JTConstantOrderedLabel
import DaggerModelsPartII.JTHigherInterleavedParameter
import DaggerModelsPartII.JTJointEndpointRelativeLift

/-! A fixed-degree ordered label contracts relative to its complete used face. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerNativeHornPointWeakEquivalences DaggerNativeStandardSimplexContraction
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRelativeLabelContraction

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open TripleBeadEndpointLabel (labels)
open OrderedNecklaceLabelDiagram (necklaceBoundaryRestriction)
open JTConstantOrderedLabel (constantCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable (W : Source) (z : Vertex W) (T : NecklaceCode)
variable {l k : SimplexCategory} (u : l ⟶ k)

private theorem simplex_map_weak : WeakEquivalence (std.map u : std.obj l ⟶ std.obj k) := by
  have hl : WeakEquivalence (toUnit (std.obj l)) :=
    contractible_terminal_weak (simplexContractible l.len)
  have hk : WeakEquivalence (toUnit (std.obj k)) :=
    contractible_terminal_weak (simplexContractible k.len)
  letI := hl
  letI := hk
  have h : std.map u ≫ toUnit (std.obj k) = toUnit (std.obj l) :=
    isTerminalTensorUnit.hom_ext _ _
  exact weakEquivalence_of_postcomp_of_fac h

/-- A positive-length native ordered label is homotopic to the literal constant
label at the SAME coefficient degree. Both the whole given support face and the
outer ordered boundary stay fixed throughout the homotopy. -/
theorem exists_relative_label_prism [Mono u]
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hT : 0 < T.len) (c : std.obj k ⟶ labels W T)
    (hboundary : c ≫ (necklaceBoundaryRestriction W).app (op T) =
      term (std.obj k) ≫ boundaryPoint W z z)
    (hsupport : std.map u ≫ c = constantCoefficient W z T l) :
    ∃ H : std.obj k ⊗ (Δ[1] : SSet.{0}) ⟶ labels W T,
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice (std.obj k) 0 ≫ H = c ∧
      DaggerOriginalCounitRightConeRelativeHomotopy.timeSlice (std.obj k) 1 ≫ H =
        constantCoefficient W z T k ∧
      (std.map u ⊗ₘ 𝟙 (Δ[1] : SSet.{0})) ≫ H =
        fst (std.obj l) (Δ[1] : SSet.{0}) ≫ constantCoefficient W z T l ∧
      H ≫ (necklaceBoundaryRestriction W).app (op T) =
        fst (std.obj k) (Δ[1] : SSet.{0}) ≫
          term (std.obj k) ≫ boundaryPoint W z z := by
  letI : Mono (std.map u : std.obj l ⟶ std.obj k) :=
    JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono u
  letI : WeakEquivalence (std.map u : std.obj l ⟶ std.obj k) := simplex_map_weak u
  letI : Fibration ((necklaceBoundaryRestriction W).app (op T)) :=
    JTOrderedNecklaceLabelFibrancy.necklaceBoundaryRestriction_fibration W hW T hT
  exact JTRelativeEndpointPrism.exists_relativePrism (std.map u)
    ((necklaceBoundaryRestriction W).app (op T))
    (term (std.obj k) ≫ boundaryPoint W z z)
    (constantCoefficient W z T l) c (constantCoefficient W z T k)
    hboundary (JTConstantOrderedLabel.constantCoefficient_boundary W z T k)
    hsupport (JTConstantOrderedLabel.constantCoefficient_ordinal W z T u).symm

end
end DaggerModels.PartII.JTRelativeLabelContraction
