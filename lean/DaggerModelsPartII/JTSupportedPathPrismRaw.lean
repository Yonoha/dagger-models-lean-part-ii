import DaggerModelsPartII.JTSupportedCoefficientPathCover
import DaggerModelsPartII.JTRelativeFamilyPrismRaw

/-! Every higher relative contraction choice retains the complete supported raw graph. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSupportedPathPrismRaw

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)
open JTSupportedCoefficientPathCover (spaces pathCoefficient)
open JTConstantOrderedLabel (constantCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W z z)
variable (S : I ⥤ SimplexCategory)
private abbrev K := JTParametrizedTargetFamilyComparison.degrees L
variable (u : S ⟶ K W z L)
variable (hs : ∀ a : I,
  std.map (u.app a) ≫ JTSupportedOrderedCoefficientChoices.old W z L a =
    JTSupportedOrderedCoefficientChoices.supportedConstant W z L S a)
variable (a : I) (n : SimplexCategory)
variable (v : ((spaces W z L S u hs).obj (op a)).obj (op n))
variable {d : SimplexCategory} (α : d ⟶ (K W z L).obj a)
variable (t : std.obj d ⟶ std.obj ⦋1⦌ ⊗ std.obj n)

/-- The whole higher contraction family at an arbitrary coefficient-time chain. -/
def chainCoefficient : std.obj d ⟶
    (OrderedNecklaceLabelDiagram.necklaceLabels W).obj (op ((codes L).obj a)) :=
  lift (std.map α) t ≫ pathCoefficient W z L S u hs a n v

variable [Mono (u.app a)] (hα : Function.Surjective α.toOrderHom)

/-- The complete inverse image of the actual used face remains literal constant,
for every simplex of the path-choice space and every homotopy-time map. -/
theorem chainCoefficient_onFace :
    std.map (JTOrdinalFaceInverseImage.incl (u.app a) α hα) ≫
      chainCoefficient W z L S u hs a n v α t =
    constantCoefficient W z ((codes L).obj a)
      (JTOrdinalFaceInverseImage.ordinal (u.app a) α) := by
  apply JTRelativeFamilyPrismRaw.chainCoefficient_onFace
    W z ((codes L).obj a) (u.app a) α hα
    (pathCoefficient W z L S u hs a n v)
    (JTSupportedCoefficientPathCover.pathCoefficient_support W z L S u hs a n v) t

variable {X : SSet.{0}} (h : X ⟶ ((codes L).obj a).toSSet) (θ : X ⟶ J.obj d)
variable (q : X ⟶ J.obj (S.obj a))

include hα in
/-- The literal joint raw equation holds on the ENTIRE supported graph, with all
higher choices retained. No natural choice of a single homotopy is assumed. -/
theorem chain_raw (hθ : θ ≫ J.map α = q ≫ J.map (u.app a)) :
    lift h θ ≫ JTNecklaceLabelRealization.realizedLabel ((codes L).obj a).toSSet W d
        (SSet.yonedaEquiv (chainCoefficient W z L S u hs a n v α t)) =
      h ≫ term ((codes L).obj a).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  exact JTRelativeFamilyPrismRaw.chain_raw W z ((codes L).obj a) (u.app a) α hα
    (pathCoefficient W z L S u hs a n v)
    (JTSupportedCoefficientPathCover.pathCoefficient_support W z L S u hs a n v)
    t h θ q hθ

end
end DaggerModels.PartII.JTSupportedPathPrismRaw
