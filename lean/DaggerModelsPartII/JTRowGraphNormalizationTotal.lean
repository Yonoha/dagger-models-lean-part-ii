import DaggerModelsPartII.JTRowGraphNormalizationDiagram
import DaggerModelsPartII.GrothendieckTotalElements
import DaggerModelsPartII.GrothendieckNerveReplacement
import DaggerModelsPartII.OrderedLabelNaturalWeakSpans

/-! The actual category of all normalization simplices over a fixed raw simplex. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphNormalizationTotal

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTMixedGraphEndpointLifts JTRowGraphNormalizationDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

/-- The category of all degrees of actual normalized endpoint families, with
the original coefficient and simplex operators. -/
abbrev NormalizedSimplices :=
  (GrothendieckTotalElements.totalDiagram (diagram hx hy)).Elements

/-- Include every normalization simplex over one fixed graph. -/
def fixedGraphInclusion (G : (JTRowGraphFiber.Fiber q)ᵒᵖ) :
    ((diagram hx hy).obj G).Elements ⥤ NormalizedSimplices hx hy :=
  Grothendieck.ι (GrothendieckTotalElements.elementDiagram (diagram hx hy)) G ⋙
    GrothendieckTotalElements.toTotal (diagram hx hy)

private theorem point_iff {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    GW (pointMap X) ↔ GW (pointMap Y) := by
  have h : f ≫ pointMap Y = pointMap X := pointIsTerminal.hom_ext _ _
  rw [← weakEquivalence_iff_GW, ← weakEquivalence_iff_GW, ← h]
  exact weakEquivalence_precomp_iff f _

/-- The whole normalization simplex category has weakly contractible nerve
for an injectively fibrant reversal diagram. -/
theorem normalizedSimplices_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (NormalizedSimplices hx hy))) := by
  let G := diagram hx hy
  let E := GrothendieckTotalElements.elementDiagram G
  let a := OrderedLabelNaturalWeakSpans.toInput G
  let b := OrderedLabelNaturalWeakSpans.toOppositeElements G
  let c := OrderedLabelNaturalWeakSpans.oppositeToRealized G
  let e := OrderedLabelNaturalWeakSpans.elementsToRealized G
  let l := GrothendieckNerveReplacement.toFiberBar E
  let r := GrothendieckNerveReplacement.toGrothendieck E
  let j := nerveMap (GrothendieckTotalElements.equivalence G).functor
  letI : WeakEquivalence a := OrderedLabelNaturalWeakSpans.toInput_weak G
  letI : WeakEquivalence b := OrderedLabelNaturalWeakSpans.toOppositeElements_weak G
  letI : WeakEquivalence c := OrderedLabelNaturalWeakSpans.oppositeToRealized_weak G
  letI : WeakEquivalence e := OrderedLabelNaturalWeakSpans.elementsToRealized_weak G
  letI : WeakEquivalence l := GrothendieckNerveReplacement.toFiberBar_weak E
  letI : WeakEquivalence r := GrothendieckNerveReplacement.toGrothendieck_weak E
  letI : WeakEquivalence j :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have ha := (point_iff a).mpr (bar_point_GW hx hy hW)
  have hc := (point_iff c).mp ((point_iff b).mp ha)
  have hl := (point_iff l).mpr ((point_iff e).mpr hc)
  exact (point_iff j).mp ((point_iff r).mp hl)

end

end DaggerModels.PartII.JTRowGraphNormalizationTotal
