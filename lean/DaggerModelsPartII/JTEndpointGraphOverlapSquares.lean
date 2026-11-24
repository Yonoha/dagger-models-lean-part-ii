import DaggerModelsPartII.JTEndpointGraphOverlapLabels

/-! Compare all internal necklaces of each original chart to the joined evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointGraphOverlapComparison

open OrdinaryJTRealization (realization)
open JTReversalInput (ordinaryInput)
open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTEndpointGraphCoefficientSlice (MixedGraphs)
open JTEndpointGraphCoefficientOverlap
open JTEndpointGraphOverlapChoices
open JTEndpointGraphOverlapFamilies (dim toFixedBead)
open JTEndpointGraphOverlapRestriction
open JTEndpointGraphOverlapLabels
open JTEndpointGraphOverlapEvaluation (sourceCylinders labelIndex lifts lifts_decorated lifts_native)
open JTNecklaceEndpointCylinder (under nativeMap nativeMap_id)
open JTHigherMixedGraphTargetLift (toNativeTarget toNativeTarget_natural)
open BoundaryNecklaceComma (diagram fiberDiagram necklaceUnder)

noncomputable section

private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {d m : ℕ}
variable {q : (Δ[d] : SSet.{0}) ⟶ realization.obj (ordinaryInput.obj W)}
variable (P : MixedGraphs q) (parents : Fin (m + 1) → MixedGraphs q)
variable (refineTo : ∀ e, parents e ⟶ P)
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

private abbrev Q := JTNormalizedGraphTargetArrow.target hx hy
private abbrev I := Index P parents refineTo hx hy
private abbrev F := projection P parents refineTo hx hy

variable (e : Fin (m + 1))

private abbrev R := toSide P parents refineTo hx hy e
private abbrev C := JTEndpointGraphCoefficientEvaluation.cylinders (parents e) hx hy
private abbrev sideCylinders := R P parents refineTo hx hy e ⋙ C parents hx hy e
private abbrev E := JTTargetCommaPullback.diagram W x y (Q hx hy)
private abbrev sideLifts := Functor.whiskerLeft (R P parents refineTo hx hy e)
  (JTEndpointGraphCoefficientEvaluation.lifts (parents e) hx hy)

def timeInclusion : sideCylinders P parents refineTo hx hy e ⟶
    sourceCylinders P parents refineTo hx hy :=
  Functor.whiskerRight
    (NatTrans.prod' (𝟙 (F P parents refineTo hx hy ⋙
      JTEndpointGraphOverlapCylinder.nativeCodes P parents refineTo))
      (Functor.whiskerLeft (F P parents refineTo hx hy) (timeToJoined P parents refineTo e)))
    NecklaceCylinderJointDiagram.cylinderUnder

private theorem timeInclusion_app (U : I P parents refineTo hx hy) :
    (timeInclusion P parents refineTo hx hy e).app U =
    (under ((JTEndpointGraphOverlapCylinder.nativeCodes P parents refineTo).obj
      ((F P parents refineTo hx hy).obj U))).map
      ((timeToJoined P parents refineTo e).app ((F P parents refineTo hx hy).obj U)) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 _) _ ≫ _ = _
  rw [nativeMap_id, Category.id_comp]
  rfl

private theorem comparePullback {S T : Under JTXiEndpointCollapse.boundary}
    {L L' : OrderedLabelElements.Index W (OrderedNecklaceVertexPoints.boundaryPoint W x y)}
    (a : L ⟶ L') (p : S ⟶ (E hx hy).obj L) (t : T ⟶ (E hx hy).obj L') (r : S ⟶ T)
    (h₁ : (p ≫ JTTargetCommaPullback.fst W x y (Q hx hy) L) ≫
        (DecoratedCylinderNecklacePresentation.underDiagram W x y).map a =
      r ≫ (t ≫ JTTargetCommaPullback.fst W x y (Q hx hy) L'))
    (h₂ : p ≫ JTTargetCommaPullback.snd W x y (Q hx hy) L =
      r ≫ (t ≫ JTTargetCommaPullback.snd W x y (Q hx hy) L')) :
    p ≫ (E hx hy).map a = r ≫ t := by
  apply pullback.hom_ext
    (f := (DecoratedCylinderNecklacePresentation.underCocone W x y).app L')
    (g := JTTargetCommaPullback.targetMap W x y (Q hx hy))
  · change (p ≫ (E hx hy).map a) ≫ JTTargetCommaPullback.fst W x y (Q hx hy) L' =
      (r ≫ t) ≫ JTTargetCommaPullback.fst W x y (Q hx hy) L'
    rw [Category.assoc p, JTTargetCommaPullback.map_fst W x y (Q hx hy) a,
      ← Category.assoc p, Category.assoc r]
    exact h₁
  · change (p ≫ (E hx hy).map a) ≫ JTTargetCommaPullback.snd W x y (Q hx hy) L' =
      (r ≫ t) ≫ JTTargetCommaPullback.snd W x y (Q hx hy) L'
    rw [Category.assoc p, JTTargetCommaPullback.map_snd W x y (Q hx hy) a, Category.assoc r]
    exact h₂

private abbrev V (U : I P parents refineTo hx hy) := (R P parents refineTo hx hy e).obj U
private abbrev L (U : I P parents refineTo hx hy) :=
  (JTEndpointGraphCoefficientLabels.labelIndex (parents e) hx hy).obj (V P parents refineTo hx hy e U)
private abbrev L' (U : I P parents refineTo hx hy) := (labelIndex P parents refineTo hx hy).obj U
private abbrev pAt (U : I P parents refineTo hx hy) := (sideLifts P parents refineTo hx hy e).app U
private abbrev tAt (U : I P parents refineTo hx hy) := (lifts P parents refineTo hx hy).app U
private abbrev aAt (U : I P parents refineTo hx hy) :=
  (toBridgeLabel P parents refineTo hx hy e).app U
private abbrev rAt (U : I P parents refineTo hx hy) := (timeInclusion P parents refineTo hx hy e).app U

set_option maxHeartbeats 350000 in
private theorem decoratedSquare (U : I P parents refineTo hx hy) :
    (pAt P parents refineTo hx hy e U ≫ JTTargetCommaPullback.fst W x y (Q hx hy)
      (L P parents refineTo hx hy e U)) ≫
        (DecoratedCylinderNecklacePresentation.underDiagram W x y).map (aAt P parents refineTo hx hy e U) =
      rAt P parents refineTo hx hy e U ≫
        (tAt P parents refineTo hx hy U ≫ JTTargetCommaPullback.fst W x y (Q hx hy) (L' P parents refineTo hx hy U)) := by
  have hp : pAt P parents refineTo hx hy e U ≫ JTTargetCommaPullback.fst W x y (Q hx hy)
      (L P parents refineTo hx hy e U) = _ :=
    JTEndpointGraphCoefficientEvaluation.lifts_decorated (parents e) hx hy (V P parents refineTo hx hy e U)
  have ht : tAt P parents refineTo hx hy U ≫ JTTargetCommaPullback.fst W x y (Q hx hy)
      (L' P parents refineTo hx hy U) = _ := lifts_decorated P parents refineTo hx hy U
  have hr := timeInclusion_app P parents refineTo hx hy e U
  change rAt P parents refineTo hx hy e U = _ at hr
  rw [hp, ht, underDiagram_toBridgeLabel, hr]
  exact (JTEndpointGraphOverlapCylinder.join_side P parents refineTo e
    ((F P parents refineTo hx hy).obj U)).symm

set_option maxHeartbeats 350000 in
private theorem nativeSquare (U : I P parents refineTo hx hy) :
    pAt P parents refineTo hx hy e U ≫ JTTargetCommaPullback.snd W x y (Q hx hy)
      (L P parents refineTo hx hy e U) =
    rAt P parents refineTo hx hy e U ≫
      (tAt P parents refineTo hx hy U ≫ JTTargetCommaPullback.snd W x y (Q hx hy) (L' P parents refineTo hx hy U)) := by
  have hp : pAt P parents refineTo hx hy e U ≫ JTTargetCommaPullback.snd W x y (Q hx hy)
      (L P parents refineTo hx hy e U) = _ :=
    JTEndpointGraphCoefficientEvaluation.lifts_native (parents e) hx hy (V P parents refineTo hx hy e U)
  have ht : tAt P parents refineTo hx hy U ≫ JTTargetCommaPullback.snd W x y (Q hx hy)
      (L' P parents refineTo hx hy U) = _ := lifts_native P parents refineTo hx hy U
  have hr := timeInclusion_app P parents refineTo hx hy e U
  change rAt P parents refineTo hx hy e U = _ at hr
  rw [hp, ht, hr, ← Category.assoc]
  have h := toNativeTarget_natural (dim P parents refineTo hx hy U)
    ((timeToJoined P parents refineTo e).app ((F P parents refineTo hx hy).obj U))
  exact (congrArg (fun k ↦ k ≫ necklaceUnder.map (toFixedBead P parents refineTo hx hy U)) h).symm

set_option maxHeartbeats 450000 in
/-- The original side lift and joined lift preserve both exact legs over the fixed target. -/
theorem comparisonSquare (U : I P parents refineTo hx hy) :
    pAt P parents refineTo hx hy e U ≫ (E hx hy).map (aAt P parents refineTo hx hy e U) =
    rAt P parents refineTo hx hy e U ≫ tAt P parents refineTo hx hy U :=
  comparePullback hx hy
    (S := (sideCylinders P parents refineTo hx hy e).obj U)
    (T := (sourceCylinders P parents refineTo hx hy).obj U)
    (L := L P parents refineTo hx hy e U) (L' := L' P parents refineTo hx hy U)
    (aAt P parents refineTo hx hy e U)
    (pAt P parents refineTo hx hy e U) (tAt P parents refineTo hx hy U) (rAt P parents refineTo hx hy e U)
    (decoratedSquare P parents refineTo hx hy e U) (nativeSquare P parents refineTo hx hy e U)

/-- The comparison retains every side necklace and uses its actual time inclusion. -/
def toJoined : BoundaryNecklaceComma.Presentation (sideCylinders P parents refineTo hx hy e) ⥤
    JTEndpointGraphOverlapEvaluation.Resolution P parents refineTo hx hy :=
  Grothendieck.map (Functor.whiskerRight (timeInclusion P parents refineTo hx hy e) diagram)

/-- Including a time copy preserves the weak type of the entire necklace presentation. -/
theorem toJoined_weak : WeakEquivalence (nerveMap (toJoined P parents refineTo hx hy e)) := by
  let F₀ := sideCylinders P parents refineTo hx hy e
  let F₁ := sourceCylinders P parents refineTo hx hy
  let w := toJoined P parents refineTo hx hy e
  let p₀ := Grothendieck.forget (fiberDiagram F₀)
  let p₁ := Grothendieck.forget (fiberDiagram F₁)
  haveI : WeakEquivalence (nerveMap p₀) :=
    GrothendieckContractibleFibers.projection_weak _ (fun U ↦
      JTHomotopyTargetComma.fiber_point_GW_at
        ((JTEndpointGraphOverlapCylinder.nativeCodes P parents refineTo).obj
          ((F P parents refineTo hx hy).obj U))
        (timeAt P parents refineTo ((F P parents refineTo hx hy).obj U)))
  haveI : WeakEquivalence (nerveMap p₁) :=
    JTEndpointGraphOverlapEvaluation.projection_weak P parents refineTo hx hy
  have he : nerveMap w ≫ nerveMap p₁ = nerveMap p₀ :=
    (nerveFunctor.map_comp w.toCatHom p₁.toCatHom).symm.trans
      (congrArg nerveMap (Grothendieck.functor_comp_forget
        (α := Functor.whiskerRight (timeInclusion P parents refineTo hx hy e) diagram)))
  exact weakEquivalence_of_postcomp_of_fac he

end
end DaggerModels.PartII.JTEndpointGraphOverlapComparison
