import DaggerModelsPartII.ClassifyingTheorem
import DaggerModelsPartII.AdjunctionUnitCorners
import DaggerModelsPartII.RepresentableTensorAdjunction
import DaggerModelsPartII.SegalLocalizationModels

/-!
# The actual unit corner on projective boundary generators

The representable unit is a local trivial cofibration. Its relative corner
with a free projective boundary generator is the corresponding simplicial
pushout-product.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen
open DaggerModels
open DaggerModels.PartII.DaggerSimplexPartIIndex

namespace DaggerModels.PartII.ActualUnitCornerGenerators

open SegalLocalizers ActualIndexProjectiveModel AdjunctionUnitCorners
open ProjectiveKanDiagram InjectiveKanDiagram

noncomputable section

private local instance : ModelCategory ReverseDaggerSpace.{0} := injectiveSegalModel

private def tensorTargetIso (V : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    (actualRestriction.{0}).obj
      ((actualLeftExtension.{0}).obj
        ((simplicialPresheafProductRight.{0, 0} ReverseSimplex K).obj V)) ≅
      (simplicialPresheafProductRight.{0, 0} ReverseSimplex K).obj
        ((actualRestriction.{0}).obj ((actualLeftExtension.{0}).obj V)) :=
  (actualRestriction.{0}).mapIso
    ((extendIndexLeft_productRight.{0, 0} actualU K).app V)

private theorem unit_tensor (V : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    (actualLeftAdjunction.{0}).unit.app
        ((simplicialPresheafProductRight.{0, 0} ReverseSimplex K).obj V) ≫
      (tensorTargetIso V K).hom =
        (simplicialPresheafProductRight.{0, 0} ReverseSimplex K).map
          ((actualLeftAdjunction.{0}).unit.app V) :=
  extendIndexLeft_unit_productRight.{0, 0} actualU V K

private theorem tensorTargetIso_naturality (V : ReverseDaggerSpace.{0})
    {K M : SSet.{0}} (j : K ⟶ M) :
    (actualLeftExtension.{0} ⋙ actualRestriction.{0}).map
        ((diagramTensor V).map j) ≫ (tensorTargetIso V M).hom =
      (tensorTargetIso V K).hom ≫
        (diagramTensor
          ((actualLeftExtension.{0} ⋙ actualRestriction.{0}).obj V)).map j := by
  let eK := (extendIndexLeft_productRight.{0, 0} actualU K).hom.app V
  let eM := (extendIndexLeft_productRight.{0, 0} actualU M).hom.app V
  have hD : (actualLeftExtension.{0}).map ((diagramTensor V).map j) ≫ eM =
      eK ≫ (diagramTensor ((actualLeftExtension.{0}).obj V)).map j := by
    apply ((actualLeftAdjunction.{0}).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    have hnat := (actualLeftAdjunction.{0}).unit.naturality
      ((diagramTensor V).map j)
    have hM := unit_tensor V M
    have hK := unit_tensor V K
    change (actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj M) ≫
      (actualRestriction.{0}).map eM =
        (simplicialPresheafProductRight.{0, 0} ReverseSimplex M).map
          ((actualLeftAdjunction.{0}).unit.app V) at hM
    change (actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj K) ≫
      (actualRestriction.{0}).map eK =
        (simplicialPresheafProductRight.{0, 0} ReverseSimplex K).map
          ((actualLeftAdjunction.{0}).unit.app V) at hK
    have htensor := ((InjectiveKanDiagram.curriedDiagramTensor
      ReverseSimplexᵒᵖ).map ((actualLeftAdjunction.{0}).unit.app V)).naturality j
    change ((diagramTensor V).map j) ≫
        (simplicialPresheafProductRight.{0, 0} ReverseSimplex M).map
          ((actualLeftAdjunction.{0}).unit.app V) =
        (simplicialPresheafProductRight.{0, 0} ReverseSimplex K).map
          ((actualLeftAdjunction.{0}).unit.app V) ≫
        (actualRestriction.{0}).map
          ((diagramTensor ((actualLeftExtension.{0}).obj V)).map j) at htensor
    calc
      (actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj K) ≫
          (actualRestriction.{0}).map
            ((actualLeftExtension.{0}).map ((diagramTensor V).map j)) ≫
          (actualRestriction.{0}).map eM =
        ((diagramTensor V).map j) ≫
          (actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj M) ≫
          (actualRestriction.{0}).map eM := by
            simpa only [Functor.id_map, Category.assoc] using
              congrArg (fun h => h ≫ (actualRestriction.{0}).map eM) hnat.symm
      _ = ((diagramTensor V).map j) ≫
          (simplicialPresheafProductRight.{0, 0} ReverseSimplex M).map
            ((actualLeftAdjunction.{0}).unit.app V) := by
              exact congrArg (fun h => ((diagramTensor V).map j) ≫ h) hM
      _ = (simplicialPresheafProductRight.{0, 0} ReverseSimplex K).map
            ((actualLeftAdjunction.{0}).unit.app V) ≫
          (actualRestriction.{0}).map
            ((diagramTensor ((actualLeftExtension.{0}).obj V)).map j) := htensor
      _ = (actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj K) ≫
          (actualRestriction.{0}).map eK ≫
          (actualRestriction.{0}).map
            ((diagramTensor ((actualLeftExtension.{0}).obj V)).map j) := by
              simpa only [Category.assoc] using
                (congrArg (fun h => h ≫ (actualRestriction.{0}).map
                  ((diagramTensor ((actualLeftExtension.{0}).obj V)).map j)) hK).symm
  exact congrArg (actualRestriction.{0}).map hD

private def tensorCornerArrowIso (V : ReverseDaggerSpace.{0})
    {K M : SSet.{0}} (j : K ⟶ M) :
    Arrow.mk ((unitPushoutCorner (actualLeftAdjunction.{0})
      ((diagramTensor V).map j)).ι) ≅
      Arrow.mk ((diagramPushoutProduct ReverseSimplexᵒᵖ
        ((actualLeftAdjunction.{0}).unit.app V) j).ι) := by
  let u := unitPushoutCorner (actualLeftAdjunction.{0}) ((diagramTensor V).map j)
  let b := diagramPushoutProduct ReverseSimplexᵒᵖ
    ((actualLeftAdjunction.{0}).unit.app V) j
  have hb : IsPushout
      ((actualLeftAdjunction.{0}).unit.app ((diagramTensor V).obj K))
      ((diagramTensor V).map j)
      ((tensorTargetIso V K).hom ≫ b.inl) b.inr := by
    apply b.isPushout.of_iso'
      (Iso.refl _) (tensorTargetIso V K) (Iso.refl _) (Iso.refl _)
    · simpa only [Iso.refl_hom, Category.id_comp] using (unit_tensor V K).symm
    · change ((diagramTensor V).map j) ≫ 𝟙 _ =
        ((diagramTensor V).map j) ≫ 𝟙 _
      rfl
    · simp
    · simp
  let hU := unitPushoutCorner_isPushout (actualLeftAdjunction.{0})
    ((diagramTensor V).map j)
  refine Arrow.isoMk (hU.isoIsPushout _ _ hb) (tensorTargetIso V M) ?_
  apply hU.hom_ext
  · simp only [← Category.assoc]
    dsimp only [Arrow.mk_hom]
    rw [hU.inl_isoIsPushout_hom _ _ hb, u.inl_ι]
    rw [Category.assoc, b.inl_ι]
    exact (tensorTargetIso_naturality V j).symm
  · simp only [← Category.assoc]
    dsimp only [Arrow.mk_hom]
    rw [hU.inr_isoIsPushout_hom _ _ hb, u.inr_ι]
    rw [b.inr_ι]
    exact (unit_tensor V M).symm

private theorem tensorCorner_trivial (V : ReverseDaggerSpace.{0})
    (hunit : injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((actualLeftAdjunction.{0}).unit.app V) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((actualLeftAdjunction.{0}).unit.app V))
    {K M : SSet.{0}} (j : K ⟶ M)
    (hj : HomotopicalAlgebra.cofibrations SSet.{0} j) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((unitPushoutCorner (actualLeftAdjunction.{0})
          ((diagramTensor V).map j)).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((unitPushoutCorner (actualLeftAdjunction.{0})
          ((diagramTensor V).map j)).ι) := by
  let b := diagramPushoutProduct ReverseSimplexᵒᵖ
    ((actualLeftAdjunction.{0}).unit.app V) j
  have hb := injectiveSegalModel_pushoutProduct_sm7
    ((actualLeftAdjunction.{0}).unit.app V) j hunit.1 hj b
  have he := tensorCornerArrowIso V j
  change cofibrations ReverseDaggerSpace.{0} _ ∧
    weakEquivalences ReverseDaggerSpace.{0} _
  exact ⟨((cofibrations ReverseDaggerSpace.{0}).arrow_mk_iso_iff
      he).mpr hb.1,
    ((weakEquivalences ReverseDaggerSpace.{0}).arrow_mk_iso_iff
      he).mpr (hb.2 (Or.inl hunit.2))⟩

private def representableBoundaryArrowIso (m n : ℕ) :
    Arrow.mk ((representableTensor (ReverseSimplex.mk m)).map
      (SSet.boundary n).ι) ≅
      Arrow.mk ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
        (op (ReverseSimplex.mk m))).map (SSet.boundary n).ι) :=
  Arrow.isoMk
    ((representableTensorIsoFree (ReverseSimplex.mk m)).app
      (SSet.boundary n).toSSet)
    ((representableTensorIsoFree (ReverseSimplex.mk m)).app (Δ[n] : SSet.{0}))
    (representableTensorIsoFree_boundary (ReverseSimplex.mk m) n).symm

/-- The actual adjunction-unit corner on every literal projective boundary
generator is a local trivial cofibration in the injective Segal model. -/
theorem boundaryGenerator_unitCorner_trivial (m n : ℕ) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((unitPushoutCorner (actualLeftAdjunction.{0})
          ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
            (op (ReverseSimplex.mk m))).map (SSet.boundary n).ι)).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((unitPushoutCorner (actualLeftAdjunction.{0})
          ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
            (op (ReverseSimplex.mk m))).map (SSet.boundary n).ι)).ι) := by
  let V := (simplicialYoneda.{0, 0} ReverseSimplex).obj (ReverseSimplex.mk m)
  let j := (SSet.boundary n).ι
  haveI : Mono j := inferInstance
  have hj : HomotopicalAlgebra.cofibrations SSet.{0} j := by
    exact (HomotopicalAlgebra.cofibration_iff j).mp
      (SSet.modelCategoryQuillen.cofibration_of_mono j)
  have hrep := tensorCorner_trivial V
    (ClassifyingTheorem.actualRepresentableUnit_trivial m) j hj
  let fre := (ProjectiveKanDiagram.free ReverseSimplexᵒᵖ
    (op (ReverseSimplex.mk m))).map j
  let rep := (representableTensor (ReverseSimplex.mk m)).map j
  change trivialCofibrations ReverseDaggerSpace.{0}
    ((unitPushoutCorner (actualLeftAdjunction.{0}) fre).ι)
  rw [← fibrations_llp]
  intro A B p hp
  have hrep' : trivialCofibrations ReverseDaggerSpace.{0}
      ((unitPushoutCorner (actualLeftAdjunction.{0}) rep).ι) := hrep
  rw [← fibrations_llp] at hrep'
  have hleft : HasLiftingProperty rep
      (matePullbackCorner (actualLeftAdjunction.{0})
        (actualRightAdjunction.{0}) p).π :=
    (unitPushoutCorner_hasLiftingProperty_iff
      (actualLeftAdjunction.{0}) (actualRightAdjunction.{0}) rep p).mp
      (hrep' p hp)
  have hright : HasLiftingProperty fre
      (matePullbackCorner (actualLeftAdjunction.{0})
        (actualRightAdjunction.{0}) p).π :=
    (HasLiftingProperty.iff_of_arrow_iso_left
      (representableBoundaryArrowIso m n)
      (matePullbackCorner (actualLeftAdjunction.{0})
        (actualRightAdjunction.{0}) p).π).mp hleft
  exact (unitPushoutCorner_hasLiftingProperty_iff
    (actualLeftAdjunction.{0}) (actualRightAdjunction.{0}) fre p).mpr hright

/-- Uniform generator form for the actual projective boundary family. -/
theorem boundaryGenerators_unitCorner_trivial {X Y : ReverseDaggerSpace.{0}}
    {f : X ⟶ Y}
    (hf : ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ f) :
    injectiveSegalModel.categoryWithCofibrations.cofibrations
        ((unitPushoutCorner (actualLeftAdjunction.{0}) f).ι) ∧
      injectiveSegalModel.categoryWithWeakEquivalences.weakEquivalences
        ((unitPushoutCorner (actualLeftAdjunction.{0}) f).ι) := by
  obtain ⟨⟨c, n⟩⟩ := hf
  induction c using Opposite.rec with | op c =>
    cases c with
    | mk m => exact boundaryGenerator_unitCorner_trivial m n

end

end DaggerModels.PartII.ActualUnitCornerGenerators
