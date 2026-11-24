import DaggerModelsPartII.DiagramMappingTensor
import DaggerModelsPartII.DiagramMappingPushout
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MonoidalClosed MorphismProperty HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

private def mappingBoxIsPullback {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) (W : C ⥤ SSet.{u})
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    IsPullback
      (diagramMappingPrecomp sq.inl W ≫ (diagramMappingTensorIso C B K).hom.app W)
      (diagramMappingPrecomp sq.inr W ≫ (diagramMappingTensorIso C A L).hom.app W)
      ((ihom K).map (diagramMappingPrecomp i W))
      ((MonoidalClosed.pre j).app (diagramMappingSpace A W)) := by
  apply (diagramMappingSpace_isPullback sq.isPushout W).of_iso
    (Iso.refl _) ((diagramMappingTensorIso C B K).app W)
    ((diagramMappingTensorIso C A L).app W)
    ((diagramMappingTensorIso C A K).app W)
  · simp
  · simp
  · exact diagramMappingTensorIso_precomp C i K W
  · exact diagramMappingTensorIso_tensorMap C A j W

private def mappingBoxArrowIso {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) (W : C ⥤ SSet.{u})
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    Arrow.mk (diagramMappingPrecomp sq.ι W) ≅
      Arrow.mk (SSet.ihomToPullback j (diagramMappingPrecomp i W)) :=
  Arrow.isoMk ((diagramMappingTensorIso C B L).app W)
    (mappingBoxIsPullback C i j W sq).isoPullback (by
      let h := mappingBoxIsPullback C i j W sq
      change ((diagramMappingTensorIso C B L).app W).hom ≫
          SSet.ihomToPullback j (diagramMappingPrecomp i W) =
        diagramMappingPrecomp sq.ι W ≫ h.isoPullback.hom
      apply pullback.hom_ext
      · simp only [Category.assoc, SSet.ihomToPullback, pullback.lift_fst,
          h.isoPullback_hom_fst]
        rw [← Category.assoc]
        rw [← diagramMappingPrecomp_comp sq.inl sq.ι W, sq.inl_ι]
        exact (diagramMappingTensorIso_tensorMap C B j W).symm
      · simp only [Category.assoc, SSet.ihomToPullback, pullback.lift_snd,
          h.isoPullback_hom_snd]
        rw [← Category.assoc]
        rw [← diagramMappingPrecomp_comp sq.inr sq.ι W, sq.inr_ι]
        exact (diagramMappingTensorIso_precomp C i L W).symm)

local instance : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- Pushout-products with simplicial monomorphisms preserve strict locality
when the target diagram is injectively fibrant. -/
theorem diagramPushoutProduct_local {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) [Mono i] [Mono j]
    (W : C ⥤ SSet.{u}) [IsFibrant W]
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j)
    (hi : homotopyMappingWeakEquivalences W i) :
    homotopyMappingWeakEquivalences W sq.ι := by
  haveI : Fibration (diagramMappingPrecomp i W) :=
    diagramMappingPrecomp_isFibration C i W
  haveI : WeakEquivalence (diagramMappingPrecomp i W) :=
    (weakEquivalence_iff _).mpr ((model_homotopyMapping_iff_strict C i).mp hi)
  have hcorner : WeakEquivalence (SSet.ihomToPullback j
      (diagramMappingPrecomp i W)) :=
    (DaggerSSetSM7.corner_trivial_of_trivial j (diagramMappingPrecomp i W)).2
  apply (model_homotopyMapping_iff_strict C sq.ι).mpr
  exact ((HomotopicalAlgebra.weakEquivalences SSet.{u}).arrow_mk_iso_iff
    (mappingBoxArrowIso C i j W sq)).mpr ((weakEquivalence_iff _).mp hcorner)

end
end DaggerModels.PartII.InjectiveKanDiagram
