import DaggerModelsPartII.InjectiveSimplicialAxiom

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

/-- Diagram mapping spaces, functorial contravariantly in the source. -/
def diagramMappingSource :
    (C ⥤ SSet.{u})ᵒᵖ ⥤ (C ⥤ SSet.{u}) ⥤ SSet.{u} where
  obj A := diagramMappingTarget A.unop
  map {A B} i := {
    app W := diagramMappingPrecomp i.unop W
    naturality W V f := by
      ext n η
      rfl }
  map_id A := by
    apply NatTrans.ext
    funext W
    simp
  map_comp i j := by
    apply NatTrans.ext
    funext W
    simp

def diagramParametrizedAdjunction :
    curriedDiagramTensor C ⊣₂ diagramMappingSource C :=
  ParametrizedAdjunction.mk'
    (fun A => diagramTensorMappingAdjunction A)
    (by
      intro A B i K W q
      rfl)

private def mappingTerminal (A : C ⥤ SSet.{u}) :
    IsTerminal (diagramMappingSpace A (⊤_ (C ⥤ SSet.{u}))) := by
  letI : PreservesLimitsOfSize.{0, 0} (diagramMappingTarget A) :=
    (diagramTensorMappingAdjunction A).rightAdjoint_preservesLimits
  exact terminalIsTerminal.isTerminalObj (diagramMappingTarget A)

def mappingTerminalPullback {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    (W : C ⥤ SSet.{u}) :
    (diagramMappingSource C).PullbackObjObj i (terminal.from W) where
  pt := diagramMappingSpace A W
  fst := 𝟙 _
  snd := (mappingTerminal C B).from _
  isPullback := by
    haveI : Mono (diagramMappingPrecomp i (⊤_ (C ⥤ SSet.{u}))) := by
      constructor
      intro Z f g h
      exact (mappingTerminal C B).hom_ext f g
    haveI : Mono (((diagramMappingSource C).map i.op).app
        (⊤_ (C ⥤ SSet.{u}))) := by
      change Mono (diagramMappingPrecomp i (⊤_ (C ⥤ SSet.{u})))
      infer_instance
    apply IsPullback.of_horiz_isIso_mono
    constructor
    exact (mappingTerminal C A).hom_ext _ _

theorem mappingTerminalPullback_π {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    (W : C ⥤ SSet.{u}) :
    (mappingTerminalPullback C i W).π = diagramMappingPrecomp i W := by
  have h := (mappingTerminalPullback C i W).π_fst
  simpa [mappingTerminalPullback] using h

theorem diagramPushoutProduct_hasLiftingProperty_terminal_iff
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L) (W : C ⥤ SSet.{u})
    (sq : Functor.PushoutObjObj (curriedDiagramTensor C) i j) :
    HasLiftingProperty sq.ι (terminal.from W) ↔
      HasLiftingProperty j (diagramMappingPrecomp i W) := by
  simpa only [mappingTerminalPullback_π] using
    (diagramParametrizedAdjunction C).hasLiftingProperty_iff sq
      (mappingTerminalPullback C i W)

local instance : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

theorem diagramMappingPrecomp_isFibration
    {A B : C ⥤ SSet.{u}} (i : A ⟶ B) [Mono i]
    (W : C ⥤ SSet.{u}) [IsFibrant W] :
    Fibration (diagramMappingPrecomp i W) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro K L j hj
  simp only [SSet.modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  let sq := diagramPushoutProduct C i (SSet.horn (n + 1) k).ι
  have hcof : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i := by
    rw [model_cofibrations C]
    exact monomorphisms.infer_property i
  have htriv : HomotopicalAlgebra.trivialCofibrations SSet.{u}
      (SSet.horn (n + 1) k).ι :=
    (DaggerOrdinaryAnodyneTensor.anodyne_iff_trivialCofibration _).mp
      (SSet.anodyneExtensions.horn_ι_mem n k)
  have hsq := model_pushoutProduct_trivial_right C i
    (SSet.horn (n + 1) k).ι hcof htriv sq
  haveI : Cofibration sq.ι := (cofibration_iff _).mpr hsq.1
  haveI : WeakEquivalence sq.ι := (weakEquivalence_iff _).mpr hsq.2
  haveI : Fibration (terminal.from W) :=
    (isFibrant_iff _).mp inferInstance
  exact (diagramPushoutProduct_hasLiftingProperty_terminal_iff C i
    (SSet.horn (n + 1) k).ι W sq).mp (inferInstance)

end
end DaggerModels.PartII.InjectiveKanDiagram
