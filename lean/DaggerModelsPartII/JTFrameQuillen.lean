import DaggerModelsPartII.JTActualCosimplicialFrame
import DaggerModelsPartII.JTFrameAdjunction
import DaggerModelsPartII.DiagramHomPrecompLifting
import DaggerModelsPartII.ProjectiveKanDiagram
import ActualDaggerRigidificationQuillen

/-!
# Right Quillen property of the actual relative JT frame nerve

The projective Kan model tests fibrations and trivial fibrations at each
reversal-simplex index. At an index `m`, the actual right adjoint is the
mapping simplicial set of the constructed cosimplicial frame `Gamma_m`.
No localization or Quillen-equivalence claim is made here.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open DaggerModels DaggerModels.PartII
open SegalLocalizers JTRelativeReedyFrame JTFrameAdjunction
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFrameQuillen

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ

/-- Naturality of the actual frame-nerve evaluation comparison as an
isomorphism of arrows. -/
def frameNerveEvaluationArrowIso (m : ReverseSimplex)
    {X Y : Coefficient} (p : X ⟶ Y) :
    Arrow.mk ((frameNerve.map p).app (op m)) ≅
      Arrow.mk ((mappingNerve m).map p) :=
  Arrow.isoMk ((frameNerveEvaluationIso m).app X)
    ((frameNerveEvaluationIso m).app Y)
      ((frameNerveEvaluationIso m).hom.naturality p)

/-- A coefficient fibration maps to a Kan fibration at each actual frame
index. -/
theorem mappingNerve_map_fibration (m : ReverseSimplex)
    {X Y : Coefficient} (p : X ⟶ Y)
    (hp : fibrations Coefficient p) :
    fibrations SSet.{0} ((mappingNerve m).map p) := by
  letI : IsFibrant (GammaOuter.obj m).op :=
    GammaOuter_op_isFibrant m
  have hcof : cofibrations Coefficientᵒᵖ p.op := by
    rw [cofibrations_op]
    exact hp
  change fibrations SSet.{0}
    (diagramHomPrecomp p.op (GammaOuter.obj m).op)
  exact diagramHomPrecomp_kanFibration _
    (JTActualCosimplicialFrame.GammaOuter_op_map_weak m) p.op hcof

/-- A coefficient trivial fibration maps to a Kan trivial fibration at
each actual frame index. -/
theorem mappingNerve_map_trivialFibration (m : ReverseSimplex)
    {X Y : Coefficient} (p : X ⟶ Y)
    (hp : trivialFibrations Coefficient p) :
    trivialFibrations SSet.{0} ((mappingNerve m).map p) := by
  letI : IsFibrant (GammaOuter.obj m).op :=
    GammaOuter_op_isFibrant m
  have hcof : trivialCofibrations Coefficientᵒᵖ p.op := by
    rw [trivialCofibrations_op]
    exact hp
  change trivialFibrations SSet.{0}
    (diagramHomPrecomp p.op (GammaOuter.obj m).op)
  exact diagramHomPrecomp_kanTrivialFibration _ p.op hcof

/-- The literal right adjoint preserves projective Kan fibrations. -/
theorem frameNerve_preservesFibrations : frameNerve.PreservesFibrations := by
  constructor
  intro X Y p hp
  apply (fibration_iff _).mpr
  change ProjectiveKanDiagram.fibrations ReverseSimplexᵒᵖ (frameNerve.map p)
  intro m
  let e := frameNerveEvaluationArrowIso m.unop p
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff e).mpr
    (mappingNerve_map_fibration m.unop p ((fibration_iff p).mp hp))

/-- The literal right adjoint preserves projective Kan trivial fibrations. -/
theorem frameNerve_preservesTrivialFibrations :
    frameNerve.PreservesTrivialFibrations := by
  constructor
  intro X Y p hp
  change (ProjectiveKanDiagram.fibrations ReverseSimplexᵒᵖ ⊓
    ProjectiveKanDiagram.weakEquivalences ReverseSimplexᵒᵖ) (frameNerve.map p)
  rw [ProjectiveKanDiagram.fibrations_inf_weakEquivalences]
  intro m
  let e := frameNerveEvaluationArrowIso m.unop p
  exact ((trivialFibrations SSet.{0}).arrow_mk_iso_iff e).mpr
    (mappingNerve_map_trivialFibration m.unop p hp)

/-- The actual coend--Hom adjunction is Quillen for the original dagger
Bergner model and the projective Kan diagram model. -/
theorem isQuillenAdjunction : adjunction.IsQuillenAdjunction := by
  letI : frameNerve.PreservesFibrations := frameNerve_preservesFibrations
  letI : frameNerve.PreservesTrivialFibrations :=
    frameNerve_preservesTrivialFibrations
  letI : frameRealization.PreservesCofibrations :=
    adjunction.preservesTrivialFibrations_iff_preservesCofibrations.mp inferInstance
  exact ⟨⟩

end

end DaggerModels.PartII.JTFrameQuillen
