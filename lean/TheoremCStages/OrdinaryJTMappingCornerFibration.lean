import OrdinaryJTRelativeMappingFrame
import OrdinaryJTMappingFrameWeak
import DaggerModelsPartII.DiagramHomKanFibration

/-!
# Two-variable ordinary JT mapping corner

The ordinary Joyal fibration of coefficients and the relative Reedy
cofibration of the actual `A × J[•]` frames give a Kan fibration of the
unmodified diagram-Hom pullback corner. The plain-Hom identification with
the literal ordinary JT mapping rows is recorded separately below.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory DaggerModels

namespace DaggerModels.PartII.OrdinaryJTMappingCornerFibration

open OrdinaryJTMappingFrameWeak

noncomputable section

section OriginalCoefficient

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences

private theorem frame_op_maps_weak (A : SSet.{0})
    {s t : SimplexCategoryᵒᵖ} (g : s ⟶ t) :
    weakEquivalences SSet.{0}ᵒᵖ ((frame A).op.map g) := by
  rw [weakEquivalences_op]
  change ordinaryJoyalModel.categoryWithWeakEquivalences.weakEquivalences
    (A ◁ GroupoidSimplex.parameter.map g.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  exact DaggerNativeJoyalMappingTensor.weak_whiskerLeft A
    (GroupoidSimplex.parameter.map g.unop)
    (JTOrdinaryEndpointFibration.parameter_map_weak g.unop)

end OriginalCoefficient

open scoped SSet.modelCategoryQuillen

/-- Postcomposition on the literal ordinary JT mapping row. -/
def mappingPost {X Y : SSet.{0}} (p : X ⟶ Y) (A : SSet.{0}) :
    mapping X A ⟶ mapping Y A :=
  Functor.whiskerLeft (frame A).op (yoneda.map p)

/-- The same row as a diagram Hom in the opposite ordinary category. -/
def rowIso (X A : SSet.{0}) :
    diagramHomSSet (op X) (frame A).op ≅ mapping X A :=
  (StrictFrameMappingWeak.nativeStrictIso X).app (frame A).op

/-- The two-variable corner of literal ordinary JT mapping rows. The first
projection postcomposes with `p`; the second restricts along `u`. -/
def corner {X Y A B : SSet.{0}} (p : X ⟶ Y) (u : A ⟶ B) :
    mapping X B ⟶
      pullback (restriction Y u) (mappingPost p A) :=
  pullback.lift (mappingPost p B) (restriction X u) (by
    apply NatTrans.ext
    funext k f
    rfl)

/-- The actual two-variable corner for a Joyal fibration and horizontal
monomorphism is a Kan fibration, with the target a literal pullback. -/
theorem diagram_corner_fibration {X Y A B : SSet.{0}}
    (p : X ⟶ Y)
    (hp : ordinaryJoyalModel.categoryWithFibrations.fibrations p)
    (u : A ⟶ B) [Mono u] :
    Fibration (diagramHomCorner p.op (NatTrans.op (frameMap u))) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : CategoryWithCofibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    ordinaryJoyalModel.categoryWithWeakEquivalences
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  letI : CategoryWithCofibrations SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
    simplicialReedyModelCategory SSet.{0}ᵒᵖ
  have hpCof : cofibrations SSet.{0}ᵒᵖ p.op := by
    rw [cofibrations_op]
    exact hp
  letI : Cofibration p.op := (cofibration_iff _).mpr hpCof
  letI : IsFibrant (frame A).op := frame_op_isFibrant A
  letI : IsFibrant (frame B).op := frame_op_isFibrant B
  have hrel : reedyMatchingProperty (fibrations SSet.{0}ᵒᵖ)
      (NatTrans.op (frameMap u)) := by
    intro n
    rw [fibrations_op]
    exact OrdinaryJTRelativeMappingFrame.frameMap_relativeCofibration u n
  have hstrict := diagramHomCorner_kan_fibration p.op
    (frame_op_maps_weak B) (frame_op_maps_weak A)
    (NatTrans.op (frameMap u)) hrel
  letI : CategoryWithFibrations SSet.{0} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  exact hstrict

#print axioms diagram_corner_fibration
#print axioms rowIso
#print axioms corner

end

end DaggerModels.PartII.OrdinaryJTMappingCornerFibration
