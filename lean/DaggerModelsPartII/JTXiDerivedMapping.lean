import DaggerModelsPartII.JTXiRelativeReedyFrame
import DaggerModelsPartII.JTDerivedOrderedMate

/-!
# The actual raw Xi ordered Hom computes the chosen derived mapping object

Relative Reedy cofibrancy of the original endpoint-collapsed Xi frame makes
the literal qX-induced Hom comparison weak. The specified raw mapping
comparison from the retained calibration is therefore invertible. This
computes the Xi side and does not assert the Gamma raw comparison weak.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTXiDerivedMapping

open JTRelativeReedyFrame JTEndpointObjects JTEndpointFrames
open JTXiAugmentation JTEndpointFrameComparison

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory (Under Bdagger) :=
  JTEndpointCobase.underModel Bdagger
private local instance : ModelCategory (Under Bdagger)ᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ (Under Bdagger)ᵒᵖ) :=
  simplicialReedyModelCategory (Under Bdagger)ᵒᵖ

/-- The original qX endpoint-cobase comparison is weak on actual strict
under-boundary Hom simplicial sets into every original fibrant coefficient. -/
theorem QXToXi_precomp_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    weakEquivalences SSet.{0}
      (JTEndpointReplacementSquare.QXToXi_precomp C x y) := by
  letI : IsFibrant XiFrame.op := JTXiRelativeReedyFrame.XiFrame_op_isFibrant
  letI : IsFibrant QXFrame.op := QXFrame_reedyCofibrant
  letI : IsFibrant (JTEndpointHom.targetUnder C x y) :=
    (UnderReedyCriterion.under_isFibrant_iff Bdagger
      (JTEndpointHom.targetUnder C x y)).2 (by
      change IsFibrant C
      infer_instance)
  exact StrictFrameMappingWeak.strictMapping_map_weak
    (JTEndpointHom.targetUnder C x y) (NatTrans.op QXToXi) QXToXi_reedyWeak

/-- The retained actual raw-to-resolved Xi comparison is Kan weak, with
both original ordered endpoints and the specified qX map unchanged. -/
theorem xiRawToResolved_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    WeakEquivalence (JTDerivedOrderedMate.xiRawToResolved C x y) := by
  haveI : WeakEquivalence (JTEndpointReplacementSquare.QXToXi_precomp C x y) :=
    (weakEquivalence_iff _).mpr (QXToXi_precomp_weak C x y)
  change WeakEquivalence
    ((JTEndpointHom.orderedHomSSetIso
      JTActualCosimplicialFrame.XiAugmentationCurried C x y).inv ≫ _)
  infer_instance

/-- The exact raw Xi mapping comparison already used in the original
mate calibration is an isomorphism in the Kan localization. -/
theorem xiRawMappingComparison_isIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    IsIso (JTDerivedOrderedMate.xiRawMappingComparison C x y) := by
  let e := Localization.isoOfHom (weakEquivalences SSet.{0}).Q
    (weakEquivalences SSet.{0}) (JTDerivedOrderedMate.xiRawToResolved C x y)
    ((weakEquivalence_iff _).mp (xiRawToResolved_weak C x y))
  change IsIso (e.hom ≫ (JTDerivedOrderedMate.xiLocalizationIso C x y).hom)
  infer_instance

/-- The actual raw Xi ordered Hom represents the retained chosen derived
mapping object, with the retained raw mapping comparison as its hom. -/
def xiRawMappingIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (JTOrderedFrameMate.XiOrdered C x y) ≅
      JTDerivedOrderedMate.orderedMappingObject C x y := by
  haveI := xiRawMappingComparison_isIso C x y
  exact asIso (JTDerivedOrderedMate.xiRawMappingComparison C x y)

/-- The chosen Xi representation retains the original calibrated map. -/
theorem xiRawMappingIso_hom (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (xiRawMappingIso C x y).hom =
      JTDerivedOrderedMate.xiRawMappingComparison C x y := rfl

end

end DaggerModels.PartII.JTXiDerivedMapping
