import DaggerModelsPartII.JTActualLambdaCellGluing
import DaggerModelsPartII.ProjectiveKanDiagram
import DaggerModelsPartII.JTWeightedFrameOrdinaryCofibrations
import CoproductCellSerialization
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Ordinary cofibrations from original projective cofibrations

A colimit-preserving realization that sends the original free boundary
generators to original ordinary cofibrations sends every original projective
cofibration to an ordinary cofibration. This uses the retained small object
argument, literal coproduct-cell serialization, and retract closure.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty DaggerModels
open DaggerOrdinaryRigidificationCof

namespace DaggerModels.PartII.JTProjectiveRealizationCofibrations

noncomputable section

variable {Index : Type} [SmallCategory Index]

private local instance : HasColimits (Index ⥤ SSet.{0}) := inferInstance
private local instance : HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : ordinaryCofibrations.{0}.IsStableUnderCobaseChange := by
  dsimp [ordinaryCofibrations]
  infer_instance
private local instance : ordinaryCofibrations.{0}.IsStableUnderRetracts := by
  dsimp [ordinaryCofibrations]
  infer_instance
private local instance :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0}
      ordinaryCofibrations.{0} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    dsimp [ordinaryCofibrations]
    infer_instance

private def preCof (G : (Index ⥤ SSet.{0}) ⥤ SimplicialCat.{0, 0}) :
    MorphismProperty (Index ⥤ SSet.{0}) := ordinaryCofibrations.inverseImage G

private instance preCof_cobase
    (G : (Index ⥤ SSet.{0}) ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    (preCof G).IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    exact ordinaryCofibrations.of_isPushout (sq.map G) hf

private instance preCof_transfinite
    (G : (Index ⥤ SSet.{0}) ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0} (preCof G) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    letI : PreservesWellOrderContinuousOfShape J G :=
      ⟨fun _ _ => inferInstance⟩
    refine ⟨?_⟩
    intro X Y f hf
    exact ordinaryCofibrations.transfiniteCompositionsOfShape_le J (G.map f)
      ⟨hf.some.map⟩

private instance preCof_retract
    (G : (Index ⥤ SSet.{0}) ⥤ SimplicialCat.{0, 0}) :
    (preCof G).IsStableUnderRetracts := by
  dsimp [preCof]
  infer_instance

/-- Generator images suffice for every original projective cofibration. -/
theorem image_projective_cofibration
    (G : (Index ⥤ SSet.{0}) ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G]
    (hboundary : ∀ m : Index, ∀ n : ℕ,
      ordinaryCofibrations
        (G.map ((ProjectiveKanDiagram.free Index m).map (SSet.boundary.{0} n).ι)))
    {A B : Index ⥤ SSet.{0}} (f : A ⟶ B)
    (hf : (ProjectiveKanDiagram.boundaryGenerators Index).rlp.llp f) :
    ordinaryCofibrations (G.map f) := by
  let I := ProjectiveKanDiagram.boundaryGenerators Index
  let P := preCof G
  have hI : I ≤ P := by
    rintro A B i ⟨⟨m, n⟩⟩
    exact hboundary m n
  have hsingle : P.pushouts ≤ P := P.pushouts_le
  have hbatchP : (coproducts.{0} P).pushouts ≤ P :=
    (DaggerCoproductCellSerialization.coproduct_pushouts_le P).trans
      ((MorphismProperty.transfiniteCompositions_monotone hsingle).trans
        P.transfiniteCompositions_le)
  have hbatchI : (coproducts.{0} I).pushouts ≤ P :=
    (MorphismProperty.pushouts_monotone
      (MorphismProperty.coproducts_monotone hI)).trans hbatchP
  have hcells : transfiniteCompositions.{0} (coproducts.{0} I).pushouts ≤ P :=
    (MorphismProperty.transfiniteCompositions_monotone hbatchI).trans
      P.transfiniteCompositions_le
  letI := ProjectiveKanDiagram.boundaryGenerators_smallObjectArgument Index
  change I.rlp.llp f at hf
  rw [MorphismProperty.llp_rlp_of_hasSmallObjectArgument] at hf
  exact ((MorphismProperty.retracts_le_iff).2 hcells) f hf

/-- The actual forgotten Γ realization maps every original projective
cofibration into the original ordinary cofibration class. -/
theorem gamma_projective_cofibration
    {A B : SegalLocalizers.ReverseDaggerSpace.{0}} (f : A ⟶ B)
    (hf : (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ).rlp.llp f) :
    ordinaryCofibrations (JTActualLambdaCellGluing.sourceRealization.map f) := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  letI : PreservesColimitsOfSize.{0, 0}
      JTActualLambdaCellGluing.sourceRealization := by
    letI : PreservesColimitsOfSize.{0, 0} JTFrameAdjunction.frameRealization :=
      JTFrameAdjunction.adjunction.leftAdjoint_preservesColimits
    infer_instance
  apply image_projective_cofibration JTActualLambdaCellGluing.sourceRealization
    (fun m n ↦ ?_) f hf
  change ordinaryCofibrations
    (DaggerSimplicialCat.forget.map
      (JTFrameAdjunction.frameRealization.map
        ((JTProjectiveGeneratorRealization.outerFree m.unop).map
          (SSet.boundary.{0} n).ι)))
  exact JTWeightedFrameOrdinaryCofibrations.gamma_free_mono_cofibration
    m.unop (SSet.boundary.{0} n).ι

/-- The actual forgotten Ξ realization has the same projective-cofibration
preservation property, without an ordinary model-category instance. -/
theorem xi_projective_cofibration
    {A B : SegalLocalizers.ReverseDaggerSpace.{0}} (f : A ⟶ B)
    (hf : (ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ).rlp.llp f) :
    ordinaryCofibrations (JTActualLambdaCellGluing.targetRealization.map f) := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  letI : PreservesColimitsOfSize.{0, 0}
      JTActualLambdaCellGluing.targetRealization := by
    letI : PreservesColimitsOfSize.{0, 0}
        (DaggerJTRealization.daggerRealization ⋙
          OrdinaryRigidification.DaggerRigidification.daggerRigidification) :=
      JTCoendMate.compositeAdjunction.leftAdjoint_preservesColimits
    infer_instance
  apply image_projective_cofibration JTActualLambdaCellGluing.targetRealization
    (fun m n ↦ ?_) f hf
  change ordinaryCofibrations
    (DaggerSimplicialCat.forget.map
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map
          ((JTProjectiveGeneratorRealization.outerFree m.unop).map
            (SSet.boundary.{0} n).ι))))
  exact JTWeightedFrameOrdinaryCofibrations.xi_free_mono_cofibration
    m.unop (SSet.boundary.{0} n).ι

end

end DaggerModels.PartII.JTProjectiveRealizationCofibrations
