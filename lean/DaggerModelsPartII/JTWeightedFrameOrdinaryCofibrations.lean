import DaggerModelsPartII.JTWeightedFrameMonomorphisms
import DaggerModelsPartII.JTProjectiveGeneratorLocalCobase
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# Ordinary cofibrations of the actual weighted JT frames

The retained ordinary latching cofibrations identify the weighted boundary
maps as original ordinary cofibrations. The native boundary-cell presentation
of a simplicial monomorphism and closure of the original LLP class extend
this to all weighted monomorphisms. The canonical all-weight isomorphisms
then transport the result to the actual free outer coefficient arrows.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty Simplicial DaggerModels

namespace DaggerModels.PartII.JTWeightedFrameOrdinaryCofibrations

noncomputable section

open JTWeightedBoundaryLatching JTWeightedFrameLocalCobase
open JTProjectiveGeneratorRealization JTProjectiveGeneratorLocalCobase
open DaggerOrdinaryRigidificationCof

private local instance : HasColimits SSet.{0} := inferInstance
private local instance : HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : PreservesColimitsOfSize.{0, 0}
    DaggerSimplicialCat.forget.{0, 0} :=
  DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
private local instance : ordinaryCofibrations.{0}.RespectsIso := by
  dsimp [ordinaryCofibrations]
  infer_instance
private local instance : ordinaryCofibrations.{0}.IsStableUnderCobaseChange := by
  dsimp [ordinaryCofibrations]
  infer_instance
private local instance :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0}
      ordinaryCofibrations.{0} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    dsimp [ordinaryCofibrations]
    infer_instance

private def preCof (G : SSet.{0} ⥤ SimplicialCat.{0, 0}) :
    MorphismProperty SSet.{0} := ordinaryCofibrations.inverseImage G

private instance preCof_cobase (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    (preCof G).IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    exact ordinaryCofibrations.of_isPushout (sq.map G) hf

private instance preCof_transfinite (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0} (preCof G) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    letI : PreservesWellOrderContinuousOfShape J G :=
      ⟨fun _ _ => inferInstance⟩
    refine ⟨?_⟩
    intro X Y f hf
    exact ordinaryCofibrations.transfiniteCompositionsOfShape_le J (G.map f)
      ⟨hf.some.map⟩

private theorem boundaries_le_preCof (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    (hboundary : ∀ n : ℕ,
      ordinaryCofibrations (G.map (SSet.boundary.{0} n).ι)) :
    SSet.modelCategoryQuillen.I.{0} ≤ preCof G := by
  rintro _ _ _ ⟨n⟩
  exact hboundary n

theorem mono_map_in_ordinaryCofibrations
    (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G]
    (hboundary : ∀ n : ℕ,
      ordinaryCofibrations (G.map (SSet.boundary.{0} n).ι))
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    ordinaryCofibrations (G.map i) := by
  let P := preCof G
  have hI : SSet.modelCategoryQuillen.I.{0} ≤ P :=
    boundaries_le_preCof G hboundary
  have hsingle : P.pushouts ≤ P := P.pushouts_le
  have hbatchP : (coproducts.{0} P).pushouts ≤ P :=
    (DaggerCoproductCellSerialization.coproduct_pushouts_le P).trans
      ((MorphismProperty.transfiniteCompositions_monotone hsingle).trans
        P.transfiniteCompositions_le)
  have hbatchI : (coproducts.{0} SSet.modelCategoryQuillen.I.{0}).pushouts ≤ P :=
    (MorphismProperty.pushouts_monotone
      (MorphismProperty.coproducts_monotone hI)).trans hbatchP
  have hcells : transfiniteCompositions.{0}
      (coproducts.{0} SSet.modelCategoryQuillen.I.{0}).pushouts ≤ P :=
    (MorphismProperty.transfiniteCompositions_monotone hbatchI).trans
      P.transfiniteCompositions_le
  have hmono : (monomorphisms SSet.{0}) i := by
    simp only [monomorphisms.iff]
    infer_instance
  rw [← SSet.modelCategoryQuillen.transfiniteCompositions_pushouts_coproducts]
    at hmono
  exact hcells i hmono

private def forgottenWeighted
    (F : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0}) :
    SSet.{0} ⥤ SimplicialCat.{0, 0} :=
  weighted F ⋙ DaggerSimplicialCat.forget

private local instance (F : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0}) :
    PreservesColimitsOfSize.{0, 0} (forgottenWeighted F) := by
  letI : PreservesColimitsOfSize.{0, 0} (weighted F) :=
    Presheaf.preservesColimitsOfSize_leftKanExtension F
  dsimp [forgottenWeighted]
  infer_instance

theorem gamma_weighted_boundary_cofibration (m : ReverseSimplex) (n : ℕ) :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      ((weighted (JTRelativeReedyFrame.GammaOuter.obj m)).map
        (SSet.boundary.{0} n).ι)) := by
  exact (ordinaryCofibrations.arrow_mk_iso_iff
    (forgottenWeightedBoundaryIso
      (JTRelativeReedyFrame.GammaOuter.obj m) n)).2
    (JTForgottenFrameCofibrancy.forgotten_Gamma_ordinary_matching_cofibration m n)

theorem xi_weighted_boundary_cofibration (m : ReverseSimplex) (n : ℕ) :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      ((weighted (CategoryTheory.Prod.sectR m SimplexCategory ⋙
        RigidifiedJTFrames.Xi)).map (SSet.boundary.{0} n).ι)) := by
  exact (ordinaryCofibrations.arrow_mk_iso_iff
    (forgottenWeightedBoundaryIso
      (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi) n)).2
    (JTXiOrdinaryLatching.actualOrdinaryXi_matching_cofibration m n)

theorem gamma_weighted_mono_cofibration (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      ((weighted (JTRelativeReedyFrame.GammaOuter.obj m)).map i)) := by
  exact mono_map_in_ordinaryCofibrations
    (forgottenWeighted (JTRelativeReedyFrame.GammaOuter.obj m))
    (gamma_weighted_boundary_cofibration m) i

theorem xi_weighted_mono_cofibration (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      ((weighted (CategoryTheory.Prod.sectR m SimplexCategory ⋙
        RigidifiedJTFrames.Xi)).map i)) := by
  exact mono_map_in_ordinaryCofibrations
    (forgottenWeighted
      (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi))
    (xi_weighted_boundary_cofibration m) i

theorem gamma_free_mono_cofibration (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      (JTFrameAdjunction.frameRealization.map ((outerFree m).map i))) := by
  apply (ordinaryCofibrations.arrow_mk_iso_iff
    (gammaFreeArrowIso m i)).2
  exact gamma_weighted_mono_cofibration m i

theorem xi_free_mono_cofibration (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    ordinaryCofibrations (DaggerSimplicialCat.forget.map
      (OrdinaryRigidification.DaggerRigidification.daggerRigidification.map
        (DaggerJTRealization.daggerRealization.map ((outerFree m).map i)))) := by
  apply (ordinaryCofibrations.arrow_mk_iso_iff
    (xiFreeArrowIso m i)).2
  change ordinaryCofibrations (DaggerSimplicialCat.forget.map
    ((weighted
      (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi)).map i))
  exact xi_weighted_mono_cofibration m i

end

end DaggerModels.PartII.JTWeightedFrameOrdinaryCofibrations
