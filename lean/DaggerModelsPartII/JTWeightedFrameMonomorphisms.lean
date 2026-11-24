import DaggerModelsPartII.JTWeightedFrameLocalCobase
import TopCatModelCategory.SSet.Skeleton
import CoproductCellSerialization

/-!
# Universal ordinary local cobase property for weighted JT monos

The actual weighted Gamma and Xi frame functors send every simplicial-set
monomorphism, after dagger forgetting, to the existing universal ordinary
local-cobase class. The proof uses the native relative boundary-cell
presentation of a mono, functorial preservation of its pushouts and
transfinite colimits, and serialization of arbitrary coproduct batches.
No ordinary model-category instance or Lambda weak comparison is used.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MorphismProperty Simplicial DaggerModels

namespace DaggerModels.PartII.JTWeightedFrameMonomorphisms

noncomputable section

open JTWeightedBoundaryLatching JTWeightedFrameLocalCobase
open OrdinaryUniversalLocalCobase

private local instance : HasColimits SSet.{0} := inferInstance
private local instance : HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : PreservesColimitsOfSize.{0, 0}
    DaggerSimplicialCat.forget.{0, 0} :=
  DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize

/-- The pullback of the already completed ordinary universal class along a
colimit-preserving coefficient functor. -/
private def preU (G : SSet.{0} ⥤ SimplicialCat.{0, 0}) :
    MorphismProperty SSet.{0} := U.inverseImage G

private instance preU_cobase (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    (preU G).IsStableUnderCobaseChange where
  of_isPushout := by
    intro A A' B B' f g f' g' sq hf
    exact U.of_isPushout (sq.map G) hf

private instance preU_transfinite (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G] :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0} (preU G) where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    letI : PreservesWellOrderContinuousOfShape J G :=
      ⟨fun _ _ => inferInstance⟩
    refine ⟨?_⟩
    intro X Y f hf
    exact U.transfiniteCompositionsOfShape_le J (G.map f)
      ⟨hf.some.map⟩

/-- Every standard boundary generator maps into the pullback class when
all literal boundary inclusions map into `U`. -/
private theorem boundaries_le_preU (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    (hboundary : ∀ n : ℕ, U (G.map (SSet.boundary.{0} n).ι)) :
    SSet.modelCategoryQuillen.I.{0} ≤ preU G := by
  rintro _ _ _ ⟨n⟩
  exact hboundary n

/-- The native skeletal boundary-cell decomposition and the existing
ordinary closure theorems give all simplicial monomorphisms, without a
retract-closure premise on `U`. -/
theorem mono_map_in_U (G : SSet.{0} ⥤ SimplicialCat.{0, 0})
    [PreservesColimitsOfSize.{0, 0} G]
    (hboundary : ∀ n : ℕ, U (G.map (SSet.boundary.{0} n).ι))
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] : U (G.map i) := by
  let P := preU G
  have hI : SSet.modelCategoryQuillen.I.{0} ≤ P :=
    boundaries_le_preU G hboundary
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

/-- The actual dagger-forgotten Yoneda-weighted realization of a frame. -/
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

/-- Every mono maps into `U` under the literal weighted Gamma frame,
after applying the original dagger-forgetful functor. -/
theorem gamma_weighted_mono_in_U (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    U (DaggerSimplicialCat.forget.map
      ((weighted (JTRelativeReedyFrame.GammaOuter.obj m)).map i)) := by
  apply mono_map_in_U (forgottenWeighted
    (JTRelativeReedyFrame.GammaOuter.obj m))
  intro n
  exact gamma_weighted_boundary_in_U m n

/-- Every mono maps into `U` under the literal weighted Xi frame,
at each original reversal index and after dagger forgetting. -/
theorem xi_weighted_mono_in_U (m : ReverseSimplex)
    {K L : SSet.{0}} (i : K ⟶ L) [Mono i] :
    U (DaggerSimplicialCat.forget.map
      ((weighted (CategoryTheory.Prod.sectR m SimplexCategory ⋙
        RigidifiedJTFrames.Xi)).map i)) := by
  apply mono_map_in_U (forgottenWeighted
    (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi))
  intro n
  exact xi_weighted_boundary_in_U m n

end

end DaggerModels.PartII.JTWeightedFrameMonomorphisms
