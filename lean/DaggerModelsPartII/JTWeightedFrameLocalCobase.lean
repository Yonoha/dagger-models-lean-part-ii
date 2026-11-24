import DaggerModelsPartII.JTWeightedBoundaryLatching
import DaggerModelsPartII.JTOrdinaryLocalCobase
import DaggerModels.DaggerSimplicialCofree

/-!
# Universal local comparison for the actual weighted JT frame boundaries

The native Yoneda-weighted realizations of the actual Gamma and Xi frames
send every simplex boundary to an ordinary arrow in the completed universal
local-cobase class after forgetting dagger. This follows from the actual
latching arrows and the colimit-preserving dagger forgetful functor.

These are statements about the original weighted frame maps. Identification
with the free outer realization, the Lambda weak comparison, and a full
ordinary model-category structure are separate requirements.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTWeightedFrameLocalCobase

open JTWeightedBoundaryLatching OrdinaryUniversalLocalCobase

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : HasLimits SimplicialCat.{0, 0}ᵒᵖ := inferInstance
private local instance : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
  DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize

/-- Forgetting the actual weighted boundary map gives the native ordinary
latching arrow, up to an arrow isomorphism with its two endpoint maps. -/
def forgottenWeightedBoundaryIso
    (F : SimplexCategory ⥤ DaggerSimplicialCat.{0, 0}) (n : ℕ) :
    Arrow.mk (DaggerSimplicialCat.forget.map
      ((weighted F).map (SSet.boundary.{0} n).ι)) ≅
      Arrow.mk (((matchingComparison n).app (F ⋙ DaggerSimplicialCat.forget).op).unop) := by
  letI : PreservesColimitsOfSize.{0, 0} (weighted F) :=
    Presheaf.preservesColimitsOfSize_leftKanExtension F
  let G := weighted F ⋙ DaggerSimplicialCat.forget
  letI : PreservesColimitsOfSize.{0, 0} G := by dsimp [G]; infer_instance
  let eFrame : SSet.stdSimplex.{0} ⋙ G ≅ F ⋙ DaggerSimplicialCat.forget :=
    (Functor.associator SSet.stdSimplex.{0} (weighted F)
      DaggerSimplicialCat.forget).symm ≪≫
      Functor.isoWhiskerRight (Presheaf.isExtensionAlongULiftYoneda F)
        DaggerSimplicialCat.forget
  exact boundaryLatchingIsoOfRepresentation G _ eFrame n

/-- Every actual Gamma weighted boundary, including degree zero, has the
universal ordinary local-cobase property after forgetting dagger. -/
theorem gamma_weighted_boundary_in_U (m : ReverseSimplex) (n : ℕ) :
    U (DaggerSimplicialCat.forget.map
      ((weighted (JTRelativeReedyFrame.GammaOuter.obj m)).map (SSet.boundary.{0} n).ι)) := by
  exact (U.arrow_mk_iso_iff
    (forgottenWeightedBoundaryIso (JTRelativeReedyFrame.GammaOuter.obj m) n)).2
      (JTOrdinaryLocalCobase.actual_Gamma_matching_in_U m n)

/-- Every literal Xi weighted boundary has the same universal ordinary
property, for all reversal indices and degrees including zero. -/
theorem xi_weighted_boundary_in_U (m : ReverseSimplex) (n : ℕ) :
    U (DaggerSimplicialCat.forget.map
      ((weighted (CategoryTheory.Prod.sectR m SimplexCategory ⋙
        RigidifiedJTFrames.Xi)).map (SSet.boundary.{0} n).ι)) := by
  exact (U.arrow_mk_iso_iff
    (forgottenWeightedBoundaryIso
      (CategoryTheory.Prod.sectR m SimplexCategory ⋙ RigidifiedJTFrames.Xi) n)).2
      (JTOrdinaryLocalCobase.actual_Xi_matching_in_U m n)

end

end DaggerModels.PartII.JTWeightedFrameLocalCobase
