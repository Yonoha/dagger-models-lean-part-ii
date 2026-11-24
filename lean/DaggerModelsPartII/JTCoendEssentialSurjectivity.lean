import DaggerModelsPartII.JTCoendComparison
import DaggerModels.DaggerSimplicialCofree
import DaggerModels.SimplicialObjectAdjunctions
import OriginalActualGlobalWeakPropertiesRecovered
import OriginalUnitaryCoherentAlgebraRecovered
import ActualTaggedWalkingIsoImageDKObstructionReconciled
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# Coherent essential surjectivity of the actual JT coend comparison

Object coverage in the target follows from the pointwise left Kan extension
colimit and preservation of colimits by the object functor. Coherent-unitary
witnesses on represented generators then pass along the colimit legs.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DaggerModels Simplicial
open DaggerUnitarySubgroupoid DaggerUnitaryInvariance

namespace DaggerModels.PartII.JTCoendEssentialSurjectivity

open JTCoendComparison JTRelativeReedyFrame
open JTFrameAdjunction DaggerJTAdjunction RigidifiedJTFrames
open OrdinaryRigidification.DaggerRigidification

noncomputable section

local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

private theorem presheafTarget_preservesColimits :
    PreservesColimits presheafTarget := by
  letI : PreservesColimits DaggerJTAdjunction.presheafRealization :=
    DaggerJTAdjunction.presheafRealization_preservesColimits
  letI : PreservesColimits daggerRigidification.{0} :=
    DaggerActualRigidificationQuillen.adjunction.leftAdjoint_preservesColimits
  dsimp [presheafTarget]
  infer_instance

/-- Every target object comes from one represented frame and one element of
the presheaf. No cofibrancy hypothesis on the presheaf is involved. -/
private theorem target_obj_covered (P : DaggerIndexᵒᵖ ⥤ Type)
    (y : (presheafTarget.obj P).Obj) :
    ∃ (j : CostructuredArrow uliftYoneda.{0} P)
      (b : (Xi.obj j.left).Obj),
      (presheafTarget.map j.hom).obj b = y := by
  let U : DaggerSimplicialCat.{0, 0} ⥤ Type :=
    DaggerSimplicialCat.forget ⋙ SimplicialCat.objects
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  letI : PreservesColimitsOfSize.{0, 0} SimplicialCat.objects.{0, 0} :=
    SimplicialCat.objectsPreservesColimitsOfSize
  letI : PreservesColimitsOfSize.{0, 0} U := inferInstance
  letI : PreservesColimitsOfSize.{0, 0} presheafTarget :=
    presheafTarget_preservesColimits
  letI : presheafTarget.IsLeftKanExtension
      (𝟙 (uliftYoneda.{0} ⋙ presheafTarget)) :=
    Presheaf.isLeftKanExtension_of_preservesColimits
      presheafTarget (Iso.refl _)
  let E := Functor.LeftExtension.mk presheafTarget
    (𝟙 (uliftYoneda.{0} ⋙ presheafTarget))
  have hc : IsColimit (E.coconeAt P) :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      presheafTarget (𝟙 _) P
  have hU : IsColimit (U.mapCocone (E.coconeAt P)) :=
    isColimitOfPreserves U hc
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hU y
  refine ⟨j, b, ?_⟩
  change (𝟙 _ ≫ presheafTarget.map j.hom).obj b = y at hb
  simpa only [Category.id_comp] using hb

/-- The represented component of the actual comparison has coherent-unitary
essential image in the target frame. -/
private theorem parameterComparison_ess (p : DaggerIndex) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective standardReplacement
      (parameterComparison.app p) := by
  rcases p with ⟨m, k⟩
  induction k using SimplexCategory.rec with | h n =>
    rw [parameterComparison_app]
    exact (comparison_component_daggerDK m n).2

/-- The actual presheaf-level comparison is coherently essentially
surjective on objects for every presheaf. -/
theorem presheafComparison_ess (P : DaggerIndexᵒᵖ ⥤ Type) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective standardReplacement
      (presheafComparison.app P) := by
  intro y
  obtain ⟨j, b, hb⟩ := target_obj_covered P y
  obtain ⟨a, v, hv⟩ := parameterComparison_ess j.left b
  let η := uliftYoneda.{0}.leftKanExtensionUnit JTFrameAdjunction.frameParameter
  let sourceLeg : JTFrameAdjunction.frameParameter.obj j.left ⟶
      JTFrameAdjunction.presheafRealization.obj P :=
    η.app j.left ≫ JTFrameAdjunction.presheafRealization.map j.hom
  have hnat : sourceLeg ≫ presheafComparison.app P =
      parameterComparison.app j.left ≫ presheafTarget.map j.hom := by
    dsimp [sourceLeg]
    calc
      η.app j.left ≫ JTFrameAdjunction.presheafRealization.map j.hom ≫
          presheafComparison.app P =
        η.app j.left ≫ presheafComparison.app (uliftYoneda.{0}.obj j.left) ≫
          presheafTarget.map j.hom := by
            exact congrArg (fun f ↦ η.app j.left ≫ f)
              (presheafComparison.naturality j.hom)
      _ = parameterComparison.app j.left ≫ presheafTarget.map j.hom := by
        rw [← Category.assoc, presheafComparison_fac_app_eq]
  have hunitary := coherentlyUnitary_map standardReplacement
    (presheafTarget.map j.hom) _ _ v hv
  have hobj : (presheafComparison.app P).obj (sourceLeg.obj a) =
      (presheafTarget.map j.hom).obj ((parameterComparison.app j.left).obj a) := by
    exact congrArg (fun f ↦ f.obj a) hnat
  refine ⟨sourceLeg.obj a, ?_⟩
  rw [hobj, ← hb]
  exact ⟨_, hunitary⟩

/-- The manuscript's capital coend comparison satisfies the coherent-unitary
object condition for every reversal simplicial space. -/
theorem comparison_ess (W : SegalLocalizers.ReverseDaggerSpace.{0}) :
    DaggerGlobalDK.CoherentlyEssentiallySurjective standardReplacement
      (JTCoendComparison.comparison.app W) := by
  let e : Arrow.mk
      (presheafComparison.app (sourceEquivalence.functor.obj W)) ≅
      Arrow.mk (JTCoendComparison.comparison.app W) :=
    Arrow.isoMk (Iso.refl _) (targetIso.app W) (by
      change presheafComparison.app (sourceEquivalence.functor.obj W) ≫
        (targetIso.app W).hom = 𝟙 _ ≫ JTCoendComparison.comparison.app W
      simp [JTCoendComparison.comparison])
  exact DaggerActualTaggedWalkingIsoImageDKObstruction.coherentlyEssentiallySurjective_of_arrowIso
      standardReplacement e
      (presheafComparison_ess (sourceEquivalence.functor.obj W))

end

end DaggerModels.PartII.JTCoendEssentialSurjectivity
