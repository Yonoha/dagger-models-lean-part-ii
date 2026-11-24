import DaggerModelsPartII.JTSpineWeak
import ActualAntiInnerJoyalMappingWeak
import OriginalActualDaggerModelConstruction

/-!
# Actual free dagger inner-horn generators

Each literal free dagger inner-horn inclusion is underlying native inner-left
and an original dagger Joyal trivial cofibration. The proof reuses the
checked two-copy pushout lifting lemma for free dagger maps and the original
rigidification weak criterion. The functorial free-inner small-object
factorization and its vertex preservation are separate subsequent steps.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification.DaggerRigidification

universe u

namespace DaggerModels.PartII.JTFreeInnerReplacement

noncomputable section

private local instance : ModelCategory DaggerSSet.{u} :=
  DaggerActualRigidificationQuillen.modelD.{u}

/-- The literal free dagger inner horn, with its original interior index. -/
def generator (a : DaggerNativeInnerHornFactorization.Index) :
    freeDagger.obj (SSet.horn.{u} (a.1 + 2) a.2.1).toSSet ⟶
      freeDagger.obj (Δ[a.1 + 2] : SSet.{u}) :=
  freeDagger.map (DaggerNativeInnerHornFactorization.generator a)

/-- Each literal inner horn contains every vertex of its ambient simplex. -/
private theorem horn_vertex_surjective (a : DaggerNativeInnerHornFactorization.Index) :
    Function.Surjective
      ((DaggerNativeInnerHornFactorization.generator.{u} a).app (op ⦋0⦌)) := by
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [SSet.horn_obj_zero]
  trivial

private theorem horn_vertex_epi (a : DaggerNativeInnerHornFactorization.Index) :
    Epi (SSetVertices.map (DaggerNativeInnerHornFactorization.generator.{u} a)) := by
  rw [NatTrans.epi_iff_epi_app]
  intro q
  exact (epi_iff_surjective _).2 (horn_vertex_surjective a)

/-- The actual free dagger inner horn is native inner-left after forgetting
the dagger; the reversed copy uses the reflected interior horn. -/
theorem generator_underlying_inner (a : DaggerNativeInnerHornFactorization.Index) :
    DaggerNativeInnerHornFactorization.innerAnodyne (generator.{u} a).hom := by
  let i := DaggerNativeInnerHornFactorization.generator.{u} a
  have hi : DaggerNativeInnerHornFactorization.innerAnodyne i :=
    DaggerNativeInnerPairing.horn_innerAnodyne _ a.2.2.1 a.2.2.2
  have hiop : DaggerNativeInnerHornFactorization.innerAnodyne
      (SSet.opFunctor.map i) :=
    DaggerActualAntiInnerJoyalMappingWeak.opposite_horn_inner a
  letI : Epi (SSetVertices.map i) := horn_vertex_epi a
  have hpush : DaggerNativeInnerHornFactorization.innerAnodyne
      (FreeDaggerPushout.mapUnderlying i) :=
    JTSpineWeak.pushoutMap_inner_of_epi i hi hiop
  let e := Arrow.isoOfNatIso FreeDaggerPushout.isoFreeDagger (Arrow.mk i)
  let eUnderlying := DaggerSSet.forget.mapArrow.mapIso e
  haveI : DaggerNativeInnerHornFactorization.innerAnodyne.{u}.RespectsIso := by
    unfold DaggerNativeInnerHornFactorization.innerAnodyne
    infer_instance
  exact (DaggerNativeInnerHornFactorization.innerAnodyne.arrow_mk_iso_iff
    eUnderlying).1 hpush

/-- Each literal generator is bijective on rigidification objects. -/
theorem generator_rigidification_objects_bijective
    (a : DaggerNativeInnerHornFactorization.Index) :
    Function.Bijective
      (daggerRigidification.map (generator.{u} a)).obj :=
  DaggerActualInnerAnodyneRigidification.object_bijective _
    (generator_underlying_inner a)

/-- The generator is original weak by its rigidified Hom maps and objects. -/
theorem generator_weak (a : DaggerNativeInnerHornFactorization.Index) :
    DaggerJoyalWeakProperties.standardJoyalWeakEquivalences (generator.{u} a) := by
  let f := generator.{u} a
  let F := daggerRigidification.map f
  have hobj : Function.Surjective F.obj :=
    (generator_rigidification_objects_bijective a).2
  have hlocal : DaggerGlobalDK.LocalGeometricWeakEquivalence F := by
    intro x y
    exact (KanQuillenReuse.weakEquivalence_iff_geometric _).1
      (DaggerActualInnerAnodyneRigidification.hom_weak f.hom
        (generator_underlying_inner a) x y)
  change DaggerGlobalDK.daggerDK DaggerUnitaryInvariance.standardReplacement F
  exact DaggerGlobalDK.daggerDK_of_surjective_local _ F hobj hlocal

/-- Each actual free dagger inner horn is an original free cofibration. -/
theorem generator_freeCofibration (a : DaggerNativeInnerHornFactorization.Index) :
    DaggerSSet.FreeCofibration (generator.{u} a) := by
  haveI : Mono (DaggerNativeInnerHornFactorization.generator.{u} a) := by
    dsimp [DaggerNativeInnerHornFactorization.generator]
    infer_instance
  unfold generator
  exact freeDagger_map_isFreeCofibration _

/-- The generator belongs to the exact original trivial-cofibration class. -/
theorem generator_trivialCofibration (a : DaggerNativeInnerHornFactorization.Index) :
    trivialCofibrations DaggerSSet.{u} (generator.{u} a) := by
  change
    ((DaggerActualRigidificationQuillen.modelD.{u}).categoryWithCofibrations.cofibrations ⊓
      (DaggerActualRigidificationQuillen.modelD.{u}).categoryWithWeakEquivalences.weakEquivalences)
        (generator.{u} a)
  rw [DaggerOriginalJoyalModel.standard_model_cof,
    DaggerOriginalJoyalModel.standard_model_weak]
  exact ⟨generator_freeCofibration a, generator_weak a⟩

end

end DaggerModels.PartII.JTFreeInnerReplacement
