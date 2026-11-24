import DaggerModelsPartII.ActualUnitNativeComparison
import Mathlib.CategoryTheory.Subfunctor.Image

/-!
# Monomorphisms of the native unit and the length-one spine identification

The actual representable unit is monic. Transporting it along the specified
isomorphisms proves the same for the native canonical map, then for the spine.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.NativeUnitMonomorphism

open SegalLocalizers SegalRepresentables ActualIndexProjectiveModel
open ActualUnitNativeComparison DaggerNerveLengthOne DaggerNerveLengthFiltration

noncomputable section

/-- The canonical native free-simplex map is monic after discretization. -/
theorem canonicalDaggerMap_discrete_mono (m : ℕ) :
    Mono (discreteDagger.map (canonicalDaggerMap m)) := by
  haveI := actualUnit_representable_mono.{0} (ReverseSimplex.mk m)
  have h : Mono (actualUnitNativeMap m) := by
    dsimp only [actualUnitNativeMap]
    infer_instance
  rwa [actualUnitNativeMap_eq_canonicalDaggerMap] at h

/-- The literal canonical spine map is monic after discretization. -/
theorem canonicalSpineMap_discrete_mono (m : ℕ) :
    Mono (discreteDagger.map (canonicalSpineMap m)) := by
  haveI := segalMap_mono.{0} m
  haveI := canonicalDaggerMap_discrete_mono m
  rw [canonicalSpineMap, discreteDagger.map_comp]
  change Mono (segalMap m ≫ discreteDagger.map (canonicalDaggerMap m))
  infer_instance

/-- The set-valued reversal presheaf map of the literal spine is monic. -/
theorem canonicalSpinePresheafMap_mono (m : ℕ) :
    Mono (canonicalSpinePresheafMap m) := by
  haveI := canonicalSpineMap_discrete_mono m
  rw [NatTrans.mono_iff_mono_app]
  intro k
  have h := (NatTrans.mono_iff_mono_app
    (discreteDagger.map (canonicalSpineMap m))).mp inferInstance k
  have hzero := (NatTrans.mono_iff_mono_app _).mp h (op ⦋0⦌)
  exact hzero

private theorem eqToHom_toFunctor_ι {C : Type*} [Category C] {F : C ⥤ Type*}
    {A B : Subfunctor F} (h : A = B) :
    eqToHom (congrArg (fun S : Subfunctor F ↦ S.toFunctor) h) ≫ B.ι = A.ι := by
  cases h
  simp

/-- The literal free dagger spine is isomorphic to X₁, not just a source
having the same image. -/
def spineLengthOneIso (m : ℕ) :
    DaggerSSet.toPresheaf.obj (freeDagger.obj (ordinarySpine.{0} m)) ≅
      (lengthFiltration m 1).toFunctor := by
  haveI := canonicalSpinePresheafMap_mono m
  exact asIso (Subfunctor.toRange (canonicalSpinePresheafMap m)) ≪≫
    eqToIso (congrArg (fun S ↦ S.toFunctor)
      (lengthFiltration_one_eq_spine_range m).symm)

/-- The length-one identification preserves the specified inclusion into
native nerve. -/
theorem spineLengthOneIso_ι (m : ℕ) :
    (spineLengthOneIso m).hom ≫ (lengthFiltration m 1).ι =
      canonicalSpinePresheafMap m := by
  change (Subfunctor.toRange (canonicalSpinePresheafMap m) ≫
    eqToHom (congrArg (fun S ↦ S.toFunctor)
      (lengthFiltration_one_eq_spine_range m).symm)) ≫
        (lengthFiltration m 1).ι = canonicalSpinePresheafMap m
  rw [Category.assoc,
    eqToHom_toFunctor_ι (lengthFiltration_one_eq_spine_range m).symm,
    Subfunctor.toRange_ι]

end

end DaggerModels.PartII.NativeUnitMonomorphism
