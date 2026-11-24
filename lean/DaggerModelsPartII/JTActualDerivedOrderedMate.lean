import DaggerModelsPartII.JTGammaStrictFiber
import DaggerModelsPartII.JTXiDerivedMapping

/-!
# The original ordered mate followed by the canonical Gamma fiber inclusion

The map is the retained actual ordered mate followed by the canonical
strict-to-chosen-homotopy-fiber map. Its comparison with QG Hom equals the
retained Xi raw-to-resolved comparison followed by the actual resolved mate.
Two-out-of-three proves this specified map weak. Its localization retains
the original normalization maps. Identifying the Xi source with an actual
nerve-row chosen homotopy fiber remains a separate bridge.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualDerivedOrderedMate

open JTRelativeReedyFrame JTEndpointFrameComparison JTDerivedOrderedMate
open JTGammaDerivedFiber JTGammaStrictFiber

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual original ordered mate, followed by the canonical inclusion
of its Gamma strict fiber into the chosen Gamma homotopy fiber. -/
def actualToGammaFiber (C : Coefficient) (x y : C.Obj) :
    JTOrderedFrameMate.XiOrdered C x y ⟶ gammaHomotopyFiber C x y :=
  JTOrderedFrameMate.orderedMate C x y ≫ gammaInclusion C x y

/-- The specified canonical map gives the original resolution square as
an exact equation, retaining the original ordered endpoints. -/
theorem actualToGammaFiber_comparison (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    actualToGammaFiber C x y ≫ gammaFiberComparison C x y =
      xiRawToResolved C x y ≫ precomp C x y := by
  rw [actualToGammaFiber, Category.assoc, gammaInclusion_comparison]
  exact orderedMate_resolution_square C x y

/-- The actual mate-to-Gamma-homotopy-fiber map is Kan weak. No weakness
of the raw Gamma strict-to-resolved comparison is assumed. -/
theorem actualToGammaFiber_weak (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    WeakEquivalence (actualToGammaFiber C x y) := by
  haveI : WeakEquivalence (xiRawToResolved C x y) :=
    JTXiDerivedMapping.xiRawToResolved_weak C x y
  haveI : WeakEquivalence (precomp C x y) :=
    (weakEquivalence_iff _).mpr (precomp_weak C x y)
  haveI : WeakEquivalence (xiRawToResolved C x y ≫ precomp C x y) := inferInstance
  haveI : WeakEquivalence (gammaFiberComparison C x y) :=
    gammaFiberComparison_weak C x y
  exact weakEquivalence_of_postcomp_of_fac (actualToGammaFiber_comparison C x y)

/-- The Gamma inclusion retains the previously specified raw Gamma
mapping comparison after localization and frame normalization. -/
theorem gammaInclusion_localization (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.map (gammaInclusion C x y) ≫
        (gammaFiberLocalizationIso C x y).hom = gammaRawMappingComparison C x y := by
  rw [gammaFiberLocalizationIso_hom, ← Category.assoc, ← Functor.map_comp,
    gammaInclusion_comparison]
  rfl

/-- Localization of the actual weak map is the specified original
ordered comparison, with its actual strict-fiber inclusion retained. -/
def actualDerivedOrderedMateIso (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (weakEquivalences SSet.{0}).Q.obj (JTOrderedFrameMate.XiOrdered C x y) ≅
      (weakEquivalences SSet.{0}).Q.obj (gammaHomotopyFiber C x y) :=
  Localization.isoOfHom (weakEquivalences SSet.{0}).Q (weakEquivalences SSet.{0})
    (actualToGammaFiber C x y)
    ((weakEquivalence_iff _).mp (actualToGammaFiber_weak C x y))

/-- The actual localized mate commutes with the original Xi and Gamma
normalizations to the same chosen derived mapping object. -/
theorem actualDerivedOrderedMate_calibration (C : Coefficient) [IsFibrant C]
    (x y : C.Obj) :
    (actualDerivedOrderedMateIso C x y).hom ≫
        (gammaFiberLocalizationIso C x y).hom =
      (JTXiDerivedMapping.xiRawMappingIso C x y).hom := by
  change (weakEquivalences SSet.{0}).Q.map
      (JTOrderedFrameMate.orderedMate C x y ≫ gammaInclusion C x y) ≫ _ = _
  rw [Functor.map_comp, Category.assoc, gammaInclusion_localization]
  exact rawOrderedMate_calibration C x y

/-- The specified localized map is exactly the comparison obtained by the
two retained normalizations, not an arbitrary isomorphism of homotopy types. -/
theorem actualDerivedOrderedMate_eq (C : Coefficient) [IsFibrant C] (x y : C.Obj) :
    (actualDerivedOrderedMateIso C x y).hom =
      (JTXiDerivedMapping.xiRawMappingIso C x y).hom ≫
        (gammaFiberLocalizationIso C x y).inv := by
  apply (cancel_mono (gammaFiberLocalizationIso C x y).hom).mp
  rw [actualDerivedOrderedMate_calibration, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end

end DaggerModels.PartII.JTActualDerivedOrderedMate
