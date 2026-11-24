import DaggerModelsPartII.DaggerJTRealization
import DaggerModels.ForgetfulReflection
import DaggerModels.Presentable
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

/-!
# The actual right adjoint of the dagger JT realization

The realization functor is the one built from the manuscript's coend. Its
underlying ordinary realization preserves colimits. Dagger forgetting
preserves and reflects colimits, so this dagger realization preserves
colimits too. The presheaf universal property then constructs its right
adjoint as restricted Yoneda on the actual represented frames.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits DaggerModels

namespace DaggerModels.PartII.DaggerJTAdjunction

open SegalLocalizers JTReversalInput OrdinaryJTRealization DaggerJTRealization

noncomputable section

/-- The actual pair of reversal and ordinary simplex indices. -/
abbrev DaggerIndex := ReverseSimplex × SimplexCategory

/-- Reassociate the two presheaf indices without changing their values. -/
def sourceEquivalence :
    ReverseDaggerSpace.{0} ≌ (DaggerIndexᵒᵖ ⥤ Type) :=
  (Functor.currying :
      (ReverseSimplexᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type) ≌
        ((ReverseSimplexᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type)).trans
    ((prodOpEquiv (C := ReverseSimplex) (D := SimplexCategory)).symm.congrLeft)

/-- The same dagger realization expressed on one presheaf index. -/
def presheafRealization : (DaggerIndexᵒᵖ ⥤ Type) ⥤ DaggerSSet.{0} :=
  sourceEquivalence.inverse ⋙ daggerRealization

/-- The literal dagger frame of a represented pair. -/
def frame : DaggerIndex ⥤ DaggerSSet.{0} :=
  uliftYoneda.{0} ⋙ presheafRealization

/-- Restricted Yoneda for the literal dagger frames. -/
def presheafNerve : DaggerSSet.{0} ⥤ (DaggerIndexᵒᵖ ⥤ Type) :=
  Presheaf.restrictedULiftYoneda.{0} frame

/-- The right adjoint is the literal Hom presheaf on the constructed dagger frames. -/
@[simp] theorem presheafNerve_obj_obj (X : DaggerSSet.{0})
    (p : DaggerIndexᵒᵖ) :
    (presheafNerve.obj X).obj p = ULift (frame.obj p.unop ⟶ X) := rfl

/-- Ordinary restriction along the simplex inclusion preserves colimits. -/
theorem ordinaryInput_preservesColimits :
    PreservesColimits ordinaryInput := by
  letI : Functor.IsEquivalence
      (Functor.uncurry :
        (SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type) ⥤
          ((SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type)) :=
    (Functor.currying :
      (SimplexCategoryᵒᵖ ⥤ SimplexCategoryᵒᵖ ⥤ Type) ≌
        ((SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ) ⥤ Type)).isEquivalence_functor
  dsimp [JTReversalInput.ordinaryInput]
  infer_instance

/-- Forgetting dagger detects preservation of colimits for the actual coend realization. -/
theorem daggerRealization_preservesColimits :
    PreservesColimits daggerRealization := by
  letI : PreservesColimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesColimits
  letI : ReflectsColimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_reflectsColimits
  letI : PreservesColimits ordinaryInput := ordinaryInput_preservesColimits
  letI : PreservesColimits realization :=
    realizationNerveAdjunction.leftAdjoint_preservesColimits
  haveI : PreservesColimits (daggerRealization ⋙ DaggerSSet.forget) := by
    rw [daggerRealization_underlying]
    infer_instance
  exact preservesColimits_of_reflects_of_preserves
    daggerRealization DaggerSSet.forget

theorem presheafRealization_preservesColimits :
    PreservesColimits presheafRealization := by
  letI : PreservesColimits daggerRealization :=
    daggerRealization_preservesColimits
  dsimp [presheafRealization]
  infer_instance

/-- The coend–Hom adjunction on the uncurried presheaf category. -/
def presheafAdjunction : presheafRealization ⊣ presheafNerve := by
  letI : HasColimits DaggerSSet.{0} := daggerSSetHasColimits
  letI : PreservesColimits presheafRealization :=
    presheafRealization_preservesColimits
  letI : presheafRealization.IsLeftKanExtension
      (𝟙 (uliftYoneda.{0} ⋙ presheafRealization)) :=
    Presheaf.isLeftKanExtension_of_preservesColimits
      presheafRealization (Iso.refl _)
  exact Presheaf.uliftYonedaAdjunction
    presheafRealization (𝟙 (uliftYoneda.{0} ⋙ presheafRealization))

/-- Right adjoint in the manuscript's original two-direction source category. -/
def daggerNerve : DaggerSSet.{0} ⥤ ReverseDaggerSpace.{0} :=
  presheafNerve ⋙ sourceEquivalence.inverse

/-- The source equivalence leaves the previously constructed realization
unchanged, up to its canonical unit isomorphism. -/
def realizationIso :
    sourceEquivalence.functor ⋙ presheafRealization ≅ daggerRealization :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight sourceEquivalence.unitIso.symm daggerRealization ≪≫
      daggerRealization.leftUnitor

/-- The actual dagger JT realization has the stated coherent right adjoint. -/
def adjunction : daggerRealization ⊣ daggerNerve :=
  (sourceEquivalence.toAdjunction.comp presheafAdjunction).ofNatIsoLeft
    realizationIso

end

end DaggerModels.PartII.DaggerJTAdjunction
