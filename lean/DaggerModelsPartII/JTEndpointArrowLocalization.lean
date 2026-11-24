import DaggerModelsPartII.JTEndpointReplacementSquare
import DaggerModelsPartII.JTEndpointArrowWeak
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The localized roof of the actual augmented endpoint-arrow comparison

The original Gamma-to-Xi endpoint comparison and its two zero-fixed
replacements live over the constant original arrow `iota`. Localizing at
pointwise original weakness on both arrow components identifies the
original comparison with the roof through the actual `Qlambda`.
This source-side statement does not construct a total derived endpoint-
cobase-Hom functor or invert either raw Hom map.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointArrowLocalization

open JTRelativeReedyFrame JTActualCosimplicialFrame JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations
open JTEndpointReplacementSquare JTXiAugmentation

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The common original target of all four arrow augmentations. -/
def augmentedTarget : SimplexCategory ⥤ Arrow Coefficient :=
  (Functor.const SimplexCategory).obj (Arrow.mk iota)

/-- Both components must be original weak at every cosimplicial degree. -/
def augmentedArrowWeak : MorphismProperty (Over augmentedTarget) :=
  fun _ _ f ↦ ∀ k : SimplexCategory,
    weakEquivalences Coefficient ((f.left.app k).left) ∧
      weakEquivalences Coefficient ((f.left.app k).right)

/-- The four actual augmented endpoint-arrow diagrams. -/
def rawGamma : Over augmentedTarget := Over.mk GammaArrowAugmentation
def rawXi : Over augmentedTarget := Over.mk XiArrowAugmentation
def replacedGamma : Over augmentedTarget := Over.mk QGaugmentation
def replacedXi : Over augmentedTarget := Over.mk QXaugmentation

/-- The original comparison and its actual zero-fixed replacement square. -/
def lambdaAug : rawGamma ⟶ rawXi :=
  Over.homMk lambda lambda_augmentation
def qGAug : replacedGamma ⟶ rawGamma := Over.homMk qG rfl
def qXAug : replacedXi ⟶ rawXi := Over.homMk qX rfl
def QlambdaAug : replacedGamma ⟶ replacedXi :=
  Over.homMk Qlambda Qlambda_augmentation

/-- The chosen maps retain the four literal underlying arrow-diagram maps. -/
theorem lambdaAug_left : lambdaAug.left = lambda := rfl
theorem qGAug_left : qGAug.left = qG := rfl
theorem qXAug_left : qXAug.left = qX := rfl
theorem QlambdaAug_left : QlambdaAug.left = Qlambda := rfl

/-- The augmented square is exactly the checked original `Qlambda_square`. -/
theorem augmented_square : QlambdaAug ≫ qXAug = qGAug ≫ lambdaAug := by
  apply Over.OverMorphism.ext
  exact Qlambda_square

/-- The first vertical map is pointwise original weak on both components. -/
theorem qGAug_weak : augmentedArrowWeak qGAug := by
  intro k
  induction k using SimplexCategory.rec with
  | h n =>
      change weakEquivalences Coefficient (qG.app ⦋n⦌).left ∧
        weakEquivalences Coefficient (qG.app ⦋n⦌).right
      exact qG_pointwiseWeak n

/-- The second vertical map is pointwise original weak on both components. -/
theorem qXAug_weak : augmentedArrowWeak qXAug := by
  intro k
  induction k using SimplexCategory.rec with
  | h n =>
      change weakEquivalences Coefficient (qX.app ⦋n⦌).left ∧
        weakEquivalences Coefficient (qX.app ⦋n⦌).right
      exact qX_pointwiseWeak n

/-- The original and replacement comparisons also retain the two-component
pointwise weakness proved for their actual underlying arrow maps. -/
theorem lambdaAug_weak : augmentedArrowWeak lambdaAug := by
  intro k
  induction k using SimplexCategory.rec with
  | h n =>
      change weakEquivalences Coefficient (lambda.app ⦋n⦌).left ∧
        weakEquivalences Coefficient (lambda.app ⦋n⦌).right
      exact JTEndpointArrowWeak.lambda_pointwiseWeak n

theorem QlambdaAug_weak : augmentedArrowWeak QlambdaAug := by
  intro k
  induction k using SimplexCategory.rec with
  | h n =>
      change weakEquivalences Coefficient (Qlambda.app ⦋n⦌).left ∧
        weakEquivalences Coefficient (Qlambda.app ⦋n⦌).right
      exact JTEndpointArrowWeak.Qlambda_pointwiseWeak n

/-- Every compatible two-sided replacement square with weak vertical maps
represents its original map by the same roof after localization. -/
private theorem localized_roof_of_square
    {A B QA QB : Over augmentedTarget}
    (f : A ⟶ B) (p : QA ⟶ A) (q : QB ⟶ B) (g : QA ⟶ QB)
    (hp : augmentedArrowWeak p) (_hq : augmentedArrowWeak q)
    (hs : g ≫ q = p ≫ f) :
    augmentedArrowWeak.Q.map f =
      ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak p hp).inv ≫
        augmentedArrowWeak.Q.map g) ≫ augmentedArrowWeak.Q.map q := by
  have h := congrArg (fun t ↦ augmentedArrowWeak.Q.map t) hs
  simp only [Functor.map_comp] at h
  calc
    augmentedArrowWeak.Q.map f =
        ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak p hp).inv ≫
          augmentedArrowWeak.Q.map p) ≫ augmentedArrowWeak.Q.map f := by simp
    _ = (Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak p hp).inv ≫
          (augmentedArrowWeak.Q.map p ≫ augmentedArrowWeak.Q.map f) :=
      Category.assoc _ _ _
    _ = (Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak p hp).inv ≫
          (augmentedArrowWeak.Q.map g ≫ augmentedArrowWeak.Q.map q) := by rw [← h]
    _ = ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak p hp).inv ≫
          augmentedArrowWeak.Q.map g) ≫ augmentedArrowWeak.Q.map q :=
      (Category.assoc _ _ _).symm

/-- The original augmented `lambda` is represented by the actual
zero-fixed `Qlambda` roof, with no substituted endpoint arrow. -/
theorem lambda_localization_roof :
    augmentedArrowWeak.Q.map lambdaAug =
      ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak qGAug
          qGAug_weak).inv ≫
        augmentedArrowWeak.Q.map QlambdaAug) ≫
          augmentedArrowWeak.Q.map qXAug :=
  localized_roof_of_square lambdaAug qGAug qXAug QlambdaAug
    qGAug_weak qXAug_weak augmented_square

/-- A second compatible weak replacement gives the same localized map. -/
theorem replacement_roof_independent
    {A B : Over augmentedTarget}
    (pA : A ⟶ rawGamma) (pB : B ⟶ rawXi) (f : A ⟶ B)
    (hpA : augmentedArrowWeak pA) (hpB : augmentedArrowWeak pB)
    (hs : f ≫ pB = pA ≫ lambdaAug) :
    ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak pA hpA).inv ≫
      augmentedArrowWeak.Q.map f) ≫ augmentedArrowWeak.Q.map pB =
        ((Localization.isoOfHom augmentedArrowWeak.Q augmentedArrowWeak qGAug
            qGAug_weak).inv ≫
          augmentedArrowWeak.Q.map QlambdaAug) ≫
            augmentedArrowWeak.Q.map qXAug := by
  rw [← localized_roof_of_square lambdaAug pA pB f hpA hpB hs,
    lambda_localization_roof]

end

end DaggerModels.PartII.JTEndpointArrowLocalization
