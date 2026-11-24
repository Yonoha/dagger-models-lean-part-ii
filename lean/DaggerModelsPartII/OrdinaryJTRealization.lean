import DaggerModelsPartII.GroupoidSimplex
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Products.Basic

/-!
# The ordinary Joyal--Tierney two-index realization

The index is literally the product of two simplex categories. The parameter
in the second coordinate is the groupoid-completed simplex, and the first
coordinate is the ordinary standard simplex. The realization is the left Kan
extension along the universe-lifted Yoneda embedding; the restricted Yoneda
functor is its actual right adjoint.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

namespace DaggerModels.PartII.OrdinaryJTRealization

noncomputable section

/-- The two ordinary simplicial indices before reversal is imposed. -/
abbrev Index := SimplexCategory × SimplexCategory

/-- Set-valued bisimplicial presheaves on the literal product index. -/
abbrev BiPresheaf := Indexᵒᵖ ⥤ Type

/-- The original two-variable JT parameter, `([m],[k]) ↦ Δ[m] × J[k]`. -/
def tFunctor : Index ⥤ SSet.{0} :=
  (SSet.stdSimplex.{0}.prod GroupoidSimplex.parameter) ⋙
    MonoidalCategory.tensor SSet.{0}

@[simp] theorem tFunctor_obj (m k : SimplexCategory) :
    tFunctor.obj (m, k) = SSet.stdSimplex.obj m ⊗ GroupoidSimplex.parameter.obj k := rfl

@[simp] theorem tFunctor_map {m m' k k' : SimplexCategory}
    (f : (m, k) ⟶ (m', k')) :
    tFunctor.map f =
      SSet.stdSimplex.map f.1 ⊗ₘ GroupoidSimplex.parameter.map f.2 := rfl

/-- The actual left Kan extension of the two-variable JT parameter. -/
def realization : BiPresheaf ⥤ SSet.{0} :=
  uliftYoneda.{0}.leftKanExtension tFunctor

/-- The restricted-Yoneda right adjoint of the same literal parameter. -/
def nerve : SSet.{0} ⥤ BiPresheaf :=
  Presheaf.restrictedULiftYoneda.{0} tFunctor

/-- The manuscript's nerve with raw Hom sets, without a universe lift. -/
def rawNerve : SSet.{0} ⥤ BiPresheaf :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj tFunctor.op

/-- The native left Kan extension unit. -/
def realizationUnit : tFunctor ⟶ uliftYoneda.{0} ⋙ realization :=
  uliftYoneda.{0}.leftKanExtensionUnit tFunctor

instance realizationIsLeftKanExtension : realization.IsLeftKanExtension realizationUnit := by
  dsimp [realization, realizationUnit]
  infer_instance

/-- Coend--Hom adjunction with the same two-index frame in both functors. -/
def realizationNerveAdjunction : realization ⊣ nerve := by
  dsimp [realization, nerve]
  exact Presheaf.uliftYonedaAdjunction.{0}
    (uliftYoneda.{0}.leftKanExtension tFunctor)
    (uliftYoneda.{0}.leftKanExtensionUnit tFunctor)

/-- Remove the harmless universe lift from the native restricted Yoneda. -/
def nativeToRawNerveIso : nerve ≅ rawNerve :=
  Functor.isoWhiskerRight
    (uliftYonedaIsoYoneda.{0} (C := SSet.{0}))
    ((Functor.whiskeringLeft _ _ _).obj tFunctor.op)

/-- The same realization is left adjoint to the literal raw-Hom nerve. -/
def realizationRawNerveAdjunction : realization ⊣ rawNerve :=
  realizationNerveAdjunction.ofNatIsoRight nativeToRawNerveIso

/-- Co-Yoneda identifies the realization of a represented pair with its
specified JT parameter. -/
def realizationRepresentableIso (p : Index) :
    realization.obj (uliftYoneda.{0}.obj p) ≅ tFunctor.obj p :=
  (Presheaf.isExtensionAlongULiftYoneda tFunctor).app p

/-- The right adjoint evaluates to the Hom set out of the literal parameter. -/
@[simp] theorem nerve_obj_obj (X : SSet.{0}) (p : Indexᵒᵖ) :
    (nerve.obj X).obj p = ULift (tFunctor.obj p.unop ⟶ X) := rfl

@[simp] theorem rawNerve_obj_obj (X : SSet.{0}) (p : Indexᵒᵖ) :
    (rawNerve.obj X).obj p = (tFunctor.obj p.unop ⟶ X) := rfl

/-- The simplex category of a bisimplicial presheaf for the pointwise left
Kan extension. -/
abbrev SimplexIndex (W : BiPresheaf) := CostructuredArrow uliftYoneda.{0} W

/-- The actual diagram whose colimit is the two-index realization. -/
def simplexDiagram (W : BiPresheaf) : SimplexIndex W ⥤ SSet.{0} :=
  CostructuredArrow.proj uliftYoneda W ⋙ tFunctor

/-- The universal cocone on the actual two-index simplex diagram. -/
def simplexCocone (W : BiPresheaf) : Cocone (simplexDiagram W) :=
  (Functor.LeftExtension.mk realization realizationUnit).coconeAt W

/-- The cocone leg corresponding to a represented pair of simplices. -/
theorem simplexCocone_leg (W : BiPresheaf) (σ : SimplexIndex W) :
    (simplexCocone W).ι.app σ =
      realizationUnit.app σ.left ≫ realization.map σ.hom := rfl

/-- The pointwise universal property, expressed on the literal simplex
category rather than only through an abstract coend notation. -/
def simplexCoconeIsColimit (W : BiPresheaf) : IsColimit (simplexCocone W) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    realization realizationUnit W

/-- Pointwise colimit formula for the realization, retaining both indices. -/
def realizationColimitIso (W : BiPresheaf) :
    realization.obj W ≅ colimit (simplexDiagram W) :=
  uliftYoneda.{0}.leftKanExtensionObjIsoColimit tFunctor W

end

end DaggerModels.PartII.OrdinaryJTRealization
