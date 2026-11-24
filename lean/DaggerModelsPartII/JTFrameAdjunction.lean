import DaggerModelsPartII.JTRelativeReedyFrame
import DaggerModelsPartII.DaggerJTAdjunction
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# The coend--Hom adjunction of the actual relative JT frames

The parameter is the constructed outer-natural cosimplicial frame, with
both of its original indices. The presheaf left Kan extension and restricted
Yoneda construct the adjunction; no adjunction or Quillen property is assumed.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite DaggerModels

namespace DaggerModels.PartII.JTFrameAdjunction

open SegalLocalizers DaggerJTAdjunction

noncomputable section

local instance : HasColimits DaggerSimplicialCat.{0, 0} := daggerSimplicialCatHasColimits

/-- The actual relative frame with the original two indices uncurried. -/
def frameParameter : DaggerIndex ⥤ DaggerSimplicialCat.{0, 0} :=
  Functor.uncurry.obj JTRelativeReedyFrame.GammaOuter

theorem frameParameter_vertical_map (m : ReverseSimplex)
    {k l : SimplexCategory} (f : k ⟶ l) :
    frameParameter.map (show (m, k) ⟶ (m, l) from (𝟙 m, f)) =
      (JTRelativeReedyFrame.GammaOuter.obj m).map f := by
  simp [frameParameter, Functor.uncurry]

/-- The literal Yoneda left Kan extension of the constructed frame. -/
def presheafRealization : (DaggerIndexᵒᵖ ⥤ Type) ⥤ DaggerSimplicialCat.{0, 0} :=
  uliftYoneda.{0}.leftKanExtension frameParameter

/-- Restricted Yoneda for the same constructed frame. -/
def presheafNerve : DaggerSimplicialCat.{0, 0} ⥤ (DaggerIndexᵒᵖ ⥤ Type) :=
  Presheaf.restrictedULiftYoneda.{0} frameParameter

/-- The native coend--Hom adjunction on the two-index presheaf category. -/
def presheafAdjunction : presheafRealization ⊣ presheafNerve :=
  Presheaf.uliftYonedaAdjunction
    (uliftYoneda.{0}.leftKanExtension frameParameter)
    (uliftYoneda.{0}.leftKanExtensionUnit frameParameter)

/-- The raw Hom presheaf written in the manuscript's formula. -/
def rawPresheafNerve : DaggerSimplicialCat.{0, 0} ⥤ (DaggerIndexᵒᵖ ⥤ Type) :=
  yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj frameParameter.op

/-- Remove the native universe lift from the same right adjoint. -/
def nativeToRawIso : presheafNerve ≅ rawPresheafNerve :=
  Functor.isoWhiskerRight
    (uliftYonedaIsoYoneda.{0} (C := DaggerSimplicialCat.{0, 0}))
    ((Functor.whiskeringLeft _ _ _).obj frameParameter.op)

/-- The frame realization on the manuscript's original source category. -/
def frameRealization : ReverseDaggerSpace.{0} ⥤ DaggerSimplicialCat.{0, 0} :=
  sourceEquivalence.functor ⋙ presheafRealization

/-- The actual frame nerve, with raw Hom sets and the original indices. -/
def frameNerve : DaggerSimplicialCat.{0, 0} ⥤ ReverseDaggerSpace.{0} :=
  rawPresheafNerve ⋙ sourceEquivalence.inverse

/-- The constructed frame realization and nerve are genuinely adjoint. -/
def adjunction : frameRealization ⊣ frameNerve :=
  sourceEquivalence.toAdjunction.comp
    (presheafAdjunction.ofNatIsoRight nativeToRawIso)

@[simp] theorem frameNerve_obj_obj (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) (k : SimplexCategory) :
    ((frameNerve.obj C).obj (op m)).obj (op k) = (frameParameter.obj (m, k) ⟶ C) := rfl

/-- The Hom simplicial set of one actual cosimplicial frame, functorial
in its dagger simplicial-category target. -/
def mappingNerve (m : ReverseSimplex) : DaggerSimplicialCat.{0, 0} ⥤ SSet.{0} :=
  opOp DaggerSimplicialCat.{0, 0} ⋙ coyoneda ⋙
    (Functor.whiskeringLeft _ _ _).obj (JTRelativeReedyFrame.GammaOuter.obj m).op

/-- Evaluation of the constructed right adjoint is the literal Hom simplicial
set of the same actual frame; the comparison is natural in the target. -/
def frameNerveEvaluationIso (m : ReverseSimplex) :
    frameNerve ⋙ (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m) ≅ mappingNerve m :=
  NatIso.ofComponents
    (fun C ↦ NatIso.ofComponents
      (fun n ↦ (show
          ((frameNerve ⋙ (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj (op m)).obj C).obj n ≃
            ((mappingNerve m).obj C).obj n from
        { toFun := fun f ↦ f.op
          invFun := fun f ↦ f.unop
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }).toIso)
      (by
        intro n n' f
        ext x
        change (frameParameter.map
          (show (m, n'.unop) ⟶ (m, n.unop) from (𝟙 m, f.unop)) ≫ x).op =
          ((JTRelativeReedyFrame.GammaOuter.obj m).map f.unop ≫ x).op
        rw [frameParameter_vertical_map]))
    (by intro C D f; ext n x; rfl)

end

end DaggerModels.PartII.JTFrameAdjunction
