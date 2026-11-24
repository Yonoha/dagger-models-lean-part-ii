import Mathlib.CategoryTheory.Presentable.Basic
import Mathlib.CategoryTheory.Limits.Comma
import Mathlib.CategoryTheory.Limits.Connected

/-! Pointwise colimit tests for the arrow functors used in the localization. -/

set_option autoImplicit false

open CategoryTheory Limits

universe u v t z u' v' w

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] {J : Type t} [Category.{z} J]

/-- An arrow cocone is colimiting if its source and target cocones are colimiting. -/
def isColimitArrowOfComponents {F : J ⥤ Arrow C} (c : Cocone F)
    (hL : IsColimit (Arrow.leftFunc.mapCocone c)) (hR : IsColimit (Arrow.rightFunc.mapCocone c)) :
    IsColimit c := by
  let d (s : Cocone F) := hL.desc (Arrow.leftFunc.mapCocone s)
  let e (s : Cocone F) := hR.desc (Arrow.rightFunc.mapCocone s)
  have h₁ (s : Cocone F) (j : J) : (c.ι.app j).left ≫ d s = (s.ι.app j).left := hL.fac _ _
  have h₂ (s : Cocone F) (j : J) : (c.ι.app j).right ≫ e s = (s.ι.app j).right := hR.fac _ _
  refine { desc := fun s ↦ Arrow.homMk (d s) (e s) ?_, fac := ?_, uniq := ?_ }
  · apply hL.hom_ext
    intro j
    calc
      (c.ι.app j).left ≫ d s ≫ s.pt.hom = (s.ι.app j).left ≫ s.pt.hom := by
        rw [← Category.assoc, h₁]
      _ = (F.obj j).hom ≫ (s.ι.app j).right := (s.ι.app j).w
      _ = (F.obj j).hom ≫ (c.ι.app j).right ≫ e s := by rw [h₂]
      _ = (c.ι.app j).left ≫ c.pt.hom ≫ e s := by
        have h : (c.ι.app j).left ≫ c.pt.hom = (F.obj j).hom ≫ (c.ι.app j).right :=
          (c.ι.app j).w
        rw [← Category.assoc, ← h, Category.assoc]
  · intro s j
    apply Arrow.hom_ext
    · exact h₁ s j
    · exact h₂ s j
  · intro s m hm
    apply Arrow.hom_ext
    · exact hL.uniq (Arrow.leftFunc.mapCocone s) m.left (fun j ↦ congrArg (fun f ↦ f.left) (hm j))
    · exact hR.uniq (Arrow.rightFunc.mapCocone s) m.right (fun j ↦ congrArg (fun f ↦ f.right) (hm j))

/-- A functor which is accessible induces an accessible functor on arrows. -/
theorem mapArrow_isCardinalAccessible {D : Type u'} [Category.{v'} D]
    [HasColimitsOfSize.{w,w} C] (F : C ⥤ D) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [F.IsCardinalAccessible κ] : F.mapArrow.IsCardinalAccessible κ := by
  constructor
  intro K _ _
  letI := F.preservesColimitsOfShape_of_isCardinalAccessible κ K
  constructor
  intro U
  constructor
  intro c hc
  refine ⟨isColimitArrowOfComponents _ ?_ ?_⟩
  · exact isColimitOfPreserves F (isColimitOfPreserves Arrow.leftFunc hc)
  · exact isColimitOfPreserves F (isColimitOfPreserves Arrow.rightFunc hc)

end

end DaggerModels.PartII
