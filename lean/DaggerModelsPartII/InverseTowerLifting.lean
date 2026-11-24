import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Opposites

/-! Lifting through a continuous inverse tower, by transfinite lifting in the opposite category. -/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty Opposite

universe v u t

namespace DaggerModels.PartII

variable {C : Type u} [Category.{v} C]
  {J : Type t} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

private def inverseTower_opTransfiniteComposition (I : MorphismProperty C)
    (G : Jᵒᵖ ⥤ C) [G.rightOp.IsWellOrderContinuous] {c : Cone G} (hc : IsLimit c)
    (h : ∀ (j : J), ¬IsMax j → I.rlp (G.map (homOfLE (Order.le_succ j)).op)) :
    (I.op.llp).TransfiniteCompositionOfShape J (c.π.app (op ⊥)).op where
  F := G.rightOp
  isoBot := Iso.refl _
  incl := (coconeRightOpOfCone c).ι
  isColimit := isColimitCoconeRightOpOfCone G hc
  fac := Category.id_comp _
  map_mem j hj _ _ i hi := (h j hj i.unop hi).op

/-- The projection from a continuous inverse tower's limit to its bottom stage
inherits any fixed right lifting property shared by the successor maps. -/
theorem rlp_limitProjection_of_inverseTower (I : MorphismProperty C)
    (G : Jᵒᵖ ⥤ C) [G.rightOp.IsWellOrderContinuous] {c : Cone G} (hc : IsLimit c)
    (h : ∀ (j : J), ¬IsMax j → I.rlp (G.map (homOfLE (Order.le_succ j)).op)) :
    I.rlp (c.π.app (op ⊥)) := by
  have hcomp := Nonempty.intro (inverseTower_opTransfiniteComposition I G hc h)
  have hw := (I.op.llp).transfiniteCompositionsOfShape_le J _ hcomp
  intro A B i hi
  exact (hw i.op hi).unop

/-- Every map to the bottom of a continuous inverse tower inherits the
right lifting property of the successor maps. -/
theorem rlp_toBottom_of_inverseTower (I : MorphismProperty C)
    (G : Jᵒᵖ ⥤ C) [G.rightOp.IsWellOrderContinuous] [HasLimit G]
    (h : ∀ (j : J), ¬IsMax j → I.rlp (G.map (homOfLE (Order.le_succ j)).op))
    (j : J) : I.rlp (G.map (homOfLE (bot_le : ⊥ ≤ j)).op) := by
  let c := inverseTower_opTransfiniteComposition I G (limit.isLimit G) h
  have hw := (I.op.llp).transfiniteCompositionsOfShape_le (Set.Iic j) _ ⟨c.iic j⟩
  intro A B i hi
  exact (hw i.op hi).unop

omit [SuccOrder J] [OrderBot J] [WellFoundedLT J] in
/-- Continuity of inverse towers is preserved by functors preserving the
limits at the limit stages. -/
theorem inverseTower_continuous_map {D : Type*} [Category* D]
    (G : Jᵒᵖ ⥤ C) (F : C ⥤ D) [G.rightOp.IsWellOrderContinuous]
    (h : ∀ (j : J), Order.IsSuccLimit j → PreservesLimitsOfShape (Set.Iio j)ᵒᵖ F) :
    (G ⋙ F).rightOp.IsWellOrderContinuous := by
  letI : PreservesWellOrderContinuousOfShape J F.op := by
    constructor
    intro j hj
    letI := h j hj
    exact preservesColimitsOfShape_op _ _
  exact inferInstanceAs (G.rightOp ⋙ F.op).IsWellOrderContinuous

end DaggerModels.PartII
