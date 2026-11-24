import DaggerModelsPartII.ReedyExtendFullDiagram

/-!
# Compatible factorizations on the initial segments

Choose the coefficient factorization of the boundary map at the next degree
and extend the intermediate object and both maps to the larger truncation.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)

/-- A factorization of the restriction of `f` below degree `n`. -/
structure ReedyFactorizationBelow (n : ℕ) where
  mid : BelowDegree n ⥤ C
  left : lowerDiagram n X ⟶ mid
  right : mid ⟶ lowerDiagram n Y
  fac : left ≫ right = CategoryTheory.Functor.whiskerLeft (belowDegree n).ι f

variable [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {n : ℕ} {f} (prev : ReedyFactorizationBelow f n)

/-- A coefficient factorization at the new degree, with the chosen relative properties. -/
structure ReedyFactorizationDegree (P Q : MorphismProperty C) where
  mid : DegreeExtension prev.mid
  left : DegreeExtension.Hom prev.left (DegreeExtension.ofDiagram n X) mid
  right : DegreeExtension.Hom prev.right mid (DegreeExtension.ofDiagram n Y)
  fac : left.app ≫ right.app = (DegreeExtension.Hom.ofDiagram f n).app
  left_mem : P left.relativeLatching
  right_mem : Q right.relativeMatching

variable {prev} (P Q : MorphismProperty C)

/-- Choose the new degree data from the coefficient factorization axiom. -/
def chooseReedyFactorizationDegree [HasFactorization P Q] :
    ReedyFactorizationDegree prev P Q := by
  let F := DegreeExtension.Hom.ofDiagram f n
  let D := factorizationData P Q (degreeFactorizationMap F prev.left prev.right prev.fac)
  refine ⟨factoredDegreeExtension F prev.left prev.right prev.fac D.i D.p D.fac,
    factoredDegreeLeft F prev.left prev.right prev.fac D.i D.p D.fac,
    factoredDegreeRight F prev.left prev.right prev.fac D.i D.p D.fac,
    factoredDegree_fac F prev.left prev.right prev.fac D.i D.p D.fac, ?_, ?_⟩
  · rw [factoredDegree_relativeLatching]
    exact D.hi
  · rw [factoredDegree_relativeMatching]
    exact D.hp

variable {P Q} (D : ReedyFactorizationDegree prev P Q)

/-- Extend the intermediate diagram and both maps of the factorization. -/
def ReedyFactorizationDegree.next : ReedyFactorizationBelow f (n + 1) where
  mid := extendBelowDiagram D.mid
  left := eqToHom (extendBelowDiagram_ofDiagram n X).symm ≫
    extendBelowTransformation (DegreeExtension.ofDiagram n X) D.left
  right := extendBelowTransformation D.mid D.right ≫ eqToHom (extendBelowDiagram_ofDiagram n Y)
  fac := by
    rw [Category.assoc, ← Category.assoc
      (extendBelowTransformation (DegreeExtension.ofDiagram n X) D.left),
      extendBelowTransformation_comp_of_fac _ D.left D.right
        (DegreeExtension.Hom.ofDiagram f n) prev.fac D.fac]
    ext s
    simp only [NatTrans.comp_app, eqToHom_app, extendBelowTransformation_ofDiagram_app,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Category.comp_id]
    rfl

/-- The intermediate diagram of the new factorization restricts to the old one. -/
theorem ReedyFactorizationDegree.next_restrict :
    belowDegreeInclusion (Nat.le_succ n) ⋙ D.next.mid = prev.mid :=
  extendBelowDiagram_restrict D.mid

/-- The left factor agrees in every degree that was already constructed. -/
theorem ReedyFactorizationDegree.next_left_app_old (s : BelowDegree n) :
    D.next.left.app ((belowDegreeInclusion (Nat.le_succ n)).obj s) =
      prev.left.app s ≫ eqToHom (CategoryTheory.Functor.congr_obj D.next_restrict s).symm := by
  change (eqToHom (extendBelowDiagram_ofDiagram n X).symm ≫
    extendBelowTransformation (DegreeExtension.ofDiagram n X) D.left).app
    ((belowDegreeInclusion (Nat.le_succ n)).obj s) = _
  simp only [NatTrans.comp_app, eqToHom_app, extendBelowTransformation_app_old,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The right factor agrees in every degree that was already constructed. -/
theorem ReedyFactorizationDegree.next_right_app_old (s : BelowDegree n) :
    D.next.right.app ((belowDegreeInclusion (Nat.le_succ n)).obj s) =
      eqToHom (CategoryTheory.Functor.congr_obj D.next_restrict s) ≫ prev.right.app s := by
  change (extendBelowTransformation D.mid D.right ≫
    eqToHom (extendBelowDiagram_ofDiagram n Y)).app
    ((belowDegreeInclusion (Nat.le_succ n)).obj s) = _
  simp only [NatTrans.comp_app, eqToHom_app, extendBelowTransformation_app_old,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- The factorization on each finite truncation obtained by iterating the degree step. -/
def reedyFactorizationBelow (f : X ⟶ Y) (P Q : MorphismProperty C) [HasFactorization P Q] :
    (n : ℕ) → ReedyFactorizationBelow f n
  | 0 => ⟨lowerDiagram 0 X, 𝟙 _, CategoryTheory.Functor.whiskerLeft (belowDegree 0).ι f,
      Category.id_comp _⟩
  | n + 1 => (chooseReedyFactorizationDegree
      (prev := reedyFactorizationBelow f P Q n) P Q).next

end

end DaggerModels.PartII
