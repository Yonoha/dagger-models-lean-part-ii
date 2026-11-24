import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Colimits of a functorial cobase with a fixed target boundary

A pointwise pushout of two colimit-preserving functors along a natural map
to a fixed object preserves colimits when regarded in the undercategory.
This includes empty and disconnected diagrams; no preservation of colimits
by the fixed-object constant functor is assumed.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace DaggerModels.PartII.CobaseFunctorColimits

noncomputable section

variable {C : Type u₁} {D : Type u₂} {J : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} J]
  {F G : C ⥤ D} (u : F ⟶ G) (A : D)
  (a : F ⟶ (Functor.const C).obj A) (R : C ⥤ Under A)
  (b : G ⟶ R ⋙ Under.forget A)
  (hp : ∀ X : C, IsPushout (u.app X) (a.app X) (b.app X) (R.obj X).hom)
  {K : J ⥤ C} {c : Cocone K} (hc : IsColimit c)
  [PreservesColimit K F] [PreservesColimit K G]

private def totalCocone (t : Cocone (K ⋙ R)) : Cocone (K ⋙ G) where
  pt := t.pt.right
  ι := {
    app := fun j ↦ b.app (K.obj j) ≫ (t.ι.app j).right
    naturality := by
      intro j k f
      change G.map (K.map f) ≫ b.app (K.obj k) ≫ (t.ι.app k).right =
        (b.app (K.obj j) ≫ (t.ι.app j).right) ≫ 𝟙 _
      rw [Category.comp_id, ← Category.assoc, b.naturality, Category.assoc]
      exact congrArg (fun h ↦ b.app (K.obj j) ≫ h.right) (t.w f) }

private def totalDesc (t : Cocone (K ⋙ R)) : G.obj c.pt ⟶ t.pt.right :=
  (isColimitOfPreserves G hc).desc (totalCocone A R b t)

private theorem totalDesc_fac (t : Cocone (K ⋙ R)) (j : J) :
    G.map (c.ι.app j) ≫ totalDesc A R b hc t =
      b.app (K.obj j) ≫ (t.ι.app j).right :=
  (isColimitOfPreserves G hc).fac (totalCocone A R b t) j

include hp in
private theorem totalDesc_compatibility (t : Cocone (K ⋙ R)) :
    u.app c.pt ≫ totalDesc A R b hc t = a.app c.pt ≫ t.pt.hom := by
  apply (isColimitOfPreserves F hc).hom_ext
  intro j
  change F.map (c.ι.app j) ≫ (u.app c.pt ≫ totalDesc A R b hc t) =
    F.map (c.ι.app j) ≫ (a.app c.pt ≫ t.pt.hom)
  calc
    _ = u.app (K.obj j) ≫ G.map (c.ι.app j) ≫ totalDesc A R b hc t := by
      have hu : F.map (c.ι.app j) ≫ u.app c.pt =
          u.app (K.obj j) ≫ G.map (c.ι.app j) := u.naturality (c.ι.app j)
      rw [← Category.assoc, hu, Category.assoc]
    _ = u.app (K.obj j) ≫ b.app (K.obj j) ≫ (t.ι.app j).right := by
      rw [totalDesc_fac]
    _ = a.app (K.obj j) ≫ (R.obj (K.obj j)).hom ≫ (t.ι.app j).right := by
      rw [← Category.assoc, (hp (K.obj j)).w, Category.assoc]
    _ = a.app (K.obj j) ≫ t.pt.hom := by
      rw [Under.w]
      rfl
    _ = _ := by
      have ha := a.naturality (c.ι.app j)
      change F.map (c.ι.app j) ≫ a.app c.pt = a.app (K.obj j) ≫ 𝟙 A at ha
      have ha' : F.map (c.ι.app j) ≫ a.app c.pt = a.app (K.obj j) :=
        ha.trans (Category.comp_id _)
      rw [← Category.assoc, ha']

private def desc (t : Cocone (K ⋙ R)) : R.obj c.pt ⟶ t.pt :=
  Under.homMk ((hp c.pt).desc (totalDesc A R b hc t) t.pt.hom
    (totalDesc_compatibility u A a R b hp hc t))
    ((hp c.pt).inr_desc _ _ _)

private theorem desc_fac (t : Cocone (K ⋙ R)) (j : J) :
    R.map (c.ι.app j) ≫ desc u A a R b hp hc t = t.ι.app j := by
  apply Under.UnderMorphism.ext
  apply (hp (K.obj j)).hom_ext
  · change b.app (K.obj j) ≫ (R.map (c.ι.app j)).right ≫
        (hp c.pt).desc _ _ _ = b.app (K.obj j) ≫ (t.ι.app j).right
    have hb : G.map (c.ι.app j) ≫ b.app c.pt =
        b.app (K.obj j) ≫ (R.map (c.ι.app j)).right := b.naturality (c.ι.app j)
    rw [← Category.assoc, ← hb, Category.assoc,
      (hp c.pt).inl_desc, totalDesc_fac]
  · change (R.obj (K.obj j)).hom ≫ (R.map (c.ι.app j)).right ≫
        (desc u A a R b hp hc t).right =
      (R.obj (K.obj j)).hom ≫ (t.ι.app j).right
    rw [← Category.assoc, Under.w, Under.w, Under.w]
    rfl

/-- The mapped cocone is colimiting when both moving legs preserve the
original colimit; the fixed boundary is retained as undercategory data. -/
def mapCoconeIsColimit : IsColimit (R.mapCocone c) where
  desc := desc u A a R b hp hc
  fac := desc_fac u A a R b hp hc
  uniq := by
    intro t m hm
    apply Under.UnderMorphism.ext
    apply (hp c.pt).hom_ext
    · change b.app c.pt ≫ m.right = b.app c.pt ≫ (hp c.pt).desc _ _ _
      rw [(hp c.pt).inl_desc]
      apply (isColimitOfPreserves G hc).hom_ext
      intro j
      change G.map (c.ι.app j) ≫ (b.app c.pt ≫ m.right) =
        G.map (c.ι.app j) ≫ totalDesc A R b hc t
      have hb : G.map (c.ι.app j) ≫ b.app c.pt =
          b.app (K.obj j) ≫ (R.map (c.ι.app j)).right := b.naturality (c.ι.app j)
      rw [← Category.assoc, hb, Category.assoc, totalDesc_fac]
      exact congrArg (fun h ↦ b.app (K.obj j) ≫ h.right) (hm j)
    · exact (Under.w m).trans (Under.w (desc u A a R b hp hc t)).symm

include u a b hp in
/-- Pointwise pushouts into a fixed undercategory preserve any colimit
preserved by the two moving functors. -/
theorem preservesColimit [HasColimit K] : PreservesColimit K R :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit K)
    (mapCoconeIsColimit u A a R b hp (colimit.isColimit K))

end

end DaggerModels.PartII.CobaseFunctorColimits
