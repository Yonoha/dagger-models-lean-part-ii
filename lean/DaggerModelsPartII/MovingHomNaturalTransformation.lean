import OriginalOrdinaryMovingHomDiagramReconciled

/-!
# Natural maps of the original moving-endpoint Hom diagrams

The original enriched maps and both endpoint transports are retained. This is
the natural-transformation counterpart of the existing `homCocone` construction.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe u

namespace DaggerModels.PartII.MovingHomNaturalTransformation

open OriginalOrdinaryMovingHomColimits

noncomputable section

variable {J : Type u} [SmallCategory J]
variable {F G : J ⥤ SimplicialCat.{u, u}}
variable (s t : ∀ j : J, (F.obj j).Obj)
variable (hs : ∀ {j k} (f : j ⟶ k), (F.map f).obj (s j) = s k)
variable (ht : ∀ {j k} (f : j ⟶ k), (F.map f).obj (t j) = t k)
variable (s' t' : ∀ j : J, (G.obj j).Obj)
variable (hs' : ∀ {j k} (f : j ⟶ k), (G.map f).obj (s' j) = s' k)
variable (ht' : ∀ {j k} (f : j ⟶ k), (G.map f).obj (t' j) = t' k)
variable (α : F ⟶ G)
variable (hx : ∀ j, (α.app j).obj (s j) = s' j)
variable (hy : ∀ j, (α.app j).obj (t j) = t' j)

/-- A natural transformation of original full functors induces a natural
transformation of their original Homs with both endpoints transported. -/
def homNatTrans : homDiagram F s t hs ht ⟶ homDiagram G s' t' hs' ht' where
  app j := castMap (α.app j) (s j) (t j) (s' j) (t' j) (hx j) (hy j)
  naturality {j k} f := by
    change castMap (F.map f) (s j) (t j) (s k) (t k) (hs f) (ht f) ≫
        castMap (α.app k) (s k) (t k) (s' k) (t' k) (hx k) (hy k) =
      castMap (α.app j) (s j) (t j) (s' j) (t' j) (hx j) (hy j) ≫
        castMap (G.map f) (s' j) (t' j) (s' k) (t' k) (hs' f) (ht' f)
    rw [← castMap_comp (F.map f) (α.app k) (s j) (t j) (s k) (t k)
      (s' k) (t' k) (hs f) (ht f) (hx k) (hy k)]
    rw [← castMap_comp (α.app j) (G.map f) (s j) (t j) (s' j) (t' j)
      (s' k) (t' k) (hx j) (hy j) (hs' f) (ht' f)]
    exact castMap_congr (α.naturality f) (s j) (t j) (s' k) (t' k) _ _ _ _

end

end DaggerModels.PartII.MovingHomNaturalTransformation
