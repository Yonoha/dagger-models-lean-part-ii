import DaggerModelsPartII.ReedyMaps

/-! Functorial relative arrows for a natural transformation of coefficient functors. -/

set_option autoImplicit false

open CategoryTheory Limits

universe v u v' u'

namespace DaggerModels.PartII

noncomputable section

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {A B : D ⥤ C} (η : A ⟶ B)

section Matching

variable [HasPullbacks C]

def relativeMatchingArrow (f : Arrow D) : Arrow C :=
  Arrow.mk (pullback.lift (η.app f.left) (A.map f.hom) (η.naturality f.hom).symm)

def relativeMatchingArrowMap {f g : Arrow D} (s : f ⟶ g) :
    relativeMatchingArrow η f ⟶ relativeMatchingArrow η g :=
  Arrow.homMk (A.map s.left)
    (pullback.map (B.map f.hom) (η.app f.right) (B.map g.hom) (η.app g.right)
      (B.map s.left) (A.map s.right) (B.map s.right)
      (by rw [← B.map_comp, ← B.map_comp, Arrow.w s])
      (η.naturality s.right).symm) (by
    apply pullback.hom_ext
    · simp [relativeMatchingArrow, Category.assoc]
    · simp [relativeMatchingArrow, Category.assoc]
      rw [← A.map_comp, ← A.map_comp, Arrow.w s])

/-- Relative matching defines a functor of arrow categories. -/
def relativeMatchingArrows : Arrow D ⥤ Arrow C where
  obj := relativeMatchingArrow η
  map := relativeMatchingArrowMap η
  map_id f := by
    apply Arrow.hom_ext
    · exact A.map_id _
    · apply pullback.hom_ext <;>
        simp [relativeMatchingArrowMap, relativeMatchingArrow]
  map_comp s t := by
    apply Arrow.hom_ext
    · exact A.map_comp _ _
    · apply pullback.hom_ext <;>
        simp [relativeMatchingArrowMap, relativeMatchingArrow, Category.assoc, A.map_comp, B.map_comp]

end Matching

section Latching

variable [HasPushouts C]

def relativeLatchingArrow (f : Arrow D) : Arrow C :=
  Arrow.mk (pushout.desc (B.map f.hom) (η.app f.right) (η.naturality f.hom).symm)

def relativeLatchingArrowMap {f g : Arrow D} (s : f ⟶ g) :
    relativeLatchingArrow η f ⟶ relativeLatchingArrow η g :=
  Arrow.homMk
    (pushout.map (η.app f.left) (A.map f.hom) (η.app g.left) (A.map g.hom)
      (B.map s.left) (A.map s.right) (A.map s.left)
      (η.naturality s.left).symm
      (by rw [← A.map_comp, ← A.map_comp, Arrow.w s]))
    (B.map s.right) (by
    apply pushout.hom_ext
    · simp only [relativeLatchingArrow, Arrow.mk_hom, Category.assoc,
        pushout.inl_desc_assoc, pushout.inl_desc]
      rw [← B.map_comp, ← B.map_comp, Arrow.w s]
    · simp [relativeLatchingArrow, Category.assoc])

/-- Relative latching defines a functor of arrow categories. -/
def relativeLatchingArrows : Arrow D ⥤ Arrow C where
  obj := relativeLatchingArrow η
  map := relativeLatchingArrowMap η
  map_id f := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext <;>
        simp [relativeLatchingArrowMap, relativeLatchingArrow]
    · exact B.map_id _
  map_comp s t := by
    apply Arrow.hom_ext
    · apply pushout.hom_ext <;>
        simp [relativeLatchingArrowMap, relativeLatchingArrow, Category.assoc, A.map_comp, B.map_comp]
    · exact B.map_comp _ _

end Latching

end

end DaggerModels.PartII
