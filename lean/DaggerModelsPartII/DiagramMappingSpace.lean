import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! The literal simplicial mapping space of simplicial-set diagrams. -/

set_option autoImplicit false

open CategoryTheory MonoidalCategory Opposite

universe u t v

namespace DaggerModels.PartII

variable {C : Type t} [Category.{v} C]

/-- Tensor a fixed diagram levelwise with a variable simplicial set. -/
def diagramTensor (A : C ⥤ SSet.{u}) : SSet.{u} ⥤ (C ⥤ SSet.{u}) where
  obj K := A ⋙ tensorRight K
  map f := {
    app c := A.obj c ◁ f
    naturality c d g := whisker_exchange (A.map g) f }
  map_id K := by
    apply NatTrans.ext
    funext c
    exact MonoidalCategory.whiskerLeft_id (A.obj c) K
  map_comp f g := by
    apply NatTrans.ext
    funext c
    exact MonoidalCategory.whiskerLeft_comp _ f g

/-- An `n`-simplex is a natural transformation `A × Δ[n] ⟶ W`. -/
def diagramMappingSpace (A W : C ⥤ SSet.{u}) : SSet.{max t u} :=
  SSet.stdSimplex.op ⋙ (diagramTensor A).op ⋙ yoneda.obj W

/-- Precomposition on the actual simplicial mapping spaces of diagrams. -/
def diagramMappingPrecomp {A B : C ⥤ SSet.{u}} (f : A ⟶ B) (W : C ⥤ SSet.{u}) :
    diagramMappingSpace B W ⟶ diagramMappingSpace A W where
  app n η := Functor.whiskerRight f (tensorRight (SSet.stdSimplex.obj n.unop)) ≫ η
  naturality {m n} g := by
    funext η
    apply NatTrans.ext
    funext c
    change (A.obj c ◁ SSet.stdSimplex.map g.unop) ≫
      ((f.app c ▷ SSet.stdSimplex.obj m.unop) ≫ η.app c) =
      (f.app c ▷ SSet.stdSimplex.obj n.unop) ≫
        ((B.obj c ◁ SSet.stdSimplex.map g.unop) ≫ η.app c)
    rw [← Category.assoc, ← Category.assoc, whisker_exchange]

/-- Postcomposition on the same simplicial mapping spaces. -/
def diagramMappingPostcomp (A : C ⥤ SSet.{u}) {W W' : C ⥤ SSet.{u}} (f : W ⟶ W') :
    diagramMappingSpace A W ⟶ diagramMappingSpace A W' :=
  Functor.whiskerLeft (SSet.stdSimplex.op ⋙ (diagramTensor A).op) (yoneda.map f)

@[simp]
theorem diagramMappingPrecomp_id (A W : C ⥤ SSet.{u}) :
    diagramMappingPrecomp (𝟙 A) W = 𝟙 (diagramMappingSpace A W) := by
  apply NatTrans.ext
  funext n η
  simp only [diagramMappingPrecomp]
  rfl

@[simp]
theorem diagramMappingPrecomp_comp {A B D : C ⥤ SSet.{u}}
    (f : A ⟶ B) (g : B ⟶ D) (W : C ⥤ SSet.{u}) :
    diagramMappingPrecomp (f ≫ g) W =
      diagramMappingPrecomp g W ≫ diagramMappingPrecomp f W := by
  apply NatTrans.ext
  funext n η
  simp only [diagramMappingPrecomp, Functor.whiskerRight_comp, Category.assoc]
  rfl

end DaggerModels.PartII
