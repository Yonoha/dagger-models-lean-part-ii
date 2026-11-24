import DaggerModelsPartII.SimplicialResolutionFunctor
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! The simplex operators of a covariant simplicial diagram, with ordinary positive
simplex operators within each Grothendieck fiber. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTParametrizedProductSimplices

noncomputable section

variable {A : Type} [SmallCategory A] (X : A ⥤ SSet.{0})

private abbrev fibers := X ⋙ SimplicialResolutionFunctor.elementsOpposite

/-- An object chooses an entire simplex on a fiber of the covariant diagram. -/
abbrev Index := Grothendieck (fibers X)

abbrev base : Index X ⥤ A := Grothendieck.forget (fibers X)

private theorem eqToHom_degree {Y : SSet.{0}} {P Q : Y.Elements} (h : P = Q) :
    (eqToHom h : P ⟶ Q).val.unop =
      eqToHom (congrArg (fun p : Y.Elements ↦ p.1.unop) h.symm) := by
  cases h
  rfl

/-- Positive simplex degree and operator, with the full base morphism retained separately. -/
def degree : Index X ⥤ SimplexCategory where
  obj P := P.fiber.unop.1.unop
  map f := f.fiber.unop.val.unop
  map_id P := by
    rw [Grothendieck.id_fiber, eqToHom_unop, eqToHom_degree]
    rfl
  map_comp {P Q R} f g := by
    rw [Grothendieck.comp_fiber, unop_comp, unop_comp, eqToHom_unop]
    change ((CategoryOfElements.π (X.obj R.base)).map (_ ≫ _ ≫ _)).unop = _
    rw [Functor.map_comp, Functor.map_comp, unop_comp, unop_comp]
    let u : P.fiber.unop.1.unop ⟶ Q.fiber.unop.1.unop := f.fiber.unop.val.unop
    let v : Q.fiber.unop.1.unop ⟶ R.fiber.unop.1.unop := g.fiber.unop.val.unop
    rw [eqToHom_map, eqToHom_unop]
    change (𝟙 P.fiber.unop.1.unop ≫ u) ≫ v = u ≫ v
    rw [Category.id_comp]

private abbrev std := SSet.stdSimplex.{0}

/-- The actual simplex in the chosen diagram value. -/
def simplex (P : Index X) : std.obj ((degree X).obj P) ⟶ X.obj P.base :=
  SSet.yonedaEquiv.symm P.fiber.unop.2

/-- Moving in the covariant base commutes with the positive simplex restriction. -/
theorem simplex_natural {P Q : Index X} (f : P ⟶ Q) :
    simplex X P ≫ X.map f.base = std.map ((degree X).map f) ≫ simplex X Q := by
  apply SSet.yonedaEquiv.injective
  unfold simplex
  rw [SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_comp]
  simp only [Equiv.apply_symm_apply]
  exact f.fiber.unop.property.symm

end
end DaggerModels.PartII.JTParametrizedProductSimplices
