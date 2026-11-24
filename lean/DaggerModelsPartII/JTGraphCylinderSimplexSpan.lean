import DaggerModelsPartII.JTGraphCylinderFiberDiagram
import DaggerModelsPartII.GrothendieckContractibleFibers
import NativeSimplicialReplacementCells
import Mathlib.CategoryTheory.Functor.Hom

/-! The original cylinder fibers over all maps of nerve simplices. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphCylinderSimplexSpan

open DaggerNativeSimplicialReplacementCells (first initialArrow initialArrow_id initialArrow_comp)
open JTGraphInterpolatedComparison (Fiber)
open JTGraphCylinderFiberDiagram (joint joint_source_time joint_time_source)
open JTGraphInterpolatedSourceComparison (sourceMap sourceMap_id)
open JTNecklaceEndpointCylinder (under)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

variable (C : Type) [SmallCategory C]

/-- The actual category of simplices of the nerve, with forward ordinal maps. -/
abbrev Simplices := (nerve C).Elementsᵒᵖ

/-- The time coordinate of a simplex. -/
def degree : Simplices C ⥤ SimplexCategory :=
  (CategoryOfElements.π (nerve C)).op ⋙ unopUnop SimplexCategory

private def firstMap {x y : (nerve C).Elements} (f : x ⟶ y) : first x.snd ⟶ first y.snd :=
  initialArrow f.val x.snd ≫ eqToHom (congrArg (fun z ↦ first z) f.property)

/-- The first vertex and its original native prefix arrow are contravariant in
forward maps of simplices. -/
def firstVertex : (nerve C).Elements ⥤ C where
  obj x := first x.snd
  map := firstMap C
  map_id x := by
    rcases x with ⟨q, v⟩
    change initialArrow (𝟙 q) v ≫ eqToHom _ = 𝟙 _
    rw [initialArrow_id, Category.id_comp]
    rfl
  map_comp f g := by
    rename_i x y z
    rcases x with ⟨p, u⟩
    rcases y with ⟨q, v⟩
    rcases z with ⟨r, w⟩
    rcases f with ⟨α, h⟩
    rcases g with ⟨β, h'⟩
    change p ⟶ q at α
    change q ⟶ r at β
    change (nerve C).map α u = v at h
    subst v
    change (nerve C).map β ((nerve C).map α u) = w at h'
    subst w
    change initialArrow (α ≫ β) u ≫ eqToHom _ =
      (initialArrow α u ≫ eqToHom _) ≫
        (initialArrow β ((nerve C).map α u) ≫ eqToHom _)
    simp only [eqToHom_refl, Category.comp_id]
    exact initialArrow_comp α β u

/-- Opposite category of elements of the hom-pairing on the simplex category.
Its objects are actual simplex maps, and its morphisms are their factorizations. -/
abbrev SpanIndex := (Functor.hom (Simplices C)).Elementsᵒᵖ

/-- The smaller simplex, covariant on factorizations. -/
def smaller : SpanIndex C ⥤ Simplices C where
  obj x := x.unop.fst.1.unop
  map f := f.unop.val.1.unop

/-- The larger simplex, contravariant on factorizations. -/
def larger : SpanIndex C ⥤ (Simplices C)ᵒᵖ where
  obj x := op x.unop.fst.2
  map f := f.unop.val.2.op

/-- An actual simplex map gives the corresponding object of the span index. -/
def interval {x y : Simplices C} (f : x ⟶ y) : SpanIndex C := op ⟨(op x, y), f⟩

/-- The leg to the identity span of the smaller simplex. -/
def toSmaller {x y : Simplices C} (f : x ⟶ y) : interval C f ⟶ interval C (𝟙 x) :=
  (CategoryOfElements.homMk _ _ (𝟙 (op x), f) (by
    change (𝟙 x) ≫ (𝟙 x) ≫ f = f
    rw [Category.id_comp, Category.id_comp])).op

/-- The leg to the identity span of the larger simplex. -/
def toLarger {x y : Simplices C} (f : x ⟶ y) : interval C f ⟶ interval C (𝟙 y) :=
  (CategoryOfElements.homMk _ _ (f.op, 𝟙 y) (by
    change f ≫ (𝟙 y) ≫ 𝟙 y = f
    rw [Category.id_comp, Category.comp_id])).op

variable (L : C ⥤ NecklaceCode)

/-- The native necklace at the first vertex of a simplex. -/
def firstCode : (Simplices C)ᵒᵖ ⥤ NecklaceCode :=
  unopUnop ((nerve C).Elements) ⋙ firstVertex C ⋙ L

/-- A span uses the larger simplex's first necklace and the smaller simplex's time. -/
def index : SpanIndex C ⥤ NecklaceCode × SimplexCategory :=
  (larger C ⋙ firstCode C L).prod' (smaller C ⋙ degree C)

/-- The smaller leg changes only the native source. -/
theorem toSmaller_index {x y : Simplices C} (f : x ⟶ y) :
    (index C L).map (toSmaller C f) = ((firstCode C L).map f.op, 𝟙 ((degree C).obj x)) := by
  change ((firstCode C L).map f.op, (degree C).map (𝟙 x)) = _
  rw [(degree C).map_id]

/-- The larger leg changes only the time simplex. -/
theorem toLarger_index {x y : Simplices C} (f : x ⟶ y) :
    (index C L).map (toLarger C f) = (𝟙 ((firstCode C L).obj (op y)), (degree C).map f) := by
  change ((firstCode C L).map (𝟙 (op y)), (degree C).map f) = _
  rw [(firstCode C L).map_id]

/-- The actual common source fibers form a functor over all simplex maps. -/
def fibers : SpanIndex C ⥤ Cat.{0, 0} := index C L ⋙ JTGraphCylinderFiberDiagram.diagram

private theorem map_id {X : Under JTXiEndpointCollapse.boundary} :
    CostructuredArrow.map (S := necklaceUnder) (𝟙 X) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (BoundaryNecklaceComma.diagram.map_id X)

/-- At the smaller simplex, the actual fiber leg is the source map of the prefix. -/
theorem toSmaller_fiber {x y : Simplices C} (f : x ⟶ y) :
    ((fibers C L).map (toSmaller C f)).toFunctor =
      CostructuredArrow.map (S := necklaceUnder)
        (sourceMap ((firstCode C L).map f.op) ((degree C).obj x)) := by
  change (JTGraphCylinderFiberDiagram.diagram.map ((index C L).map (toSmaller C f))).toFunctor = _
  rw [toSmaller_index]
  change joint ((firstCode C L).map f.op) (𝟙 ((degree C).obj x)) = _
  rw [joint_source_time, (under _).map_id, map_id, Functor.comp_id]

/-- At the larger simplex, the actual fiber leg is the original time map. -/
theorem toLarger_fiber {x y : Simplices C} (f : x ⟶ y) :
    ((fibers C L).map (toLarger C f)).toFunctor =
      CostructuredArrow.map (S := necklaceUnder)
        ((under ((firstCode C L).obj (op y))).map ((degree C).map f)) := by
  change (JTGraphCylinderFiberDiagram.diagram.map ((index C L).map (toLarger C f))).toFunctor = _
  rw [toLarger_index]
  change joint (𝟙 ((firstCode C L).obj (op y))) ((degree C).map f) = _
  rw [joint_time_source, sourceMap_id, map_id, Functor.comp_id]

/-- The full Grothendieck category of these original fibers maps by a Kan weak
nerve equivalence to the category of actual simplex-map factorizations. -/
theorem projection_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (fibers C L))) :=
  GrothendieckContractibleFibers.projection_weak (fibers C L) fun x ↦
    JTHomotopyTargetComma.fiber_point_GW_at ((index C L).obj x).1 ((index C L).obj x).2

end

end DaggerModels.PartII.JTGraphCylinderSimplexSpan
