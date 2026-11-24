import DaggerModelsPartII.CosimplicialMappingInvariance
import Mathlib.CategoryTheory.Yoneda

/-!
# Weak invariance of strict Hom simplicial sets of Reedy frames

The original native mapping functor uses opposite-category morphisms.
The native coyoneda/yoneda isomorphism identifies it with plain Hom sets.
Brown preservation therefore applies to the actual strict Hom simplicial
sets of any weak map between Reedy fibrant opposite frames.
-/

set_option autoImplicit false
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

universe v u
namespace DaggerModels.PartII.StrictFrameMappingWeak

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- The actual plain Hom simplicial set of an opposite cosimplicial diagram. -/
def strictMapping (Z : C) : (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) ⥤ SSet.{v} :=
  (Functor.whiskeringRight _ _ _).obj (yoneda.obj Z)

/-- The native opposite-morphism mapping functor is naturally plain Hom. -/
def nativeStrictIso (Z : C) :
    CosimplicialResolution.mappingFromOppositeDiagram Z ≅ strictMapping Z :=
  (Functor.whiskeringRight _ _ _).mapIso (Coyoneda.objOpOp Z)

/-- A Reedy weak map between Reedy fibrant opposite frames induces a Kan
weak map on their literal Hom simplicial sets into every fibrant target. -/
theorem strictMapping_map_weak (Z : C) [IsFibrant Z]
    {D E : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} [IsFibrant D] [IsFibrant E]
    (g : D ⟶ E) (hg : weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) g) :
    weakEquivalences SSet.{v} ((strictMapping Z).map g) := by
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  have h : weakEquivalences SSet.{v} (F.map g) :=
    map_weak_of_trivialFibration F
      (fun p hp ↦ (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration
        Z p hp).2) g hg
  let e := nativeStrictIso Z
  let ea : Arrow.mk (F.map g) ≅ Arrow.mk ((strictMapping Z).map g) :=
    Arrow.isoMk (e.app D) (e.app E) (e.hom.naturality g).symm
  exact ((weakEquivalences SSet.{v}).arrow_mk_iso_iff ea).1 h

end

end DaggerModels.PartII.StrictFrameMappingWeak
