import DaggerModelsPartII.JTRowGraphCategory
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The category of all coefficient presentations of one actual raw simplex
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphFiber

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphParameterSupport JTRowGraphNormalForm
open DaggerOriginalFlagFlankification (nerveDiscreteIso)

noncomputable section

variable {W : BiPresheaf} {d : SimplexCategory}
variable (q : SSet.stdSimplex.{0}.obj d ⟶ realization.obj W)

/-- The exact fixed-raw-value condition on the original graph category. -/
def fixed : ObjectProperty (Graph W d) := fun G ↦ G.value = q

abbrev Fiber := (fixed q).FullSubcategory

/-- The normalization support stays over the same entire raw simplex. -/
def supportAt : Fiber q ⥤ Fiber q where
  obj G := ⟨support G.obj, (support_step G.obj).value_eq.trans G.property⟩
  map f := ⟨supportArrow f.hom⟩
  map_id G := InducedCategory.hom_ext
    ((supportFunctor W d).map_id G.obj)
  map_comp f g := InducedCategory.hom_ext
    ((supportFunctor W d).map_comp f.hom g.hom)

/-- The actual ordinal support inclusion inside the fixed-value category. -/
def inclusionAt : supportAt q ⟶ 𝟭 (Fiber q) where
  app G := ⟨(supportInclusion W d).app G.obj⟩
  naturality _ _ f := InducedCategory.hom_ext
    ((supportInclusion W d).naturality f.hom)

/-- The same normal form is a graph over the exact raw map. -/
def center : Fiber q := ⟨canonical q, canonical_value q⟩

/-- All support reductions compare naturally to that one normal form. -/
def reductionAt : supportAt q ⟶ (Functor.const (Fiber q)).obj (center q) where
  app G := ⟨supportToNormal G.obj ≫ eqToHom
    ((normal_eq_canonical G.obj).trans (congrArg canonical G.property))⟩
  naturality G _ _ := by
    apply InducedCategory.hom_ext
    apply hom_ext_of_label_surjective
    exact source_vertex_surjective G.obj.parameter

/-- All coefficient presentations of the same raw simplex have weakly
contractible nerve, with both homotopies induced by actual arrows. -/
theorem point_GW : GW (pointMap (nerve (Fiber q))) := by
  let F : Fiber q ⥤ Discrete PUnit.{1} := (Functor.const _).obj ⟨PUnit.unit⟩
  let G : Discrete PUnit.{1} ⥤ Fiber q := (Functor.const _).obj (center q)
  let hR : supportAt q ⟶ F ⋙ G :=
    { app P := (reductionAt q).app P
      naturality _ _ f := (reductionAt q).naturality f }
  let hG : G ⋙ F ⟶ 𝟭 (Discrete PUnit.{1}) :=
    { app P := eqToHom (Subsingleton.elim _ P)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have hC : DaggerNerveHomotopy.NatTransZigzag (F ⋙ G) (𝟭 (Fiber q)) :=
    .trans _ (supportAt q) _ (.symm _ _ (.rel _ _ ⟨hR⟩)) (.rel _ _ ⟨inclusionAt q⟩)
  haveI : WeakEquivalence (nerveMap F) := (weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW F G hC (.rel _ _ ⟨hG⟩))
  have he : nerveMap F ≫ (nerveDiscreteIso PUnit.{1}).hom = pointMap (nerve (Fiber q)) :=
    pointIsTerminal.hom_ext _ _
  rw [← he]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTRowGraphFiber
