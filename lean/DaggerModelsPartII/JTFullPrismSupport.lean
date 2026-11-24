import DaggerModelsPartII.JTPrismRectangle
import DaggerModelsPartII.JTJointRelativeParameters

/-! The used coefficient vertices support the entire map on a bead prism. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTPrismRectangle

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTRowGraphParameterSupport
open JTCodiscreteParameterPairing (coord coord_map)
open JTJointRelativeParameters (parameter_ext)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev prism (d t : SimplexCategory) := std.obj d ⊗ J.obj t
private abbrev supportedDegree {d t k : SimplexCategory} (p : prism d t ⟶ J.obj k) :=
  supportOrdinal (sample d t ≫ p)
private abbrev supportInclusion {d t k : SimplexCategory} (p : prism d t ⟶ J.obj k) :=
  inclusion (sample d t ≫ p)

variable {d t k : SimplexCategory} (p : prism d t ⟶ J.obj k)

private def usedVertex (u : (prism d t).obj zero) : used (sample d t ≫ p) :=
  ⟨vertexLabels (parameterCodiscreteIso.app k).hom (p.app zero u), by
    have hu : _ ∈ Set.range (fun x ↦
        vertexLabels (parameterCodiscreteIso.app k).hom (p.app zero x)) := ⟨u, rfl⟩
    rwa [← used_sample_eq_range d t p] at hu⟩

private def supportedLabels (u : (prism d t).obj zero) : Fin ((supportedDegree p).len + 1) :=
  (supportOrderIso (sample d t ≫ p)).symm (usedVertex p u)

/-- Restrict the actual whole prism, in every degree, to the ordinal of its used vertices. -/
def supportedParameter : prism d t ⟶ J.obj (supportedDegree p) :=
  mapOfVertices _ (supportedLabels p) ≫ (parameterCodiscreteIso.app (supportedDegree p)).inv

private theorem supportedParameter_label (u : (prism d t).obj zero) :
    coord (supportedDegree p) zero ((supportedParameter p).app zero u) 0 =
      supportedLabels p u := by
  have h : supportedParameter p ≫ (parameterCodiscreteIso.app (supportedDegree p)).hom =
      mapOfVertices (prism d t) (supportedLabels p) := by
    rw [supportedParameter, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have f := congrFun (NatTrans.congr_app h zero) u
  have g := congrArg (fun Z ↦ (Z.obj (0 : Fin 1)).as) f
  change _ = supportedLabels p
    ((prism d t).map ((⦋0⦌ : SimplexCategory).const (⦋0⦌ : SimplexCategory) 0).op u) at g
  have hid : (⦋0⦌ : SimplexCategory).const (⦋0⦌ : SimplexCategory) 0 = 𝟙 ⦋0⦌ :=
    SimplexCategory.isTerminalZero.hom_ext _ _
  rw [hid, op_id] at g
  rw [(prism d t).map_id zero] at g
  exact g

/-- The supported prism recovers the original map, on all simplices. -/
theorem supportedParameter_factor :
    supportedParameter p ≫ J.map (supportInclusion p) = p := by
  apply parameter_ext
  intro u
  change coord k zero ((J.map (supportInclusion p)).app zero ((supportedParameter p).app zero u))
    0 = _
  rw [coord_map, supportedParameter_label]
  exact congrArg Subtype.val ((supportOrderIso (sample d t ≫ p)).apply_symm_apply (usedVertex p u))

private theorem cancel_parameterMap {X : SSet.{0}}
    {f g : X ⟶ J.obj (supportedDegree p)}
    (h : f ≫ J.map (supportInclusion p) = g ≫ J.map (supportInclusion p)) : f = g := by
  apply parameter_ext
  intro u
  apply inclusion_injective (sample d t ≫ p)
  have h' := congrFun (NatTrans.congr_app h zero) u
  have he := congrArg (fun v ↦ coord k zero v 0) h'
  exact (coord_map (supportInclusion p) zero _ _).symm.trans
    (he.trans (coord_map (supportInclusion p) zero _ _))

section Change

variable {d' t' k' : SimplexCategory} (q : prism d' t' ⟶ J.obj k')
variable (g : prism d t ⟶ prism d' t') (b : k ⟶ k') (h : g ≫ q = p ≫ J.map b)

include h in
private theorem image_mem_support (u : Fin ((supportedDegree p).len + 1)) :
    b.toOrderHom ((supportInclusion p).toOrderHom u) ∈ used (sample d' t' ≫ q) := by
  have hi : (supportInclusion p).toOrderHom u ∈ used (sample d t ≫ p) :=
    ((supportOrderIso (sample d t ≫ p)) u).property
  rw [← Finset.mem_coe, used_sample_eq_range] at hi ⊢
  obtain ⟨x, hx⟩ := hi
  refine ⟨g.app zero x, ?_⟩
  have he := congrFun (NatTrans.congr_app h zero) x
  change q.app zero (g.app zero x) = (J.map b).app zero (p.app zero x) at he
  change coord k' zero (q.app zero (g.app zero x)) 0 = _
  change coord k zero (p.app zero x) 0 = _ at hx
  rw [he, coord_map, hx]

/-- A compatible prism map induces the original coefficient operator on
precisely the used vertices, without a choice of a comparison of samples. -/
def supportMap : supportedDegree p ⟶ supportedDegree q :=
  SimplexCategory.Hom.mk
    ⟨fun u ↦ (supportOrderIso (sample d' t' ≫ q)).symm
      ⟨b.toOrderHom ((supportInclusion p).toOrderHom u), image_mem_support p q g b h u⟩,
    fun _ _ hu ↦ (supportOrderIso (sample d' t' ≫ q)).symm.monotone
      (b.toOrderHom.monotone ((supportInclusion p).toOrderHom.monotone hu))⟩

theorem supportMap_inclusion :
    supportMap p q g b h ≫ supportInclusion q = supportInclusion p ≫ b := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext u
  let a : used (sample d' t' ≫ q) :=
    ⟨b.toOrderHom ((supportInclusion p).toOrderHom u), image_mem_support p q g b h u⟩
  exact congrArg Subtype.val ((supportOrderIso (sample d' t' ≫ q)).apply_symm_apply a)

include h in
/-- Restricting to the used vertices preserves the complete parameter square. -/
theorem supportedParameter_natural :
    g ≫ supportedParameter q = supportedParameter p ≫ J.map (supportMap p q g b h) := by
  apply cancel_parameterMap q
  rw [Category.assoc, supportedParameter_factor, Category.assoc, ← J.map_comp,
    supportMap_inclusion, J.map_comp, ← Category.assoc, supportedParameter_factor]
  exact h

end Change

end

end DaggerModels.PartII.JTPrismRectangle
