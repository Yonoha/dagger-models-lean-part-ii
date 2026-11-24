import DaggerModelsPartII.JTRowGraphHorizontalSupport
import DaggerModelsPartII.JTCodiscreteParameterPairing
import ChosenNecklaceMapInclusion

/-!
# Used-vertex support for arbitrary native necklaces

A codiscrete parameter extends uniquely to the ambient simplex because the
necklace contains every vertex. Thus the existing two-operator support
comparison applies to multi-bead necklaces and to the point.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.JTNecklaceParameterSupport

open JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev iso (k : SimplexCategory) := GroupoidSimplex.parameterCodiscreteIso.app k
private abbrev Δ (T : NecklaceCode) := SSet.stdSimplex.{0}.obj ⦋T.len⦌

variable {T U : NecklaceCode} {k l : SimplexCategory}

private theorem inclusion_surjective :
    Function.Surjective (T.inclusion.app (op ⦋0⦌) : T.toSSet.obj (op ⦋0⦌) →
      (Δ T).obj (op ⦋0⦌)) := by
  intro v
  let w : NecklaceCode.Vertices.{0} T := ULift.up (SSet.stdSimplex.obj₀Equiv v)
  refine ⟨T.verticesEquiv.symm w, SSet.stdSimplex.obj₀Equiv.injective ?_⟩
  exact T.inclusion_vertex w

/-- A parameter map out of the ambient simplex is determined by its restriction. -/
theorem inclusion_injective {s t : Δ T ⟶ J.obj k}
    (h : T.inclusion ≫ s = T.inclusion ≫ t) : s = t := by
  have hv (z : (Δ T).obj (op ⦋0⦌)) : s.app (op ⦋0⦌) z = t.app (op ⦋0⦌) z := by
    obtain ⟨v, rfl⟩ := inclusion_surjective (T := T) z
    exact congrFun (NatTrans.congr_app h (op ⦋0⦌)) v
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let i := (iso k).hom
  change (((s ≫ i).app q z).obj v).as = (((t ≫ i).app q z).obj v).as
  rw [← vertexLabels_natural (s ≫ i) q z v, ← vertexLabels_natural (t ≫ i) q z v]
  change vertexLabels i (s.app (op ⦋0⦌) _) = vertexLabels i (t.app (op ⦋0⦌) _)
  rw [hv]

/-- Extend the unchanged parameter across the native inclusion in the ambient simplex. -/
def ambient (s : T.toSSet ⟶ J.obj k) : Δ T ⟶ J.obj k := by
  letI : Nonempty (GroupoidSimplex.vertices.obj k) := ⟨(0 : Fin (k.len + 1))⟩
  exact extension T.inclusion (s ≫ (iso k).hom) ≫ (iso k).inv

theorem inclusion_ambient (s : T.toSSet ⟶ J.obj k) : T.inclusion ≫ ambient s = s := by
  letI : Nonempty (GroupoidSimplex.vertices.obj k) := ⟨(0 : Fin (k.len + 1))⟩
  rw [ambient, ← Category.assoc, extension_spec, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The simplex operator of the full original native necklace map. -/
abbrev ordinal (u : T ⟶ U) : ⦋T.len⦌ ⟶ ⦋U.len⦌ :=
  SimplexCategory.Hom.mk (NecklaceCode.orderMap (NecklaceCode.Hom.map.{0} u))

/-- Mixed equations extend to the entire ambient simplex of each necklace. -/
theorem ambient_mixed (u : T ⟶ U) (b : k ⟶ l)
    {s : T.toSSet ⟶ J.obj k} {t : U.toSSet ⟶ J.obj l}
    (h : s ≫ J.map b = u.map ≫ t) :
    ambient s ≫ J.map b = SSet.stdSimplex.map (ordinal u) ≫ ambient t := by
  apply inclusion_injective (T := T)
  rw [← Category.assoc, inclusion_ambient, ← Category.assoc, ← NecklaceCode.map_inclusion,
    Category.assoc, inclusion_ambient, h]

/-- The original parameter is restricted to the used ordinal on the same necklace. -/
def supportedParameter (s : T.toSSet ⟶ J.obj k) :
    T.toSSet ⟶ J.obj (supportOrdinal (ambient s)) :=
  T.inclusion ≫ source (ambient s)

theorem supportedParameter_factor (s : T.toSSet ⟶ J.obj k) :
    supportedParameter s ≫ J.map (inclusion (ambient s)) = s := by
  rw [supportedParameter, Category.assoc, source_factor, inclusion_ambient]

/-- The simultaneous support operator obeys the full mixed equation on the
original, possibly multi-bead, source. -/
theorem supportedParameter_mixed (u : T ⟶ U) (b : k ⟶ l)
    {s : T.toSSet ⟶ J.obj k} {t : U.toSSet ⟶ J.obj l}
    (h : s ≫ J.map b = u.map ≫ t) :
    supportedParameter s ≫ J.map
      (JTRowGraphHorizontalSupport.operator (ordinal u) b (ambient_mixed u b h)) =
        u.map ≫ supportedParameter t := by
  rw [supportedParameter, supportedParameter, Category.assoc,
    JTRowGraphHorizontalSupport.operator_parameter, ← Category.assoc,
    ← NecklaceCode.map_inclusion, Category.assoc]

end

end DaggerModels.PartII.JTNecklaceParameterSupport
