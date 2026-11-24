import DaggerModelsPartII.JTNecklaceCylinderSimplexLift

/-!
# Reflection of reduced graph equality across a native label map
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphBoundaryReflection

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter

/-- A native map reflects membership in the ordered endpoint boundary simplexwise. -/
def ReflectsBoundary {T L : NecklaceCode} (f : T ⟶ L) : Prop :=
  ∀ (q : SimplexCategoryᵒᵖ) (x : T.toSSet.obj q),
    (∃ a : B.obj q, (endpointInclusion L).app q a = f.map.app q x) →
      ∃ a : B.obj q, (endpointInclusion T).app q a = x

/-- A monic native map reflects the ordered endpoint boundary. -/
theorem reflectsBoundary_of_mono {T L : NecklaceCode} (f : T ⟶ L)
    [Mono f.map] : ReflectsBoundary f := by
  intro q x h
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  apply (CategoryTheory.mono_iff_injective (f.map.app q)).mp
    ((NatTrans.mono_iff_mono_app f.map).mp inferInstance q)
  have hn := congrFun (NatTrans.congr_app (endpointInclusion_natural f) q) a
  exact hn.trans ha

private theorem boundary_value (T : NecklaceCode) (k : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (a : B.obj q) (u : (J.obj k).obj q) :
    ((cylinder T).app k).app q ((endpointInclusion T).app q a, u) =
      ((boundary T).app k).app q a := by
  exact congrFun (NatTrans.congr_app (isPushout T k).w q) (a, u)

/-- Equality of reduced graph maps descends along a boundary-reflecting
native label map. The source graph map need not be monic. -/
theorem graph_eq_of_reflectsBoundary {S T L : NecklaceCode} (g : S ⟶ T)
    (f : T ⟶ L) (hf : ReflectsBoundary f) (k : SimplexCategory)
    (s t : S.toSSet ⟶ J.obj k)
    (hEq : lift (g ≫ f).map s ≫ (cylinder L).app k =
      lift (g ≫ f).map t ≫ (cylinder L).app k) :
    lift g.map s ≫ (cylinder T).app k =
      lift g.map t ≫ (cylinder T).app k := by
  apply NatTrans.ext
  funext q
  induction q using Opposite.rec with | op q =>
  induction q using SimplexCategory.rec with | h d =>
    funext z
    let q := op ⦋d⦌
    have hpoint : ((cylinder L).app k).app q
        ((g ≫ f).map.app q z, s.app q z) =
        ((cylinder L).app k).app q ((g ≫ f).map.app q z, t.app q z) :=
      congrFun (NatTrans.congr_app hEq q) z
    obtain hs | ⟨a, ha⟩ :=
      JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary L k d
        ((g ≫ f).map.app q z, s.app q z)
        ((g ≫ f).map.app q z, t.app q z) hpoint
    · change s.app q z = t.app q z at hs
      change ((cylinder T).app k).app q (g.map.app q z, s.app q z) =
        ((cylinder T).app k).app q (g.map.app q z, t.app q z)
      rw [hs]
    · change (endpointInclusion L).app q a = (g ≫ f).map.app q z at ha
      have hfactor : (g ≫ f).map.app q z = f.map.app q (g.map.app q z) := rfl
      obtain ⟨b, hb⟩ := hf q (g.map.app q z) ⟨a, ha.trans hfactor⟩
      change ((cylinder T).app k).app q (g.map.app q z, s.app q z) =
        ((cylinder T).app k).app q (g.map.app q z, t.app q z)
      rw [← hb]
      exact (boundary_value T k q b (s.app q z)).trans
        (boundary_value T k q b (t.app q z)).symm

/-- The monic native-map case of graph equality reflection. -/
theorem graph_eq_of_mono {S T L : NecklaceCode} (g : S ⟶ T)
    (f : T ⟶ L) [Mono f.map] (k : SimplexCategory)
    (s t : S.toSSet ⟶ J.obj k)
    (hEq : lift (g ≫ f).map s ≫ (cylinder L).app k =
      lift (g ≫ f).map t ≫ (cylinder L).app k) :
    lift g.map s ≫ (cylinder T).app k =
      lift g.map t ≫ (cylinder T).app k :=
  graph_eq_of_reflectsBoundary g f (reflectsBoundary_of_mono f) k s t hEq

end

end DaggerModels.PartII.JTGraphBoundaryReflection
