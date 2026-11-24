import DaggerModelsPartII.JTGraphParameterSourceRestriction
import DaggerModelsPartII.JTVertexAssignmentCover

/-!
# Natural extensions preserving exact graph maps

Patch a natural coefficient trace along the overlap of changing source complexes.
The reduced-cylinder graphs are unchanged if the trace agrees at the overlap
vertices incident to non-boundary simplices.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTExactGraphRelativeExtension

open JTGraphParameterSourceRestriction (RigidVertex exact_parameter_graph_eq_iff)
open JTJointRelativeParameters (parameter_ext extend extend_away restrict_extend)
open JTNecklaceEndpointCylinder (cylinder)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)

/-- Taking the image of a rigid vertex under a source map preserves rigidity
when both native maps land in the same necklace. -/
theorem rigidVertex_map {X Y : SSet.{0}} (T : NecklaceCode)
    (g : X ⟶ Y) (f : Y ⟶ T.toSSet) (x : X.obj zero) :
    RigidVertex T (g ≫ f) x → RigidVertex T f (g.app zero x) := by
  rintro ⟨d, z, v, hn, hv⟩
  refine ⟨d, z ≫ g, v, ?_, ?_⟩
  · simpa only [Category.assoc] using hn
  · rw [← Category.assoc, SSet.yonedaEquiv_comp, hv]

/-- Agreement on all rigid vertices suffices to preserve the entire
reduced-cylinder graph. -/
theorem exact_graph_of_rigid_agreement {X : SSet.{0}} (T : NecklaceCode)
    (k : SimplexCategory) (f : X ⟶ T.toSSet) (s t : X ⟶ J.obj k)
    (h : ∀ x : X.obj zero, RigidVertex T f x →
      coord k zero (s.app zero x) 0 = coord k zero (t.app zero x) 0) :
    lift f s ≫ (cylinder T).app k = lift f t ≫ (cylinder T).app k := by
  apply (exact_parameter_graph_eq_iff T k f s t).2
  intro d z hn
  apply parameter_ext
  intro x
  let v : Δ[0] ⟶ (Δ[d] : SSet.{0}) := SSet.yonedaEquiv.symm x
  have hv : SSet.yonedaEquiv (v ≫ z) = z.app zero x := by
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  exact h _ ⟨d, z, v, hn, hv⟩

section Diagram

variable {I : Type} [SmallCategory I] {M X : I ⥤ SSet.{0}}
variable (a : M ⟶ X) {k : I ⥤ SimplexCategory}
variable (trace : M ⟶ k ⋙ J) (reference : X ⟶ k ⋙ J)
variable (injective : ∀ p, Function.Injective ((a.app p).app zero))
variable (reflects : ∀ {p q : I} (f : p ⟶ q) (v : (X.obj p).obj zero),
  (X.map f).app zero v ∈ Set.range ((a.app q).app zero) →
    v ∈ Set.range ((a.app p).app zero))

/-- The functorial patch of a trace along a vertex-reflecting subdiagram
preserves the exact side graph whenever the overlap trace agrees on the
ambient side's rigid vertices. -/
theorem extend_preserves_graph (p : I) (T : NecklaceCode) (f : X.obj p ⟶ T.toSSet)
    (h : ∀ u : (M.obj p).obj zero, RigidVertex T f ((a.app p).app zero u) →
      coord (k.obj p) zero ((trace.app p).app zero u) 0 =
        coord (k.obj p) zero ((reference.app p).app zero ((a.app p).app zero u)) 0) :
    lift f ((extend a trace reference injective reflects).app p) ≫ (cylinder T).app (k.obj p) =
      lift f (reference.app p) ≫ (cylinder T).app (k.obj p) := by
  apply exact_graph_of_rigid_agreement
  intro x hx
  by_cases hmem : x ∈ Set.range ((a.app p).app zero)
  · obtain ⟨u, rfl⟩ := hmem
    have hu := congrFun (NatTrans.congr_app
      (NatTrans.congr_app (restrict_extend a trace reference injective reflects) p) zero) u
    change ((extend a trace reference injective reflects).app p).app zero
      ((a.app p).app zero u) = (trace.app p).app zero u at hu
    rw [hu]
    exact h u hx
  · exact extend_away a trace reference injective reflects p x hmem

end Diagram

section Cover

open JTVertexAssignmentCover (cover projection trace_allowed projection_trivialFibration
  extendAllowed extendAllowed_mapsTo)

variable {I : Type} [SmallCategory I] {M X : I ⥤ SSet.{0}}
variable (a : M ⟶ X) {k : I ⥤ SimplexCategory} (reference : X ⟶ k ⋙ J)
variable (allowed : ∀ p, (M.obj p).obj zero → Set (Fin ((k.obj p).len + 1)))
variable (injective : ∀ p, Function.Injective ((a.app p).app zero))
variable (reflects : ∀ {p q : I} (f : p ⟶ q) (v : (X.obj p).obj zero),
  (X.map f).app zero v ∈ Set.range ((a.app q).app zero) →
    v ∈ Set.range ((a.app p).app zero))
variable (stable : ∀ {p q : I} (f : p ⟶ q) (u : (M.obj p).obj zero),
  Set.MapsTo (k.map f).toOrderHom (allowed p u) (allowed q ((M.map f).app zero u)))

include injective reflects stable in
private theorem sideStable {p q : I} (f : p ⟶ q) (v : (X.obj p).obj zero) :
    Set.MapsTo (k.map f).toOrderHom (extendAllowed a reference allowed p v)
      (extendAllowed a reference allowed q ((X.map f).app zero v)) :=
  extendAllowed_mapsTo a reference allowed injective (@reflects) (@stable) f v

/-- The full side cover retains all allowed values on the overlap and uses
the side reference elsewhere. -/
abbrev sideCover :=
  cover X k (extendAllowed a reference allowed) (sideStable a reference allowed injective
    (@reflects) (@stable))

/-- The cover for a whole side projects back to its original source. -/
abbrev sideProjection :=
  projection X k (extendAllowed a reference allowed) (sideStable a reference allowed injective
    (@reflects) (@stable))

/-- The parameter of the whole side cover uses the chosen values above the overlap. -/
abbrev sideParameter :=
  JTVertexAssignmentCover.trace X k (extendAllowed a reference allowed)
    (@sideStable _ _ _ _ a _ reference allowed injective (@reflects) (@stable))

/-- Every side simplex receives a weakly contractible space of lifts if
the compatible overlap values are nonempty. -/
theorem sideProjection_trivialFibration (h : ∀ p u, (allowed p u).Nonempty) (p : I) :
    HomotopicalAlgebra.trivialFibrations SSet.{0}
      ((sideProjection a reference allowed injective (@reflects) (@stable)).app p) := by
  exact projection_trivialFibration X k _ _
    (JTVertexAssignmentCover.extendAllowed_nonempty a reference allowed injective h) p

/-- The tautological parameter on the whole side cover leaves the reference
reduced-cylinder graph unchanged after projection to the side. -/
theorem sideCover_preserves_graph (p : I) (T : NecklaceCode) (f : X.obj p ⟶ T.toSSet)
    (h : ∀ (u : (M.obj p).obj zero) (c : Fin ((k.obj p).len + 1)),
      c ∈ allowed p u → RigidVertex T f ((a.app p).app zero u) →
      c = coord (k.obj p) zero ((reference.app p).app zero ((a.app p).app zero u)) 0) :
    let π := (sideProjection a reference allowed injective (@reflects) (@stable)).app p
    let σ := (sideParameter a reference allowed injective (@reflects) (@stable)).app p
    lift (π ≫ f) σ ≫ (cylinder T).app (k.obj p) =
      π ≫ lift f (reference.app p) ≫ (cylinder T).app (k.obj p) := by
  dsimp only
  rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
  apply exact_graph_of_rigid_agreement
  intro x hx
  let w := ((sideProjection a reference allowed injective (@reflects) (@stable)).app p).app zero x
  let c := coord (k.obj p) zero
    (((sideParameter a reference allowed injective (@reflects) (@stable)).app p).app zero x) 0
  change c = coord (k.obj p) zero ((reference.app p).app zero w) 0
  have hc : c ∈ extendAllowed a reference allowed p w := trace_allowed X k _ _ p x
  have hw : RigidVertex T f w := rigidVertex_map T _ f x hx
  by_cases hmem : w ∈ Set.range ((a.app p).app zero)
  · obtain ⟨u, hu⟩ := hmem
    rw [← hu]
    exact h u c (hc.1 u hu) (hu.symm ▸ hw)
  · exact hc.2 hmem

section SharedTrace

open JTVertexAssignmentCover (liftOfAssignments liftOfAssignments_projection
  liftOfAssignments_trace_vertex)

variable {C : I ⥤ SSet.{0}} (π : C ⟶ M) (τ : C ⟶ k ⋙ J)

private abbrev vertex (p : I) (u : (C.obj p).obj zero) :=
  coord (k.obj p) zero ((τ.app p).app zero u) 0

private theorem vertex_natural {p q : I} (f : p ⟶ q) (u : (C.obj p).obj zero) :
    vertex τ q ((C.map f).app zero u) = (k.map f).toOrderHom (vertex τ p u) := by
  have h := congrFun (NatTrans.congr_app (τ.naturality f) zero) u
  change (τ.app q).app zero ((C.map f).app zero u) =
    (J.map (k.map f)).app zero ((τ.app p).app zero u) at h
  change coord (k.obj q) zero ((τ.app q).app zero ((C.map f).app zero u)) 0 = _
  rw [h, JTCodiscreteParameterPairing.coord_map]

variable (valid : ∀ p (u : (C.obj p).obj zero),
  vertex τ p u ∈ allowed p ((π.app p).app zero u))

include injective valid in
private theorem value_allowed_on_side (p : I) (u : (C.obj p).obj zero) :
    vertex τ p u ∈ extendAllowed a reference allowed p (((π ≫ a).app p).app zero u) := by
  let m := (π.app p).app zero u
  change vertex τ p u ∈ extendAllowed a reference allowed p ((a.app p).app zero m)
  exact ⟨fun u' hu ↦ (injective p hu).symm ▸ valid p u,
    fun ho ↦ (ho ⟨m, rfl⟩).elim⟩

/-- The common overlap trace maps naturally into the whole side cover,
using exactly the same coefficient on both sides. -/
def liftSharedTrace : C ⟶ sideCover a reference allowed injective (@reflects) (@stable) :=
  liftOfAssignments X k _ (sideStable a reference allowed injective (@reflects) (@stable))
    C (π ≫ a) (vertex τ) (vertex_natural τ) (value_allowed_on_side a reference allowed
      injective π τ valid)

/-- The lift covers the inclusion of the original overlap. -/
theorem liftSharedTrace_projection :
    liftSharedTrace a reference allowed injective (@reflects) (@stable) π τ valid ≫
      sideProjection a reference allowed injective (@reflects) (@stable) = π ≫ a :=
  liftOfAssignments_projection X k _ _ C _ _ _ _

/-- Both side parameters restrict to the same chosen trace on the overlap cover. -/
theorem liftSharedTrace_parameter :
    liftSharedTrace a reference allowed injective (@reflects) (@stable) π τ valid ≫
      sideParameter a reference allowed injective (@reflects) (@stable) = τ := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro u
  exact liftOfAssignments_trace_vertex X k _ _ C _ _ _ _ p u

end SharedTrace

end Cover

end

end DaggerModels.PartII.JTExactGraphRelativeExtension
