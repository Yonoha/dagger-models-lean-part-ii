import DaggerModelsPartII.JTFrameAugmentation
import DaggerModelsPartII.JTParameterReversal
import DaggerModels.FreeDaggerPushout
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-!
# The strict endpoint-collapse span for the represented dagger JT frame

This scratch module constructs the two spans in the manuscript's strict
endpoint-collapse comparison. The final natural dagger isomorphism is not
asserted here: it requires a quotient comparison preserving both ordered
endpoint inclusions and the actual dagger involution.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiEndpointCollapse

open DaggerJTAdjunction DaggerJTFrameUnderlying JTFrameAugmentation
open GroupoidSimplex

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

/-- The ordinary boundary and interval used in the strict quotient. -/
def boundary : SSet.{0} := (SSet.boundary 1).toSSet
def interval : SSet.{0} := (Δ[1] : SSet.{0})

/-- The constant diagram on an ordinary simplicial set, multiplied by the
actual groupoid-completed parameter `J`. -/
def parameterProduct (X : SSet.{0}) : SimplexCategory ⥤ SSet.{0} :=
  (((Functor.const SimplexCategory).obj X).prod' parameter) ⋙
    MonoidalCategory.tensor SSet.{0}

/-- The boundary cylinder `∂Δ¹ × J^k`. -/
def boundaryCylinder : SimplexCategory ⥤ SSet.{0} := parameterProduct boundary

/-- The interval cylinder `Δ¹ × J^k`. -/
def intervalCylinder : SimplexCategory ⥤ SSet.{0} := parameterProduct interval

/-- The literal boundary inclusion in each parameter degree. -/
def cylinderInclusion : boundaryCylinder ⟶ intervalCylinder :=
  Functor.whiskerRight
    (NatTrans.prod'
      ((Functor.const SimplexCategory).map (SSet.boundary 1).ι)
      (𝟙 parameter))
    (MonoidalCategory.tensor SSet.{0})

/-- Collapse the entire copy of `J^k` at each boundary vertex. -/
def cylinderProjection : boundaryCylinder ⟶
    (Functor.const SimplexCategory).obj boundary where
  app k := CartesianMonoidalCategory.fst boundary (parameter.obj k)
  naturality k l f := by
    change (𝟙 boundary ⊗ₘ parameter.map f) ≫
      CartesianMonoidalCategory.fst boundary (parameter.obj l) =
        CartesianMonoidalCategory.fst boundary (parameter.obj k)
    simpa only [Category.comp_id] using
      (CartesianMonoidalCategory.tensorHom_fst
        (𝟙 boundary) (parameter.map f))

/-- The ordinary cosimplicial endpoint-collapsed interval `C_E^•`. -/
def CE : SimplexCategory ⥤ SSet.{0} :=
  pushout cylinderInclusion cylinderProjection

/-- The ordered boundary inclusion into the endpoint-collapsed interval. -/
def CE_boundary : (Functor.const SimplexCategory).obj boundary ⟶ CE :=
  pushout.inr cylinderInclusion cylinderProjection

/-- The interval-cylinder map into the endpoint-collapsed interval. -/
def CE_interval : intervalCylinder ⟶ CE :=
  pushout.inl cylinderInclusion cylinderProjection

/-- The two reversal indices used for the raw represented frame. -/
def m0 : ReverseSimplex := ReverseSimplex.inclusion.obj ⦋0⦌
def m1 : ReverseSimplex := ReverseSimplex.inclusion.obj ⦋1⦌

/-- The actual represented frame at horizontal degree zero. -/
def frame0 : SimplexCategory ⥤ DaggerSSet.{0} :=
  CategoryTheory.Prod.sectR m0 SimplexCategory ⋙ frame

/-- The actual represented frame at horizontal degree one. -/
def frame1 : SimplexCategory ⥤ DaggerSSet.{0} :=
  CategoryTheory.Prod.sectR m1 SimplexCategory ⋙ frame

/-- A selected ordered endpoint as an actual reversal-simplex morphism. -/
def reversalEndpoint (i : Fin 2) : m0 ⟶ m1 where
  toFun := fun _ ↦ i
  monotone_or_antitone := Or.inl (fun _ _ _ ↦ le_refl i)

/-- The endpoint is constant in the ordinary simplex parameter. -/
def endpointSection (i : Fin 2) :
    CategoryTheory.Prod.sectR m0 SimplexCategory ⟶
      CategoryTheory.Prod.sectR m1 SimplexCategory where
  app k := (reversalEndpoint i, 𝟙 k)
  naturality k l f := by
    apply Prod.ext
    · exact (Category.comp_id _).symm
    · simp

/-- The two literal endpoint cofaces of the dagger JT frame. -/
def frameEndpoint (i : Fin 2) : frame0 ⟶ frame1 :=
  Functor.whiskerRight (endpointSection i) frame

/-- Projection from the zero horizontal frame onto its degree-zero value,
followed by the chosen free-dagger zero-simplex normalization. -/
def frame0Projection : frame0 ⟶
    (Functor.const SimplexCategory).obj (freeDagger.obj (Δ[0] : SSet.{0})) where
  app k := frameAugmentation.app (m0, k) ≫
    (reversalSimplexFreeIso.app ⦋0⦌).hom
  naturality k l f := by
    have h : frame0.map f ≫ frameAugmentation.app (m0, l) =
        frameAugmentation.app (m0, k) := by
      simp [frame0]
    simpa only [Functor.const_obj_map, Category.comp_id, Category.assoc] using
      congrArg (fun t ↦ t ≫ (reversalSimplexFreeIso.app ⦋0⦌).hom) h

/-- The `i`-th vertex is in the boundary of the standard interval. -/
def boundaryVertex (i : Fin 2) : boundary.obj (Opposite.op ⦋0⦌) :=
  ⟨SSet.stdSimplex.objEquiv.symm (SimplexCategory.const ⦋0⦌ ⦋1⦌ i), by
    change ¬Function.Surjective (fun _ : Fin 1 ↦ i)
    intro h
    obtain ⟨a, ha⟩ := h 0
    obtain ⟨b, hb⟩ := h 1
    exact (by decide : (0 : Fin 2) ≠ 1) (ha.symm.trans hb)⟩

/-- The ordered simplicial vertex inclusion into `∂Δ¹`. -/
def boundaryVertexMap (i : Fin 2) : (Δ[0] : SSet.{0}) ⟶ boundary :=
  SSet.yonedaEquiv.symm (boundaryVertex i)

/-- The manuscript's literal free dagger boundary object. -/
def B : DaggerSSet.{0} := freeDagger.obj boundary

/-- The two ordered endpoint collapses into the constant two-vertex object. -/
def endpointCollapse (i : Fin 2) : frame0 ⟶
    (Functor.const SimplexCategory).obj B :=
  frame0Projection ≫
    (Functor.const SimplexCategory).map
      (freeDagger.map (boundaryVertexMap i))

/-- The raw attachment span, with its two endpoint faces. -/
def rawFaces : frame0 ⨿ frame0 ⟶ frame1 :=
  coprod.desc (frameEndpoint 0) (frameEndpoint 1)

/-- The raw collapse span, with the same ordering as `rawFaces`. -/
def rawEndpoints : frame0 ⨿ frame0 ⟶
    (Functor.const SimplexCategory).obj B :=
  coprod.desc (endpointCollapse 0) (endpointCollapse 1)

/-- The actual raw endpoint collapse of the represented dagger frame. -/
def rawCollapse : SimplexCategory ⥤ DaggerSSet.{0} :=
  pushout rawFaces rawEndpoints

/-- The ordered inclusion of the free dagger boundary into the raw collapse. -/
def rawBoundary : (Functor.const SimplexCategory).obj B ⟶ rawCollapse :=
  pushout.inr rawFaces rawEndpoints

/-- The strict target diagram before dagger rigidification. -/
def CEFree : SimplexCategory ⥤ DaggerSSet.{0} := CE ⋙ freeDagger

/-- The prescribed boundary inclusion into the free dagger of `C_E^•`.
The constant-functor comparison is necessary because composition with
`freeDagger` does not preserve the chosen constant functor definitionally. -/
def CEFreeBoundary : (Functor.const SimplexCategory).obj B ⟶ CEFree :=
  (Functor.constComp SimplexCategory boundary freeDagger).inv ≫
    Functor.whiskerRight CE_boundary freeDagger

end

end DaggerModels.PartII.JTXiEndpointCollapse
