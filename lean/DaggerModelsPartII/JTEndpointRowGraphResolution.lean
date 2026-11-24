import DaggerModelsPartII.JTEndpointSimplexSlice
import DaggerModelsPartII.JTRowGraphFaceResolution

/-! All independent raw graph representatives on endpoint-preserving horizontal sources. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointRowGraphResolution

open JTEndpointSimplexSlice
open OrdinaryJTRealization (BiPresheaf realization)

noncomputable section

variable {W : BiPresheaf} {d : ℕ}

/-- Forget the condition on horizontal operators without changing their raw values. -/
abbrev toSimplexSlice : Slice d ⥤ Over ⦋d⦌ :=
  Over.post (wideSubcategoryInclusion preservesEnds)

/-- Keep all coefficient graphs above each endpoint-preserving horizontal operator. -/
abbrev diagram (q : (Δ[d] : SSet.{0}) ⟶ realization.obj W) :
    (Slice d)ᵒᵖ ⥤ Cat.{0, 0} :=
  (toSimplexSlice (d := d)).op ⋙ JTRowGraphFaceResolution.diagram q

abbrev Resolution (q : (Δ[d] : SSet.{0}) ⟶ realization.obj W) :=
  Grothendieck (diagram q)

variable (q : (Δ[d] : SSet.{0}) ⟶ realization.obj W)

/-- The formula for the raw graph value is exactly precomposition into the fixed target. -/
abbrev value (P : Slice d) : SSet.stdSimplex.{0}.obj P.left.obj ⟶ realization.obj W :=
  JTRowGraphFaceResolution.value q (toSimplexSlice.obj P)

/-- The weak projection retains all horizontal operators and drops only coefficient choices. -/
theorem projection_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (diagram q))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun P ↦
    (SynchronizedSimplicialParameters.point_op_iff _).2
      (JTRowGraphFiber.point_GW (value q P.unop)))

/-- The entire endpoint-preserving mixed graph index has weakly contractible nerve. -/
theorem point_GW : GW (pointMap (nerve (Resolution q))) := by
  let P := Grothendieck.forget (diagram q)
  let p := pointMap (nerve (Slice d)ᵒᵖ)
  letI : WeakEquivalence (nerveMap P) := projection_weak q
  letI : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    ((SynchronizedSimplicialParameters.point_op_iff _).2 (DaggerNativeOverNerveWeakContractibility.point_GW (simplex d)))
  rw [← pointIsTerminal.hom_ext (nerveMap P ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTEndpointRowGraphResolution
