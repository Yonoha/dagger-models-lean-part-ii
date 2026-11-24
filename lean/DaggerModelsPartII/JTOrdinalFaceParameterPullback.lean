import DaggerModelsPartII.JTOrdinalFaceInverseImage
import DaggerModelsPartII.JTJointRelativeParameters

/-! Exact groupoid parameter factorization through the entire inverse-image face. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTOrdinalFaceParameterPullback

open JTOrdinalFaceInverseImage (vertices ordinal enumerate incl toFace toFace_fac mem_vertices)
open JTJointRelativeParameters (parameter_ext)
open JTCodiscreteParameterPairing (coord coord_map)
open DaggerOriginalCodiscreteNerveInjective

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)

variable {s k d : SimplexCategory} (u : s ⟶ k) (α : d ⟶ k)
variable (hα : Function.Surjective α.toOrderHom)
variable {X : SSet.{0}} (q : X ⟶ J.obj d) (g : X ⟶ J.obj s)

private theorem in_preimage (h : q ≫ J.map α = g ≫ J.map u) (x : X.obj zero) :
    coord d zero (q.app zero x) 0 ∈ vertices u α := by
  apply (mem_vertices u α _).mpr
  refine ⟨coord s zero (g.app zero x) 0, ?_⟩
  have he := congrArg (fun v ↦ coord k zero v 0)
    (congrFun (NatTrans.congr_app h zero) x)
  simpa only [coord_map] using he.symm

private def vertexLift (h : q ≫ J.map α = g ≫ J.map u) (x : X.obj zero) :
    Fin ((ordinal u α).len + 1) :=
  (enumerate u α hα).symm ⟨coord d zero (q.app zero x) 0, in_preimage u α q g h x⟩

/-- Factor any parameter through the full coefficient preimage, preserving its exact values. -/
def factor (h : q ≫ J.map α = g ≫ J.map u) : X ⟶ J.obj (ordinal u α) :=
  mapOfVertices X (vertexLift u α hα q g h) ≫
    (GroupoidSimplex.parameterCodiscreteIso.app (ordinal u α)).inv

private theorem factor_coord (h : q ≫ J.map α = g ≫ J.map u) (x : X.obj zero) :
    coord (ordinal u α) zero ((factor u α hα q g h).app zero x) 0 =
      vertexLift u α hα q g h x := by
  have hc : factor u α hα q g h ≫
      (GroupoidSimplex.parameterCodiscreteIso.app (ordinal u α)).hom =
    mapOfVertices X (vertexLift u α hα q g h) := by
    rw [factor, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun z ↦ (z.obj (0 : Fin 1)).as)
    (congrFun (NatTrans.congr_app hc zero) x)
  change coord (ordinal u α) zero ((factor u α hα q g h).app zero x) 0 =
    vertexLift u α hα q g h
      (X.map ((⦋0⦌ : SimplexCategory).const ⦋0⦌ 0).op x) at hv
  simpa only [SimplexCategory.const_eq_id, op_id, FunctorToTypes.map_id_apply] using hv

/-- The factor recovers the whole original groupoid parameter in every simplicial degree. -/
theorem factor_incl (h : q ≫ J.map α = g ≫ J.map u) :
    factor u α hα q g h ≫ J.map (incl u α hα) = q := by
  apply parameter_ext
  intro x
  change coord d zero ((J.map (incl u α hα)).app zero
    ((factor u α hα q g h).app zero x)) 0 = coord d zero (q.app zero x) 0
  rw [coord_map, factor_coord]
  change (enumerate u α hα ((enumerate u α hα).symm _)).val = _
  exact congrArg Subtype.val ((enumerate u α hα).apply_symm_apply _)

variable (hu : Function.Injective u.toOrderHom)

/-- Its old face coordinate is also the prescribed one, without a new section choice. -/
theorem factor_toFace (h : q ≫ J.map α = g ≫ J.map u) :
    factor u α hα q g h ≫ J.map (toFace u α hα hu) = g := by
  have he : (factor u α hα q g h ≫ J.map (toFace u α hα hu)) ≫ J.map u =
      g ≫ J.map u := by
    rw [Category.assoc, ← J.map_comp, toFace_fac, J.map_comp, ← Category.assoc,
      factor_incl]
    exact h
  apply parameter_ext
  intro x
  apply hu
  have hv := congrArg (fun z ↦ coord k zero z 0)
    (congrFun (NatTrans.congr_app he zero) x)
  simpa only [NatTrans.comp_app, types_comp_apply, coord_map] using hv

end
end DaggerModels.PartII.JTOrdinalFaceParameterPullback
