import DaggerModelsPartII.JTNecklaceCylinderSimplexLift
import Mathlib.CategoryTheory.Limits.Types.Pushouts

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphJointSeparation

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter

private theorem endpoint_first (T : NecklaceCode) :
    SSet.boundary₁.ι₀ ≫ endpointInclusion T = pointAt T (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₀_desc]
  rfl

private theorem endpoint_last (T : NecklaceCode) :
    SSet.boundary₁.ι₁ ≫ endpointInclusion T =
      pointAt T (ULift.up (Fin.last T.len)) := by
  change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₁_desc]
  rfl

private theorem boundary_point_is_endpoint (T : NecklaceCode)
    (a : (Δ[0] : SSet.{0}) ⟶ T.toSSet)
    (b : B.obj (op ⦋0⦌))
    (hb : (endpointInclusion T).app (op ⦋0⦌) b =
      SSet.yonedaEquiv a) :
    a = pointAt T (ULift.up 0) ∨
      a = pointAt T (ULift.up (Fin.last T.len)) := by
  have sq := (SSet.boundary₁.isPushout.{0}).map
    (SSet.evaluation.obj (op ⦋0⦌))
  have hfactor (v : (Δ[0] : SSet.{0}).obj (op ⦋0⦌))
      (e : (Δ[0] : SSet.{0}) ⟶ B)
      (he : e.app (op ⦋0⦌) v = b) :
      a = e ≫ endpointInclusion T := by
    apply SSet.yonedaEquiv.injective
    calc
      SSet.yonedaEquiv a = (endpointInclusion T).app (op ⦋0⦌) b := hb.symm
      _ = (endpointInclusion T).app (op ⦋0⦌) (e.app (op ⦋0⦌) v) := by rw [he]
      _ = SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ e ≫ endpointInclusion T) := by
        rw [← Category.assoc, SSet.yonedaEquiv_comp,
          SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
      _ = SSet.yonedaEquiv (e ≫ endpointInclusion T) := by
        rw [show SSet.yonedaEquiv.symm v = 𝟙 (Δ[0] : SSet.{0}) from
          SSet.stdSimplex.isTerminalObj₀.hom_ext _ _, Category.id_comp]
  obtain ⟨v, hv⟩ | ⟨v, hv⟩ := Types.eq_or_eq_of_isPushout sq b
  · left
    exact (hfactor v SSet.boundary₁.ι₀ hv).trans (endpoint_first T)
  · right
    exact (hfactor v SSet.boundary₁.ι₁ hv).trans (endpoint_last T)

/-- Equal reduced-cylinder vertices either have the same parameter or lie over
one of the two original ordered endpoints. -/
theorem parameter_eq_or_endpoint (T : NecklaceCode) (k : SimplexCategory)
    (a : (Δ[0] : SSet.{0}) ⟶ T.toSSet)
    (u v : (Δ[0] : SSet.{0}) ⟶ J.obj k)
    (h : lift a u ≫ (cylinder T).app k =
      lift a v ≫ (cylinder T).app k) :
    u = v ∨ a = pointAt T (ULift.up 0) ∨
      a = pointAt T (ULift.up (Fin.last T.len)) := by
  let p := SSet.yonedaEquiv (lift a u)
  let p' := SSet.yonedaEquiv (lift a v)
  have hp : ((cylinder T).app k).app (op ⦋0⦌) p =
      ((cylinder T).app k).app (op ⦋0⦌) p' := by
    simpa only [p, p', SSet.yonedaEquiv_comp] using
      congrArg SSet.yonedaEquiv h
  obtain hparam | ⟨b, hb⟩ :=
    JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary
      T k 0 p p' hp
  · left
    apply SSet.yonedaEquiv.injective
    have hparam' : SSet.yonedaEquiv
        (lift a u ≫ snd T.toSSet (J.obj k)) =
        SSet.yonedaEquiv (lift a v ≫ snd T.toSSet (J.obj k)) := by
      simpa only [p, p', SSet.yonedaEquiv_comp] using hparam
    simpa only [lift_snd] using hparam'
  · right
    have ha : (endpointInclusion T).app (op ⦋0⦌) b =
        SSet.yonedaEquiv a := by
      simpa only [p, SSet.yonedaEquiv_comp, lift_fst] using hb
    exact boundary_point_is_endpoint T a b ha

end

end DaggerModels.PartII.JTGraphJointSeparation
