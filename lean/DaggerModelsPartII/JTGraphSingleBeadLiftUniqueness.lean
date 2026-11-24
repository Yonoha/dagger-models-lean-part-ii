import DaggerModelsPartII.JTGraphLiftTransport

/-!
# Uniqueness of the parameter of a one-bead graph lift off the ordered seam
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphSingleBeadLiftUniqueness

open JTProjectiveOrderedFiberComparison
open JTNecklaceEndpointCylinder JTGraphLiftTransport
open JTCommaGraphPredecessor (augmentationCode)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter

private theorem equal_endpoints_of_constant {T : NecklaceCode} {d : ℕ}
    (f : single d ⟶ T) (p : (single d).toSSet ⟶ (Δ[0] : SSet.{0}))
    (v : (Δ[0] : SSet.{0}) ⟶ T.toSSet) (hf : f.map = p ≫ v) : NecklaceCode.first.{0} T = NecklaceCode.last.{0} T := by
  have h : f.map.app (op ⦋0⦌) (single d).first =
      f.map.app (op ⦋0⦌) (single d).last := by
    rw [hf]
    change v.app _ (p.app _ (single d).first) = v.app _ (p.app _ (single d).last)
    exact congrArg (v.app (op ⦋0⦌)) (Subsingleton.elim _ _)
  exact f.first.symm.trans (h.trans f.last)

private theorem not_boundary {T : NecklaceCode} {d : ℕ}
    (f : single d ⟶ T) (ht : NecklaceCode.first.{0} T ≠ NecklaceCode.last.{0} T) :
    ¬ ∃ a : B.obj (op ⦋d⦌), (endpointInclusion T).app (op ⦋d⦌) a =
      SSet.yonedaEquiv ((singleIso d).inv ≫ f.map) := by
  rintro ⟨a, ha⟩
  have h := (SSet.boundary₁.isPushout.{0}).map (SSet.evaluation.obj (op ⦋d⦌))
  have hconst (v : (Δ[0] : SSet.{0}).obj (op ⦋d⦌))
      (e : (Δ[0] : SSet.{0}) ⟶ B) (hv : e.app (op ⦋d⦌) v = a) : NecklaceCode.first.{0} T = NecklaceCode.last.{0} T := by
    have hv' : SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ e) = a :=
      (SSet.yonedaEquiv_comp _ _).trans (by rw [Equiv.apply_symm_apply]; exact hv)
    have hcomp : (singleIso d).inv ≫ f.map =
        SSet.yonedaEquiv.symm v ≫ e ≫ endpointInclusion T := by
      apply SSet.yonedaEquiv.injective
      exact ha.symm.trans (by rw [← Category.assoc, SSet.yonedaEquiv_comp, hv'])
    refine equal_endpoints_of_constant f ((singleIso d).hom ≫ SSet.yonedaEquiv.symm v)
      (e ≫ endpointInclusion T) ?_
    calc
      f.map = (singleIso d).hom ≫ (singleIso d).inv ≫ f.map := (Iso.hom_inv_id_assoc _ _).symm
      _ = _ := by rw [hcomp, Category.assoc]
  obtain ⟨v, hv⟩ | ⟨v, hv⟩ := Types.eq_or_eq_of_isPushout h a
  · exact ht (hconst v SSet.boundary₁.ι₀ hv)
  · exact ht (hconst v SSet.boundary₁.ι₁ hv)

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : Pres (W := W) (x := x) (y := y)}

/-- The same native collapse on a one-bead code forces the entire parameter
when the original label code has distinct endpoints. -/
theorem parameter_eq_of_same_collapse {d : ℕ} (D E : GraphLift P (single d))
    (hcollapse : D.collapse = E.collapse) (ht : NecklaceCode.first.{0} (code P) ≠ NecklaceCode.last.{0} (code P)) :
    D.parameter = E.parameter := by
  let f := D.collapse ≫ augmentationCode P
  let i := (singleIso d).inv
  let z := SSet.yonedaEquiv (i ≫ lift f.map D.parameter)
  let z' := SSet.yonedaEquiv (i ≫ lift f.map E.parameter)
  have hE := E.comm
  rw [← hcollapse] at hE
  have hGraph : lift f.map D.parameter ≫ (cylinder (code P)).app (degree P) =
      lift f.map E.parameter ≫ (cylinder (code P)).app (degree P) := D.comm.trans hE.symm
  have cyl_eq (t : (single d).toSSet ⟶ J.obj (degree P)) :
      ((cylinder (code P)).app (degree P)).app (op ⦋d⦌)
        (SSet.yonedaEquiv (i ≫ lift f.map t)) =
      SSet.yonedaEquiv (i ≫ lift f.map t ≫ (cylinder (code P)).app (degree P)) := by
    rw [← Category.assoc]
    exact (SSet.yonedaEquiv_comp _ _).symm
  have hz : ((cylinder (code P)).app (degree P)).app (op ⦋d⦌) z =
      ((cylinder (code P)).app (degree P)).app (op ⦋d⦌) z' :=
    (cyl_eq D.parameter).trans ((congrArg (fun m ↦ SSet.yonedaEquiv (i ≫ m)) hGraph).trans
      (cyl_eq E.parameter).symm)
  obtain hs | ⟨a, ha⟩ := JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary
    (code P) (degree P) d z z' hz
  · have coord (t : (single d).toSSet ⟶ J.obj (degree P)) :
        (snd (code P).toSSet (J.obj (degree P))).app (op ⦋d⦌)
          (SSet.yonedaEquiv (i ≫ lift f.map t)) = SSet.yonedaEquiv (i ≫ t) := by
      refine (SSet.yonedaEquiv_comp _ _).symm.trans ?_
      rw [Category.assoc, lift_snd]
    exact (cancel_epi i).mp (SSet.yonedaEquiv.injective
      ((coord D.parameter).symm.trans (hs.trans (coord E.parameter))))
  · have coord : (fst (code P).toSSet (J.obj (degree P))).app (op ⦋d⦌) z =
        SSet.yonedaEquiv (i ≫ f.map) := by
      refine (SSet.yonedaEquiv_comp _ _).symm.trans ?_
      rw [Category.assoc, lift_fst]
    exact (not_boundary f ht ⟨a, ha.trans coord⟩).elim

end

end DaggerModels.PartII.JTGraphSingleBeadLiftUniqueness
