import DaggerModelsPartII.JTTraceFiberDescent
import DaggerModelsPartII.JTJointClippedParameters

/-!
# Exact vertex criterion for a trace on the full joint interval

Collapsing the full inverse image of a target joint forgets the horizontal
vertex but retains the independent time vertex. This identifies exactly the
fibers on which a groupoid parameter must be constant to admit a trace.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointTraceVertexCriterion

open JTTargetJointMarks (Joint)
open JTTargetIntervalOverMapping (overlap whole)
open JTTargetIntervalPullback (sourceInterval)
open JTJointIntervalQuotient (joint overlapToJoint overlapToWhole)
open JTJointRelativeParameters (withTime withTimeMap withTimeMap_app)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev J := GroupoidSimplex.parameter

variable (U : NecklaceCode) (j : Joint U)
variable {X : SSet.{0}} (q : U.toSSet ⟶ X)
variable {I : Type} [SmallCategory I] (K : SimplexCategory ⥤ SSet.{0})
variable (time : I ⥤ SimplexCategory) (D : I ⥤ Over U)

private abbrev a := withTimeMap q K time D (overlapToJoint U j)
private abbrev source := withTime q K time D (overlap U j)
private abbrev target := withTime q K time D (joint U j)

/-- The joint collapse retains exactly the time coordinate on vertices. -/
theorem overlapToJoint_vertex (p : I) (v : (source U j q K time D).obj p |>.obj zero) :
    ((a U j q K time D).app p).app zero v =
      (((overlapToJoint U j).app (D.obj p)).left.app zero v.1, v.2) := by
  rw [a, withTimeMap_app]
  rfl

/-- The vertex map of the full joint collapse is surjective. -/
theorem overlapToJoint_vertex_surjective (p : I) :
    Function.Surjective (((a U j q K time D).app p).app zero) := by
  intro v
  let P := D.obj p
  let u : ((overlap U j).obj P).left.obj zero :=
    (sourceInterval P.hom j j le_rfl).verticesEquiv.symm (ULift.up 0)
  haveI : Subsingleton (((joint U j).obj P).left.obj zero) := by
    change Subsingleton ((Δ[0] : SSet.{0}).obj zero)
    infer_instance
  refine ⟨(u, v.2), ?_⟩
  rw [overlapToJoint_vertex]
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · rfl

/-- Two overlap vertices have the same joint image exactly when their time
coordinates agree. -/
theorem overlapToJoint_vertex_eq_iff (p : I)
    (v w : (source U j q K time D).obj p |>.obj zero) :
    ((a U j q K time D).app p).app zero v =
        ((a U j q K time D).app p).app zero w ↔ v.2 = w.2 := by
  haveI : Subsingleton (((joint U j).obj (D.obj p)).left.obj zero) := by
    change Subsingleton ((Δ[0] : SSet.{0}).obj zero)
    infer_instance
  rw [overlapToJoint_vertex, overlapToJoint_vertex]
  constructor
  · intro e
    exact congrArg (fun z => z.2) e
  · intro e
    exact Prod.ext (Subsingleton.elim _ _) e

variable (k : I ⥤ SimplexCategory)
variable (s : withTime q K time D (whole U) ⟶ k ⋙ J)

/-- Equal-time overlap vertices carry equal values of the original parameter. -/
def TimeFiberConstant : Prop :=
  ∀ p (v w : (source U j q K time D).obj p |>.obj zero), v.2 = w.2 →
    coord (k.obj p) zero
        (((withTimeMap q K time D (overlapToWhole U j) ≫ s).app p).app zero v) 0 =
      coord (k.obj p) zero
        (((withTimeMap q K time D (overlapToWhole U j) ≫ s).app p).app zero w) 0

private theorem fiberConstant_iff_timeFiberConstant :
    JTTraceFiberDescent.FiberConstant (a U j q K time D) k
        (withTimeMap q K time D (overlapToWhole U j) ≫ s) ↔
      TimeFiberConstant U j q K time D k s := by
  constructor
  · intro hf p v w ht
    exact hf p v w ((overlapToJoint_vertex_eq_iff U j q K time D p v w).mpr ht)
  · intro hf p v w he
    exact hf p v w ((overlapToJoint_vertex_eq_iff U j q K time D p v w).mp he)

/-- A natural trace exists uniquely exactly when the original restriction is
constant on overlap vertices with the same time coordinate. -/
theorem existsUnique_trace_iff_timeFiberConstant :
    (∃! trace : target U j q K time D ⟶ k ⋙ J,
      JTJointClippedParameters.TraceFactors U j q K time D k s trace) ↔
      TimeFiberConstant U j q K time D k s := by
  have hdesc := JTTraceFiberDescent.existsUnique_iff_fiberConstant
    (a U j q K time D) k
    (withTimeMap q K time D (overlapToWhole U j) ≫ s)
    (overlapToJoint_vertex_surjective U j q K time D)
  rw [← fiberConstant_iff_timeFiberConstant U j q K time D k s]
  constructor
  · rintro ⟨trace, htrace, _⟩
    exact JTTraceFiberDescent.fiberConstant_of_precomp
      (a U j q K time D) k
      (withTimeMap q K time D (overlapToWhole U j) ≫ s) trace htrace.symm
  · intro hf
    obtain ⟨trace, htrace, huniq⟩ := hdesc.mpr hf
    refine ⟨trace, htrace.symm, ?_⟩
    intro trace' htrace'
    exact huniq trace' htrace'.symm

end

end DaggerModels.PartII.JTJointTraceVertexCriterion
