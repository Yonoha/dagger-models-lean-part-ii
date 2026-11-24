import DaggerModelsPartII.JTMixedGraphHorizontalTraversal
import DaggerModelsPartII.JTGraphJointSeparation
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# Reduced cylinders detect the full padded graph parameter

The middle bead of a padded graph lies away from the two collapsed endpoints.
This also holds for a middle bead of length zero and under horizontal
degeneracies preserving the two outer beads.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open CartesianMonoidalCategory DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.JTPaddedGraphParameterRecognition

open JTNecklaceEndpointCylinder MixedGraphCylinderTraversal
open JTMixedGraphHorizontalTraversal (padded padded_middle collapse_natural parameter_factor)
open JTMixedGraphRawRefinement (nativeGraphParameter)

noncomputable section

private abbrev A := single 1
private abbrev M (d : ℕ) := tripleRightU.{0} A (single d) A
private abbrev J := GroupoidSimplex.parameter

variable {d e : ℕ}
variable {k : SimplexCategory}

private abbrev Point := (Δ[0] : SSet.{0})

/-- The padded middle bead maps to interior vertices, including at its ends. -/
theorem middle_ne_endpoints (p : Point ⟶ (single e).toSSet) :
    p ≫ M e ≠ pointAt (code e) (ULift.up 0) ∧
      p ≫ M e ≠ pointAt (code e) (ULift.up (Fin.last (code e).len)) := by
  let v := (single e).verticesEquiv (SSet.yonedaEquiv p)
  have hp : p = pointAt (single e) v := by
    apply SSet.yonedaEquiv.injective
    rw [pointAt_vertex, Equiv.symm_apply_apply]
  let w := wedgeRight A (wedge (single e) A) (wedgeLeft (single e) A v.down)
  have h : p ≫ M e = pointAt (code e) (ULift.up w) := by
    rw [hp]
    unfold M tripleRightU
    rw [← Category.assoc, pointAt_comp, wedgeιLeft_vertices, pointAt_comp, wedgeιRight_vertices]
    rfl
  have hw : w.val = 1 + v.down.val := rfl
  have hlen : (code e).len = 1 + (e + 1) := rfl
  have hv : v.down.val < e + 1 := v.down.isLt
  constructor
  · intro H
    have h' := congrArg
      (fun t : Point ⟶ (code e).toSSet ↦ (code e).verticesEquiv (SSet.yonedaEquiv t))
      (h.symm.trans H)
    simp only [pointAt_vertex, Equiv.apply_symm_apply] at h'
    have h₀ : w.val = 0 := congrArg (fun z : Vertices.{0} (code e) ↦ z.down.val) h'
    omega
  · intro H
    have h' := congrArg
      (fun t : Point ⟶ (code e).toSSet ↦ (code e).verticesEquiv (SSet.yonedaEquiv t))
      (h.symm.trans H)
    simp only [pointAt_vertex, Equiv.apply_symm_apply] at h'
    have h₁ : w.val = (code e).len := congrArg (fun z : Vertices.{0} (code e) ↦ z.down.val) h'
    omega

/-- Equality of the reduced graphs over the middle bead detects all parameters. -/
theorem middle_parameter_eq {X : SSet.{0}} (f : X ⟶ (single e).toSSet)
    {s t : X ⟶ J.obj k}
    (h : lift (f ≫ M e) s ≫ (cylinder (code e)).app k =
      lift (f ≫ M e) t ≫ (cylinder (code e)).app k) :
    s = t := by
  have hv (z : X.obj (op ⦋0⦌)) : s.app (op ⦋0⦌) z = t.app (op ⦋0⦌) z := by
    let p := SSet.yonedaEquiv.symm z
    have hp : lift ((p ≫ f) ≫ M e) (p ≫ s) ≫ (cylinder (code e)).app k =
        lift ((p ≫ f) ≫ M e) (p ≫ t) ≫ (cylinder (code e)).app k := by
      have h' := congrArg (fun g ↦ p ≫ g) h
      simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift] at h'
      exact h'
    have he := JTGraphJointSeparation.parameter_eq_or_endpoint (code e) k
      ((p ≫ f) ≫ M e) (p ≫ s) (p ≫ t) hp
    rcases he with he | he | he
    · simpa only [p, SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using
        congrArg SSet.yonedaEquiv he
    · exact ((middle_ne_endpoints (p ≫ f)).1 he).elim
    · exact ((middle_ne_endpoints (p ≫ f)).2 he).elim
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let i := (GroupoidSimplex.parameterCodiscreteIso.app k).hom
  change (((s ≫ i).app q z).obj v).as = (((t ≫ i).app q z).obj v).as
  rw [← vertexLabels_natural (s ≫ i) q z v, ← vertexLabels_natural (t ≫ i) q z v]
  change vertexLabels i (s.app (op ⦋0⦌) _) = vertexLabels i (t.app (op ⦋0⦌) _)
  rw [hv]

/-- Equality of reduced graphs over a padded map detects both parameters
whenever they factor through the prescribed collapse of the outer beads. -/
theorem parameter_eq_of_factor (u : single d ⟶ single e)
    (s t : (single d).toSSet ⟶ J.obj k)
    (h : lift (padded u).map (collapseMap d ≫ s) ≫ (cylinder (code e)).app k =
      lift (padded u).map (collapseMap d ≫ t) ≫ (cylinder (code e)).app k) :
    s = t := by
  apply middle_parameter_eq u.map
  have h' := congrArg (fun g ↦ M d ≫ g) h
  change M d ≫ _ = M d ≫ _ at h'
  simp only [← Category.assoc, CartesianMonoidalCategory.comp_lift, padded_middle,
    collapseMap_middle, Category.id_comp] at h'
  exact h'

/-- The original reduced equality detects the parameter equation of a
horizontal padded operator and an arbitrary coefficient operator. -/
theorem mixed_parameter_eq {l : SimplexCategory} (u : single d ⟶ single e)
    (b : k ⟶ l)
    (s : (SSet.stdSimplex.{0}.obj ⦋d⦌) ⟶ J.obj k)
    (t : (SSet.stdSimplex.{0}.obj ⦋e⦌) ⟶ J.obj l)
    (h : lift (padded u).map (nativeGraphParameter s ≫ J.map b) ≫ (cylinder (code e)).app l =
      lift (padded u).map ((padded u).map ≫ nativeGraphParameter t) ≫ (cylinder (code e)).app l) :
    nativeGraphParameter s ≫ J.map b = (padded u).map ≫ nativeGraphParameter t := by
  have hc := congrArg (fun g : code d ⟶ single e ↦ g.map) (collapse_natural u)
  change (padded u).map ≫ collapseMap e = collapseMap d ≫ u.map at hc
  have h₀ : nativeGraphParameter s ≫ J.map b =
      collapseMap d ≫ ((singleIso d).hom ≫ s ≫ J.map b) := by
    rw [parameter_factor]
    simp only [Category.assoc]
  have h₁ : (padded u).map ≫ nativeGraphParameter t =
      collapseMap d ≫ (u.map ≫ (singleIso e).hom ≫ t) := by
    rw [parameter_factor, ← Category.assoc, hc, Category.assoc]
  rw [h₀, h₁] at h ⊢
  exact congrArg (fun v ↦ collapseMap d ≫ v) (parameter_eq_of_factor u _ _ h)

end

end DaggerModels.PartII.JTPaddedGraphParameterRecognition
