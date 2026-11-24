import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTParameterContraction
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Simplex lifts and fiber separation for native reduced necklace cylinders

The cylinder leg is degreewise surjective for every
native necklace, including the point code. Equal images of two prism simplices
either have equal parameter simplices or the first horizontal point lies in the
original ordered boundary. The second result is stronger than the vertex claim.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNecklaceCylinderSimplexLift

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

/-- A parameter vertex splits the projection from the boundary cylinder. -/
private def boundaryParameterSection (k : SimplexCategory) : B ⟶ B ⊗ J.obj k :=
  CartesianMonoidalCategory.lift (𝟙 B)
    (SSet.stdSimplex.isTerminalObj₀.from B ≫ JTParameterContraction.parameterVertex k 0)

private theorem boundaryParameterSection_fst (k : SimplexCategory) :
    boundaryParameterSection k ≫ CartesianMonoidalCategory.fst B (J.obj k) = 𝟙 B :=
  CartesianMonoidalCategory.lift_fst _ _

/-- Every simplex of the actual reduced cylinder has an uncollapsed prism lift. -/
theorem simplex_lift (T : NecklaceCode) (k : SimplexCategory) (d : ℕ)
    (z : ((value T).obj k).obj (op ⦋d⦌)) :
    ∃ p : (T.toSSet ⊗ J.obj k).obj (op ⦋d⦌),
      ((cylinder T).app k).app (op ⦋d⦌) p = z := by
  let q : SimplexCategoryᵒᵖ := op ⦋d⦌
  have sq := (isPushout T k).map (SSet.evaluation.obj q)
  obtain ⟨p, hp⟩ | ⟨a, ha⟩ := Types.eq_or_eq_of_isPushout sq z
  · exact ⟨p, hp⟩
  · let s := boundaryParameterSection k
    let t := endpointInclusion T ⊗ₘ 𝟙 (J.obj k)
    refine ⟨t.app q (s.app q a), ?_⟩
    have hw := congrFun sq.w (s.app q a)
    have hs : (CartesianMonoidalCategory.fst B (J.obj k)).app q (s.app q a) = a := by
      change ((s ≫ CartesianMonoidalCategory.fst B (J.obj k)).app q) a = a
      rw [show s = boundaryParameterSection k from rfl, boundaryParameterSection_fst]
      rfl
    calc
      ((cylinder T).app k).app q (t.app q (s.app q a)) =
          ((boundary T).app k).app q
            ((CartesianMonoidalCategory.fst B (J.obj k)).app q (s.app q a)) := by
        change ((cylinder T).app k).app q (t.app q (s.app q a)) =
          ((boundary T).app k).app q
            ((CartesianMonoidalCategory.fst B (J.obj k)).app q (s.app q a)) at hw
        exact hw
      _ = ((boundary T).app k).app q a := by rw [hs]
      _ = z := ha

/-- A point outside the seam cannot be identified with another left-leg point
in a pushout of types. This needs no monomorphism hypothesis on the seam. -/
private theorem left_eq_or_seam {A X Y P : Type}
    (t : A ⟶ X) (g : A ⟶ Y) (r : X ⟶ P) (b : Y ⟶ P)
    (sq : IsPushout t g r b) (x x' : X) (h : r x = r x') :
    x = x' ∨ ∃ a : A, t a = x := by
  classical
  by_cases heq : x = x'
  · exact Or.inl heq
  right
  by_contra hnone
  have hx : ∀ a : A, t a ≠ x := by
    intro a ha
    exact hnone ⟨a, ha⟩
  let mark : X ⟶ Bool := fun v ↦ decide (v = x)
  let blank : Y ⟶ Bool := fun _ ↦ false
  have hcompat : t ≫ mark = g ≫ blank := by
    funext a
    simp [mark, blank, hx a]
  let classify : P ⟶ Bool := sq.desc mark blank hcompat
  have hclass : mark x = mark x' := by
    calc
      mark x = classify (r x) := (congrFun (sq.inl_desc mark blank hcompat) x).symm
      _ = classify (r x') := congrArg classify h
      _ = mark x' := congrFun (sq.inl_desc mark blank hcompat) x'
  have hne : x' ≠ x := Ne.symm heq
  simp [mark, hne] at hclass

/-- Equal images in an actual native reduced cylinder have equal parameter
simplices unless the first horizontal simplex comes from the ordered boundary.
No positive-length or injectivity premise is needed. -/
theorem equal_lifts_parameter_or_boundary (T : NecklaceCode)
    (k : SimplexCategory) (d : ℕ)
    (p p' : (T.toSSet ⊗ J.obj k).obj (op ⦋d⦌))
    (h : ((cylinder T).app k).app (op ⦋d⦌) p =
      ((cylinder T).app k).app (op ⦋d⦌) p') :
    (CartesianMonoidalCategory.snd T.toSSet (J.obj k)).app (op ⦋d⦌) p =
        (CartesianMonoidalCategory.snd T.toSSet (J.obj k)).app (op ⦋d⦌) p' ∨
      ∃ a : B.obj (op ⦋d⦌),
        (endpointInclusion T).app (op ⦋d⦌) a =
          (CartesianMonoidalCategory.fst T.toSSet (J.obj k)).app (op ⦋d⦌) p := by
  let q : SimplexCategoryᵒᵖ := op ⦋d⦌
  let t := endpointInclusion T ⊗ₘ 𝟙 (J.obj k)
  let fB := CartesianMonoidalCategory.fst B (J.obj k)
  let fT := CartesianMonoidalCategory.fst T.toSSet (J.obj k)
  have sq := (isPushout T k).map (SSet.evaluation.obj q)
  obtain heq | ⟨a, ha⟩ := left_eq_or_seam
    (t.app q) (fB.app q) (((cylinder T).app k).app q)
    (((boundary T).app k).app q) sq p p' h
  · left
    exact congrArg (fun v ↦
      (CartesianMonoidalCategory.snd T.toSSet (J.obj k)).app q v) heq
  · right
    refine ⟨fB.app q a, ?_⟩
    have hf := CartesianMonoidalCategory.tensorHom_fst
      (endpointInclusion T) (𝟙 (J.obj k))
    have hfa := congrArg (fun v : B ⊗ J.obj k ⟶ T.toSSet ↦ v.app q a) hf
    change fT.app q (t.app q a) =
      (endpointInclusion T).app q (fB.app q a) at hfa
    rw [ha] at hfa
    exact hfa.symm

end

end DaggerModels.PartII.JTNecklaceCylinderSimplexLift
