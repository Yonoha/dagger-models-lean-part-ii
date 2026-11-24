import DaggerModelsPartII.JTGraphParameterFiber

/-!
# Relative extension of fixed reduced-cylinder graph parameters
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerOriginalCodiscreteNerveInjective

namespace DaggerModels.PartII.JTGraphParameterRelative

open GroupoidSimplex
open JTNecklaceEndpointCylinder JTCodiscreteParameterPairing JTGraphParameterInterpolation

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev vertex (Y : SSet.{0}) := Y.obj (op ⦋0⦌)

private def vertexSlice {X Y : SSet.{0}} (y : vertex Y) : X ⟶ X ⊗ Y :=
  lift (𝟙 X) (SSet.stdSimplex.isTerminalObj₀.from X ≫ SSet.yonedaEquiv.symm y)

private theorem vertexSlice_fst {X Y : SSet.{0}} (y : vertex Y) :
    vertexSlice (X := X) y ≫ fst X Y = 𝟙 X := lift_fst _ _

private theorem vertexSlice_natural {X A Y : SSet.{0}} (j : A ⟶ Y) (a : vertex A) :
    vertexSlice (X := X) a ≫ (X ◁ j) = vertexSlice (j.app (op ⦋0⦌) a) := by
  have h : SSet.yonedaEquiv.symm a ≫ j = SSet.yonedaEquiv.symm (j.app (op ⦋0⦌) a) := by
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, whiskerLeft_fst, vertexSlice_fst, vertexSlice_fst]
  · rw [Category.assoc, whiskerLeft_snd, ← Category.assoc]
    simp only [vertexSlice, lift_snd, Category.assoc, h]

private theorem vertexSlice_app {X Y : SSet.{0}} (x : vertex X) (y : vertex Y) :
    (vertexSlice (X := X) y).app (op ⦋0⦌) x = (x, y) := by
  let u := SSet.stdSimplex.isTerminalObj₀.from X
  change (x, (SSet.yonedaEquiv.symm y).app (op ⦋0⦌) (u.app (op ⦋0⦌) x)) = (x, y)
  have hu : u.app (op ⦋0⦌) x = SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})) :=
    Subsingleton.elim _ _
  rw [hu]
  apply congrArg (fun w : vertex Y ↦ (x, w))
  exact (SSet.yonedaEquiv_comp (𝟙 _) (SSet.yonedaEquiv.symm y)).symm.trans (by
    rw [Category.id_comp, Equiv.apply_symm_apply])

private theorem eq_of_slices {X Y : SSet.{0}} {k : SimplexCategory} {s t : X ⊗ Y ⟶ J.obj k}
    (h : ∀ y : vertex Y, vertexSlice y ≫ s = vertexSlice y ≫ t) : s = t := by
  have hv (z : (X ⊗ Y).obj (op ⦋0⦌)) : s.app (op ⦋0⦌) z = t.app (op ⦋0⦌) z := by
    have hh := congrFun (NatTrans.congr_app (h z.2) (op ⦋0⦌)) z.1
    change s.app (op ⦋0⦌) ((vertexSlice (X := X) z.2).app (op ⦋0⦌) z.1) =
      t.app (op ⦋0⦌) ((vertexSlice (X := X) z.2).app (op ⦋0⦌) z.1) at hh
    rw [vertexSlice_app] at hh
    exact hh
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let e := (parameterCodiscreteIso.app k).hom
  change (((s ≫ e).app q z).obj v).as = (((t ≫ e).app q z).obj v).as
  rw [← vertexLabels_natural (s ≫ e) q z v, ← vertexLabels_natural (t ≫ e) q z v]
  change vertexLabels e (s.app (op ⦋0⦌) _) = vertexLabels e (t.app (op ⦋0⦌) _)
  rw [hv]

private theorem slice_fiber {X A : SSet.{0}} (T : NecklaceCode) (k : SimplexCategory)
    (f : X ⟶ T.toSSet) (g : X ⟶ (value T).obj k) (p : X ⊗ A ⟶ J.obj k)
    (h : lift (fst X A ≫ f) p ≫ (cylinder T).app k = fst X A ≫ g)
    (a : vertex A) :
    lift f (vertexSlice a ≫ p) ≫ (cylinder T).app k = g := by
  have h' := congrArg (fun u ↦ vertexSlice (X := X) a ≫ u) h
  simp only [← Category.assoc, vertexSlice_fst, Category.id_comp] at h'
  rw [CartesianMonoidalCategory.comp_lift, ← Category.assoc, vertexSlice_fst,
    Category.id_comp] at h'
  exact h'

/-- A prescribed parameter family on a time subobject extends to the whole
time object with its exact reduced-cylinder image, once a reference lift
of that image is supplied. -/
theorem extend_time {X A Y : SSet.{0}} (j : A ⟶ Y) [Mono j]
    (T : NecklaceCode) (k : SimplexCategory) (f : X ⟶ T.toSSet)
    (g : X ⟶ (value T).obj k) (t : X ⟶ J.obj k)
    (ht : lift f t ≫ (cylinder T).app k = g)
    (p : X ⊗ A ⟶ J.obj k)
    (hp : lift (fst X A ≫ f) p ≫ (cylinder T).app k = fst X A ≫ g) :
    ∃ q : X ⊗ Y ⟶ J.obj k, (X ◁ j) ≫ q = p ∧
      lift (fst X Y ≫ f) q ≫ (cylinder T).app k = fst X Y ≫ g := by
  classical
  let s (a : vertex A) := vertexSlice a ≫ p
  let S := Function.extend (j.app (op ⦋0⦌)) s (fun _ ↦ t)
  have hj : Function.Injective (j.app (op ⦋0⦌)) := (mono_iff_injective _).1 inferInstance
  have hS (a : vertex A) : S (j.app (op ⦋0⦌) a) = s a := hj.extend_apply _ _ _
  have hF (y : vertex Y) : lift f (S y) ≫ (cylinder T).app k = g := by
    by_cases hy : ∃ a : vertex A, j.app (op ⦋0⦌) a = y
    · obtain ⟨a, rfl⟩ := hy
      rw [hS]
      exact slice_fiber T k f g p hp a
    · change lift f (Function.extend (j.app (op ⦋0⦌)) s (fun _ ↦ t) y) ≫
          (cylinder T).app k = g
      rw [Function.extend_apply' _ _ _ hy]
      exact ht
  refine ⟨interpolateBy S, ?_, ?_⟩
  · apply eq_of_slices
    intro a
    rw [← Category.assoc, vertexSlice_natural]
    exact (slice_interpolateBy S (j.app (op ⦋0⦌) a)).trans (hS a)
  · refine JTGraphParameterFiber.fiber_of_coordinates T k f S t g hF ht (interpolateBy S) ?_
    intro n z i
    exact ⟨Y.map (SimplexCategory.const ⦋0⦌ n.unop i).op z.2, coord_interpolateBy S n z i⟩

end

end DaggerModels.PartII.JTGraphParameterRelative
