import DaggerModelsPartII.JTVariableFixedLiftChoiceDiagram

/-! Evaluate complete relative choices on arbitrary simplicial time objects. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTVariableFixedLiftEvaluation

open JTVariableFixedLiftChoiceDiagram (Diagram square fiber choices)

noncomputable section

variable {I : Type} [SmallCategory I] (D : Diagram I)

/-- The full coefficient map represented by an arbitrary family of exact lifts. -/
def liftMap (a : I) {T : SSet.{0}} (g : T ⟶ (choices D).obj (op a)) :
    D.domain.obj a ⊗ T ⟶ D.values.obj (op a) :=
  uncurry (g ≫ (fiber D a).ι)

/-- The entire prescribed support remains stationary for arbitrary time families. -/
theorem liftMap_support (a : I) {T : SSet.{0}}
    (g : T ⟶ (choices D).obj (op a)) :
    (D.incl.app a ▷ T) ≫ liftMap D a g =
      fst (D.support.obj a) T ≫ D.onSupport a := by
  have h : (g ≫ (fiber D a).ι) ≫ (MonoidalClosed.pre (D.incl.app a)).app
      (D.values.obj (op a)) = SSet.const (SSet.ihom₀Equiv.symm (D.onSupport a)) := by
    rw [Category.assoc, SSet.ihomToPullbackFiber_pre_app, SSet.comp_const]
  simpa only [uncurry_pre_app, SSet.const_ihom₀Equiv_symm_apply, liftMap] using
    congrArg uncurry h

/-- The original base and the full outer boundary stay fixed throughout every family. -/
theorem liftMap_boundary (a : I) {T : SSet.{0}}
    (g : T ⟶ (choices D).obj (op a)) :
    liftMap D a g ≫ D.restriction.app (op a) =
      fst (D.domain.obj a) T ≫ D.base a := by
  have h : (g ≫ (fiber D a).ι) ≫ (ihom (D.domain.obj a)).map
      (D.restriction.app (op a)) = SSet.const (SSet.ihom₀Equiv.symm (D.base a)) := by
    rw [Category.assoc, SSet.ihomToPullbackFiber_ihom_map, SSet.comp_const]
  simpa only [uncurry_natural_right, SSet.const_ihom₀Equiv_symm_apply, liftMap] using
    congrArg uncurry h

/-- Restrict an arbitrary simplicial time family, retaining every coefficient point. -/
theorem liftMap_time (a : I) {T T' : SSet.{0}}
    (v : T' ⟶ T) (g : T ⟶ (choices D).obj (op a)) :
    liftMap D a (v ≫ g) = (D.domain.obj a ◁ v) ≫ liftMap D a g := by
  unfold liftMap
  rw [Category.assoc, uncurry_natural_left]

/-- Native and coefficient operators act on the full map by their exact
precomposition and contravariant native-label postcomposition. -/
theorem liftMap_restrict {a b : I} (f : a ⟶ b) {T : SSet.{0}}
    (g : T ⟶ (choices D).obj (op b)) :
    liftMap D a (g ≫ (choices D).map f.op) =
      (D.domain.map f ▷ T) ≫ liftMap D b g ≫ D.values.map f.op := by
  unfold liftMap
  change uncurry (g ≫ JTVariableFixedLiftChoiceDiagram.restrict D f ≫
    (fiber D a).ι) = _
  rw [JTVariableFixedLiftChoiceDiagram.restrict_ι]
  simp only [← Category.assoc]
  rw [uncurry_natural_right, uncurry_pre_app]

/-- The simultaneous time and original diagram restriction for the entire prism. -/
theorem liftMap_natural {a b : I} (f : a ⟶ b) {T T' : SSet.{0}}
    (v : T' ⟶ T) (g : T ⟶ (choices D).obj (op b)) :
    liftMap D a (v ≫ g ≫ (choices D).map f.op) =
      (D.domain.map f ⊗ₘ v) ≫ liftMap D b g ≫ D.values.map f.op := by
  rw [liftMap_time, liftMap_restrict]
  rw [← Category.assoc, ← tensorHom_def']

end
end DaggerModels.PartII.JTVariableFixedLiftEvaluation
