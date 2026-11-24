import KanHomotopyMonomorphismCancellation
import NativeSSetFibrationSquareFibreWeak

/-!
# Weak diagonals on exact fibers of a Kan fibration square

The paired base remembers the original total and base maps. Its fibration
property uses the actual relative corner fibration, first to lift the common
target face and then to lift the two source faces with that same target face.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra Simplicial Opposite MorphismProperty
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.KanHomotopyMonomorphismFibre

noncomputable section

open KanHomotopyMonomorphism (diagonal)

/-- The literal corner map of the commuting fibration square. -/
def corner {X Y A B : SSet.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : p ≫ g = f ≫ q) :
    X ⟶ pullback q g :=
  pullback.lift f p h.symm

/-- A pair of `f`-equal source points has a pair of `g`-equal base points. -/
def pairedBase {X Y A B : SSet.{0}} (p : X ⟶ A) (q : Y ⟶ B)
    (f : X ⟶ Y) (g : A ⟶ B) (h : p ≫ g = f ≫ q) :
    pullback f f ⟶ pullback g g :=
  pullback.lift (pullback.fst f f ≫ p) (pullback.snd f f ≫ p) (by
    simp only [Category.assoc, h]
    exact congrArg (fun t => t ≫ q)
      (pullback.condition (f := f) (g := f)))

/-- The paired-base map is a Kan fibration when the original target and
relative corner maps are Kan fibrations. -/
theorem pairedBase_fibration {X Y A B : SSet.{0}} (p : X ⟶ A)
    (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : p ≫ g = f ≫ q) [Fibration q]
    (hc : Fibration (corner p q f g h)) :
    Fibration (pairedBase p q f g h) := by
  apply (fibration_iff (pairedBase p q f g h)).mpr
  rw [← trivialCofibrations_rlp]
  intro U V k hk
  have hq₀ : (trivialCofibrations SSet.{0}).rlp q := by
    rw [trivialCofibrations_rlp]
    exact (fibration_iff q).mp inferInstance
  have hc₀ : (trivialCofibrations SSet.{0}).rlp (corner p q f g h) := by
    rw [trivialCofibrations_rlp]
    exact (fibration_iff _).mp hc
  letI : HasLiftingProperty k q := hq₀ k hk
  letI : HasLiftingProperty k (corner p q f g h) := hc₀ k hk
  constructor
  intro α β sq
  let yU : U ⟶ Y := α ≫ pullback.fst f f ≫ f
  let a₁ : V ⟶ A := β ≫ pullback.fst g g
  let a₂ : V ⟶ A := β ≫ pullback.snd g g
  let zV : V ⟶ B := a₁ ≫ g
  have ha : a₁ ≫ g = a₂ ≫ g := by
    dsimp only [a₁, a₂]
    simpa only [Category.assoc] using
      congrArg (fun t => β ≫ t) (pullback.condition (f := g) (g := g))
  have hyq : yU ≫ q = k ≫ zV := by
    have hs := congrArg (fun t => t ≫ pullback.fst g g ≫ g) sq.w
    calc
      yU ≫ q = α ≫ pullback.fst f f ≫ p ≫ g := by
        dsimp only [yU]
        simp only [Category.assoc, h]
      _ = (α ≫ pairedBase p q f g h) ≫ pullback.fst g g ≫ g := by
        simp [pairedBase, Category.assoc]
      _ = (k ≫ β) ≫ pullback.fst g g ≫ g := hs
      _ = k ≫ zV := by simp only [zV, a₁, Category.assoc]
  let sqQ : CommSq yU k q zV := ⟨hyq⟩
  haveI : sqQ.HasLift := inferInstance
  let yV : V ⟶ Y := sqQ.lift
  let t₁ : V ⟶ pullback q g := pullback.lift yV a₁ (by
    change yV ≫ q = zV
    exact sqQ.fac_right)
  let t₂ : V ⟶ pullback q g := pullback.lift yV a₂ (by
    rw [sqQ.fac_right]
    exact ha)
  have hff : α ≫ pullback.fst f f ≫ f =
      α ≫ pullback.snd f f ≫ f := by
    simpa only [Category.assoc] using
      congrArg (fun t => α ≫ t) (pullback.condition (f := f) (g := f))
  have hα₁ : (α ≫ pullback.fst f f) ≫ p = k ≫ a₁ := by
    have hs := congrArg (fun t => t ≫ pullback.fst g g) sq.w
    simpa only [a₁, pairedBase, Category.assoc, pullback.lift_fst] using hs
  have hα₂ : (α ≫ pullback.snd f f) ≫ p = k ≫ a₂ := by
    have hs := congrArg (fun t => t ≫ pullback.snd g g) sq.w
    simpa only [a₂, pairedBase, Category.assoc, pullback.lift_snd] using hs
  let sq₁ : CommSq (α ≫ pullback.fst f f) k (corner p q f g h) t₁ := ⟨by
    apply pullback.hom_ext
    · simpa only [corner, t₁, yU, Category.assoc, pullback.lift_fst] using
        sqQ.fac_left.symm
    · simpa only [corner, t₁, Category.assoc, pullback.lift_snd] using hα₁⟩
  let sq₂ : CommSq (α ≫ pullback.snd f f) k (corner p q f g h) t₂ := ⟨by
    apply pullback.hom_ext
    · calc
        (α ≫ pullback.snd f f) ≫ corner p q f g h ≫ pullback.fst q g =
            α ≫ pullback.snd f f ≫ f := by simp [corner, Category.assoc]
        _ = yU := hff.symm
        _ = k ≫ yV := sqQ.fac_left.symm
        _ = (k ≫ t₂) ≫ pullback.fst q g := by
          simp [t₂, Category.assoc]
    · simpa only [corner, t₂, Category.assoc, pullback.lift_snd] using hα₂⟩
  haveI : sq₁.HasLift := inferInstance
  haveI : sq₂.HasLift := inferInstance
  let x₁ : V ⟶ X := sq₁.lift
  let x₂ : V ⟶ X := sq₂.lift
  have hf₁ : x₁ ≫ f = yV := by
    have hs := congrArg (fun t => t ≫ pullback.fst q g) sq₁.fac_right
    simpa only [x₁, corner, t₁, Category.assoc, pullback.lift_fst] using hs
  have hf₂ : x₂ ≫ f = yV := by
    have hs := congrArg (fun t => t ≫ pullback.fst q g) sq₂.fac_right
    simpa only [x₂, corner, t₂, Category.assoc, pullback.lift_fst] using hs
  have hp₁ : x₁ ≫ p = a₁ := by
    have hs := congrArg (fun t => t ≫ pullback.snd q g) sq₁.fac_right
    simpa only [x₁, corner, t₁, Category.assoc, pullback.lift_snd] using hs
  have hp₂ : x₂ ≫ p = a₂ := by
    have hs := congrArg (fun t => t ≫ pullback.snd q g) sq₂.fac_right
    simpa only [x₂, corner, t₂, Category.assoc, pullback.lift_snd] using hs
  let x : V ⟶ pullback f f := pullback.lift x₁ x₂ (hf₁.trans hf₂.symm)
  refine CommSq.HasLift.mk' ⟨x, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa only [x, Category.assoc, pullback.lift_fst] using sq₁.fac_left
    · simpa only [x, Category.assoc, pullback.lift_snd] using sq₂.fac_left
  · apply pullback.hom_ext
    · simp only [x, pairedBase, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc,
        hp₁, a₁]
    · simp only [x, pairedBase, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc,
        hp₂, a₂]

/-- The exact map of vertex fibers induced by both original strict diagonals
is weak. Its target retains the paired-base pullback pending calibration to
the strict self-pullback of the original fiber map. -/
theorem diagonal_fiberMap_weak {X Y A B : SSet.{0}} (p : X ⟶ A)
    (q : Y ⟶ B) (f : X ⟶ Y) (g : A ⟶ B)
    (h : p ≫ g = f ≫ q) (b : (Δ[0] : SSet.{0}) ⟶ A)
    [Fibration p] [Fibration q]
    (hc : Fibration (corner p q f g h))
    [WeakEquivalence (diagonal f)] [WeakEquivalence (diagonal g)] :
    WeakEquivalence (DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
      p (pairedBase p q f g h) (diagonal f) (diagonal g)
      (by
        apply pullback.hom_ext
        · simp [KanHomotopyMonomorphism.diagonal, pairedBase, Category.assoc]
        · simp [KanHomotopyMonomorphism.diagonal, pairedBase, Category.assoc])
      b (b ≫ diagonal g) rfl) := by
  letI : Fibration (pairedBase p q f g h) := pairedBase_fibration p q f g h hc
  exact DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_weakEquivalence
    p (pairedBase p q f g h) (diagonal f) (diagonal g)
    (by
      apply pullback.hom_ext
      · simp [KanHomotopyMonomorphism.diagonal, pairedBase, Category.assoc]
      · simp [KanHomotopyMonomorphism.diagonal, pairedBase, Category.assoc])
    b (b ≫ diagonal g) rfl

#print axioms pairedBase_fibration
#print axioms diagonal_fiberMap_weak

end
end DaggerModels.PartII.KanHomotopyMonomorphismFibre
