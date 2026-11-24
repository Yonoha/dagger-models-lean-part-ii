import DaggerModelsPartII.JTGraphLiftTransport
import DaggerModelsPartII.JTNecklaceCylinderSimplexLift

/-!
# Identity graph lift of a single-bead presentation
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphIdentityLift

open JTGraphLiftTransport JTNecklaceEndpointCylinder JTNecklaceCylinderSimplexLift
open JTCommaGraphPredecessor (augmentationCode)
open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : Pres (W := W) (x := x) (y := y)} {d : ℕ}

/-- A single-bead presentation has an uncollapsed graph parameter. -/
theorem exists_parameter (hP : P.fiber.left = single d) :
    ∃ s : P.fiber.left.toSSet ⟶ J.obj (degree P),
      lift (augmentationCode P).map s ≫ (cylinder (code P)).app (degree P) =
        P.fiber.hom.right := by
  let e : P.fiber.left.toSSet ≅ (Δ[d] : SSet.{0}) :=
    eqToIso (congrArg NecklaceCode.toSSet hP) ≪≫ singleIso d
  let u := P.fiber.hom.right
  let m := e.inv ≫ u
  obtain ⟨z, hz⟩ := simplex_lift (code P) (degree P) d (SSet.yonedaEquiv m)
  let Z := e.hom ≫ SSet.yonedaEquiv.symm z
  have h₀ : SSet.yonedaEquiv.symm z ≫ (cylinder (code P)).app (degree P) = m := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz
  have h₁ : Z ≫ (cylinder (code P)).app (degree P) = u := by
    dsimp only [Z, m] at *
    rw [Category.assoc, h₀, Iso.hom_inv_id_assoc]
  have h₂ : Z ≫ fst (code P).toSSet (J.obj (degree P)) =
      u ≫ NecklaceCylinderAugmentation.augmentation (code P) (degree P) := by
    rw [← NecklaceCylinderAugmentation.augmentation_cylinder,
      ← Category.assoc, h₁]
  have h₃ : lift (u ≫ NecklaceCylinderAugmentation.augmentation (code P) (degree P))
      (Z ≫ snd (code P).toSSet (J.obj (degree P))) = Z := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, h₂]
    · rw [lift_snd]
  refine ⟨Z ≫ snd (code P).toSSet (J.obj (degree P)), ?_⟩
  change lift (u ≫ NecklaceCylinderAugmentation.augmentation (code P) (degree P))
      (Z ≫ snd (code P).toSSet (J.obj (degree P))) ≫
      (cylinder (code P)).app (degree P) = u
  rw [h₃, h₁]

/-- The identity native collapse retains the entire original traversal. -/
theorem exists_identity_lift (hP : P.fiber.left = single d) :
    ∃ D : GraphLift P P.fiber.left, D.collapse = 𝟙 _ := by
  obtain ⟨s, hs⟩ := exists_parameter (P := P) (d := d) hP
  refine ⟨⟨𝟙 _, s, ?_⟩, rfl⟩
  change lift (augmentationCode P).map s ≫ (cylinder (code P)).app (degree P) =
    P.fiber.hom.right
  exact hs

end

end DaggerModels.PartII.JTGraphIdentityLift
