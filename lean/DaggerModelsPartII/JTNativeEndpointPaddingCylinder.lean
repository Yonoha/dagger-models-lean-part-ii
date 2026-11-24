import DaggerModelsPartII.JTNativeEndpointPadding
import DaggerModelsPartII.NecklaceCylinderJointDiagram

/-! Add endpoint beads to the native cylinder and preserve its full native map. -/

set_option autoImplicit false
set_option maxHeartbeats 240000

open CategoryTheory Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeEndpointPadding

noncomputable section

variable {I : Type} [SmallCategory I]
variable (T : I ⥤ NecklaceCode) (time : I ⥤ SimplexCategory)

private abbrev cylinder := NecklaceCylinderJointDiagram.cylinderUnder

/-- The original source cylinders with two outer beads adjoined at each object. -/
abbrev cylinders := ((T ⋙ pad).prod' time) ⋙ cylinder

private abbrev original := (T.prod' time) ⋙ cylinder

/-- Collapse the two extra beads, with time and both ordered endpoints fixed. -/
def collapseCylinders : cylinders T time ⟶ original T time := by
  let h : T ⋙ pad ⟶ T :=
    { app := fun i ↦ collapse.app (T.obj i)
      naturality := fun {_ _} f ↦ collapse.naturality (T.map f) }
  exact Functor.whiskerRight (NatTrans.prod' h (𝟙 time)) cylinder

variable {Q : NecklaceCode}
variable (u : T ⟶ (Functor.const I).obj Q)
variable {targetTime : I ⥤ SimplexCategory} (a : time ⟶ targetTime)

/-- The complete padded source maps naturally to the cylinders over the
same padded target, retaining any specified compatible time operator. -/
def mapToPaddedTarget :
    cylinders T time ⟶ ((Functor.const I).obj (pad.obj Q)).prod' targetTime ⋙ cylinder := by
  let v : T ⋙ pad ⟶ (Functor.const I).obj (pad.obj Q) :=
    { app := fun i ↦ pad.map (u.app i)
      naturality := fun {i j} f ↦ by
        change pad.map (T.map f) ≫ pad.map (u.app j) = pad.map (u.app i) ≫ 𝟙 _
        rw [Category.comp_id, ← pad.map_comp]
        exact congrArg (fun g : T.obj i ⟶ Q ↦ pad.map g)
          ((u.naturality f).trans (Category.comp_id _)) }
  exact Functor.whiskerRight (NatTrans.prod' v a) cylinder

open NecklaceCylinderAugmentation (augmentation)

private theorem augmentation_square {T₀ T₁ : NecklaceCode} {k₀ k₁ : SimplexCategory}
    (f : T₀ ⟶ T₁) (g : k₀ ⟶ k₁) :
    ((cylinder.map (show (T₀, k₀) ⟶ (T₁, k₁) from (f, g))).right) ≫ augmentation T₁ k₁ =
      augmentation T₀ k₀ ≫ f.map :=
  NecklaceCylinderJointDiagram.augmentation.naturality
    (show (T₀, k₀) ⟶ (T₁, k₁) from (f, g))

private theorem pasteAugmentations {X Y Z T₀ U V : SSet.{0}}
    (l : X ⟶ Y) (r : X ⟶ Z) (a₁ : Y ⟶ U) (a₂ : Z ⟶ V) (a₀ : X ⟶ T₀)
    (f₁ : T₀ ⟶ U) (f₂ : T₀ ⟶ V) {C : SSet.{0}} (g₁ : U ⟶ C) (g₂ : V ⟶ C)
    (h₁ : l ≫ a₁ = a₀ ≫ f₁) (h₂ : r ≫ a₂ = a₀ ≫ f₂)
    (h : f₁ ≫ g₁ = f₂ ≫ g₂) : l ≫ a₁ ≫ g₁ = r ≫ a₂ ≫ g₂ := by
  rw [← Category.assoc, h₁, Category.assoc, h, ← Category.assoc, ← h₂, Category.assoc]

/-- The padded target cylinder recovers the full original native leg after
augmentation and collapse, even when the time degree moves. -/
theorem mapToPaddedTarget_native (i : I) :
    ((mapToPaddedTarget T time u a).app i).right ≫
        augmentation (pad.obj Q) (targetTime.obj i) ≫ (collapse.app Q).map =
      ((collapseCylinders T time).app i).right ≫
        augmentation (T.obj i) (time.obj i) ≫ (u.app i).map := by
  have h₁ := augmentation_square (pad.map (u.app i)) (a.app i)
  have h₂ := augmentation_square (collapse.app (T.obj i)) (𝟙 (time.obj i))
  have h : pad.map (u.app i) ≫ collapse.app Q = collapse.app (T.obj i) ≫ u.app i :=
    collapse.naturality (u.app i)
  have hm := congrArg (fun f : pad.obj (T.obj i) ⟶ Q ↦ f.map) h
  exact pasteAugmentations _ _ _ _ _ _ _ _ _ h₁ h₂ hm

end

end DaggerModels.PartII.JTNativeEndpointPadding
