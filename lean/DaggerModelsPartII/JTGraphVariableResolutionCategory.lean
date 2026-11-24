import DaggerModelsPartII.GrothendieckContractibleFibers
import DaggerModelsPartII.JTGraphVariableTimeTransport

/-! The total category of the original resolutions, and the comparison on it. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableResolutionCategory

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex (resolution_point_GW)
open JTGraphVariableTimeTransport (resolutionDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

section Generic

variable {B D : Type} [SmallCategory B] [SmallCategory D]
variable {F : B ⥤ Cat.{0, 0}} {L : B ⥤ D}
variable {P : ∀ b, (F.obj b) ⥤ D}
variable {α : ∀ {b b' : B} (a : b ⟶ b'), P b ⟶ (F.map a).toFunctor ⋙ P b'}
variable {h₁ : ∀ b, α (𝟙 b) = eqToHom (by rw [F.map_id]; rfl)}
variable {h₂ : ∀ b b' b'' (a : b ⟶ b') (b₁ : b' ⟶ b''),
    α (a ≫ b₁) =
      α a ≫ Functor.whiskerLeft (F.map a).toFunctor (α b₁) ≫
        eqToHom (by rw [F.map_comp]; rfl)}

variable (p : ∀ b, P b ⟶ (Functor.const (F.obj b)).obj (L.obj b))
variable (hp : ∀ {b b'} (a : b ⟶ b') (z : F.obj b),
    (α a).app z ≫ (p b').app ((F.map a).toFunctor.obj z) = (p b).app z ≫ L.map a)

/-- Compatible comparisons on the fibers induce one comparison over the whole total category. -/
def toProjection :
    Grothendieck.functorFrom P α h₁ h₂ ⟶ Grothendieck.forget F ⋙ L where
  app z := (p z.base).app z.fiber
  naturality {_ z} f := by
    change ((α f.base).app _ ≫ (P z.base).map f.fiber) ≫ (p z.base).app z.fiber =
      _ ≫ L.map f.base
    rw [Category.assoc]
    have h := (p z.base).naturality f.fiber
    change (P z.base).map f.fiber ≫ (p z.base).app z.fiber =
      (p z.base).app _ ≫ 𝟙 _ at h
    rw [h, Category.comp_id]
    exact hp f.base _

end Generic

/-- Pulling back the complete resolution along a diagram of original comma
objects still forgets by a Kan weak nerve map. -/
theorem projection_weak_of {B : Type} [SmallCategory B]
    (L : B ⥤ TargetComma Q) :
    WeakEquivalence (nerveMap (Grothendieck.forget (L ⋙ resolutionDiagram Q))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun b ↦ resolution_point_GW (L.obj b))

/-- The Grothendieck projection of the original resolution diagram is weak. -/
theorem projection_weak
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    WeakEquivalence (nerveMap (Grothendieck.forget (resolutionDiagram Q))) :=
  GrothendieckContractibleFibers.projection_weak _ (fun U ↦ resolution_point_GW U)

end
end DaggerModels.PartII.JTGraphVariableResolutionCategory
