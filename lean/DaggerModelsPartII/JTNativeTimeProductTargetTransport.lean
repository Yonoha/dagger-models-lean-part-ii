import DaggerModelsPartII.JTNativeTimeProductTransport

/-!
Transport the whole native product and its collapse together. The forward
native isomorphism in the product cancels its inverse in the fixed-target
collapse. The two native object expressions need not be identified first.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeTimeProductTargetTransport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev SF := NecklaceCode.simplicialFunctor

variable {I : Type} [SmallCategory I] {N M : I ⥤ NecklaceCode}
variable (e : N ≅ M) (time : I ⥤ SimplexCategory)
variable {U : NecklaceCode} (c : N ⟶ (Functor.const I).obj U)

/-- Transport the native collapse backwards along the same isomorphism
used forwards on the complete product graph. -/
def collapse : M ⟶ (Functor.const I).obj U := e.inv ≫ c

/-- The complete fixed-target native leg is preserved, including its actual
source graph and the entire original time coordinate. -/
theorem native_square (a : I) {X : SSet.{0}}
    (h : X ⟶ (N.obj a).toSSet ⊗ J.obj (time.obj a)) :
    (h ≫ (JTNativeTimeProductTransport.iso e time).hom.app a) ≫
        fst (M.obj a).toSSet (J.obj (time.obj a)) ≫
          ((collapse e c).app a).map =
      h ≫ fst (N.obj a).toSSet (J.obj (time.obj a)) ≫ (c.app a).map := by
  rw [JTNativeTimeProductTransport.hom_app]
  change (h ≫ ((e.hom.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a)))) ≫
      fst (M.obj a).toSSet (J.obj (time.obj a)) ≫
        ((e.inv.app a).map ≫ (c.app a).map) = _
  have hf : ((e.hom.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
      fst (M.obj a).toSSet (J.obj (time.obj a)) =
        fst (N.obj a).toSSet (J.obj (time.obj a)) ≫ (e.hom.app a).map :=
    tensorHom_fst _ _
  have hi : (e.hom.app a).map ≫ (e.inv.app a).map = 𝟙 (N.obj a).toSSet := by
    change SF.map (e.hom.app a) ≫ SF.map (e.inv.app a) = _
    rw [← SF.map_comp, e.hom_inv_id_app, SF.map_id]
    rfl
  calc
    _ = h ≫
        ((((e.hom.app a).map ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫
          fst (M.obj a).toSSet (J.obj (time.obj a))) ≫
            ((e.inv.app a).map ≫ (c.app a).map)) := by
      simp only [Category.assoc]
    _ = h ≫
        ((fst (N.obj a).toSSet (J.obj (time.obj a)) ≫ (e.hom.app a).map) ≫
          ((e.inv.app a).map ≫ (c.app a).map)) :=
      congrArg (fun g ↦ h ≫ (g ≫ ((e.inv.app a).map ≫ (c.app a).map))) hf
    _ = h ≫ fst (N.obj a).toSSet (J.obj (time.obj a)) ≫
        (((e.hom.app a).map ≫ (e.inv.app a).map) ≫ (c.app a).map) := by
      simp only [Category.assoc]
    _ = _ := by rw [hi, Category.id_comp]

end
end DaggerModels.PartII.JTNativeTimeProductTargetTransport
