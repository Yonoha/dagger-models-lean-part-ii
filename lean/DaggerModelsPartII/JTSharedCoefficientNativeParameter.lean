import DaggerModelsPartII.JTBinaryPrismParameter
import DaggerModelsPartII.JTJoinedGraphCylinderTransport

/-! Restriction of a joined parameter along the original native and time maps. -/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTSharedCoefficientNativeParameter

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1

variable {T U T' U' : NecklaceCode} (f : T ⟶ T') (g : U ⟶ U')
variable {n n' : SimplexCategory} (a : n ⟶ n')
variable {X : SSet.{0}}
variable (p' : (JTOrderedLabelBinaryGlue.code T' U').toSSet ⊗ J.obj n' ⟶ X)

/-- Pull back the entire junction parameter through both native sides and time. -/
def pull : (JTOrderedLabelBinaryGlue.code T U).toSSet ⊗ J.obj n ⟶ X :=
  ((JTBinaryPrismParameter.sideMap f g).map ⊗ₘ J.map a) ≫ p'

theorem pull_postcomp {Y : SSet.{0}} (q : X ⟶ Y) :
    pull f g a (p' ≫ q) = pull f g a p' ≫ q := (Category.assoc _ _ _).symm

/-- Restriction to the left source is exactly its native and time pullback. -/
theorem pull_left :
    (tripleRightT T E U ⊗ₘ 𝟙 (J.obj n)) ≫ pull f g a p' =
      (f.map ⊗ₘ J.map a) ≫
        (tripleRightT T' E U' ⊗ₘ 𝟙 (J.obj n')) ≫ p' := by
  unfold pull
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    JTBinaryPrismParameter.sideMap_left]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- Restriction to the right source is exactly its native and time pullback. -/
theorem pull_right :
    (tripleRightV T E U ⊗ₘ 𝟙 (J.obj n)) ≫ pull f g a p' =
      (g.map ⊗ₘ J.map a) ≫
        (tripleRightV T' E U' ⊗ₘ 𝟙 (J.obj n')) ≫ p' := by
  unfold pull
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
    JTBinaryPrismParameter.sideMap_right]
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

/-- Pullback of the full parameter respects simultaneous composition of both
native side maps and the original time map. -/
theorem pull_comp {T'' U'' : NecklaceCode} (f' : T' ⟶ T'') (g' : U' ⟶ U'')
    {n'' : SimplexCategory} (a' : n' ⟶ n'')
    (p : (JTOrderedLabelBinaryGlue.code T'' U'').toSSet ⊗ J.obj n'' ⟶ X) :
    pull f g a (pull f' g' a' p) = pull (f ≫ f') (g ≫ g') (a ≫ a') p := by
  have hc : (JTBinaryPrismParameter.sideMap (f ≫ f') (g ≫ g')).map =
      (JTBinaryPrismParameter.sideMap f g).map ≫ (JTBinaryPrismParameter.sideMap f' g').map :=
    congrArg NecklaceCode.Hom.map (JTJoinedGraphCylinderTransport.sideMap_comp f g f' g')
  unfold pull
  rw [← Category.assoc, tensorHom_comp_tensorHom, hc, J.map_comp]

end
end DaggerModels.PartII.JTSharedCoefficientNativeParameter
