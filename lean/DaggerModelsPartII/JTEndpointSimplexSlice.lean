import Mathlib.CategoryTheory.WideSubcategory
import DaggerModelsPartII.JTMixedGraphHorizontalTraversal

/-! Endpoint-preserving simplex operators over a fixed bead, including degeneracies. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTEndpointSimplexSlice

open JTMixedGraphHorizontalTraversal MixedGraphCylinderTraversal

noncomputable section

/-- An operator preserves the two ordered endpoints, even in degree zero. -/
def preservesEnds : MorphismProperty SimplexCategory :=
  fun a b f ↦ f.toOrderHom 0 = 0 ∧ f.toOrderHom (Fin.last a.len) = Fin.last b.len

instance : preservesEnds.IsMultiplicative where
  id_mem _ := ⟨rfl, rfl⟩
  comp_mem f g hf hg := by
    change g.toOrderHom (f.toOrderHom 0) = 0 ∧
      g.toOrderHom (f.toOrderHom (Fin.last _)) = Fin.last _
    change f.toOrderHom 0 = 0 ∧ f.toOrderHom (Fin.last _) = Fin.last _ at hf
    change g.toOrderHom 0 = 0 ∧ g.toOrderHom (Fin.last _) = Fin.last _ at hg
    rw [hf.1, hf.2]
    exact hg

abbrev EndpointSimplex := WideSubcategory preservesEnds

abbrev simplex (d : ℕ) : EndpointSimplex := ⟨⦋d⦌⟩

/-- Objects and morphisms both preserve the ordered endpoints. -/
abbrev Slice (d : ℕ) := Over (simplex d)

private theorem single_id (d : ℕ) :
    singleOperator (𝟙 ⦋d⦌) rfl rfl = 𝟙 (single d) := by
  apply Hom.ext
  change (singleIso d).hom ≫ SSet.stdSimplex.map (𝟙 ⦋d⦌) ≫ (singleIso d).inv = _
  have hm : SSet.stdSimplex.{0}.map (𝟙 ⦋d⦌) = 𝟙 _ := SSet.stdSimplex.{0}.map_id _
  rw [hm, Category.id_comp, Iso.hom_inv_id]
  rfl

private theorem single_comp {a b c : ℕ}
    (f : ⦋a⦌ ⟶ ⦋b⦌) (g : ⦋b⦌ ⟶ ⦋c⦌) (hf : preservesEnds f) (hg : preservesEnds g) :
    singleOperator (f ≫ g) (preservesEnds.comp_mem f g hf hg).1
        (preservesEnds.comp_mem f g hf hg).2 =
      singleOperator f hf.1 hf.2 ≫ singleOperator g hg.1 hg.2 := by
  apply Hom.ext
  change (singleIso a).hom ≫ SSet.stdSimplex.map (f ≫ g) ≫ (singleIso c).inv =
    ((singleIso a).hom ≫ SSet.stdSimplex.map f ≫ (singleIso b).inv) ≫
      ((singleIso b).hom ≫ SSet.stdSimplex.map g ≫ (singleIso c).inv)
  simp only [SSet.stdSimplex.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- Interpret an endpoint-preserving simplex operator as an actual native necklace map. -/
def bead : EndpointSimplex ⥤ NecklaceCode where
  obj a := single a.obj.len
  map f := singleOperator f.1 f.2.1 f.2.2
  map_id a := single_id a.obj.len
  map_comp {a b c} f g := single_comp (a := a.obj.len) (b := b.obj.len) (c := c.obj.len)
    f.1 g.1 f.2 g.2

/-- Keep the two exterior beads fixed while changing the middle bead. -/
def paddedBead : EndpointSimplex ⥤ NecklaceCode where
  obj a := code a.obj.len
  map f := padded (bead.map f)
  map_id a := by
    rw [bead.map_id]
    change wedgeMap (Hom.id.{0} (single 1))
      (wedgeMap (Hom.id (single a.obj.len)) (Hom.id (single 1))) = _
    rw [wedgeMap_id, wedgeMap_id]
    rfl
  map_comp f g := by rw [bead.map_comp, padded_comp]

/-- The padded cylinder's native code at each horizontal operator. -/
abbrev paddedSource (d : ℕ) : Slice d ⥤ NecklaceCode :=
  Over.forget (simplex d) ⋙ paddedBead

/-- The maps from the varying padded codes to the padded fixed target. -/
def paddedToTarget (d : ℕ) : paddedSource d ⟶ (Functor.const _).obj (code d) where
  app A := paddedBead.map A.hom
  naturality {A B} f := by
    change paddedBead.map f.left ≫ paddedBead.map B.hom = paddedBead.map A.hom ≫ 𝟙 _
    rw [← Functor.map_comp, Over.w, Category.comp_id]

end
end DaggerModels.PartII.JTEndpointSimplexSlice
