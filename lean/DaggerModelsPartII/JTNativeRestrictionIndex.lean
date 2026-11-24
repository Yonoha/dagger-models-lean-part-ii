import DaggerModelsPartII.GrothendieckCommaRetraction
import ChosenNecklaceCode

/-!
All native restrictions into a varying original necklace form the actual comma
category of the native-code functor. The projection retains all original base
arrows. Its identity section and canonical deformation supply the existing nerve
homotopy-equivalence criterion, with no chosen restriction or new weak-cover axiom.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerChosenRigidificationNecklace HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNativeRestrictionIndex

noncomputable section

variable {A : Type} [SmallCategory A] (N : A ⥤ NecklaceCode)

/-- Every object is a whole endpoint-preserving native map into an old source. -/
abbrev Index := Comma (𝟭 NecklaceCode) N

/-- Retain the actual original index and every original operator. -/
abbrev projection : Index N ⥤ A := Comma.snd (𝟭 NecklaceCode) N

/-- Retain the whole restricted native source and its exact native operators. -/
abbrev native : Index N ⥤ NecklaceCode := Comma.fst (𝟭 NecklaceCode) N

/-- The canonical native comparison to the varying old source. -/
abbrev collapse : native N ⟶ projection N ⋙ N := Comma.natTrans (𝟭 NecklaceCode) N

/-- The unchanged original necklace is one actual restriction at every index. -/
def sectionFunctor : A ⥤ Index N where
  obj a := ⟨N.obj a, a, 𝟙 (N.obj a)⟩
  map f := ⟨N.map f, f, by
    change N.map f ≫ 𝟙 _ = 𝟙 _ ≫ N.map f
    exact (Category.comp_id _).trans (Category.id_comp _).symm⟩
  map_id a := CommaMorphism.ext (N.map_id a) rfl
  map_comp f g := CommaMorphism.ext (N.map_comp f g) rfl

/-- The section projects to the identical original full diagram. -/
theorem section_projection : sectionFunctor N ⋙ projection N = 𝟭 A := rfl

/-- Each actual native restriction compares to its original whole source. -/
def deformation : 𝟭 (Index N) ⟶ projection N ⋙ sectionFunctor N where
  app P := ⟨P.hom, 𝟙 P.right,
    by
      change P.hom ≫ 𝟙 (N.obj P.right) = P.hom ≫ N.map (𝟙 P.right)
      rw [N.map_id]⟩
  naturality {P Q} f := by
    apply CommaMorphism.ext
    · change f.left ≫ Q.hom = P.hom ≫ N.map f.right
      exact f.w
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- Keeping all native restrictions is a weak resolution of the exact old index. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection N)) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW (projection N) (sectionFunctor N)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨deformation N⟩))
      (Relation.EqvGen.rel _ _ ⟨eqToHom (section_projection N)⟩))

end
end DaggerModels.PartII.JTNativeRestrictionIndex
