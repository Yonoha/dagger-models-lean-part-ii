import DaggerModelsPartII.PresheafMonoGeneration

set_option autoImplicit false
open CategoryTheory Limits
universe u v w
namespace DaggerModels.PartII.PresheafMonoGeneration
variable {D : Type u} [Category.{u} D]

private theorem sup_has_index {I : Type w} {B : D ⥤ Type v}
    (S : I → Subfunctor B) (d : D) (z : (⨆ i, S i).toFunctor.obj d) :
    ∃ i : I, z.val ∈ (S i).obj d := by
  simpa only [Subfunctor.iSup_obj, Set.mem_iUnion] using z.property

private noncomputable def sup_chooseIndex {I : Type w} {B : D ⥤ Type v}
    (S : I → Subfunctor B) (d : D) (z : (⨆ i, S i).toFunctor.obj d) : I :=
  Classical.choose (sup_has_index S d z)

private theorem sup_chooseMem {I : Type w} {B : D ⥤ Type v}
    (S : I → Subfunctor B) (d : D) (z : (⨆ i, S i).toFunctor.obj d) :
    z.val ∈ (S (sup_chooseIndex S d z)).obj d :=
  Classical.choose_spec (sup_has_index S d z)

/-- Pairwise compatible maps out of subfunctors glue over their union. -/
noncomputable def glueOnISup {I : Type w} {B X : D ⥤ Type v}
    (S : I → Subfunctor B) (t : ∀ i, (S i).toFunctor ⟶ X)
    (hcompat : ∀ i j d (y : B.obj d) (hi : y ∈ (S i).obj d)
      (hj : y ∈ (S j).obj d),
      (t i).app d ⟨y, hi⟩ = (t j).app d ⟨y, hj⟩) :
    (⨆ i, S i).toFunctor ⟶ X where
  app d z :=
    (t (sup_chooseIndex S d z)).app d ⟨z.val, sup_chooseMem S d z⟩
  naturality d e f := by
    funext z
    let i := sup_chooseIndex S d z
    let j := sup_chooseIndex S e ((⨆ i, S i).toFunctor.map f z)
    have h₁ := sup_chooseMem S d z
    have h₂ := sup_chooseMem S e ((⨆ i, S i).toFunctor.map f z)
    have h₃ : B.map f z.val ∈ (S i).obj e := (S i).map f h₁
    have hcmp := hcompat j i e (B.map f z.val) h₂ h₃
    have hnat := FunctorToTypes.naturality (S i).toFunctor X (t i) f ⟨z.val, h₁⟩
    exact hcmp.trans hnat

/-- The glued map restricts to each member of the family. -/
theorem homOfLe_glueOnISup {I : Type w} {B X : D ⥤ Type v}
    (S : I → Subfunctor B) (t : ∀ i, (S i).toFunctor ⟶ X)
    (hcompat : ∀ i j d (y : B.obj d) (hi : y ∈ (S i).obj d)
      (hj : y ∈ (S j).obj d),
      (t i).app d ⟨y, hi⟩ = (t j).app d ⟨y, hj⟩)
    (i : I) :
    Subfunctor.homOfLe (le_iSup S i) ≫ glueOnISup S t hcompat = t i := by
  ext d z
  exact hcompat _ i d z.val (sup_chooseMem S d
    ((Subfunctor.homOfLe (le_iSup S i)).app d z)) z.property

end DaggerModels.PartII.PresheafMonoGeneration
