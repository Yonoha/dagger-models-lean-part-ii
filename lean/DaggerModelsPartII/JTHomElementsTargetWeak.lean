import DaggerModelsPartII.JTGraphCylinderSpanProjection
import DaggerModelsPartII.TotalElementsWeakComparison

/-! The target projection of the original arrow-factorization elements. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHomElementsTargetWeak

noncomputable section

variable (D : Type) [SmallCategory D]

private abbrev E := (Functor.hom D).Elements

private def reverseObj (x : E D) : (Functor.hom Dᵒᵖ).Elements :=
  ⟨(op (op x.fst.2), x.fst.1), x.snd.op⟩

private def reverseMap {x y : E D} (f : x ⟶ y) :
    reverseObj D x ⟶ reverseObj D y := by
  refine CategoryOfElements.homMk _ _ ((f.val.2.op).op, f.val.1) ?_
  change f.val.2.op ≫ x.snd.op ≫ f.val.1 = y.snd.op
  have hf : f.val.1.unop ≫ x.snd ≫ f.val.2 = y.snd := f.property
  simpa only [op_comp, Category.assoc] using congrArg Quiver.Hom.op hf

def reverse : E D ⥤ (Functor.hom Dᵒᵖ).Elements where
  obj := reverseObj D
  map := reverseMap D
  map_id x := by
    apply CategoryOfElements.ext
    apply Prod.ext <;> rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    apply Prod.ext <;> rfl

private theorem reverse_full : (reverse D).Full where
  map_surjective {x y} g := by
    let f : x ⟶ y := CategoryOfElements.homMk _ _
      (g.val.2, g.val.1.unop.unop) (by
        change g.val.2.unop ≫ x.snd ≫ g.val.1.unop.unop = y.snd
        have hg : g.val.1.unop ≫ x.snd.op ≫ g.val.2 = y.snd.op := g.property
        simpa only [unop_comp, Category.assoc] using congrArg Quiver.Hom.unop hg)
    refine ⟨f, ?_⟩
    apply CategoryOfElements.ext
    apply Prod.ext <;> rfl

private theorem reverse_faithful : (reverse D).Faithful where
  map_injective {x y} f g h := by
    apply CategoryOfElements.ext
    have hh := congrArg (fun z : reverseObj D x ⟶ reverseObj D y ↦ z.val) h
    apply Prod.ext
    · exact congrArg Prod.snd hh
    · exact congrArg (fun z ↦ z.unop.unop) (congrArg Prod.fst hh)

private theorem reverse_surjective : Function.Surjective (reverse D).obj := by
  intro y
  let x : E D := ⟨(y.fst.2, y.fst.1.unop.unop), y.snd.unop⟩
  exact ⟨x, rfl⟩

private theorem target_factorization :
    reverse D ⋙
      (CategoryOfElements.π (Functor.hom Dᵒᵖ) ⋙
        CategoryTheory.Prod.fst (Dᵒᵖ)ᵒᵖ Dᵒᵖ) ⋙ unopUnop D =
      CategoryOfElements.π (Functor.hom D) ⋙ CategoryTheory.Prod.snd Dᵒᵖ D := by
  rfl

/-- The exact target projection of hom elements is Kan weak. -/
theorem homElements_target_weak :
    WeakEquivalence (nerveMap (CategoryOfElements.π (Functor.hom D) ⋙
      CategoryTheory.Prod.snd Dᵒᵖ D)) := by
  letI : (reverse D).Full := reverse_full D
  letI : (reverse D).Faithful := reverse_faithful D
  letI : (reverse D).EssSurj := Functor.essSurj_of_surj (reverse_surjective D)
  letI : (reverse D).IsEquivalence := {}
  haveI : WeakEquivalence (nerveMap (reverse D)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence (reverse D)
  haveI : WeakEquivalence (nerveMap
      (CategoryOfElements.π (Functor.hom Dᵒᵖ) ⋙
        CategoryTheory.Prod.fst (Dᵒᵖ)ᵒᵖ Dᵒᵖ)) :=
    JTGraphCylinderSpanProjection.homElements_source_weak Dᵒᵖ
  haveI : WeakEquivalence (nerveMap (unopUnop D)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  rw [← target_factorization D]
  change WeakEquivalence
    (nerveMap (reverse D) ≫
      nerveMap (CategoryOfElements.π (Functor.hom Dᵒᵖ) ⋙
        CategoryTheory.Prod.fst (Dᵒᵖ)ᵒᵖ Dᵒᵖ) ≫
        nerveMap (unopUnop D))
  infer_instance

end

end DaggerModels.PartII.JTHomElementsTargetWeak
