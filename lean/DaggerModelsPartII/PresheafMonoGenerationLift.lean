import DaggerModelsPartII.PresheafMonoGenerationBridge
import Mathlib.CategoryTheory.LiftingProperties.Adjunction

set_option autoImplicit false
open CategoryTheory Limits MorphismProperty
open scoped Simplicial
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

/-- The quotient-subobject family tests every cyclic-intersection inclusion
in the uncurried Type-valued diagram. -/
theorem quotientSubobjectGenerators_rlp_cyclicIntersection
    {X Y G : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : (quotientSubobjectGenerators C).rlp p)
    (S : Subfunctor (Functor.uncurry.obj G))
    (c : C) (n : ℕ)
    (x : (Functor.uncurry.obj G).obj (c, Opposite.op ⦋n⦌)) :
    HasLiftingProperty
      (Subfunctor.homOfLe
        (inf_le_right : S ⊓ PresheafMonoGeneration.cyclicSubfunctor
          (Functor.uncurry.obj G) x ≤
            PresheafMonoGeneration.cyclicSubfunctor
              (Functor.uncurry.obj G) x))
      (Functor.uncurry.map p) := by
  let B := Functor.uncurry.obj G
  let T := PresheafMonoGeneration.cyclicSubfunctor B x
  let j : (S ⊓ T).toFunctor ⟶ T.toFunctor :=
    Subfunctor.homOfLe inf_le_right
  let Q : C ⥤ SSet.{u} := Functor.curry.obj T.toFunctor
  obtain ⟨e, he⟩ := cyclicSubfunctor_regularEpi C G c n x
  letI : IsRegularEpi e := he
  let jc : Functor.curry.obj (S ⊓ T).toFunctor ⟶ Q := Functor.curry.map j
  letI : Functor.IsEquivalence (Functor.curry :
      (C × SimplexCategoryᵒᵖ ⥤ Type u) ⥤ (C ⥤ SSet.{u})) :=
    (Functor.currying :
      (C ⥤ SSet.{u}) ≌ (C × SimplexCategoryᵒᵖ ⥤ Type u)).isEquivalence_inverse
  haveI : Mono jc := inferInstance
  have hs : HasLiftingProperty (Subobject.mk jc).arrow p :=
    quotientSubobjectGenerators_rlp_regularEpi_subobject C p hp c n Q e (Subobject.mk jc)
  have hjc : HasLiftingProperty jc p := by
    let iso : Arrow.mk jc ≅ Arrow.mk (Subobject.mk jc).arrow :=
      Arrow.isoMk (Subobject.underlyingIso jc).symm (Iso.refl Q) (by simp)
    exact (HasLiftingProperty.iff_of_arrow_iso_left iso p).mpr hs
  let adj := (Functor.currying :
    (C ⥤ SSet.{u}) ≌ (C × SimplexCategoryᵒᵖ ⥤ Type u)).symm.toAdjunction
  exact (adj.hasLiftingProperty_iff j p).mp hjc

end
end DaggerModels.PartII.InjectiveKanDiagram
