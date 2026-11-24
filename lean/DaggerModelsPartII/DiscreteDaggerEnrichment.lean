import ActualConstantEnrichmentFunctor
import OriginalUnitaryDiscreteEnrichmentRecovered

/-! Ordinary dagger functors are exactly enriched dagger functors between constant enrichments. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerActualConstantEnrichmentFunctor DaggerUnitaryDiscrete

universe u

namespace DaggerModels.PartII

noncomputable section

variable {A B : Type u} [Category.{u} A] [DaggerCategory A] [Category.{u} B] [DaggerCategory B]

/-- Extend an ordinary dagger functor to the constant simplicial enrichments. -/
def discreteDaggerFunctor (F : A ⥤ B) [DaggerFunctor F] :
    ordinaryEnrichment A ⟶ ordinaryEnrichment B where
  toEnrichedFunctor := constantMap F
  map_dagger x y := by
    apply NatTrans.ext
    funext n f
    exact DaggerFunctor.map_dagger f |>.symm

/-- Restrict a functor between constant enrichments to degree zero. -/
def fromDiscreteDaggerFunctor (F : ordinaryEnrichment A ⟶ ordinaryEnrichment B) : A ⥤ B where
  obj := F.obj
  map {x y} f := (F.map x y).app (op ⦋0⦌) f
  map_id x := congrFun (congr_app (F.map_id x) (op ⦋0⦌)) PUnit.unit
  map_comp f g := congrFun (congr_app (F.map_comp _ _ _) (op ⦋0⦌)) (f, g)

instance fromDiscreteDaggerFunctor_preservesDagger
    (F : ordinaryEnrichment A ⟶ ordinaryEnrichment B) :
    DaggerFunctor (fromDiscreteDaggerFunctor F) where
  map_dagger f := (congrFun (congr_app (F.map_dagger _ _) (op ⦋0⦌)) f).symm

/-- The identification uses all enriched dagger functors, since naturality
forces their maps between constant Hom simplicial sets to be degreewise constant. -/
def discreteDaggerFunctorEquiv :
    {F : A ⥤ B // DaggerFunctor F} ≃ (ordinaryEnrichment A ⟶ ordinaryEnrichment B) where
  toFun F := @discreteDaggerFunctor _ _ _ _ _ _ F.1 F.2
  invFun F := ⟨fromDiscreteDaggerFunctor F, inferInstance⟩
  left_inv F := by
    apply Subtype.ext
    rfl
  right_inv F := by
    apply DaggerSimplicialCat.Hom.ext
    change constantMap (fromDiscreteDaggerFunctor F) = F.toEnrichedFunctor
    letI : EnrichedCategory SSet.{u} A := ordinaryEnriched A
    letI : EnrichedCategory SSet.{u} B := ordinaryEnriched B
    letI := (DaggerActualConstantSimplicialCategory.constant A).enriched
    letI := (DaggerActualConstantSimplicialCategory.constant B).enriched
    apply EnrichedFunctor.ext SSet (F := constantMap (fromDiscreteDaggerFunctor F))
      (G := F.toEnrichedFunctor) (fun _ ↦ rfl)
    intro x y
    simp only [eqToHom_refl, Category.comp_id]
    apply NatTrans.ext
    funext n f
    let p : op ⦋0⦌ ⟶ n := (SimplexCategory.const n.unop ⦋0⦌ 0).op
    exact (congrFun ((F.map x y).naturality p) f).symm

end

end DaggerModels.PartII
