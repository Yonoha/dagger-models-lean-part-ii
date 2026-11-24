import DaggerModelsPartII.GrothendieckNerveMapWeak
import DaggerModelsPartII.GrothendieckTotalElements
import DaggerModelsPartII.SimplicialResolutionFunctor
import NativeSimplicialOppositeKanWeak

/-! Pointwise Kan weak natural transformations on the original total labels. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.TotalElementsWeakComparison

noncomputable section

/-- Taking the opposite of the actual indexing functor preserves and reflects
Kan weakness of its nerve. -/
theorem nerveMap_op_iff {C D : Type} [SmallCategory C] [SmallCategory D] (f : C ⥤ D) :
    WeakEquivalence (nerveMap f.op) ↔ WeakEquivalence (nerveMap f) := by
  let e := DaggerNativeNerveOppositeIso.nerveOppositeIso C
  let e' := DaggerNativeNerveOppositeIso.nerveOppositeIso D
  have h : SSet.opFunctor.map (nerveMap f) ≫ e'.hom = e.hom ≫ nerveMap f.op :=
    DaggerNativeNerveOppositeIso.nerveOppositeNatIso.hom.naturality f.toCatHom
  calc
    WeakEquivalence (nerveMap f.op) ↔ WeakEquivalence (e.hom ≫ nerveMap f.op) :=
      (weakEquivalence_precomp_iff _ _).symm
    _ ↔ WeakEquivalence (SSet.opFunctor.map (nerveMap f) ≫ e'.hom) := by rw [h]
    _ ↔ WeakEquivalence (SSet.opFunctor.map (nerveMap f)) := weakEquivalence_postcomp_iff _ _
    _ ↔ WeakEquivalence (nerveMap f) := DaggerNativeSimplicialOppositeKanWeak.weak_op_iff _

/-- The actual opposite simplex-category nerve detects Kan weakness of a map. -/
theorem elementsOpposite_weak_iff {X Y : SSet.{0}} (f : X ⟶ Y) :
    WeakEquivalence (nerveMap (NatTrans.mapElements f).op) ↔ WeakEquivalence f := by
  open SimplicialResolutionFunctor in
  haveI := augmentation_weak X
  haveI := augmentation_weak Y
  haveI := SimplicialResolutionFunctor.elementsProjection_weak X
  haveI := SimplicialResolutionFunctor.elementsProjection_weak Y
  have hp : resolutionFunctor.map f ≫ elementsProjection.app Y =
      elementsProjection.app X ≫ nerveMap (NatTrans.mapElements f).op :=
    elementsProjection.naturality f
  have ha : resolutionFunctor.map f ≫ augmentation.app Y = augmentation.app X ≫ f :=
    augmentation.naturality f
  calc
    WeakEquivalence (nerveMap (NatTrans.mapElements f).op) ↔
        WeakEquivalence (elementsProjection.app X ≫ nerveMap (NatTrans.mapElements f).op) :=
      (weakEquivalence_precomp_iff _ _).symm
    _ ↔ WeakEquivalence (resolutionFunctor.map f ≫ elementsProjection.app Y) := by rw [hp]
    _ ↔ WeakEquivalence (resolutionFunctor.map f) := weakEquivalence_postcomp_iff _ _
    _ ↔ WeakEquivalence (resolutionFunctor.map f ≫ augmentation.app Y) :=
      (weakEquivalence_postcomp_iff _ _).symm
    _ ↔ WeakEquivalence (augmentation.app X ≫ f) := by rw [ha]
    _ ↔ WeakEquivalence f := weakEquivalence_precomp_iff _ _

private theorem elementsMap_weak {X Y : SSet.{0}} (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (nerveMap (Functor.elementsFunctor.map f).toFunctor) :=
  (nerveMap_op_iff _).mp ((elementsOpposite_weak_iff f).mpr inferInstance)

variable {C : Type} [SmallCategory C] {F G : C ⥤ SSet.{0}} (α : F ⟶ G)

/-- The map acts on the whole label and retains both of its original indices. -/
def totalMap :
    (GrothendieckTotalElements.totalDiagram F).Elements ⥤
      (GrothendieckTotalElements.totalDiagram G).Elements :=
  (Functor.uncurry.map α).mapElements

private theorem totalMap_square :
    GrothendieckTotalElements.toTotal F ⋙ totalMap α =
      Grothendieck.map (Functor.whiskerRight α Functor.elementsFunctor) ⋙
        GrothendieckTotalElements.toTotal G := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply CategoryOfElements.ext
  apply Prod.ext
  · rfl
  · have degree_eq {A : SSet.{0}} {i j : A.Elements} (h : i = j) :
        (eqToHom h : i ⟶ j).val = eqToHom (congrArg Sigma.fst h) := by
      cases h
      rfl
    let β := Functor.whiskerRight α Functor.elementsFunctor
    change f.fiber.val =
      ((eqToHom (β.naturality f.base).symm).toNatTrans.app X.fiber ≫
          ((Functor.elementsFunctor.map (α.app Y.base)).toFunctor.map f.fiber)).val
    simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
    rw [CategoryOfElements.comp_val, degree_eq]
    change f.fiber.val = 𝟙 X.fiber.fst ≫ f.fiber.val
    exact (Category.id_comp _).symm

/-- Pointwise Kan weak maps induce Kan weak maps of the original total
categories of labels, with no choice of a weak zigzag between their objects. -/
theorem totalMap_weak (h : ∀ c, WeakEquivalence (α.app c)) :
    WeakEquivalence (nerveMap (totalMap α)) := by
  let β := Functor.whiskerRight α Functor.elementsFunctor
  haveI : WeakEquivalence (nerveMap (Grothendieck.map β)) :=
    GrothendieckNerveMapWeak.map_weak β fun c ↦ by
      haveI := h c
      exact elementsMap_weak (α.app c)
  haveI : WeakEquivalence (nerveMap (GrothendieckTotalElements.toTotal F)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (GrothendieckTotalElements.equivalence F).functor
  haveI : WeakEquivalence (nerveMap (GrothendieckTotalElements.toTotal G)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence
      (GrothendieckTotalElements.equivalence G).functor
  have hs := congrArg (fun f ↦ nerveMap f) (totalMap_square α)
  change nerveFunctor.map ((GrothendieckTotalElements.toTotal F).toCatHom ≫
    (totalMap α).toCatHom) =
      nerveFunctor.map ((Grothendieck.map β).toCatHom ≫
        (GrothendieckTotalElements.toTotal G).toCatHom) at hs
  simp only [nerveFunctor.map_comp] at hs
  change nerveMap (GrothendieckTotalElements.toTotal F) ≫ nerveMap (totalMap α) =
    nerveMap (Grothendieck.map β) ≫ nerveMap (GrothendieckTotalElements.toTotal G) at hs
  exact weakEquivalence_of_precomp_of_fac hs

end

end DaggerModels.PartII.TotalElementsWeakComparison
