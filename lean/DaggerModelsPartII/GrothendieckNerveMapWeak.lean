import DaggerModelsPartII.GrothendieckNerveReplacement

/-! Fiberwise weak maps of category diagrams induce weak maps of their original total nerves. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementWeightsChange
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.GrothendieckNerveMapWeak

open GrothendieckNerveReplacement

noncomputable section

variable {C : Type u} [Category.{u} C] {F G : C ⥤ Cat.{u,u}} (α : F ⟶ G)

private abbrev π (H : C ⥤ Cat.{u,u}) := Grothendieck.forget H

private def commaAt (c : C) : CostructuredArrow (π F) c ⥤ CostructuredArrow (π G) c :=
  CostructuredArrow.pre (Grothendieck.map α) (π G) c

private theorem commaAt_natural {c d : C} (g : c ⟶ d) :
    CostructuredArrow.map g ⋙ commaAt α d = commaAt α c ⋙ CostructuredArrow.map g := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply CostructuredArrow.hom_ext
  rfl

private def commaChange : commaNerves F ⟶ commaNerves G :=
  Functor.whiskerRight
    { app c := (commaAt α c).toCatHom
      naturality := fun _ _ g ↦ Cat.Hom.ext (commaAt_natural α g) }
    nerveFunctor

private theorem retractSquare (c : C) :
    commaAt α c ⋙ GrothendieckCommaRetraction.retract G c =
      GrothendieckCommaRetraction.retract F c ⋙ (α.app c).toFunctor := by
  have objEq (X : CostructuredArrow (π F) c) :
      (G.map X.hom).toFunctor.obj ((α.app X.left.base).toFunctor.obj X.left.fiber) =
        (α.app c).toFunctor.obj ((F.map X.hom).toFunctor.obj X.left.fiber) :=
    congrArg (fun H : Cat.of (F.obj X.left.base) ⥤ G.obj c ↦ H.obj X.left.fiber)
      (congrArg Cat.Hom.toFunctor (α.naturality X.hom)).symm
  refine CategoryTheory.Functor.ext objEq ?_
  intro X Y f
  have h : (F.map Y.hom ≫ α.app c).toFunctor =
      (α.app Y.left.base ≫ G.map Y.hom).toFunctor :=
    congrArg Cat.Hom.toFunctor (α.naturality Y.hom)
  change eqToHom _ ≫ (G.map Y.hom).toFunctor.map ((Grothendieck.map α).map f.left).fiber =
      eqToHom _ ≫ (α.app c).toFunctor.map
        (eqToHom _ ≫ (F.map Y.hom).toFunctor.map f.left.fiber) ≫ eqToHom _
  simp only [Grothendieck.map, Functor.map_comp, eqToHom_map, Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    Category.assoc, eqToHom_trans_assoc, ← Cat.Hom.comp_map]
  rw [Functor.congr_hom h f.left.fiber]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem commaAt_weak (h : ∀ c : C, WeakEquivalence (nerveMap (α.app c).toFunctor))
    (c : C) : WeakEquivalence (nerveMap (commaAt α c)) := by
  have hcomm : nerveMap (commaAt α c) ≫ nerveMap (GrothendieckCommaRetraction.retract G c) =
      nerveMap (GrothendieckCommaRetraction.retract F c) ≫ nerveMap (α.app c).toFunctor := by
    have hfun := congrArg (fun f ↦ nerveMap f) (retractSquare α c)
    change nerveFunctor.map ((commaAt α c).toCatHom ≫
      (GrothendieckCommaRetraction.retract G c).toCatHom) =
        nerveFunctor.map ((GrothendieckCommaRetraction.retract F c).toCatHom ≫
          α.app c) at hfun
    simpa only [nerveFunctor.map_comp] using hfun
  haveI := GrothendieckCommaRetraction.retract_weak G c
  haveI := GrothendieckCommaRetraction.retract_weak F c
  haveI := h c
  exact weakEquivalence_of_postcomp_of_fac hcomm

private theorem change_weak (h : ∀ c : C, WeakEquivalence (nerveMap (α.app c).toFunctor)) :
    WeakEquivalence (diagonalChange (commaChange α)) := by
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_row
  intro q
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  exact DaggerNativeFamilyWeak.familyMap_weak _
    (fun c ↦ commaAt_weak α h (first c))

private theorem augmentation_square :
    diagonalChange (commaChange α) ≫ toGrothendieck G =
      toGrothendieck F ≫ nerveMap (Grothendieck.map α) := by
  apply NatTrans.ext
  funext k x
  rfl

/-- The actual total functor of a fiberwise weak natural transformation is Kan weak. -/
theorem map_weak (h : ∀ c : C, WeakEquivalence (nerveMap (α.app c).toFunctor)) :
    WeakEquivalence (nerveMap (Grothendieck.map α)) := by
  haveI := change_weak α h
  haveI := toGrothendieck_weak F
  haveI := toGrothendieck_weak G
  exact weakEquivalence_of_precomp_of_fac (augmentation_square α).symm

end

end DaggerModels.PartII.GrothendieckNerveMapWeak
