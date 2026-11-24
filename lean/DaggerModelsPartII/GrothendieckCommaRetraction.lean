import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import NerveHomotopy
import NativeGroupoidCompletionNerveBaseCases

/-!
# The actual comma-to-fiber retraction of a Grothendieck projection

The component functor uses the original transport and fiber morphisms.
No fiber contractibility or invertibility assumption is introduced.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.GrothendieckCommaRetraction

noncomputable section

variable {C : Type u} [Category.{u} C] (F : C ⥤ Cat.{u,u})

private abbrev π := Grothendieck.forget F

/-- The exact transport equality determined by the actual comma triangle. -/
private theorem transportEq {c : C} {P Q : CostructuredArrow (π F) c} (f : P ⟶ Q) :
    (F.map P.hom).toFunctor.obj P.left.fiber =
      (F.map Q.hom).toFunctor.obj ((F.map f.left.base).toFunctor.obj P.left.fiber) := by
  rw [← Cat.Hom.comp_obj, ← F.map_comp]
  have h : f.left.base ≫ Q.hom = P.hom := CostructuredArrow.w f
  rw [h]

/-- Apply the actual target transport to the actual Grothendieck fiber arrow. -/
private def retractMap {c : C} {P Q : CostructuredArrow (π F) c} (f : P ⟶ Q) :
    (F.map P.hom).toFunctor.obj P.left.fiber ⟶
      (F.map Q.hom).toFunctor.obj Q.left.fiber :=
  eqToHom (transportEq F f) ≫ (F.map Q.hom).toFunctor.map f.left.fiber

/-- Retraction of the actual projection comma onto the original target fiber. -/
def retract (c : C) : CostructuredArrow (π F) c ⥤ F.obj c where
  obj P := (F.map P.hom).toFunctor.obj P.left.fiber
  map := retractMap F
  map_id P := by
    simp only [retractMap, CostructuredArrow.id_left, Grothendieck.id_fiber,
      eqToHom_map, eqToHom_trans, eqToHom_refl]
  map_comp {P Q R} f g := by
    have h : g.left.base ≫ R.hom = Q.hom := CostructuredArrow.w g
    have hc : F.map g.left.base ≫ F.map R.hom = F.map Q.hom := by
      rw [← F.map_comp, h]
    have hf := congrArg Cat.Hom.toFunctor hc
    simp only [retractMap, CostructuredArrow.comp_left, Grothendieck.comp_fiber,
      Functor.map_comp, eqToHom_map, ← Cat.Hom.comp_map, Category.assoc]
    rw [Functor.congr_hom hf f.left.fiber]
    simp only [Category.assoc, eqToHom_trans_assoc]

private theorem postcompObj {c d : C} (g : c ⟶ d)
    (P : CostructuredArrow (π F) c) :
    (retract F d).obj ((CostructuredArrow.map g).obj P) =
      (F.map g).toFunctor.obj ((retract F c).obj P) := by
  change (F.map (P.hom ≫ g)).toFunctor.obj P.left.fiber = _
  rw [F.map_comp]
  rfl

/-- Retraction commutes with every original base arrow, as an equality of full functors. -/
theorem retract_natural {c d : C} (g : c ⟶ d) :
    CostructuredArrow.map g ⋙ retract F d = retract F c ⋙ (F.map g).toFunctor := by
  refine CategoryTheory.Functor.ext (postcompObj F g) ?_
  intro P Q f
  have hf := congrArg Cat.Hom.toFunctor (F.map_comp Q.hom g)
  dsimp only [Functor.comp_map, retract]
  simp only [retractMap, Functor.map_comp, eqToHom_map,
    ← Cat.Hom.comp_map, Category.assoc, eqToHom_trans_assoc]
  change eqToHom _ ≫ (F.map (Q.hom ≫ g)).toFunctor.map f.left.fiber =
    eqToHom _ ≫ (F.map Q.hom ≫ F.map g).toFunctor.map f.left.fiber ≫ eqToHom _
  rw [Functor.congr_hom hf f.left.fiber]
  simp only [eqToHom_trans_assoc]

/-- The actual comma-to-fiber retraction is natural on the whole Cat diagram. -/
def retraction : CostructuredArrow.functor (π F) ⟶ F where
  app c := (retract F c).toCatHom
  naturality {_ _} g := by
    apply Cat.Hom.ext
    exact retract_natural F g

/-- The actual original fiber includes over the identity base arrow. -/
def inclusion (c : C) : F.obj c ⥤ CostructuredArrow (π F) c where
  obj x := CostructuredArrow.mk (Y := (Grothendieck.ι F c).obj x) (𝟙 c)
  map f := CostructuredArrow.homMk ((Grothendieck.ι F c).map f) (by
    change 𝟙 c ≫ 𝟙 c = 𝟙 c
    exact Category.id_comp _)
  map_id x := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι F c).map_id x
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    exact (Grothendieck.ι F c).map_comp f g

/-- The fiber roundtrip is the identity on the original full fiber functor. -/
theorem inclusion_retract (c : C) : inclusion F c ⋙ retract F c = 𝟭 (F.obj c) := by
  have h : inclusion F c ⋙ retract F c = (F.map (𝟙 c)).toFunctor := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro x y f
    dsimp only [Functor.comp_map, inclusion, retract, retractMap, Grothendieck.ι]
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change eqToHom _ ≫ (F.map (𝟙 c)).toFunctor.map (eqToHom _ ≫ f) =
      (F.map (𝟙 c)).toFunctor.map f
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
  rw [h, F.map_id]
  rfl

/-- Original Grothendieck transport deforms every comma object to its fiber image. -/
def deformation (c : C) :
    𝟭 (CostructuredArrow (π F) c) ⟶ retract F c ⋙ inclusion F c where
  app P := CostructuredArrow.homMk (Grothendieck.toTransport P.left P.hom) (by
    change P.hom ≫ 𝟙 c = P.hom
    exact Category.comp_id _)
  naturality {P Q} f := by
    apply CostructuredArrow.hom_ext
    refine Grothendieck.ext _ _ ?_ ?_
    · change f.left.base ≫ Q.hom = P.hom ≫ 𝟙 c
      have h : f.left.base ≫ Q.hom = P.hom := CostructuredArrow.w f
      exact h.trans (Category.comp_id _).symm
    · change eqToHom _ ≫ (f.left ≫ Grothendieck.toTransport Q.left Q.hom).fiber =
        (Grothendieck.toTransport P.left P.hom ≫
          (Grothendieck.ι F c).map (retractMap F f)).fiber
      simp only [Grothendieck.comp_fiber, Grothendieck.toTransport, Grothendieck.ι,
        retractMap, Category.comp_id, eqToHom_trans_assoc]
      rw [(F.map (𝟙 c)).toFunctor.map_id]
      simp only [Category.id_comp, eqToHom_trans_assoc]

/-- The actual comma-to-original-fiber nerve map is Kan weak for every fiber. -/
theorem retract_weak (c : C) : WeakEquivalence (nerveMap (retract F c)) :=
  (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW (retract F c) (inclusion F c)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨deformation F c⟩))
      (Relation.EqvGen.rel _ _ ⟨eqToHom (inclusion_retract F c)⟩))

end

end DaggerModels.PartII.GrothendieckCommaRetraction
