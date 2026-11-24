import DaggerModelsPartII.JTGraphCylinderSpanProjection
import NativeOverChainDecomposition
import NativeFullChainInjectivity
import NativeOverNerveWeakContractibility

/-! The actual last-vertex functor of the simplex category and its weak nerve. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphSimplexLastVertex

open JTGraphCylinderSimplexSpan (Simplices)
open DaggerNativeDualTheoremACells (last lastArrow lastArrow_id lastArrow_comp)
open DaggerNativeOverChainDecomposition (chainLift chainLift_forget chainLift_last overChainEquiv)

noncomputable section

variable (C : Type) [SmallCategory C]

private def lastMap {x y : Simplices C} (f : x ⟶ y) : last x.unop.snd ⟶ last y.unop.snd :=
  eqToHom (congrArg (fun a ↦ last a) f.unop.property).symm ≫ lastArrow f.unop.val y.unop.snd

/-- Take the last object of the original chain, with the original terminal suffix arrow. -/
def lastVertex : Simplices C ⥤ C where
  obj x := last x.unop.snd
  map := lastMap C
  map_id x := by
    rcases x with ⟨⟨q, u⟩⟩
    change eqToHom _ ≫ lastArrow (𝟙 q) u = 𝟙 _
    rw [lastArrow_id]
    exact Category.id_comp _
  map_comp {x y z} f g := by
    obtain ⟨f, rfl⟩ : ∃ k : y.unop ⟶ x.unop, k.op = f := ⟨f.unop, rfl⟩
    obtain ⟨g, rfl⟩ : ∃ k : z.unop ⟶ y.unop, k.op = g := ⟨g.unop, rfl⟩
    rcases x with ⟨⟨p, u⟩⟩
    rcases y with ⟨⟨q, v⟩⟩
    rcases z with ⟨⟨r, w⟩⟩
    rcases f with ⟨α, h⟩
    rcases g with ⟨β, h'⟩
    change q ⟶ p at α
    change r ⟶ q at β
    change (nerve C).map β w = v at h'
    subst v
    change (nerve C).map α ((nerve C).map β w) = u at h
    subst u
    change eqToHom _ ≫ lastArrow (β ≫ α) w =
      (eqToHom _ ≫ lastArrow α ((nerve C).map β w)) ≫ (eqToHom _ ≫ lastArrow β w)
    simp only [eqToHom_refl, Category.id_comp]
    exact lastArrow_comp β α w

private def forgetSimplices (c : C) : Simplices (Over c) ⥤ Simplices C :=
  (CategoryOfElements.map (nerveMap (Over.forget c))).op

private theorem last_arrow_naturality (c : C) {x y : Simplices (Over c)} (f : x ⟶ y) :
    (lastVertex C).map ((forgetSimplices C c).map f) ≫ (last y.unop.snd).hom =
      (last x.unop.snd).hom := by
  obtain ⟨f, rfl⟩ : ∃ k : y.unop ⟶ x.unop, k.op = f := ⟨f.unop, rfl⟩
  rcases x with ⟨⟨p, u⟩⟩
  rcases y with ⟨⟨q, v⟩⟩
  rcases f with ⟨α, h⟩
  change q ⟶ p at α
  change (nerve (Over c)).map α v = u at h
  subst u
  change (eqToHom _ ≫ (lastArrow α v).left) ≫ (last v).hom =
    (last ((nerve (Over c)).map α v)).hom
  simp only [eqToHom_refl, Category.id_comp]
  exact Over.w (lastArrow α v)

/-- A simplex over `c` gives its original base simplex and original final arrow to `c`. -/
def toComma (c : C) : Simplices (Over c) ⥤ CostructuredArrow (lastVertex C) c :=
  (forgetSimplices C c).toCostructuredArrow (lastVertex C) c
    (fun x ↦ (last x.unop.snd).hom) (fun f ↦ last_arrow_naturality C c f)

private theorem toComma_faithful (c : C) : (toComma C c).Faithful where
  map_injective {x y} f g h := by
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    exact congrArg (fun a : (toComma C c).obj x ⟶ (toComma C c).obj y ↦ a.left.unop.val) h

private theorem hom_heq {X Y c : C} (h : X = Y) (f : X ⟶ c) (g : Y ⟶ c)
    (w : eqToHom h.symm ≫ f = g) : HEq f g := by
  subst Y
  rw [eqToHom_refl, Category.id_comp] at w
  exact heq_of_eq w

private theorem toComma_full (c : C) : (toComma C c).Full where
  map_surjective {x y} f := by
    let α := f.left.unop.val
    have hA : ((nerve (Over c)).map α y.unop.snd) ⋙ Over.forget c =
        x.unop.snd ⋙ Over.forget c := f.left.unop.property
    have hL : (lastVertex C).map f.left ≫ (last y.unop.snd).hom =
        (last x.unop.snd).hom := CostructuredArrow.w f
    have hB : (nerve (Over c)).map α y.unop.snd = x.unop.snd := by
      apply (overChainEquiv C c x.unop.fst.unop.len).injective
      refine Sigma.ext hA ?_
      apply hom_heq C (congrArg (fun A ↦ A.obj (Fin.last x.unop.fst.unop.len)) hA)
      change eqToHom _ ≫ (last ((nerve (Over c)).map α y.unop.snd)).hom =
        (last x.unop.snd).hom
      rw [← Over.w (lastArrow α y.unop.snd), ← Category.assoc]
      exact hL
    refine ⟨(CategoryOfElements.homMk y.unop x.unop α hB).op, ?_⟩
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    rfl

private theorem toComma_surjective (c : C) : Function.Surjective (toComma C c).obj := by
  intro x
  let A := x.left.unop.snd
  let B := chainLift A x.hom
  refine ⟨op ⟨x.left.unop.fst, B⟩, ?_⟩
  apply DaggerNativeFullChainInjectivity.comma_object_eq
  · exact congrArg (fun a : (nerve C).obj x.left.unop.fst ↦
        op ((nerve C).elementsMk x.left.unop.fst a)) (chainLift_forget A x.hom)
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (chainLift_last A x.hom)

/-- The actual comma over `c` is equivalent to the simplex category of the original slice. -/
def commaEquivalence (c : C) : Simplices (Over c) ≌ CostructuredArrow (lastVertex C) c := by
  letI : (toComma C c).Full := toComma_full C c
  letI : (toComma C c).Faithful := toComma_faithful C c
  letI : (toComma C c).EssSurj := Functor.essSurj_of_surj (toComma_surjective C c)
  letI : (toComma C c).IsEquivalence := {}
  exact (toComma C c).asEquivalence

private theorem simplex_point_GW (c : C) : GW (pointMap (nerve (Simplices (Over c)))) := by
  let g := DaggerModels.PartII.SimplicialResolutionFunctor.elementsProjection.app (nerve (Over c))
  let h := DaggerModels.PartII.SimplicialResolutionFunctor.augmentation.app (nerve (Over c))
  have hg := DaggerModels.PartII.SimplicialResolutionFunctor.elementsProjection_weak (nerve (Over c))
  have hh := DaggerModels.PartII.SimplicialResolutionFunctor.augmentation_weak (nerve (Over c))
  have hp : WeakEquivalence (pointMap (nerve (Over c))) :=
    (weakEquivalence_iff_GW _).mpr (DaggerNativeOverNerveWeakContractibility.point_GW c)
  have hpoint : g ≫ pointMap (nerve (Simplices (Over c))) =
      h ≫ pointMap (nerve (Over c)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff g _).mp
  rw [hpoint]
  infer_instance

/-- The original last-vertex functor induces a Kan weak equivalence of nerves. -/
theorem lastVertex_weak : WeakEquivalence (nerveMap (lastVertex C)) := by
  apply (weakEquivalence_iff_GW _).mpr
  apply DaggerNerveTheoremA.nerveMap_GW
  intro c
  let f := nerveMap (commaEquivalence C c).functor
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have h : f ≫ pointMap (nerve (CostructuredArrow (lastVertex C) c)) =
      pointMap (nerve (Simplices (Over c))) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff f _).mp
  rw [h]
  exact (weakEquivalence_iff_GW _).mpr (simplex_point_GW C c)

/-- Forget the common cylinder fiber and take the last vertex of the domain simplex. -/
def toOriginal (L : C ⥤ NecklaceCode) :
    Grothendieck (JTGraphCylinderSimplexSpan.fibers C L) ⥤ C :=
  JTGraphCylinderSpanProjection.toSimplices C L ⋙ lastVertex C

/-- The direct projection from the entire cylinder-fiber resolution to the
original category induces a Kan weak equivalence of nerves. -/
theorem toOriginal_weak (L : C ⥤ NecklaceCode) : WeakEquivalence (nerveMap (toOriginal C L)) := by
  haveI := JTGraphCylinderSpanProjection.toSimplices_weak C L
  haveI := lastVertex_weak C
  change WeakEquivalence
    (nerveMap (JTGraphCylinderSpanProjection.toSimplices C L) ≫ nerveMap (lastVertex C))
  infer_instance

end

end DaggerModels.PartII.JTGraphSimplexLastVertex
