import DaggerModelsPartII.JTFrameAdjunction
import DaggerModelsPartII.JTEndpointAugmentations
import DaggerModelsPartII.JTEndpointHom
import DaggerModelsPartII.EndpointMappingFiber

/-!
# The actual Gamma mapping row and its ordered endpoint arrow

The source of the endpoint arrow is the literal pair of outer-zero frames.
Taking Hom into a fixed dagger simplicial category identifies its row with
the product of the two outer-zero Hom rows. The selected boundary map is sent
to the two specified object points, in their original order.

This module concerns strict mapping simplicial sets. It does not assert a
homotopy-fiber comparison or a weak equivalence.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTGammaRowEndpoints

open JTFrameAdjunction JTRelativeReedyFrame JTOrderedFrameMate
open JTEndpointHom JTEndpointObjects JTZeroObjects JTActualCosimplicialFrame

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits

/-- The actual row of the frame nerve, with its raw Hom elements. -/
def gammaRow (C : DaggerSimplicialCat.{0, 0}) (m : ReverseSimplex) : SSet.{0} :=
  (frameNerve.obj C).obj (op m)

/-- Evaluation of the actual frame nerve is the Hom row of the same original
Gamma frame. The components fix each raw Hom element. -/
def gammaRowMappingIso (C : DaggerSimplicialCat.{0, 0})
    (m : ReverseSimplex) :
    gammaRow C m ≅ EndpointMappingFiber.mapping (Z := C)
      (GammaOuter.obj m) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro j k θ
    ext f
    change frameParameter.map
        (show (m, k.unop) ⟶ (m, j.unop) from (𝟙 m, θ.unop)) ≫ f =
      (GammaOuter.obj m).map θ.unop ≫ f
    rw [frameParameter_vertical_map])

/-- The Hom row of the actual two-copy endpoint source. -/
def endpointSourceRow (C : DaggerSimplicialCat.{0, 0}) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := C) (endpointSource Gamma)

/-- The ordered product of the two outer-zero Hom rows, written pointwise. -/
def zeroPairRow (C : DaggerSimplicialCat.{0, 0}) : SSet.{0} where
  obj k := ((Gamma.obj k.unop).obj zeroIndex ⟶ C) ×
    ((Gamma.obj k.unop).obj zeroIndex ⟶ C)
  map θ p :=
    (((Gamma.map θ.unop).app zeroIndex ≫ p.1),
      ((Gamma.map θ.unop).app zeroIndex ≫ p.2))
  map_id k := by
    funext p
    change (((Gamma.map (𝟙 k.unop)).app zeroIndex ≫ p.1),
      ((Gamma.map (𝟙 k.unop)).app zeroIndex ≫ p.2)) = p
    apply Prod.ext <;> simp only [Gamma.map_id, NatTrans.id_app, Category.id_comp]
  map_comp θ ψ := by
    funext p
    change (((Gamma.map (ψ.unop ≫ θ.unop)).app zeroIndex ≫ p.1),
      ((Gamma.map (ψ.unop ≫ θ.unop)).app zeroIndex ≫ p.2)) =
        (((Gamma.map ψ.unop).app zeroIndex ≫
          ((Gamma.map θ.unop).app zeroIndex ≫ p.1)),
          ((Gamma.map ψ.unop).app zeroIndex ≫
            ((Gamma.map θ.unop).app zeroIndex ≫ p.2)))
    apply Prod.ext <;>
      simp only [Gamma.map_comp, NatTrans.comp_app, Category.assoc]

/-- The coproduct universal property in every actual vertical degree. -/
def endpointSourceHomEquiv (C : DaggerSimplicialCat.{0, 0})
    (k : SimplexCategory) :
    ((endpointSource Gamma).obj k ⟶ C) ≃
      (((Gamma.obj k).obj zeroIndex ⟶ C) ×
        ((Gamma.obj k).obj zeroIndex ⟶ C)) where
  toFun f := (coprod.inl ≫ f, coprod.inr ≫ f)
  invFun p := coprod.desc p.1 p.2
  left_inv f := by
    apply coprod.hom_ext <;> simp
  right_inv p := by
    apply Prod.ext <;> simp

/-- The actual two-copy source row equals the ordered product row, naturally
in the entire simplex operator, not just degree by degree. -/
def endpointSourceRowIso (C : DaggerSimplicialCat.{0, 0}) :
    endpointSourceRow C ≅ zeroPairRow C :=
  NatIso.ofComponents
    (fun k => (endpointSourceHomEquiv C k.unop).toIso)
    (by
      intro j k θ
      ext f
      apply Prod.ext
      · change coprod.inl ≫
          (coprod.map ((Gamma.map θ.unop).app zeroIndex)
            ((Gamma.map θ.unop).app zeroIndex) ≫ f) =
            (Gamma.map θ.unop).app zeroIndex ≫ (coprod.inl ≫ f)
        rw [← Category.assoc, coprod.inl_map, Category.assoc]
      · change coprod.inr ≫
          (coprod.map ((Gamma.map θ.unop).app zeroIndex)
            ((Gamma.map θ.unop).app zeroIndex) ≫ f) =
            (Gamma.map θ.unop).app zeroIndex ≫ (coprod.inr ≫ f)
        rw [← Category.assoc, coprod.inr_map, Category.assoc])

/-- The actual outer-one endpoint arrow, before choosing a boundary point. -/
def gammaEndpointArrow (C : DaggerSimplicialCat.{0, 0}) :
    gammaRow C oneIndex ⟶ endpointSourceRow C :=
  (gammaRowMappingIso C oneIndex).hom ≫
    EndpointMappingFiber.precomp (Z := C) (endpointFaces Gamma)

/-- The chosen ordered endpoint point in the actual source Hom row. -/
def boundaryPoint (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    (Δ[0] : SSet.{0}) ⟶ endpointSourceRow C :=
  EndpointMappingFiber.endpointPoint (endpointCollapse augmentation)
    (boundaryTarget C x y)

/-- Under the coproduct Hom isomorphism, the endpoint arrow has exactly
the two ordered restrictions along the original outer vertex maps. -/
theorem gammaEndpointArrow_val (C : DaggerSimplicialCat.{0, 0})
    (k : SimplexCategory) (f : (Gamma.obj k).obj oneIndex ⟶ C) :
    (endpointSourceRowIso C).hom.app (op k)
        ((gammaEndpointArrow C).app (op k) f) =
      ((Gamma.obj k).map (vertex 0) ≫ f,
        (Gamma.obj k).map (vertex 1) ≫ f) := by
  apply Prod.ext
  · change coprod.inl ≫
      (coprod.desc ((Gamma.obj k).map (vertex 0)) ((Gamma.obj k).map (vertex 1)) ≫ f) = _
    rw [← Category.assoc, coprod.inl_desc]
  · change coprod.inr ≫
      (coprod.desc ((Gamma.obj k).map (vertex 0)) ((Gamma.obj k).map (vertex 1)) ≫ f) = _
    rw [← Category.assoc, coprod.inr_desc]

/-- The prescribed boundary point has precisely the two original object
points after the Hom-coproduct identification. -/
theorem boundaryPoint_val (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) (k : SimplexCategory) :
    (endpointSourceHomEquiv C k)
      ((endpointCollapse augmentation).app k ≫ boundaryTarget C x y) =
      (((augmentation.app k).app zeroIndex ≫ objectMap C x),
        ((augmentation.app k).app zeroIndex ≫ objectMap C y)) := by
  apply Prod.ext
  · change coprod.inl ≫
      (coprod.desc ((augmentation.app k).app zeroIndex ≫ endpointMap 0)
        ((augmentation.app k).app zeroIndex ≫ endpointMap 1) ≫ boundaryTarget C x y) = _
    rw [← Category.assoc, coprod.inl_desc, Category.assoc,
      endpointMap_boundaryTarget_zero]
  · change coprod.inr ≫
      (coprod.desc ((augmentation.app k).app zeroIndex ≫ endpointMap 0)
        ((augmentation.app k).app zeroIndex ≫ endpointMap 1) ≫ boundaryTarget C x y) = _
    rw [← Category.assoc, coprod.inr_desc, Category.assoc,
      endpointMap_boundaryTarget_one]

/-- The same endpoint calibration for the actual natural point map. -/
theorem boundaryPoint_app (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) (k : SimplexCategory)
    (s : (Δ[0] : SSet.{0}).obj (op k)) :
    (endpointSourceRowIso C).hom.app (op k)
        ((boundaryPoint C x y).app (op k) s) =
      (((augmentation.app k).app zeroIndex ≫ objectMap C x),
        ((augmentation.app k).app zeroIndex ≫ objectMap C y)) := by
  exact boundaryPoint_val C x y k

end

end DaggerModels.PartII.JTGammaRowEndpoints
