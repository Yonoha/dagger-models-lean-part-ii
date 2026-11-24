import DaggerModelsPartII.JTCEJoyalResolution
import DaggerModelsPartII.EndpointMappingFiber

/-!
# Literal target maps on the fixed-boundary CE Hom simplicial set

The native coyoneda mapping functor from the actual CE diagram is
transported to the literal Hom simplicial set under its original ordered
boundary. Target morphisms act by postcomposition in `Under boundary`.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
  DaggerModels

namespace DaggerModels.PartII.JTCEPlainMappingTarget

open JTXiEndpointCollapse JTCEJoyalResolution

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel

private local instance : ModelCategory (Under boundary) :=
  JTEndpointCobase.underModel boundary

/-- The specified Hom simplicial set with its literal ordered boundary. -/
def plainCEHom (X : Under boundary) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := X) (Under.lift CE CE_boundary)

/-- Postcompose a map from the actual CE diagram by an under-boundary
target morphism. The resulting map still agrees with the fixed boundary. -/
def plainCEHomMap {X Y : Under boundary} (f : X ⟶ Y) :
    plainCEHom X ⟶ plainCEHom Y where
  app _ g := g ≫ f
  naturality {k l} θ := by
    funext (g : (Under.lift CE CE_boundary).obj k.unop ⟶ X)
    change ((Under.lift CE CE_boundary).map θ.unop ≫ g) ≫ f =
      (Under.lift CE CE_boundary).map θ.unop ≫ (g ≫ f)
    exact Category.assoc _ _ _

/-- Every simplex is sent by actual target postcomposition, including its
ordered boundary equation. -/
theorem plainCEHomMap_app {X Y : Under boundary} (f : X ⟶ Y)
    (k : SimplexCategoryᵒᵖ)
    (g : (Under.lift CE CE_boundary).obj k.unop ⟶ X) :
    (plainCEHomMap f).app k g = g ≫ f := rfl

/-- The postcomposed simplex still has the literal ordered CE boundary
specified by its target in `Under boundary`. -/
theorem plainCEHomMap_boundary {X Y : Under boundary} (f : X ⟶ Y)
    (k : SimplexCategory)
    (g : (Under.lift CE CE_boundary).obj k ⟶ X) :
    CE_boundary.app k ≫ ((plainCEHomMap f).app (op k) g).right = Y.hom := by
  exact Under.w ((plainCEHomMap f).app (op k) g)

/-- The original native-to-plain map is natural in the actual target of
the fixed-boundary CE Hom simplicial set. -/
theorem mapE_plainIso_naturality {X Y : Under boundary} (f : X ⟶ Y) :
    mapE.map f ≫ (mapE_plainIso Y).hom =
      (mapE_plainIso X).hom ≫ plainCEHomMap f := by
  apply NatTrans.ext
  funext k g
  rfl

open scoped SSet.modelCategoryQuillen in
/-- The literal postcomposition map is Kan weak whenever the target map
is an original ordinary Joyal weak equivalence between fibrant objects
under the same ordered boundary. -/
theorem plainCEHomMap_weak {X Y : Under boundary}
    [IsFibrant X] [IsFibrant Y] (f : X ⟶ Y)
    (hf : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences f.right) :
    DaggerSSetGluing.GW (plainCEHomMap f) := by
  let e : Arrow.mk (mapE.map f) ≅ Arrow.mk (plainCEHomMap f) :=
    Arrow.isoMk (mapE_plainIso X) (mapE_plainIso Y)
      (mapE_plainIso_naturality f).symm
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have hnative : weakEquivalences SSet.{0} (mapE.map f) := by
    rw [← weakEquivalence_iff]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (mapE_map_weak f hf)
  have hplain : weakEquivalences SSet.{0} (plainCEHomMap f) :=
    ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).1 hnative
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((weakEquivalence_iff _).2 hplain)

end

end DaggerModels.PartII.JTCEPlainMappingTarget
