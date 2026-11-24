import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.EndpointMappingFiber
import Mathlib.CategoryTheory.Limits.Over

/-!
# Parametrized maps over a fixed simplicial set

The source is tensored with a cosimplicial parameter. The map to the
fixed base factors through the original source projection in every
degree. These mapping spaces carry pushouts over the base to pullbacks.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTOverParametrizedMapping

noncomputable section

variable (K : SimplexCategory ⥤ SSet.{0}) (U : SSet.{0})

private def frameObj (P : Over U) : SimplexCategory ⥤ Over U :=
  Over.lift (K ⋙ tensorLeft P.left) {
    app k := fst P.left (K.obj k) ≫ P.hom
    naturality := by
      intro k l g
      change (𝟙 P.left ⊗ₘ K.map g) ≫ fst P.left (K.obj l) ≫ P.hom =
        (fst P.left (K.obj k) ≫ P.hom) ≫ 𝟙 U
      have h := tensorHom_fst (𝟙 P.left) (K.map g)
      simpa only [Category.assoc, Category.comp_id] using
        congrArg (fun t ↦ t ≫ P.hom) h }

private def frameMap {P P' : Over U} (g : P ⟶ P') : frameObj K U P ⟶ frameObj K U P' where
  app k := Over.homMk (g.left ⊗ₘ 𝟙 (K.obj k)) (by
    change (g.left ⊗ₘ 𝟙 (K.obj k)) ≫ fst P'.left (K.obj k) ≫ P'.hom =
      fst P.left (K.obj k) ≫ P.hom
    rw [← Category.assoc, tensorHom_fst, Category.assoc, Over.w g])
  naturality {_ _} g' := by
    apply Over.OverMorphism.ext
    change (𝟙 P.left ⊗ₘ K.map g') ≫ (g.left ⊗ₘ 𝟙 _) =
      (g.left ⊗ₘ 𝟙 _) ≫ (𝟙 P'.left ⊗ₘ K.map g')
    simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

/-- Tensor over the base by the full cosimplicial parameter. -/
def frame : Over U ⥤ SimplexCategory ⥤ Over U where
  obj := frameObj K U
  map := frameMap K U
  map_id P := by
    apply NatTrans.ext
    funext k
    apply Over.OverMorphism.ext
    exact id_tensorHom_id P.left (K.obj k)
  map_comp {P _ _} g h := by
    apply NatTrans.ext
    funext k
    apply Over.OverMorphism.ext
    change ((g.left ≫ h.left) ⊗ₘ 𝟙 (K.obj k)) =
      (g.left ⊗ₘ 𝟙 (K.obj k)) ≫ (h.left ⊗ₘ 𝟙 (K.obj k))
    simp only [tensorHom_comp_tensorHom, Category.id_comp]

theorem frame_obj_hom (P : Over U) (k : SimplexCategory) :
    (((frame K U).obj P).obj k).hom = fst P.left (K.obj k) ≫ P.hom := rfl

theorem frame_map_left {P P' : Over U} (g : P ⟶ P') (k : SimplexCategory) :
    (((frame K U).map g).app k).left = g.left ⊗ₘ 𝟙 (K.obj k) := rfl

/-- All simplicial parameter maps over the base to one fixed object. -/
def mapping (P A : Over U) : SSet.{0} :=
  EndpointMappingFiber.mapping (Z := A) ((frame K U).obj P)

/-- Restriction of the whole parametrized map along a source arrow. -/
def precomp {P P' : Over U} (g : P ⟶ P') (A : Over U) :
    mapping K U P' A ⟶ mapping K U P A :=
  EndpointMappingFiber.precomp (Z := A) ((frame K U).map g)

/-- Postcomposition of the whole parametrized map along a target arrow. -/
def postcomp (P : Over U) {A A' : Over U} (h : A ⟶ A') :
    mapping K U P A ⟶ mapping K U P A' :=
  Functor.whiskerLeft ((frame K U).obj P).op (yoneda.map h)

@[reassoc]
theorem precomp_postcomp {P P' A A' : Over U} (g : P ⟶ P') (h : A ⟶ A') :
    precomp K U g A ≫ postcomp K U P h =
      postcomp K U P' h ≫ precomp K U g A' := by
  apply NatTrans.ext
  funext k v
  change ((((frame K U).map g).app k.unop ≫ v) ≫ h) =
    (((frame K U).map g).app k.unop ≫ (v ≫ h))
  exact Category.assoc _ _ _

variable {M L R P : Over U} {ml : M ⟶ L} {mr : M ⟶ R}
  {l : L ⟶ P} {r : R ⟶ P}

/-- The frame of a pushout over the base is a pushout in each parameter degree. -/
theorem frameAt_isPushout (sq : IsPushout ml mr l r) (k : SimplexCategory) :
    IsPushout (((frame K U).map ml).app k) (((frame K U).map mr).app k)
      (((frame K U).map l).app k) (((frame K U).map r).app k) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfShape WalkingSpan (tensorRight (K.obj k)) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (K.obj k))
  apply IsPushout.of_map_of_faithful (Over.forget U)
  exact (sq.map (Over.forget U)).map (tensorRight (K.obj k))

/-- Mapping a pushout over the base gives the strict pullback of the three
restriction spaces, for every degree of the chosen parameter. -/
theorem mapping_isPullback (sq : IsPushout ml mr l r) (A : Over U) :
    IsPullback (precomp K U l A) (precomp K U r A)
      (precomp K U ml A) (precomp K U mr A) := by
  have at_degree (k : SimplexCategoryᵒᵖ) :
      IsPullback ((precomp K U l A).app k) ((precomp K U r A).app k)
        ((precomp K U ml A).app k) ((precomp K U mr A).app k) :=
    ((frameAt_isPushout K U sq k.unop).op.map (yoneda.obj A)).flip
  refine ⟨?_, ⟨evaluationJointlyReflectsLimits _ (fun k ↦ ?_)⟩⟩
  · constructor
    apply NatTrans.ext
    funext k v
    exact congrFun (at_degree k).w v
  · exact (PullbackCone.isLimitMapConeEquiv _ _).2 (at_degree k).isLimit

end

end DaggerModels.PartII.JTOverParametrizedMapping
