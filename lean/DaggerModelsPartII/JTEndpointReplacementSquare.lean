import DaggerModelsPartII.JTXiAugmentation
import DaggerModelsPartII.JTEndpointFrameComparison
import DaggerModelsPartII.JTEndpointMateUnder

/-!
# The actual replacement square for ordered endpoint cobases

The first zero-fixed replacement map induces a boundary-preserving map to
the original Gamma endpoint cobase. The actual Qlambda square then gives a
strict square with the existing Xi comparison and the original collapsed
Gamma-to-Xi map. Precomposition yields the corresponding literal square of
ordered-boundary Hom simplicial sets.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTEndpointReplacementSquare

open JTRelativeReedyFrame JTActualCosimplicialFrame JTEndpointObjects
open JTEndpointCofibrancy
open JTEndpointArrowReplacement JTEndpointAugmentations JTEndpointFrames
open JTEndpointCobaseAugmentations JTEndpointCobaseComparison
open JTEndpointHom JTEndpointMateUnder JTXiAugmentation

noncomputable section

private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : ModelCategory (Under Bdagger) :=
  JTEndpointCobase.underModel Bdagger

/-- The actual original Gamma arrow augmentation to the fixed `iota`. -/
def GammaArrowAugmentation :
    G ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota) :=
  arrowAugmentation augmentation

/-- The original Gamma endpoint cobase under its literal ordered boundary. -/
def GammaFrame : SimplexCategory ⥤ Under Bdagger :=
  underDiagram GammaArrowAugmentation

theorem GammaFrame_eq : GammaFrame = collapsedUnder augmentation := rfl

/-- The actual `qG` map, cobased under the unchanged ordered boundary. -/
def QGToGamma : QGFrame ⟶ GammaFrame :=
  underComparison qG QGaugmentation GammaArrowAugmentation rfl

/-- The target component of a composite arrow-diagram map is the composite
of its target components. -/
private theorem targetMap_comp
    {F F' F'' : SimplexCategory ⥤ Arrow Coefficient}
    (f : F ⟶ F') (g : F' ⟶ F'') :
    targetMap (f ≫ g) = targetMap f ≫ targetMap g := by
  ext k
  rfl

/-- Functoriality of the literal cobase comparison, verified on its two
specified pushout coprojections. -/
private theorem comparison_comp
    {F F' F'' : SimplexCategory ⥤ Arrow Coefficient}
    (f : F ⟶ F') (g : F' ⟶ F'')
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (a' : F' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (a'' : F'' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (hf : f ≫ a' = a) (hg : g ≫ a'' = a') :
    comparison f a a' hf ≫ comparison g a' a'' hg =
      comparison (f ≫ g) a a'' (by rw [Category.assoc, hg, hf]) := by
  apply pushout.hom_ext
  · calc
      boundary a ≫ (comparison f a a' hf ≫ comparison g a' a'' hg) =
          boundary a' ≫ comparison g a' a'' hg := by
            rw [← Category.assoc, boundary_comparison]
      _ = boundary a'' := boundary_comparison g a' a'' hg
      _ = boundary a ≫ comparison (f ≫ g) a a''
          (by rw [Category.assoc, hg, hf]) :=
        (boundary_comparison (f ≫ g) a a''
          (by rw [Category.assoc, hg, hf])).symm
  · calc
      frameInclusion a ≫ (comparison f a a' hf ≫ comparison g a' a'' hg) =
          (targetMap f ≫ frameInclusion a') ≫
            comparison g a' a'' hg := by
              rw [← Category.assoc, frameInclusion_comparison]
      _ = targetMap f ≫ (targetMap g ≫ frameInclusion a'') := by
            rw [Category.assoc, frameInclusion_comparison]
      _ = targetMap (f ≫ g) ≫ frameInclusion a'' := by
            rw [← Category.assoc, targetMap_comp]
      _ = frameInclusion a ≫ comparison (f ≫ g) a a''
          (by rw [Category.assoc, hg, hf]) :=
        (frameInclusion_comparison (f ≫ g) a a''
          (by rw [Category.assoc, hg, hf])).symm

private theorem underComparison_comp
    {F F' F'' : SimplexCategory ⥤ Arrow Coefficient}
    (f : F ⟶ F') (g : F' ⟶ F'')
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (a' : F' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (a'' : F'' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (hf : f ≫ a' = a) (hg : g ≫ a'' = a') :
    underComparison f a a' hf ≫ underComparison g a' a'' hg =
      underComparison (f ≫ g) a a''
        (by rw [Category.assoc, hg, hf]) := by
  apply NatTrans.ext
  funext k
  apply Under.UnderMorphism.ext
  exact NatTrans.congr_app (comparison_comp f g a a' a'' hf hg) k

private theorem underComparison_congr
    {F F' : SimplexCategory ⥤ Arrow Coefficient}
    {f g : F ⟶ F'} (hfg : f = g)
    (a : F ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (a' : F' ⟶ (Functor.const SimplexCategory).obj (Arrow.mk iota))
    (hf : f ≫ a' = a) (hg : g ≫ a' = a) :
    underComparison f a a' hf = underComparison g a a' hg := by
  cases hfg
  rfl

/-- The generic cobase comparison of the original `lambda` is the already
calibrated literal collapsed comparison of the original frames. -/
private theorem rawComparison_eq :
    underComparison lambda GammaArrowAugmentation XiArrowAugmentation
      lambda_augmentation = collapsedUnderComparison := by
  apply NatTrans.ext
  funext k
  apply Under.UnderMorphism.ext
  rfl

/-- The exact replacement square, without any raw Gamma weakness premise. -/
theorem replacement_square :
    JTEndpointFrameComparison.comparison ≫ QXToXi =
      QGToGamma ≫ collapsedUnderComparison := by
  let h₁ : (Qlambda ≫ qX) ≫ XiArrowAugmentation = QGaugmentation := by
    simpa only [QXaugmentation, Category.assoc] using Qlambda_augmentation
  let h₂ : (qG ≫ lambda) ≫ XiArrowAugmentation = QGaugmentation := by
    rw [Category.assoc]
    change qG ≫ (lambda ≫ arrowAugmentation XiAugmentationCurried) =
      qG ≫ arrowAugmentation augmentation
    rw [lambda_augmentation]
  calc
    JTEndpointFrameComparison.comparison ≫ QXToXi =
        underComparison (Qlambda ≫ qX) QGaugmentation
          XiArrowAugmentation h₁ :=
      underComparison_comp Qlambda qX QGaugmentation
        QXaugmentation XiArrowAugmentation Qlambda_augmentation rfl
    _ = underComparison (qG ≫ lambda) QGaugmentation
          XiArrowAugmentation h₂ :=
      underComparison_congr Qlambda_square QGaugmentation
        XiArrowAugmentation h₁ h₂
    _ = QGToGamma ≫ collapsedUnderComparison := by
      rw [← rawComparison_eq]
      exact (underComparison_comp qG lambda QGaugmentation
        GammaArrowAugmentation XiArrowAugmentation rfl lambda_augmentation).symm

/-- Precomposition by the actual `qG` cobase map on fixed-endpoint Hom
simplicial sets. -/
def QGToGamma_precomp (C : Coefficient) (x y : C.Obj) :
    underHomSSet augmentation C x y ⟶
      JTEndpointFrameComparison.homSSet QGFrame C x y :=
  Functor.whiskerRight (NatTrans.op QGToGamma)
    (yoneda.obj (targetUnder C x y))

/-- Precomposition by the actual `qX` cobase map on the same ordered pair. -/
def QXToXi_precomp (C : Coefficient) (x y : C.Obj) :
    underHomSSet XiAugmentationCurried C x y ⟶
      JTEndpointFrameComparison.homSSet QXFrame C x y :=
  Functor.whiskerRight (NatTrans.op QXToXi)
    (yoneda.obj (targetUnder C x y))

/-- The original raw ordered mate and the resolved comparison commute
strictly under the literal Hom identifications. -/
theorem hom_square (C : Coefficient) (x y : C.Obj) :
    underPrecomp C x y ≫ QGToGamma_precomp C x y =
      QXToXi_precomp C x y ≫ JTEndpointFrameComparison.precomp C x y := by
  have h := congrArg
    (fun t : QGFrame ⟶ XiFrame ↦
      Functor.whiskerRight (NatTrans.op t)
        (yoneda.obj (targetUnder C x y))) replacement_square
  simpa only [NatTrans.op_comp, Functor.whiskerRight_comp,
    underPrecomp, QGToGamma_precomp, QXToXi_precomp,
    JTEndpointFrameComparison.precomp] using h.symm

end

end DaggerModels.PartII.JTEndpointReplacementSquare
