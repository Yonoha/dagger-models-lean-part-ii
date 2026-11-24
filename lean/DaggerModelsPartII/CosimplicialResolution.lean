import DaggerModelsPartII.SimplicialReedyModel
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.AlgebraicTopology.ModelCategory.Opposite

/-! Cosimplicial resolutions obtained from the Reedy model in the opposite category. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance cosimplicialResolutionOppositeModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

/-- A cosimplicial resolution in opposite form, with a trivial fibration to the constant
diagram after reversing arrows. -/
structure CosimplicialResolution (X : C) where
  oppositeDiagram : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ
  augmentationOp : (Functor.const SimplexCategoryᵒᵖ).obj (op X) ⟶ oppositeDiagram
  augmentationOp_mem : trivialCofibrations _ augmentationOp
  fibrantOp : IsFibrant oppositeDiagram

/-- Choose a cosimplicial resolution by factoring the opposite constant diagram's terminal map. -/
def cosimplicialResolution (X : C) : CosimplicialResolution X :=
  let d := factorizationData (trivialCofibrations _) (fibrations _)
    (terminal.from ((Functor.const SimplexCategoryᵒᵖ).obj (op X)))
  { oppositeDiagram := d.Z
    augmentationOp := d.i
    augmentationOp_mem := d.hi
    fibrantOp := (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr
      ((fibration_iff _).mpr d.hp) }

namespace CosimplicialResolution

variable {X : C} (R : CosimplicialResolution X)

/-- Each level of the augmentation is a weak equivalence in the original model. -/
theorem augmentation_weak (n : SimplexCategoryᵒᵖ) :
    weakEquivalences C (R.augmentationOp.app n).unop := by
  have h := R.augmentationOp_mem.2
  change simplicialReedyWeakEquivalences Cᵒᵖ R.augmentationOp at h
  have hn := h n
  change weakEquivalences Cᵒᵖ (R.augmentationOp.app n) at hn
  rw [weakEquivalences_op] at hn
  exact hn

/-- The simplicial set obtained by mapping the resolution levelwise into a target. -/
def mappingSSet : C ⥤ SSet.{v} :=
  opOp C ⋙ coyoneda ⋙ (Functor.whiskeringLeft _ _ _).obj R.oppositeDiagram

/-- A lift of a source map through two chosen resolutions, in opposite form. -/
structure Comparison {Y : C} (S : CosimplicialResolution Y) (f : X ⟶ Y) where
  mapOp : S.oppositeDiagram ⟶ R.oppositeDiagram
  comm : S.augmentationOp ≫ mapOp =
    (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ R.augmentationOp

/-- Any source map has a comparison between the two chosen resolutions. -/
def comparison {Y : C} (S : CosimplicialResolution Y) (f : X ⟶ Y) : Comparison R S f := by
  let a := (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ R.augmentationOp
  letI := R.fibrantOp
  have sq : CommSq a S.augmentationOp (terminal.from R.oppositeDiagram)
      (terminal.from S.oppositeDiagram) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  letI : HasLiftingProperty S.augmentationOp (terminal.from R.oppositeDiagram) :=
    hasLiftingProperty_of_wfs S.augmentationOp _
      S.augmentationOp_mem (mem_fibrations _)
  exact ⟨sq.lift, sq.fac_left⟩

namespace Comparison

variable {R} {Y : C} {S : CosimplicialResolution Y} {f : X ⟶ Y}
  (g : Comparison R S f)

/-- A comparison over a weak equivalence is a weak equivalence at every level. -/
theorem levelwise_weak (hf : weakEquivalences C f) (n : SimplexCategoryᵒᵖ) :
    weakEquivalences C (g.mapOp.app n).unop := by
  have h := congr_app g.comm n
  have h' : (g.mapOp.app n).unop ≫ (S.augmentationOp.app n).unop =
      (R.augmentationOp.app n).unop ≫ f := congrArg Quiver.Hom.unop h
  apply (weakEquivalences C).of_postcomp _ _ (S.augmentation_weak n)
  rw [h']
  exact (weakEquivalences C).comp_mem _ _ (R.augmentation_weak n) hf

/-- The map on mapping simplicial sets induced by precomposition with a comparison. -/
def precomp (Z : C) : S.mappingSSet.obj Z ⟶ R.mappingSSet.obj Z :=
  Functor.whiskerRight g.mapOp (coyoneda.obj (op (op Z)))

end Comparison

end CosimplicialResolution

end

end DaggerModels.PartII
