import DaggerModelsPartII.JTJointRelativeGraphFamily
import DaggerModelsPartII.JTJointIntervalQuotient
import DaggerModelsPartII.JTFullPrismSupportedDiagram
import DaggerModelsPartII.JTParametrizedProductSimplices

/-!
# The original parameter on every full joint-overlap prism

The index contains every horizontal simplex in each full inverse interval.
Pulling the original parameter back along the tautological simplex and the
identity time operator yields a natural parameter on their mixed prisms.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointOverlapPrismDiagram

open JTParametrizedTargetFamilies (Family)
open JTJointRelativeGraphFamily (native originalParameter coefficient)
open JTJointRelativeParameters (withTime withTimeMap)
open JTJointIntervalQuotient (overlapToWhole)
open JTTargetIntervalOverMapping (overlap)
open JTTargetJointMarks (Joint)
open JTParametrizedProductSimplices (Index base degree simplex simplex_natural)
open JTFullPrismSupportedDiagram (prisms)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- The actual full inverse interval, before collapsing any horizontal vertex. -/
abbrev overlapSimplices : A ⥤ SSet.{0} :=
  native F ⋙ overlap Q.code j ⋙ Over.forget Q.code.toSSet

/-- The restriction of the original parameter to the full overlap interval. -/
private abbrev restricted :
    withTime Q.map J time (native F) (overlap Q.code j) ⟶
      coefficient (L := L) ⋙ J :=
  withTimeMap Q.map J time (native F) (overlapToWhole Q.code j) ≫
    originalParameter F

/-- The original coefficient parameter on every horizontal simplex of the
full overlap interval, with the entire independent time simplex. -/
def parameter :
    prisms (degree (overlapSimplices F j)) (base (overlapSimplices F j) ⋙ time) ⟶
      (base (overlapSimplices F j) ⋙ coefficient (L := L)) ⋙ J where
  app a := (simplex (overlapSimplices F j) a ⊗ₘ
      𝟙 (J.obj (time.obj a.base))) ≫ (restricted F j).app a.base
  naturality {a b} f := by
    have hs := simplex_natural (overlapSimplices F j) f
    have hr := (restricted F j).naturality f.base
    change ((std.map ((degree (overlapSimplices F j)).map f) ⊗ₘ
        J.map (time.map f.base)) ≫
          ((simplex (overlapSimplices F j) b ⊗ₘ
            𝟙 (J.obj (time.obj b.base))) ≫ (restricted F j).app b.base)) =
        ((simplex (overlapSimplices F j) a ⊗ₘ
          𝟙 (J.obj (time.obj a.base))) ≫ (restricted F j).app a.base) ≫
          J.map ((coefficient (L := L)).map f.base)
    change ((overlapSimplices F j).map f.base ⊗ₘ J.map (time.map f.base)) ≫
      (restricted F j).app b.base =
        (restricted F j).app a.base ≫ J.map ((coefficient (L := L)).map f.base) at hr
    calc
      _ = ((std.map ((degree (overlapSimplices F j)).map f) ≫
            simplex (overlapSimplices F j) b) ⊗ₘ J.map (time.map f.base)) ≫
          (restricted F j).app b.base := by
            rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
      _ = ((simplex (overlapSimplices F j) a ≫
            (overlapSimplices F j).map f.base) ⊗ₘ J.map (time.map f.base)) ≫
          (restricted F j).app b.base := by rw [← hs]
      _ = ((simplex (overlapSimplices F j) a ⊗ₘ
            𝟙 (J.obj (time.obj a.base))) ≫
          ((overlapSimplices F j).map f.base ⊗ₘ J.map (time.map f.base))) ≫
          (restricted F j).app b.base := by
            rw [tensorHom_comp_tensorHom, Category.id_comp]
      _ = (simplex (overlapSimplices F j) a ⊗ₘ
            𝟙 (J.obj (time.obj a.base))) ≫
          (((overlapSimplices F j).map f.base ⊗ₘ J.map (time.map f.base)) ≫
            (restricted F j).app b.base) := Category.assoc _ _ _
      _ = (simplex (overlapSimplices F j) a ⊗ₘ
            𝟙 (J.obj (time.obj a.base))) ≫
          ((restricted F j).app a.base ≫
            J.map ((coefficient (L := L)).map f.base)) := by rw [hr]
      _ = ((simplex (overlapSimplices F j) a ⊗ₘ
            𝟙 (J.obj (time.obj a.base))) ≫ (restricted F j).app a.base) ≫
          J.map ((coefficient (L := L)).map f.base) := (Category.assoc _ _ _).symm

end

end DaggerModels.PartII.JTJointOverlapPrismDiagram
