import DaggerModelsPartII.JTActualSpanPrismLiftCover
import DaggerModelsPartII.JTJointMarkArrowDecomposition
import DaggerModelsPartII.FiniteSupportWeakCoverNullhomotopy

/-! Contractible joint-mark fibers over the exact original full-prism span evaluation. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerNerveHomotopy DaggerSSetGluing DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget (pointMap)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualSpanMarkedCover

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private def terminalSection {I : Type} [SmallCategory I] (D : I ⥤ Cat.{0, 0})
    (t : ∀ i : I, D.obj i) (ht : ∀ i : I, IsTerminal (t i)) :
    I ⥤ Grothendieck D where
  obj i := ⟨i, t i⟩
  map f := ⟨f, (ht _).from _⟩
  map_id i := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber => exact (ht i).hom_ext _ _
  map_comp f g := by
    apply Grothendieck.ext
    case w_base => rfl
    case w_fiber => exact (ht _).hom_ext _ _

variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (A : (nerve (TargetComma Q)).Subcomplex)
variable (P : ObjectProperty (JTSemisimplicialSpanEvaluation.Presentation Q A))

/-- The exact full-prism evaluation, with its complete native map to the original target. -/
abbrev native : JTActualSpanPrismLiftCover.Lifted Q A P ⥤ Over Q.code :=
  JTActualSpanPrismLiftCover.evaluation Q A P ⋙
    JTTargetJointMarks.nativeOver W x y Q

/-- All simultaneous target-joint marks on the original lifted span. -/
def marksDiagram : JTActualSpanPrismLiftCover.Lifted Q A P ⥤ Cat.{0, 0} :=
  native Q A P ⋙ JTTargetJointMarks.nativeDiagram Q.code

/-- Original full-prism spans equipped with all target-joint marks. -/
abbrev Marked := Grothendieck (marksDiagram Q A P)

/-- Forget all marks while retaining each original full-prism object and arrow. -/
abbrev forgetMarks : Marked Q A P ⥤ JTActualSpanPrismLiftCover.Lifted Q A P :=
  Grothendieck.forget (marksDiagram Q A P)

/-- Every mark fiber has a terminal object, hence a weakly contractible nerve. -/
theorem marks_point_GW (a : JTActualSpanPrismLiftCover.Lifted Q A P) :
    GW (pointMap (nerve ((marksDiagram Q A P).obj a))) :=
  JTTargetJointMarks.marks_point_GW ((native Q A P).obj a).hom

/-- Marks provide a weak cover of the exact original full-prism span category. -/
theorem forgetMarks_weak : WeakEquivalence (nerveMap (forgetMarks Q A P)) :=
  GrothendieckContractibleFibers.projection_weak (marksDiagram Q A P)
    (marks_point_GW Q A P)

/-- The greatest mark at every joint of an original full-prism span. -/
private def greatest (a : JTActualSpanPrismLiftCover.Lifted Q A P) :
    (marksDiagram Q A P).obj a :=
  JTTargetJointMarks.greatest ((native Q A P).obj a).hom

private def greatest_terminal (a : JTActualSpanPrismLiftCover.Lifted Q A P) :
    IsTerminal (greatest Q A P a) :=
  JTTargetJointMarks.greatestIsTerminal ((native Q A P).obj a).hom

/-- A functorial greatest-mark section, including every original arrow. -/
def greatestMarkSection : JTActualSpanPrismLiftCover.Lifted Q A P ⥤ Marked Q A P :=
  terminalSection (marksDiagram Q A P) (greatest Q A P) (greatest_terminal Q A P)

/-- The section recovers original full-prism objects and arrows exactly. -/
theorem greatestMarkSection_forget :
    greatestMarkSection Q A P ⋙ forgetMarks Q A P =
      𝟭 (JTActualSpanPrismLiftCover.Lifted Q A P) := rfl

/-- The marked evaluation is the unchanged exact evaluation after forgetting marks. -/
def markedEvaluation : Marked Q A P ⥤ TargetComma Q :=
  forgetMarks Q A P ⋙ JTActualSpanPrismLiftCover.evaluation Q A P

/-- The marked spans still weakly cover the original finite full subcategory. -/
def projection : Marked Q A P ⥤ P.FullSubcategory :=
  forgetMarks Q A P ⋙ JTActualSpanPrismLiftCover.projection Q A P

theorem projection_weak : WeakEquivalence (nerveMap (projection Q A P)) := by
  letI : WeakEquivalence (nerveMap (forgetMarks Q A P)) := forgetMarks_weak Q A P
  letI : WeakEquivalence
      (nerveMap (JTActualSpanPrismLiftCover.projection Q A P)) :=
    JTActualSpanPrismLiftCover.projection_weak Q A P
  change WeakEquivalence (nerveMap (forgetMarks Q A P) ≫
    nerveMap (JTActualSpanPrismLiftCover.projection Q A P))
  infer_instance

/-- A nullhomotopy of the exact marked evaluation descends to the unchanged
full-prism evaluation with the same target vertex. -/
theorem nullhomotopic_of_marked
    (v : (Δ[0] : SSet.{0}) ⟶ nerve (TargetComma Q))
    (H : SSet.Homotopy (R.map (nerveMap (markedEvaluation Q A P)))
      (R.map (SSet.stdSimplex.isTerminalObj₀.from (nerve (Marked Q A P)) ≫ v))) :
    Nonempty (SSet.Homotopy
      (R.map (nerveMap (JTActualSpanPrismLiftCover.evaluation Q A P)))
      (R.map (SSet.stdSimplex.isTerminalObj₀.from
        (nerve (JTActualSpanPrismLiftCover.Lifted Q A P)) ≫ v))) := by
  letI : WeakEquivalence (nerveMap (forgetMarks Q A P)) := forgetMarks_weak Q A P
  exact FiniteLastVertexSupport.nullhomotopic_of_weak_cover
    (forgetMarks Q A P) (JTActualSpanPrismLiftCover.evaluation Q A P)
    (markedEvaluation Q A P) (.refl _) v H

/-- Every marked arrow factors as original native transport followed by a
vertical movement of its marks. -/
theorem arrow_factor {a b : Marked Q A P} (f : a ⟶ b) :
    Grothendieck.toTransport a f.base ≫
      JTJointMarkArrowDecomposition.vertical Q.code (native Q A P) f = f :=
  JTJointMarkArrowDecomposition.factor Q.code (native Q A P) f

/-- A target-joint cut can move upward after exact horizontal transport. -/
abbrev cut_image_le {a b : Marked Q A P} (f : a ⟶ b) (j : Joint Q.code) :=
  JTJointMarkArrowDecomposition.cut_image_le Q.code (native Q A P) f j

end
end DaggerModels.PartII.JTActualSpanMarkedCover
