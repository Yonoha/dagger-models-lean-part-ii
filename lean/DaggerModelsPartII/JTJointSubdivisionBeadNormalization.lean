import DaggerModelsPartII.JTJointSubdivisionBeadCharts
import DaggerModelsPartII.JTJointBeadContractionNullhomotopy

/-!
Full supported normalization on the actual adjacent-subdivision image charts.
The original native maps determine the simplex operators and the pullback
factorizations through the actual target-joint interval. Every chart input
to the existing normalization and contraction is derived from the original
family. The final nullhomotopy is in the point-target comma at that joint;
no global whiskered nullhomotopy or weak chart projection is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointSubdivisionBeadNormalization

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTJointSubdivisionBeadCharts (Index base singleNative singleInclusions)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem single_inverse_natural {m n : ℕ} (f : single m ⟶ single n) :
    (singleIso m).inv ≫ f.map =
      std.map (SimplexCategory.Hom.mk (orderMap f.map) : ⦋m⦌ ⟶ ⦋n⦌) ≫
        (singleIso n).inv := by
  have h := map_inclusion f.map
  rw [← singleIso_hom m, ← singleIso_hom n] at h
  apply (cancel_mono (singleIso n).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

/-- The actual interval width and the original native vertex operator on every chart arrow. -/
def degrees : Index F j ⥤ SimplexCategory where
  obj p := ⦋p.2.lastCut.val - p.2.firstCut.val⦌
  map f := SimplexCategory.Hom.mk (orderMap ((singleNative F j).map f).map)
  map_id p := by
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    funext v
    change orderMap ((singleNative F j).map (𝟙 p)).map v = v
    rw [(singleNative F j).map_id]
    exact DaggerOriginalProductGadget.orderMap_id_apply _ _
  map_comp f g := by
    apply SimplexCategory.Hom.ext'
    apply OrderHom.ext
    funext v
    change orderMap ((singleNative F j).map (f ≫ g)).map v =
      orderMap ((singleNative F j).map g).map
        (orderMap ((singleNative F j).map f).map v)
    rw [(singleNative F j).map_comp]
    exact orderMap_comp_apply _ _ _

/-- First chart endpoints are preserved, including all zero-width charts. -/
theorem first_map {p q : Index F j} (f : p ⟶ q) :
    ((degrees F j).map f).toOrderHom 0 = 0 :=
  orderMap_first ((singleNative F j).map f)

/-- The same original map preserves the last chart endpoint. -/
theorem last_map {p q : Index F j} (f : p ⟶ q) :
    ((degrees F j).map f).toOrderHom (Fin.last ((degrees F j).obj p).len) =
      Fin.last ((degrees F j).obj q).len :=
  orderMap_last ((singleNative F j).map f)

/-- The full actual single-chart inclusion in its unchanged original native source. -/
abbrev inclusion (p : Index F j) :
    (single ((degrees F j).obj p).len).toSSet ⟶
      ((codes L).obj ((base F j).obj p)).toSSet :=
  (singleInclusions F j).app p

private abbrev pair (p : Index F j) := (JTJointSubdivisionBeadCharts.toPairs F j).obj p

/-- The actual chart lies over the literal original target joint in every simplicial degree. -/
theorem inclusion_joint (p : Index F j) :
    inclusion F j p ≫ (F.collapse.app ((base F j).obj p)).map =
      term (single ((degrees F j).obj p).len).toSSet ≫ pointAt Q.code (ULift.up j.val) := by
  have h := JTActualJointGapPrism.native_constant F (pair F j p).1
    (pair F j p).2.left.val (pair F j p).2.right.val (pair F j p).2.le j
    (pair F j p).2.left.property (pair F j p).2.right.property
  change JTJointPairGapDiagram.inclusion F j (pair F j p) ≫
      (F.collapse.app ((base F j).obj p)).map =
    term (JTJointPairGapDiagram.code F j (pair F j p)).toSSet ≫
      pointAt Q.code (ULift.up j.val) at h
  change (JTJointSubdivisionBeadCharts.simplexIso F j p).inv.map ≫
    (JTJointPairGapDiagram.inclusion F j (pair F j p) ≫
      (F.collapse.app ((base F j).obj p)).map) = _
  rw [h, ← Category.assoc]
  congr 1

/-- Factor the actual single chart through the full inverse interval of its target joint. -/
def toJointInterval (p : Index F j) :
    (single ((degrees F j).obj p).len).toSSet ⟶
      (JTTargetIntervalPullback.sourceInterval
        (F.collapse.app ((base F j).obj p)) j j le_rfl).toSSet :=
  (JTTargetIntervalGluing.middlePB (F.collapse.app ((base F j).obj p)) j).lift
    (inclusion F j p) (term (single ((degrees F j).obj p).len).toSSet)
    (inclusion_joint F j p)

/-- The pullback factor recovers the complete original native inclusion. -/
theorem toJointInterval_fac (p : Index F j) :
    toJointInterval F j p ≫
        JTTargetIntervalGluing.middleInclusion (F.collapse.app ((base F j).obj p)) j =
      inclusion F j p :=
  (JTTargetIntervalGluing.middlePB (F.collapse.app ((base F j).obj p)) j).lift_fst _ _ _

/-- Full native transport of the actual chart inclusion, without choosing a parameter lift. -/
theorem inclusion_natural {p q : Index F j} (f : p ⟶ q) :
    ((singleNative F j).map f).map ≫ inclusion F j q =
      inclusion F j p ≫ ((codes L).map ((base F j).map f)).map :=
  (singleInclusions F j).naturality f

/-- The exact original native chart square required by all full timed bead constructions. -/
theorem native_natural {p q : Index F j} (f : p ⟶ q) :
    (singleIso ((degrees F j).obj p).len).inv ≫
        (toJointInterval F j p ≫ JTTargetIntervalGluing.middleInclusion
          (F.collapse.app ((base F j).obj p)) j) ≫
        ((codes L).map ((base F j).map f)).map =
      std.map ((degrees F j).map f) ≫ (singleIso ((degrees F j).obj q).len).inv ≫
        (toJointInterval F j q ≫ JTTargetIntervalGluing.middleInclusion
          (F.collapse.app ((base F j).obj q)) j) := by
  rw [toJointInterval_fac, toJointInterval_fac]
  calc
    _ = ((singleIso ((degrees F j).obj p).len).inv ≫
        ((singleNative F j).map f).map) ≫ inclusion F j q := by
      rw [Category.assoc, inclusion_natural]
    _ = _ := by rw [single_inverse_natural, Category.assoc]; rfl

/-- All higher endpoint choices and coefficient chains of these actual charts. -/
abbrev NormalizationIndex := JTJointBeadNormalizationDiagram.Index F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- The complete supported normalized label functor on the actual chart source. -/
abbrev labels := JTJointBeadNormalizationDiagram.labels F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- Forget normalization choices and chains, retaining every original actual chart arrow. -/
abbrev toCharts : NormalizationIndex F j ⥤ Index F j :=
  JTJointBeadNormalizationDiagram.toCharts F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j)

/-- This normalization projection is weak only to the actual image-chart category. -/
theorem toCharts_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toCharts F j)) :=
  JTJointBeadNormalizationDiagram.toCharts_weak F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j) hW

/-- The full inverse-image support of the actual normalized bead coefficient. -/
abbrev support := JTJointBeadNormalizationSupport.support F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- Its natural monic inclusion in the unchanged full normalization-chain degree. -/
abbrev supportIncl := JTJointBeadNormalizationSupport.incl F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- Every actual inverse-image support inclusion is monic. -/
theorem supportIncl_mono (p : NormalizationIndex F j) :
    Mono ((supportIncl F j).app p) :=
  JTJointBeadNormalizationSupport.incl_mono F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j) p

/-- The full normalized coefficient is literally the joint constant on that support. -/
theorem coefficient_onSupport (p : NormalizationIndex F j) :
    std.map ((supportIncl F j).app p) ≫ JTSupportedOrderedCoefficientChoices.old W
        (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) (labels F j) p =
      JTSupportedOrderedCoefficientChoices.supportedConstant W
        (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)
        (labels F j) (support F j) p :=
  JTJointBeadContractionChoices.old_onSupport F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j) p

/-- The entire supported native-time graph, derived from the original full family. -/
abbrev graph := JTJointBeadSupportedGraph.graph F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- Retain every padded native coordinate and the entire original time coordinate. -/
abbrev graphProjection := JTJointBeadSupportedGraph.projection F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- The full actual graph projection is a trivial fibration at every normalization chain. -/
theorem graphProjection_trivialFibration (p : NormalizationIndex F j) :
    trivialFibrations SSet.{0} ((graphProjection F j).app p) :=
  JTJointBeadSupportedGraph.projection_trivialFibration F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j) p

/-- The complete graph data for all higher supported contractions. -/
abbrev graphData := JTJointBeadSupportedGraph.data F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- The complete contraction presentation in the fixed point-target comma. -/
abbrev reduced := JTJointBeadContractionEvaluation.reduced F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- Every internal necklace of every full supported contraction evaluates at the same joint. -/
abbrev evaluation := JTJointBeadContractionEvaluation.evaluation F j
  (base F j) (degrees F j) (first_map F j) (last_map F j)
  (toJointInterval F j) (native_natural F j)

/-- The actual complete point-target contraction evaluation is nullhomotopic after R.
This does not assert a relative or globally whiskered nullhomotopy in the original Q. -/
theorem evaluation_nullhomotopic :
    ∃ v : (Δ[0] : SSet.{0}) ⟶ nerve (JTGraphFactoredPresentation.TargetComma
        (JTPointTargetEvaluationCone.pointTarget W
          (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j))),
      Nonempty (SSet.Homotopy (R.map (nerveMap (evaluation F j)))
        (R.map (term (nerve (BoundaryNecklaceComma.Presentation (reduced F j))) ≫ v))) :=
  JTJointBeadContractionNullhomotopy.evaluation_nullhomotopic F j
    (base F j) (degrees F j) (first_map F j) (last_map F j)
    (toJointInterval F j) (native_natural F j)

end
end DaggerModels.PartII.JTJointSubdivisionBeadNormalization
