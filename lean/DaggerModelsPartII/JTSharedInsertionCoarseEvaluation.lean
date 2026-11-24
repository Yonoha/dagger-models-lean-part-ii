import DaggerModelsPartII.JTSharedInsertionCoarseGraph
import DaggerModelsPartII.JTSharedInsertionCoarseRawData
import DaggerModelsPartII.JTSharedInsertionCoarseRaw
import DaggerModelsPartII.JTGraphCoveredLiftComparison
import DaggerModelsPartII.JTGraphCoveredPresentationWeak

/-!
# Full original-Q evaluation of the ACTUAL coarse graph

Use every original-time coefficient lift and the complete inverse image of both
endpoint lines. Existing graph-covered pullback lifts and evaluation retain ALL
internal necklaces and the original global endpoints. No new Family, raw,
support or compatibility premise is supplied by a caller.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionCoarseEvaluation

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilyComparison (degrees)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

private def productProjection {I : Type} [SmallCategory I]
    (N : I ⥤ NecklaceCode) (t : I ⥤ SimplexCategory) (U : NecklaceCode)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) (c : N ⟶ (Functor.const I).obj U)
    {Y : I ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) :=
  π ≫ (JTGraphCoveredProductInterface.iso N t U q c).hom

private theorem productProjection_app {I : Type} [SmallCategory I]
    (N : I ⥤ NecklaceCode) (t : I ⥤ SimplexCategory) (U : NecklaceCode)
    {X : SSet.{0}} (q : U.toSSet ⟶ X) (c : N ⟶ (Functor.const I).obj U)
    {Y : I ⥤ SSet.{0}} (π : Y ⟶ JTGraphCoveredProductInterface.product N t) (p : I) :
    ((productProjection N t U q c π).app p :
        Y.obj p ⟶ (N.obj p).toSSet ⊗ J.obj (t.obj p)) = π.app p := by
  rw [productProjection, NatTrans.comp_app, JTGraphCoveredProductInterface.iso_hom_app]
  exact Category.comp_id _

private theorem ordered_generator (W : Source) (x y : Vertex W) (N : NecklaceCode)
    (d : SimplexCategory)
    (a : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj (op N)).obj (op d)) :
    SSet.yonedaEquiv (JTOrderedLabelBinaryGlue.coefficient W x y N d a) =
      JTRealizedLabelEndpoints.orderedLabel W x y N d a :=
  Equiv.apply_symm_apply _ _

section GenericRaw

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)
variable {Y : I ⥤ SSet.{0}}
variable (π : Y ⟶ JTGraphCoveredProductInterface.product (codes L) t)
variable (θ : Y ⟶ degrees L ⋙ J)

private def LiteralRaw : Prop := ∀ p,
  lift (π.app p ≫ fst ((codes L).obj p).toSSet (J.obj (t.obj p))) (θ.app p) ≫
      JTNecklaceLabelRealization.realizedLabel ((codes L).obj p).toSSet W
        ((degrees L).obj p)
        (SSet.yonedaEquiv (JTOrderedLabelBinaryGlue.coefficient W x y ((codes L).obj p)
          ((degrees L).obj p) (L.obj p).unop.2)) =
    (π.app p ≫ fst _ _) ≫ (c.app p).map ≫ Q.map

private theorem raw_from_literal (h : LiteralRaw Q L t c π θ) :
    JTGraphCoveredLiftComparison.RawEquation Q L t c
      (productProjection (codes L) t Q.code Q.map c π) θ := by
  intro p
  have hp := h p
  have hg := ordered_generator W x y ((codes L).obj p) ((degrees L).obj p) (L.obj p).unop.2
  have hs := congrArg (fun a ↦
    lift (π.app p ≫ fst ((codes L).obj p).toSSet (J.obj (t.obj p))) (θ.app p) ≫
      JTNecklaceLabelRealization.realizedLabel ((codes L).obj p).toSSet W
        ((degrees L).obj p) a) hg
  have hp' := hs.symm.trans hp
  simpa only [productProjection, NatTrans.comp_app,
    JTGraphCoveredProductInterface.iso_hom_app, Category.comp_id] using hp'

end GenericRaw

section GenericLift

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : I ⥤ SimplexCategory)
variable (c : codes L ⟶ (Functor.const I).obj Q.code)
variable {Y : I ⥤ SSet.{0}}
variable (π : Y ⟶ JTJointRelativeParameters.withTime Q.map J t (Over.lift (codes L) c)
  (JTTargetIntervalOverMapping.whole Q.code))
variable (θ : Y ⟶ degrees L ⋙ J)
variable (h : JTGraphCoveredLiftComparison.RawEquation Q L t c π θ)

private theorem coveredLift_fst (p : I) :
    (JTGraphCoveredLiftInterface.pullbackLift Q L t c π θ h).app p ≫
        JTTargetCommaPullback.fst W x y Q (L.obj p) =
      (JTGraphCoveredLabelEvaluation.decorated Q L t c π θ).app p :=
  JTDecoratedIntervalCylinder.liftFromProjections_fst Q L
    (JTGraphCoveredLabelEvaluation.reduced Q L t c π)
    (JTGraphCoveredLabelEvaluation.decorated Q L t c π θ)
    (JTGraphCoveredLabelEvaluation.nativeLeg Q L t c π)
    (JTGraphCoveredLabelEvaluation.raw_square Q L t c π θ h) p

private theorem coveredLift_snd (p : I) :
    (JTGraphCoveredLiftInterface.pullbackLift Q L t c π θ h).app p ≫
        JTTargetCommaPullback.snd W x y Q (L.obj p) =
      (JTGraphCoveredLabelEvaluation.nativeLeg Q L t c π).app p :=
  JTDecoratedIntervalCylinder.liftFromProjections_snd Q L
    (JTGraphCoveredLabelEvaluation.reduced Q L t c π)
    (JTGraphCoveredLabelEvaluation.decorated Q L t c π θ)
    (JTGraphCoveredLabelEvaluation.nativeLeg Q L t c π)
    (JTGraphCoveredLabelEvaluation.raw_square Q L t c π θ h) p

end GenericLift

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original shared insertion choices, without any new choices. -/
abbrev Index := JTSharedInsertionCoarseGraph.Index F j

/-- The ACTUAL complete corrected coarse decorated labels. -/
abbrev labels := JTSharedInsertionCoarseLabels.labels F j

/-- Keep the entire original time, separately from the common coefficient clock. -/
abbrev oldTime := JTSharedInsertionCoarseGraph.oldTime F j

/-- The unchanged original fixed Q, with its original global endpoints. -/
abbrev target := JTSharedInsertionCoarseNative.target F j

/-- Every lift through the original full coefficient projection is retained. -/
abbrev graph := JTSharedInsertionCoarseGraph.graph F j

/-- The existing product interface has identity components and all original operators. -/
def productIso := JTGraphCoveredProductInterface.iso (codes (labels F j)) (oldTime F j)
  Q.code Q.map (target F j)

/-- Read every graph point in the EXISTING original-time product diagram. -/
def projection := productProjection (codes (labels F j)) (oldTime F j)
  Q.code Q.map (target F j) (JTSharedInsertionCoarseGraph.projection F j)

/-- Both actual product representations retain exactly the SAME graph map. -/
theorem projection_app (p : Index F j) :
    ((projection F j).app p : (graph F j).obj p ⟶
        ((codes (labels F j)).obj p).toSSet ⊗ J.obj ((oldTime F j).obj p)) =
      (JTSharedInsertionCoarseGraph.projection F j).app p :=
  productProjection_app (codes (labels F j)) (oldTime F j) Q.code Q.map
    (target F j) (JTSharedInsertionCoarseGraph.projection F j) p

/-- The full given common-chain parameter, typed at the actual label degree. -/
def parameter : graph F j ⟶ degrees (labels F j) ⋙ J :=
  JTSharedInsertionCoarseGraph.parameter F j

/-- The complete original native endpoint lines, with the entire original time. -/
abbrev boundary := JTGraphCoveredLabelEvaluation.boundary Q (labels F j) (oldTime F j)
  (target F j)

/-- The ENTIRE inverse image of both endpoint lines is used in the quotient. -/
abbrev endpointInclusion := JTEndpointReducedPullbackCover.boundaryInclusion
  (projection F j) (boundary F j)

/-- The other projection of that exact endpoint inverse image. -/
abbrev endpointProjection := JTEndpointReducedPullbackCover.boundaryProjection
  (projection F j) (boundary F j)

/-- Collapse precisely that full inverse image, retaining its original boundary. -/
abbrev reduced := JTGraphCoveredLabelEvaluation.reduced Q (labels F j) (oldTime F j)
  (target F j) (projection F j)

/-- The reduced graph maps to the literal original reduced native-time cylinder. -/
abbrev reducedProjection := JTGraphCoveredLabelEvaluation.projection Q (labels F j)
  (oldTime F j) (target F j) (projection F j)

/-- The complete decorated leg retains the actual whole coefficient parameter. -/
abbrev decorated := JTGraphCoveredLabelEvaluation.decorated Q (labels F j) (oldTime F j)
  (target F j) (projection F j) (parameter F j)

/-- The complete native leg uses the SAME original fixed Q. -/
abbrev nativeLeg := JTGraphCoveredLabelEvaluation.nativeLeg Q (labels F j) (oldTime F j)
  (target F j) (projection F j)


/-- Both product interfaces act by the literal identity at every actual object. -/
theorem productIso_hom_app (p : Index F j) : (productIso F j).hom.app p = 𝟙 _ :=
  JTGraphCoveredProductInterface.iso_hom_app (codes (labels F j)) (oldTime F j)
    Q.code Q.map (target F j) p

/-- The actual graph projection changes only its existing product interface. -/
theorem projection_eq : projection F j = JTSharedInsertionCoarseGraph.projection F j ≫
    (productIso F j).hom := rfl

/-- The full endpoint inverse image retains its strict original product square. -/
theorem endpoint_square : endpointInclusion F j ≫ projection F j =
    endpointProjection F j ≫ boundary F j :=
  JTEndpointReducedPullbackCover.boundary_square (projection F j) (boundary F j)

/-- The entire graph-domain summand in the complete endpoint quotient. -/
abbrev cylinderInclusion := JTGraphCoveredCylinderEquations.inc Q (labels F j) (oldTime F j)
  (target F j) (projection F j)

/-- The original-time cylinder coordinate of the reduced graph projection is literal. -/
theorem projection_cylinder (p : Index F j) :
    (cylinderInclusion F j).app p ≫ ((reducedProjection F j).app p).right =
      (projection F j).app p ≫ (JTNecklaceEndpointCylinder.cylinder
        ((codes (labels F j)).obj p)).app ((oldTime F j).obj p) :=
  JTGraphCoveredCylinderEquations.projection_cylinder Q (labels F j) (oldTime F j)
    (target F j) (projection F j) p

/-- The decorated cylinder pairs the actual whole native coordinate and full parameter. -/
theorem decorated_cylinder (p : Index F j) :
    (cylinderInclusion F j).app p ≫ ((decorated F j).app p).right =
      lift ((projection F j).app p ≫ fst ((codes (labels F j)).obj p).toSSet
          (J.obj ((oldTime F j).obj p))) ((parameter F j).app p) ≫
        (JTNecklaceEndpointCylinder.cylinder ((codes (labels F j)).obj p)).app
          ((degrees (labels F j)).obj p) :=
  JTGraphCoveredCylinderEquations.decorated_cylinder Q (labels F j) (oldTime F j)
    (target F j) (projection F j) (parameter F j) p

/-- Forget only the complete internal-necklace presentation to its actual shared choices. -/
abbrev toChoices : BoundaryNecklaceComma.Presentation (reduced F j) ⥤ Index F j :=
  Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (reduced F j))


private theorem literal_raw : LiteralRaw Q (labels F j) (oldTime F j) (target F j)
    (JTSharedInsertionCoarseGraph.projection F j) (parameter F j) := by
  intro p
  exact JTSharedInsertionCoarseRaw.ordered_raw F j p

/-- The EXISTING whole covered evaluator's raw condition is DERIVED from actual coarse raw.
No caller raw, Family, support or compatibility premise is added. -/
theorem rawEquation : JTGraphCoveredLiftComparison.RawEquation Q (labels F j) (oldTime F j)
    (target F j) (projection F j) (parameter F j) :=
  raw_from_literal Q (labels F j) (oldTime F j) (target F j)
    (JTSharedInsertionCoarseGraph.projection F j) (parameter F j) (literal_raw F j)

/-- Lift the entire reduced graph into the literal ORIGINAL fixed-Q pullback diagram. -/
abbrev pullbackLift := JTGraphCoveredLiftInterface.pullbackLift Q (labels F j) (oldTime F j)
  (target F j) (projection F j) (parameter F j) (rawEquation F j)

/-- The first literal pullback projection is the complete decorated leg. -/
theorem pullbackLift_fst (p : Index F j) :
    (pullbackLift F j).app p ≫ JTTargetCommaPullback.fst W x y Q ((labels F j).obj p) =
      (decorated F j).app p :=
  coveredLift_fst Q (labels F j) (oldTime F j) (target F j) (projection F j)
    (parameter F j) (rawEquation F j) p

/-- The second literal pullback projection is the complete original-Q native leg. -/
theorem pullbackLift_snd (p : Index F j) :
    (pullbackLift F j).app p ≫ JTTargetCommaPullback.snd W x y Q ((labels F j).obj p) =
      (nativeLeg F j).app p :=
  coveredLift_snd Q (labels F j) (oldTime F j) (target F j) (projection F j)
    (parameter F j) (rawEquation F j) p

/-- Evaluate ALL internal necklaces of the complete coarse graph in the SAME original Q. -/
def evaluation : BoundaryNecklaceComma.Presentation (reduced F j) ⥤
    JTGraphFactoredPresentation.TargetComma Q :=
  JTGraphCoveredLabelEvaluation.evaluation Q (labels F j) (oldTime F j) (target F j)
    (projection F j) (parameter F j) (rawEquation F j)

/-- The complete evaluation is exactly the existing full pullback-presentation evaluation. -/
theorem evaluation_eq_mapPresentation : evaluation F j =
    JTBoundaryNecklacePresentationCone.mapPresentation (JTTargetCommaPullback.diagram W x y Q)
      (reduced F j) (labels F j) (pullbackLift F j) ⋙
        JTTargetCommaExactEvaluation.fromPresentation W x y Q :=
  JTGraphCoveredLiftInterface.evaluation_eq_mapPresentation Q (labels F j) (oldTime F j)
    (target F j) (projection F j) (parameter F j) (rawEquation F j)


/-- The literal identity product interface preserves the ACTUAL objectwise graph cover. -/
theorem projection_trivialFibration (p : Index F j) :
    trivialFibrations SSet.{0} ((projection F j).app p) := by
  rw [projection_app]
  exact JTSharedInsertionCoarseGraph.projection_trivialFibration F j p

/-- The FULL presentation projects weakly to Shared.Index by the existing full-inverse-image
fiber theorem. This asserts no weakness of a projection to the original A or marked source. -/
theorem toChoices_weak : WeakEquivalence (nerveMap (toChoices F j)) :=
  JTGraphCoveredPresentationWeak.forget_weak Q (labels F j) (oldTime F j) (target F j)
    (projection F j) (projection_trivialFibration F j)

end
end DaggerModels.PartII.JTSharedInsertionCoarseEvaluation
