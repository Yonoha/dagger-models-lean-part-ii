import DaggerModelsPartII.JTMarkedStaircaseGraphs
import DaggerModelsPartII.JTSharedCoefficientEvaluation
import DaggerModelsPartII.JTHomotopyTargetComma
import DaggerModelsPartII.FiniteLastVertexFactor

/-! Both ends of each admissible staircase step compare into one actual evaluation. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode DaggerSSetGluing DaggerNerveHomotopy

namespace DaggerModels.PartII.JTMarkedStaircaseEvaluation

open JTParameterBlocks (common leftIn rightIn)
open JTOrdinalStaircaseComparison (before after)
open JTMarkedStaircaseGraphs (stepInputs stepParameter step_over_wedge stepInputs_adjacent
  stepInputs_last stepInputs_first)
open JTOrderedLabelBinaryGlue (reindex code)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTBinaryPrismRealization (realizeProduct collapse)
open JTCodiscreteParameterPairing (coord)
open JTSharedCoefficientEvaluation (evaluate evaluate_congr restrict_raw)
open DecoratedCylinderNecklacePresentation (toTarget)
open JTNecklaceEndpointCylinder (under)
open BoundaryNecklaceComma (necklaceUnder)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode} {k l n : SimplexCategory}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {i₀ i₁ : Fin (k.len + 1)} {j₀ j₁ : Fin (l.len + 1)}
variable (hi : i₀ ≤ i₁) (hj : j₀ ≤ j₁) (d : Fin ((common k l).len + 1))
variable (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
variable (hs : ∀ q a v, coord k q (s.app q a) v ≤ i₀)
variable (ht : ∀ q a v, j₁ ≤ coord l q (t.app q a) v)
variable (hs' : realizeProduct W k s (orderedLabel W x z T k u) = fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
variable (ht' : realizeProduct W l t (orderedLabel W z y U l v) = fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map)

private abbrev joined (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l) :=
  JTBinaryPrismParameter.parameter T U (common k l) (J.obj n)
    (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l))
private abbrev stage := stepInputs hi hj d u v
private abbrev step := stepParameter (joined s t) d
private abbrev N (n : SimplexCategory) := JTDoubledGraphTime.degree n
private abbrev Fiber (T U : NecklaceCode) (n : SimplexCategory) :=
  CostructuredArrow necklaceUnder ((under (code T U)).obj n)

include hs ht hs' ht' in
private theorem step_raw :
    JTBinaryPrismRealization.realizeInputs (stage hi hj d u v) (step d s t) =
      fst (code T U).toSSet (J.obj (N n)) ≫ (collapse c e).map ≫
        (NecklacesOver.wedge P Q).map :=
  step_over_wedge hi hj d (joined s t) s t
    (JTBinaryPrismParameter.parameter_left _ _ _ _ _ _)
    (JTBinaryPrismParameter.parameter_right _ _ _ _ _ _) hs ht u v c e hs' ht'

/-- The comparison is evaluated on the original native wedge. -/
def stepEvaluation : Fiber T U (N n) ⥤ CostructuredArrow (toTarget W x y) (NecklacesOver.wedge P Q) :=
  evaluate _ (collapse c e) (stage hi hj d u v) (step d s t)
    (step_raw hi hj d u v c e s t hs ht hs' ht')

/-- The common target of the two restriction maps has weakly contractible nerve. -/
theorem step_point_GW (T U : NecklaceCode) (n : SimplexCategory) :
    GW (pointMap (nerve (Fiber T U (N n)))) :=
  JTHomotopyTargetComma.fiber_point_GW_at (code T U) (N n)

private abbrev leftTime (n : SimplexCategory) := leftIn n n
private abbrev rightTime (n : SimplexCategory) := rightIn n n
private abbrev leftCoefficient (d : Fin ((common k l).len + 1)) := before (common k l) d
private abbrev rightCoefficient (d : Fin ((common k l).len + 1)) := after (common k l) d

private theorem step_left :
    ((code T U).toSSet ◁ J.map (leftTime n)) ≫ step d s t =
      joined s t ≫ J.map (leftCoefficient d) :=
  JTDoubledGraphTime.extend_left (joined s t) (leftCoefficient d) (rightCoefficient d)

private theorem step_right :
    ((code T U).toSSet ◁ J.map (rightTime n)) ≫ step d s t =
      joined s t ≫ J.map (rightCoefficient d) :=
  JTDoubledGraphTime.extend_right (joined s t) (leftCoefficient d) (rightCoefficient d)

/-- The first restriction of the step, using the original undoubled time. -/
def beforeEvaluation :=
  evaluate (NecklacesOver.wedge P Q) (collapse c e)
    (reindex (leftCoefficient d) (stage hi hj d u v)) (joined s t)
    (restrict_raw (NecklacesOver.wedge P Q) (collapse c e) (stage hi hj d u v)
      (leftCoefficient d) (leftTime n) (step d s t) (joined s t)
      (step_raw hi hj d u v c e s t hs ht hs' ht') (step_left d s t))

/-- The second restriction of the step, using the original undoubled time. -/
def afterEvaluation :=
  evaluate (NecklacesOver.wedge P Q) (collapse c e)
    (reindex (rightCoefficient d) (stage hi hj d u v)) (joined s t)
    (restrict_raw (NecklacesOver.wedge P Q) (collapse c e) (stage hi hj d u v)
      (rightCoefficient d) (rightTime n) (step d s t) (joined s t)
      (step_raw hi hj d u v c e s t hs ht hs' ht') (step_right d s t))

/-- The first endpoint evaluation compares naturally to the step evaluation
after the actual first time inclusion on all internal necklaces. -/
def compareBefore :=
  JTSharedCoefficientEvaluation.compare (NecklacesOver.wedge P Q) (collapse c e)
    (stage hi hj d u v) (leftCoefficient d) (leftTime n) (step d s t) (joined s t)
    (step_raw hi hj d u v c e s t hs ht hs' ht') (step_left d s t)

/-- The second endpoint evaluation compares naturally to the same step
evaluation after the actual second time inclusion. -/
def compareAfter :=
  JTSharedCoefficientEvaluation.compare (NecklacesOver.wedge P Q) (collapse c e)
    (stage hi hj d u v) (rightCoefficient d) (rightTime n) (step d s t) (joined s t)
    (step_raw hi hj d u v c e s t hs ht hs' ht') (step_right d s t)

/-- The two actual evaluations at a step are homotopic after singular realization. -/
def stepHomotopy :
    SSet.Homotopy
      (R.map (nerveMap (beforeEvaluation hi hj d u v c e s t hs ht hs' ht')))
      (R.map (nerveMap (afterEvaluation hi hj d u v c e s t hs ht hs' ht'))) := by
  exact FiniteLastVertexFactor.homotopy_of_roof
    (compareBefore hi hj d u v c e s t hs ht hs' ht')
    (compareAfter hi hj d u v c e s t hs ht hs' ht') (step_point_GW T U n)

private theorem adjacent_evaluation (d' : Fin ((common k l).len + 1)) (hd : d.val + 1 = d'.val) :
    beforeEvaluation hi hj d u v c e s t hs ht hs' ht' =
      afterEvaluation hi hj d' u v c e s t hs ht hs' ht' := by
  unfold beforeEvaluation afterEvaluation
  apply evaluate_congr
  exact stepInputs_adjacent hi hj d d' hd u v

private def fromFirst (a : Fin ((common k l).len + 1)) :
    SSet.Homotopy
      (R.map (nerveMap (afterEvaluation hi hj 0 u v c e s t hs ht hs' ht')))
      (R.map (nerveMap (beforeEvaluation hi hj a u v c e s t hs ht hs' ht'))) := by
  induction a using Fin.induction with
  | zero => exact (stepHomotopy hi hj 0 u v c e s t hs ht hs' ht').symm
  | succ a H =>
    have h := adjacent_evaluation hi hj a.castSucc u v c e s t hs ht hs' ht' a.succ rfl
    have hR := congrArg (fun F ↦ R.map (nerveMap F)) h
    exact (H.congr rfl hR).trans (stepHomotopy hi hj a.succ u v c e s t hs ht hs' ht').symm

/-- The unexpanded evaluation for a specified admissible pair of marks. -/
def markedEvaluation (i : Fin (k.len + 1)) (j : Fin (l.len + 1))
    (hu : ∀ q a v, coord k q (s.app q a) v ≤ i)
    (hv : ∀ q a v, j ≤ coord l q (t.app q a) v) :
    Fiber T U n ⥤ CostructuredArrow (toTarget W x y) (NecklacesOver.wedge P Q) :=
  evaluate (NecklacesOver.wedge P Q) (collapse c e) (JTMarkedBinaryLabels.inputs u v i j)
    (joined s t) (JTMarkedBinaryLabels.raw_over_wedge u v i j c e s t (joined s t)
      (JTBinaryPrismParameter.parameter_left _ _ _ _ _ _)
      (JTBinaryPrismParameter.parameter_right _ _ _ _ _ _) hu hv hs' ht')

/-- For two ordered pairs of admissible marks, the full actual evaluations
of the same internal-necklace category are homotopic after singular realization. -/
def orderedMarkHomotopy :
    SSet.Homotopy
      (R.map (nerveMap (markedEvaluation u v c e s t hs' ht' i₀ j₀ hs
        (fun q a v ↦ hj.trans (ht q a v)))))
      (R.map (nerveMap (markedEvaluation u v c e s t hs' ht' i₁ j₁
        (fun q a v ↦ (hs q a v).trans hi) ht))) := by
  let last := Fin.last (common k l).len
  have A : beforeEvaluation hi hj last u v c e s t hs ht hs' ht' =
      markedEvaluation u v c e s t hs' ht' i₀ j₀ hs (fun q a v ↦ hj.trans (ht q a v)) := by
    unfold beforeEvaluation markedEvaluation
    apply evaluate_congr
    exact stepInputs_last hi hj u v
  have B : afterEvaluation hi hj 0 u v c e s t hs ht hs' ht' =
      markedEvaluation u v c e s t hs' ht' i₁ j₁ (fun q a v ↦ (hs q a v).trans hi) ht := by
    unfold afterEvaluation markedEvaluation
    apply evaluate_congr
    exact stepInputs_first hi hj u v
  rw [← A, ← B]
  exact (fromFirst hi hj u v c e s t hs ht hs' ht' last).symm

/-- Any two admissible pairs of marks give homotopic evaluations of all
the same internal necklaces over the unchanged native target. -/
def markHomotopy (i i' : Fin (k.len + 1)) (j j' : Fin (l.len + 1))
    (hu : ∀ q a v, coord k q (s.app q a) v ≤ i)
    (hu' : ∀ q a v, coord k q (s.app q a) v ≤ i')
    (hv : ∀ q a v, j ≤ coord l q (t.app q a) v)
    (hv' : ∀ q a v, j' ≤ coord l q (t.app q a) v) :
    SSet.Homotopy
      (R.map (nerveMap (markedEvaluation u v c e s t hs' ht' i j hu hv)))
      (R.map (nerveMap (markedEvaluation u v c e s t hs' ht' i' j' hu' hv'))) := by
  have hmax (q) (a) (v) : max j j' ≤ coord l q (t.app q a) v := max_le (hv q a v) (hv' q a v)
  have H := orderedMarkHomotopy (le_max_left i i') (le_max_left j j')
    u v c e s t hu hmax hs' ht'
  have H' := orderedMarkHomotopy (le_max_right i i') (le_max_right j j')
    u v c e s t hu' hmax hs' ht'
  exact H.trans H'.symm

end

end DaggerModels.PartII.JTMarkedStaircaseEvaluation
