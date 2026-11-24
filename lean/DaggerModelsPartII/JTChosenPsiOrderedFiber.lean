import DaggerModelsPartII.JTRightMateOrderedFiber
import DaggerModelsPartII.JTXiOrderedPointCalibration
import DaggerModelsPartII.JTAFlatFromRawWeak

/-! The actual chosen strictification map on its original ordered fibers. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChosenPsiOrderedFiber

open JTStrictificationCoefficients JTChosenOrdinaryAdjoint JTChosenCEUnitBoundary
open JTGtildeOrderedFiberAction JTAFlatOrderedFiberAction JTXiRowEndpoints
open JTGammaDerivedFiber JTRightMateOrderedFiber
open ChosenHomotopyFiberComparison ChosenHomotopyFiberFunctor

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev C (W : Source) := rigidCoefficient (chosenT W)
private abbrev Vertex (W : Source) := (sourceRow W ⦋0⦌).obj (op ⦋0⦌)

private local instance : HasLimits JTRelativeReedyFrame.Coefficient :=
  daggerSimplicialCatHasLimits
private local instance : HasColimits JTRelativeReedyFrame.Coefficient :=
  daggerSimplicialCatHasColimits
private local instance : ModelCategory JTRelativeReedyFrame.Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The ordered target objects of the actual coefficient, obtained from
the vertices of the specified adjunction unit. -/
def coefficientVertices (W : Source) (x y : Vertex W) : (C W).Obj × (C W).Obj :=
  let z := chosenVertices W (targetVertices W x y).1 (targetVertices W x y).2
  let e := OrdinaryRigidification.NerveVertices.vertexEquiv (C W).toSimplicialCat
  (e z.1, e z.2)

private theorem aFlat_point (W : Source) (x y : Vertex W) :
    sourcePoint W x y ≫ aBase W = boundaryPoint (C W)
      (coefficientVertices W x y).1 (coefficientVertices W x y).2 :=
  (aPoint_eq_original W x y).trans
    (JTXiOrderedPointCalibration.daggerEndpointPoint_eq_boundaryPoint (C W) _ _)

private def aFlatToXi (W : Source) (x y : Vertex W) :
    chosenFiber (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      JTXiChosenFiber.xiHomotopyFiber (C W)
        (coefficientVertices W x y).1 (coefficientVertices W x y).2 :=
  chosenMap (sourceEndpointArrow W) (xiEndpointArrow (C W))
    (aRow W ⦋1⦌) (aBase W) (aArrow_square W)
    (sourcePoint W x y) (boundaryPoint (C W)
      (coefficientVertices W x y).1 (coefficientVertices W x y).2)
    (aFlat_point W x y)

private theorem chosenMap_weak_of_point_eq {X Y B D K : SSet.{0}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) {d d' : K ⟶ D}
    (hd : b ≫ g = d) (he : d = d') (hw : WeakEquivalence (chosenMap p q f g h b d hd)) :
    WeakEquivalence (chosenMap p q f g h b d' (hd.trans he)) := by
  subst d'
  exact hw

private theorem aFlatToXi_weak (W : Source) (x y : Vertex W)
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (aFlatToXi W x y) :=
  chosenMap_weak_of_point_eq (sourceEndpointArrow W) (xiEndpointArrow (C W))
    (aRow W ⦋1⦌) (aBase W) (aArrow_square W) (sourcePoint W x y)
    (aPoint_eq_original W x y)
    (JTXiOrderedPointCalibration.daggerEndpointPoint_eq_boundaryPoint (C W) _ _)
    (JTAFlatFromRawWeak.chosenFiberMap_weak_of_raw W x y hraw)

/-- The exact outer-one row of the literal chosen strictification map. -/
def psiRow (W : Source) :
    sourceRow W ⦋1⦌ ⟶ JTGammaRowEndpoints.gammaRow (C W) JTOrderedFrameMate.oneIndex :=
  aRow W ⦋1⦌ ≫ mateRow (C W)

/-- Its component is the original chosenPsi on the unchanged input row. -/
theorem psiRow_app (W : Source) (k : SimplexCategoryᵒᵖ) :
    (psiRow W).app k = ((chosenPsi W).app (op JTOrderedFrameMate.oneIndex)).app k := by
  rw [chosenPsi_eq_chosenAFlat_rightMate]
  rfl

/-- The ordered base map of the same chosen endpoint square. -/
def psiBase (W : Source) := aBase W ≫ mateBase (C W)

private theorem psiSquare (W : Source) :
    sourceEndpointArrow W ≫ psiBase W = psiRow W ≫ rawArrow (C W) := by
  dsimp only [psiBase, psiRow]
  rw [← Category.assoc, aArrow_square, Category.assoc]
  have h := mateSquare (C W)
  change JTRightAdjointOrderedFiber.daggerEndpointArrow
    (OrdinaryRigidification.DaggerNerve.daggerCoherentNerve.obj (C W)) ≫ mateBase (C W) =
      mateRow (C W) ≫ rawArrow (C W) at h
  rw [h, Category.assoc]

private theorem psiPoint (W : Source) (x y : Vertex W) :
    sourcePoint W x y ≫ psiBase W = rawPoint (C W)
      (coefficientVertices W x y).1 (coefficientVertices W x y).2 := by
  rw [psiBase, ← Category.assoc, aFlat_point, matePoint]

/-- The chosen fiber map of the original strictification square. -/
def psiChosenMap (W : Source) (x y : Vertex W) :
    chosenFiber (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      gammaHomotopyFiber (C W) (coefficientVertices W x y).1 (coefficientVertices W x y).2 :=
  chosenMap (sourceEndpointArrow W) (rawArrow (C W)) (psiRow W) (psiBase W) (psiSquare W)
    (sourcePoint W x y) (rawPoint (C W) (coefficientVertices W x y).1
      (coefficientVertices W x y).2) (psiPoint W x y)

/-- Weakness of the original raw ordered-fiber comparison implies weakness
of the map induced by the literal chosen strictification square. -/
theorem psiChosenMap_weak_of_raw (W : Source) (x y : Vertex W)
    (hraw : WeakEquivalence (JTRawOrdinaryAdjoint.rawChosenFiberMapAtP W x y)) :
    WeakEquivalence (psiChosenMap W x y) := by
  let Q := (weakEquivalences SSet.{0}).Q
  let v := coefficientVertices W x y
  haveI : IsFibrant (C W) := rigidCoefficient_fibrant (chosenT W)
  haveI : WeakEquivalence (aFlatToXi W x y) := aFlatToXi_weak W x y hraw
  haveI : WeakEquivalence (mateChosenMap (C W) v.1 v.2) := mateChosenMap_weak (C W) _ _
  haveI : IsIso (Q.map (aFlatToXi W x y)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
  haveI : IsIso (Q.map (mateChosenMap (C W) v.1 v.2)) :=
    Localization.inverts Q (weakEquivalences SSet.{0}) _ (mem_weakEquivalences _)
  have hcomp : Q.map (aFlatToXi W x y) ≫ Q.map (mateChosenMap (C W) v.1 v.2) =
      Q.map (psiChosenMap W x y) :=
    chosenMap_comp (sourceEndpointArrow W) (xiEndpointArrow (C W)) (rawArrow (C W))
      (aRow W ⦋1⦌) (aBase W) (aArrow_square W) (mateRow (C W)) (mateBase (C W))
      (mateSquare (C W)) (sourcePoint W x y) (boundaryPoint (C W) v.1 v.2)
      (rawPoint (C W) v.1 v.2) (aFlat_point W x y) (matePoint (C W) v.1 v.2)
  apply (DaggerNativeAllCofibrantLocalizationSaturation.weakEquivalence_iff_localization_isIso
    Q (psiChosenMap W x y)).2
  rw [← hcomp]
  infer_instance

end

end DaggerModels.PartII.JTChosenPsiOrderedFiber
