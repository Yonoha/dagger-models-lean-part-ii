import DaggerModelsPartII.DecoratedCylinderNecklacePresentation
import DaggerModelsPartII.MovingHomNaturalTransformation
import DaggerModelsPartII.OrderedLabelNaturalWeakSpans
import NativeSimplicialReplacementReindex

/-!
# The actual presentation-necklace Hom bar over the original decorated evaluator

Every internal native necklace, its full map into the decorated cylinder, and
both actual ordered endpoints are retained. The resulting whole-bar map is
weak and commutes with the SAME original raw-Hom evaluator. No target-functor
or evaluator weakness is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerChosenRigidificationNecklace
open DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementWeightsChange
open DaggerNativeSimplicialReplacementReindex
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.DecoratedNecklacePresentationHom

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open DecoratedCylinderNecklacePresentation
open DecoratedNecklaceHomDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev B := JTXiEndpointCollapse.boundary

variable (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))

private abbrev P := Presentation W x y
private abbrev p (s : P W x y) := (projection W x y).obj s
private abbrev c (s : P W x y) :=
  (BoundaryNecklaceComma.sourceCode (underDiagram W x y)).obj s
private abbrev T (s : P W x y) :=
  OrderedLabelElements.necklace W (boundaryPoint W x y) (p W x y s)
private abbrev k (s : P W x y) :=
  OrderedLabelElements.degree W (boundaryPoint W x y) (p W x y s)

/-- The SAME original internal native necklace in every presentation. -/
def internalDiagram : P W x y ⥤ SSet.{0} :=
  BoundaryNecklaceComma.sourceCode (underDiagram W x y) ⋙
    NecklaceCode.simplicialFunctor

/-- The actual selected decorated cylinder, pulled back to each presentation. -/
def outerDiagram : P W x y ⥤ SSet.{0} :=
  projection W x y ⋙ cylinderDiagram W x y

/-- The actual internal necklace map is an under-boundary natural map into
the selected decorated cylinder, with both operator axes preserved. -/
def internalEvaluation : internalDiagram W x y ⟶ outerDiagram W x y :=
  Functor.whiskerRight
    (BoundaryNecklaceComma.evaluation (underDiagram W x y)) (Under.forget B)

private def internalFirst (s : P W x y) :
    (rigidification.obj ((internalDiagram W x y).obj s)).Obj :=
  RV ((c W x y s).toSSet) (c W x y s).first

private def internalLast (s : P W x y) :
    (rigidification.obj ((internalDiagram W x y).obj s)).Obj :=
  RV ((c W x y s).toSSet) (c W x y s).last

private def outerFirst (s : P W x y) :
    (rigidification.obj ((outerDiagram W x y).obj s)).Obj :=
  RV ((JTNecklaceEndpointCylinder.value (T W x y s)).obj (k W x y s))
    (NecklaceCylinderHomSpan.firstVertex (T W x y s) (k W x y s))

private def outerLast (s : P W x y) :
    (rigidification.obj ((outerDiagram W x y).obj s)).Obj :=
  RV ((JTNecklaceEndpointCylinder.value (T W x y s)).obj (k W x y s))
    (NecklaceCylinderHomSpan.lastVertex (T W x y s) (k W x y s))

private theorem internalFirst_map {s t : P W x y} (f : s ⟶ t) :
    (rigidification.map ((internalDiagram W x y).map f)).obj
      (internalFirst W x y s) = internalFirst W x y t := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((c W x y t).toSSet))
  exact ((BoundaryNecklaceComma.sourceCode (underDiagram W x y)).map f).first

private theorem internalLast_map {s t : P W x y} (f : s ⟶ t) :
    (rigidification.map ((internalDiagram W x y).map f)).obj
      (internalLast W x y s) = internalLast W x y t := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((c W x y t).toSSet))
  exact ((BoundaryNecklaceComma.sourceCode (underDiagram W x y)).map f).last

private theorem outerFirst_map {s t : P W x y} (f : s ⟶ t) :
    (rigidification.map ((outerDiagram W x y).map f)).obj
      (outerFirst W x y s) = outerFirst W x y t := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((outerDiagram W x y).obj t))
  have h := congrFun (NatTrans.congr_app
    (Under.w ((underDiagram W x y).map f.base)) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₀)
  change ((outerDiagram W x y).map f).app (op ⦋0⦌)
      (NecklaceCylinderHomSpan.firstVertex (T W x y s) (k W x y s)) =
    NecklaceCylinderHomSpan.firstVertex (T W x y t) (k W x y t)
  exact h

private theorem outerLast_map {s t : P W x y} (f : s ⟶ t) :
    (rigidification.map ((outerDiagram W x y).map f)).obj
      (outerLast W x y s) = outerLast W x y t := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((outerDiagram W x y).obj t))
  have h := congrFun (NatTrans.congr_app
    (Under.w ((underDiagram W x y).map f.base)) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₁)
  change ((outerDiagram W x y).map f).app (op ⦋0⦌)
      (NecklaceCylinderHomSpan.lastVertex (T W x y s) (k W x y s)) =
    NecklaceCylinderHomSpan.lastVertex (T W x y t) (k W x y t)
  exact h

private theorem evaluation_first (s : P W x y) :
    ((Functor.whiskerRight (internalEvaluation W x y) rigidification).app s).obj
      (internalFirst W x y s) = outerFirst W x y s := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((outerDiagram W x y).obj s))
  have h := ((BoundaryNecklaceComma.toNative ((underDiagram W x y).obj s.base)).obj
    s.fiber).first
  change s.fiber.hom.right.app (op ⦋0⦌) s.fiber.left.first =
    BoundaryNecklaceComma.first ((underDiagram W x y).obj s.base) at h
  rw [BoundaryNecklaceComma.first_eq] at h
  change ((internalEvaluation W x y).app s).app (op ⦋0⦌)
      (c W x y s).first =
    NecklaceCylinderHomSpan.firstVertex (T W x y s) (k W x y s)
  exact h

private theorem evaluation_last (s : P W x y) :
    ((Functor.whiskerRight (internalEvaluation W x y) rigidification).app s).obj
      (internalLast W x y s) = outerLast W x y s := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (RV ((outerDiagram W x y).obj s))
  have h := ((BoundaryNecklaceComma.toNative ((underDiagram W x y).obj s.base)).obj
    s.fiber).last
  change s.fiber.hom.right.app (op ⦋0⦌) s.fiber.left.last =
    BoundaryNecklaceComma.last ((underDiagram W x y).obj s.base) at h
  rw [BoundaryNecklaceComma.last_eq] at h
  change ((internalEvaluation W x y).app s).app (op ⦋0⦌)
      (c W x y s).last =
    NecklaceCylinderHomSpan.lastVertex (T W x y s) (k W x y s)
  exact h

/-- Full original rigidification Hom of each INTERNAL presentation necklace. -/
def internalHomDiagram : P W x y ⥤ SSet.{0} :=
  homDiagram (internalDiagram W x y ⋙ rigidification)
    (internalFirst W x y) (internalLast W x y)
    (internalFirst_map W x y) (internalLast_map W x y)

/-- The actual original Hom map induced by every internal necklace map. -/
def leftHomMap : internalHomDiagram W x y ⟶
    projection W x y ⋙ cylinderHomDiagram W x y :=
  MovingHomNaturalTransformation.homNatTrans
    (F := internalDiagram W x y ⋙ rigidification)
    (G := outerDiagram W x y ⋙ rigidification)
    (internalFirst W x y) (internalLast W x y)
    (internalFirst_map W x y) (internalLast_map W x y)
    (outerFirst W x y) (outerLast W x y)
    (outerFirst_map W x y) (outerLast_map W x y)
    (Functor.whiskerRight (internalEvaluation W x y) rigidification)
    (evaluation_first W x y) (evaluation_last W x y)

/-- The source internal necklace Hom is weakly contractible, including length zero. -/
private theorem internalHom_point_GW (s : P W x y) :
    DaggerSSetGluing.GW (DaggerOriginalProductGadget.pointMap
      ((internalHomDiagram W x y).obj s)) := by
  change DaggerSSetGluing.GW (DaggerOriginalProductGadget.pointMap
    (NecklaceCylinderHomSpan.necklaceHom (c W x y s)))
  exact DecoratedNecklaceHomBar.necklaceHom_point_GW (c W x y s)

/-- Both endpoint Hom weights are contractible, so the actual component map is weak. -/
theorem leftHomMap_weak (s : P W x y) : WeakEquivalence ((leftHomMap W x y).app s) := by
  have hs : WeakEquivalence (DaggerOriginalProductGadget.pointMap
      ((internalHomDiagram W x y).obj s)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (internalHom_point_GW W x y s)
  have ht : WeakEquivalence (DaggerOriginalProductGadget.pointMap
      ((cylinderHomDiagram W x y).obj (p W x y s))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DecoratedCylinderNecklacePresentation.cylinderHom_point_GW W x y (p W x y s))
  have he : (leftHomMap W x y).app s ≫
      DaggerOriginalProductGadget.pointMap
        ((cylinderHomDiagram W x y).obj (p W x y s)) =
      DaggerOriginalProductGadget.pointMap ((internalHomDiagram W x y).obj s) :=
    DaggerOriginalProductGadget.pointIsTerminal.hom_ext _ _
  rw [← he] at hs
  letI : WeakEquivalence
      (DaggerOriginalProductGadget.pointMap
        ((cylinderHomDiagram W x y).obj (p W x y s))) := ht
  letI : WeakEquivalence
      ((leftHomMap W x y).app s ≫
        DaggerOriginalProductGadget.pointMap
          ((cylinderHomDiagram W x y).obj (p W x y s))) := hs
  exact weakEquivalence_of_postcomp ((leftHomMap W x y).app s)
    (DaggerOriginalProductGadget.pointMap ((cylinderHomDiagram W x y).obj (p W x y s)))

/-- The full original replacement diagonal of internal native necklace Homs. -/
def internalBar : SSet.{0} := DaggerBisimplicialDiagonal.diag
  (replacement (internalHomDiagram W x y))

/-- Retain the whole presentation chain, change every entire Hom simplex, and
then reindex its whole chain by the actual projection to the decorated index. -/
def toCylinderBar : internalBar W x y ⟶
    DecoratedNecklaceHomBar.cylinderBar W x y :=
  diagonalChange (leftHomMap W x y) ≫
    diagonalReindex (projection W x y) (cylinderHomDiagram W x y)

/-- The actual presentation-over-cylinder Hom-bar leg is Kan weak. -/
theorem toCylinderBar_weak : WeakEquivalence (toCylinderBar W x y) := by
  have hleft : WeakEquivalence (diagonalChange (leftHomMap W x y)) :=
    OrderedLabelNaturalWeakSpans.diagonalChange_weak
      (leftHomMap W x y) (leftHomMap_weak W x y)
  have hreindex : WeakEquivalence
      (diagonalReindex (projection W x y) (cylinderHomDiagram W x y)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (diagonalReindex_GW (projection W x y) (cylinderHomDiagram W x y)
        ((DaggerSSetGluing.weakEquivalence_iff_GW _).mp
          (DecoratedCylinderNecklacePresentation.projection_weak W x y))
        (DecoratedCylinderNecklacePresentation.cylinderHom_point_GW W x y))
  dsimp only [toCylinderBar]
  letI : WeakEquivalence (diagonalChange (leftHomMap W x y)) := hleft
  letI : WeakEquivalence
      (diagonalReindex (projection W x y) (cylinderHomDiagram W x y)) := hreindex
  infer_instance

/-- The same original evaluator, now on every complete internal presentation chain. -/
def internalRight : internalHomDiagram W x y ⟶
    (Functor.const (P W x y)).obj (rawHom W x y) :=
  leftHomMap W x y ≫
    Functor.whiskerLeft (projection W x y) (rightMap W x y)

def internalEvaluator : internalBar W x y ⟶ rawHom W x y :=
  diagonalAugmentation (internalHomDiagram W x y) (internalRight W x y)

/-- Exact whole-bar triangle over the SAME original raw rigidification Hom.
No inversion, endpoint substitution, or target weak premise enters. -/
theorem evaluator_triangle :
    toCylinderBar W x y ≫ DecoratedNecklaceHomBar.evaluator W x y =
      internalEvaluator W x y := by
  dsimp only [toCylinderBar, DecoratedNecklaceHomBar.evaluator, internalEvaluator,
    internalRight]
  rw [Category.assoc,
    DaggerNativeSimplicialReplacementReindex.augmentation_square]
  exact DaggerNativeSimplicialReplacementWeightsChange.augmentation_square
    (leftHomMap W x y) (Functor.whiskerLeft (projection W x y) (rightMap W x y))

end

end DaggerModels.PartII.DecoratedNecklacePresentationHom
