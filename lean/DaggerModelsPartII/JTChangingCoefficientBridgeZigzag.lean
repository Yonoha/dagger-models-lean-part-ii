import DaggerModelsPartII.JTChangingCoefficientBridgePullback
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# Connecting the two restrictions in the actual target comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChangingCoefficientBridgeZigzag

open JTHigherInterleavedParameter (common)
open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism (vertical)
open JTChangingCoefficientBridgePullback
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {T : NecklaceCode} {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b')
variable (n : SimplexCategory)
variable (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj
  (op T)).obj (op (bridge k n)))
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q
private abbrev Fiber (T : NecklaceCode) (a : SimplexCategory) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj a)
private abbrev Original :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable (U : (under T).obj (time n) ⟶ (D Q).obj (bridgeIndex n z))

/-- The actual single functor on all internal necklaces in the joining time simplex. -/
def joinedComma : Fiber T (time n) ⥤ Original Q :=
  CostructuredArrow.map U ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (D Q)) (bridgeIndex n z) ⋙
    (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem bridgePresentation_eq (e : Fin 2) :
    bridgePresentation n z Q U e ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse =
      CostructuredArrow.map ((under T).map (timeSide n e)) ⋙ joinedComma n z Q U := by
  let G := BoundaryNecklaceComma.diagram
  have H := congrArg Cat.Hom.toFunctor (G.map_comp ((under T).map (timeSide n e)) U)
  change CostructuredArrow.map ((under T).map (timeSide n e) ≫ U) =
    CostructuredArrow.map ((under T).map (timeSide n e)) ⋙ CostructuredArrow.map U at H
  simp only [bridgePresentation, joinedComma, H, Functor.assoc]

include c h z in
private theorem joiningFiber_point_GW :
    DaggerSSetGluing.GW (DaggerOriginalProductGadget.pointMap
      (nerve (Fiber T (time n)))) := by
  let j := vertical c h n 0
  let w := ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map j.op z
  let I := OrderedLabelElements.mk W (boundaryPoint W x y) T (time n) w
  exact DecoratedCylinderNecklacePresentation.fiber_point_GW W x y I

private theorem zigzag_of_point_weak {C : Type} [Category C]
    (hw : WeakEquivalence (DaggerOriginalProductGadget.pointMap (nerve C)))
    (P P' : C) : Relation.EqvGen (fun A B : C ↦ Nonempty (A ⟶ B)) P P' := by
  letI := hw
  let e := DaggerOriginalProductGadget.pointIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  let p := DaggerOriginalProductGadget.pointMap (nerve C) ≫ e.hom
  haveI : WeakEquivalence p := by dsimp only [p]; infer_instance
  have hi := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero p).1
  letI : Subsingleton (SSet.π₀ (nerve C)) := hi.subsingleton
  have hπ : SSet.π₀.mk (X := nerve C) (ComposableArrows.mk₀ P) =
      SSet.π₀.mk (X := nerve C) (ComposableArrows.mk₀ P') :=
    Subsingleton.elim _ _
  have hz := (SSet.π₀.mk_eq_mk_iff (X := nerve C)
    (ComposableArrows.mk₀ P) (ComposableArrows.mk₀ P')).mp hπ
  have H : ∀ {a b : (nerve C).obj (op ⦋0⦌)},
      Relation.EqvGen (SSet.π₀Rel (X := nerve C)) a b →
      Relation.EqvGen (fun A B : C ↦ Nonempty (A ⟶ B))
        (CategoryTheory.nerveEquiv a) (CategoryTheory.nerveEquiv b) := by
    intro a b hab
    induction hab with
    | rel a b e =>
        obtain ⟨edge, first, last⟩ := e
        exact Relation.EqvGen.rel _ _
          ⟨CategoryTheory.nerve.homEquiv (SSet.Edge.mk edge first last)⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  simpa [CategoryTheory.nerveEquiv] using H hz

variable (s : T.toSSet ⟶ GroupoidSimplex.parameter.obj k)
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
  bridgeCylinder c h n z s)

/-- The exact side lift as a functor into the original target comma. -/
def sideComma (e : Fin 2) : Fiber T n ⥤ Original Q :=
  sidePresentation c h n z s Q U hU e ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse

/-- Each exact side comparison maps to the same joining comma functor. -/
def compareSide (e : Fin 2) : sideComma c h n z Q U s hU e ⟶
    CostructuredArrow.map ((under T).map (timeSide n e)) ⋙ joinedComma n z Q U :=
  compareComma c h n z s Q U hU e ≫ eqToHom (bridgePresentation_eq n z Q U e)

/-- The two side comparisons are connected in the actual target comma
for arbitrary choices of internal native necklaces on the two sides. -/
theorem side_zigzag (P P' : Fiber T n) :
    Relation.EqvGen (fun A B : Original Q ↦ Nonempty (A ⟶ B))
      ((sideComma c h n z Q U s hU 0).obj P)
      ((sideComma c h n z Q U s hU 1).obj P') := by
  let a := (CostructuredArrow.map ((under T).map (timeSide n 0))).obj P
  let b := (CostructuredArrow.map ((under T).map (timeSide n 1))).obj P'
  have hw : WeakEquivalence (DaggerOriginalProductGadget.pointMap (nerve (Fiber T (time n)))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (joiningFiber_point_GW c h n z)
  have hab := zigzag_of_point_weak hw a b
  have H {a b : Fiber T (time n)}
      (hab : Relation.EqvGen (fun A B : Fiber T (time n) ↦ Nonempty (A ⟶ B)) a b) :
      Relation.EqvGen (fun A B : Original Q ↦ Nonempty (A ⟶ B))
        ((joinedComma n z Q U).obj a) ((joinedComma n z Q U).obj b) := by
    induction hab with
    | rel A B f => exact Relation.EqvGen.rel _ _ ⟨(joinedComma n z Q U).map f.some⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _
    ⟨(compareSide c h n z Q U s hU 0).app P⟩) (Relation.EqvGen.trans _ _ _ (H hab)
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
        ⟨(compareSide c h n z Q U s hU 1).app P'⟩)))

end

end DaggerModels.PartII.JTChangingCoefficientBridgeZigzag
