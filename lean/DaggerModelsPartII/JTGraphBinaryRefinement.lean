import DaggerModelsPartII.JTGraphBinaryTraversal
import DaggerModelsPartII.JTOrderedLabelBinaryGlue

/-!
# Strict graph refinements are closed under the native wedge
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphBinaryRefinement

open OrdinaryJTRealization JTReversalInput ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison JTNecklaceLabelRealization JTGraphRefinement
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints JTRealizedLabelEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev F := discreteFree.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x z y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {P : NecklacesOver (R W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (R W) (rawVertex W z) (rawVertex W y)}
variable (D : Refinement W x z P) (E : Refinement W z y Q)

private abbrev K := JTParameterBlocks.common D.degree E.degree
private abbrev C := JTOrderedLabelBinaryGlue.code D.code E.code
private abbrev A := single 1
private abbrev L := tripleRightT.{0} D.code A E.code
private abbrev M := tripleRightU.{0} D.code A E.code
private abbrev V := tripleRightV.{0} D.code A E.code

private def inputs : JTOrderedLabelBinaryGlue.Inputs W D.code E.code (K D E) x z y where
  left := ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op D.code)).map
    (JTParameterBlocks.leftRet D.degree E.degree).op D.label
  right := ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op E.code)).map
    (JTParameterBlocks.rightRet D.degree E.degree).op E.label

private abbrev η := orderedLabel W x y (C D E) (K D E)
  (JTOrderedLabelBinaryGlue.orderedTriplePoint (inputs D E))

private abbrev g := JTGraphBinaryTraversal.parameter D.code E.code D.parameter E.parameter

private theorem label_reindex (a b : (row W ⦋0⦌).obj (op ⦋0⦌))
    (T : NecklaceCode) {k l : SimplexCategory} (r : k ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W a b)).obj (op T)).obj (op l)) :
    orderedLabel W a b T k
        (((orderedNecklaceLabels W (boundaryPoint W a b)).obj (op T)).map r.op u) =
      (diagramTensor (F.obj T.toSSet)).map (SSet.stdSimplex.map r) ≫
        orderedLabel W a b T l u :=
  congrFun ((pullback.fst ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W a b)).naturality r.op) u

private theorem left_realize :
    L D E ≫ realizeGraph W (K D E) (g D E) (η D E) =
      realizeGraph W D.degree D.parameter (orderedLabel W x z D.code D.degree D.label) := by
  rw [realizeGraph_comp, JTGraphBinaryTraversal.parameter_left]
  have h := congrArg SSet.yonedaEquiv
    (JTOrderedLabelBinaryGlue.orderedTriplePoint_left (inputs D E))
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    JTOrderedLabelBinaryGlue.leftCoefficient, JTOrderedLabelBinaryGlue.coefficient] at h
  erw [Equiv.apply_symm_apply] at h
  change Functor.whiskerRight (F.map (L D E))
      (tensorRight (SSet.stdSimplex.obj (K D E))) ≫ η D E =
    orderedLabel W x z D.code (K D E) (inputs D E).left at h
  rw [h]
  change _ = realizeGraph W D.degree D.parameter (orderedLabel W x z D.code D.degree D.label)
  unfold inputs
  erw [label_reindex]
  exact realizeGraph_split W _ _ (JTParameterBlocks.left_split D.degree E.degree) _ _

private theorem right_realize :
    V D E ≫ realizeGraph W (K D E) (g D E) (η D E) =
      realizeGraph W E.degree E.parameter (orderedLabel W z y E.code E.degree E.label) := by
  rw [realizeGraph_comp, JTGraphBinaryTraversal.parameter_right]
  have h := congrArg SSet.yonedaEquiv
    (JTOrderedLabelBinaryGlue.orderedTriplePoint_right (inputs D E))
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    JTOrderedLabelBinaryGlue.rightCoefficient, JTOrderedLabelBinaryGlue.coefficient] at h
  erw [Equiv.apply_symm_apply] at h
  change Functor.whiskerRight (F.map (V D E))
      (tensorRight (SSet.stdSimplex.obj (K D E))) ≫ η D E =
    orderedLabel W z y E.code (K D E) (inputs D E).right at h
  rw [h]
  change _ = realizeGraph W E.degree E.parameter (orderedLabel W z y E.code E.degree E.label)
  unfold inputs
  erw [label_reindex]
  exact realizeGraph_split W _ _ (JTParameterBlocks.right_split D.degree E.degree) _ _

private theorem middle_realize :
    M D E ≫ realizeGraph W (K D E) (g D E) (η D E) =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [realizeGraph_comp]
  have h := congrArg SSet.yonedaEquiv
    (JTOrderedLabelBinaryGlue.orderedTriplePoint_middle (inputs D E))
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
    JTOrderedLabelBinaryGlue.middleCoefficient] at h
  change Functor.whiskerRight (F.map (M D E))
      (tensorRight (SSet.stdSimplex.obj (K D E))) ≫ η D E =
    identityCoefficient W z (K D E) at h
  rw [h, realizeGraph, realizedIdentityCoefficient, ← Category.assoc]
  congr 1

private abbrev collapse : C D E ⟶ (NecklacesOver.wedge P Q).code :=
  JTGraphBinaryTraversal.collapse D.code E.code ≫ wedgeMap D.collapse E.collapse

private theorem collapse_comp :
    realizeGraph W (K D E) (g D E) (η D E) =
      (collapse D E).map ≫ (NecklacesOver.wedge P Q).map := by
  apply tripleRight_hom_ext (T := D.code) (U := A) (V := E.code)
  · rw [left_realize, D.comm]
    change _ = L D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map
    rw [← Category.assoc (L D E), ← Category.assoc (L D E),
      JTGraphBinaryTraversal.collapse_left, wedgeMap_left, Category.assoc,
      NecklacesOver.wedge_left]
  · rw [middle_realize]
    change _ = M D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map
    rw [← Category.assoc (M D E), ← Category.assoc (M D E),
      JTGraphBinaryTraversal.collapse_middle, JTGraphBinaryTraversal.joint]
    simp only [Category.assoc]
    rw [← Category.assoc (wedgeιLeft D.code E.code), wedgeMap_left,
      Category.assoc, NecklacesOver.wedge_left]
    have h : pointAt D.code (ULift.up (Fin.last D.code.len)) ≫ D.collapse.map =
        pointAt P.code (ULift.up (Fin.last P.code.len)) := by
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
      exact D.collapse.last
    rw [← Category.assoc (pointAt D.code _), h]
    congr 1
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, pointAt_vertex, Equiv.apply_symm_apply]
    exact P.last.symm
  · rw [right_realize, E.comm]
    change _ = V D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map
    rw [← Category.assoc (V D E), ← Category.assoc (V D E),
      JTGraphBinaryTraversal.collapse_right, wedgeMap_right, Category.assoc,
      NecklacesOver.wedge_right]

/-- Glue two strict graph refinements over the original native wedge. -/
def wedge : Refinement W x y (NecklacesOver.wedge P Q) where
  code := C D E
  degree := K D E
  label := JTOrderedLabelBinaryGlue.orderedTriplePoint (inputs D E)
  parameter := g D E
  collapse := collapse D E
  comm := collapse_comp D E

end

end DaggerModels.PartII.JTGraphBinaryRefinement
