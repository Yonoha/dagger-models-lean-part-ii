import DaggerModelsPartII.JTParameterBlocks
import DaggerModelsPartII.JTRawVertexRecovery
import DaggerModelsPartII.JTNativeRowLabel
import ChosenNecklaceTripleWedge
import ChosenNecklaceWedgeFunctor

/-!
# Joining two graph traversals over a common JT parameter

The middle one-edge graph connects the actual terminal and initial parameter
vertices. Its horizontal collapse is a map of original necklace codes.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphBinaryTraversal

open JTParameterBlocks JTParameterContraction JTParameterVertexKan
open JTRawVertexRecovery

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev E := single 1

variable (T U : NecklaceCode)

private abbrev C := wedge T (wedge E U)
private abbrev L := tripleRightT.{0} T E U
private abbrev M := tripleRightU.{0} T E U
private abbrev P := tripleRightV.{0} T E U

variable {k l : SimplexCategory} (s : T.toSSet ⟶ J.obj k) (t : U.toSSet ⟶ J.obj l)

private abbrev K := common k l
private abbrev a := parameterIndex k (pointAt T (ULift.up (Fin.last T.len)) ≫ s)
private abbrev b := parameterIndex l (pointAt U (ULift.up 0) ≫ t)

private def connector : E.toSSet ⟶ J.obj (K (k := k) (l := l)) :=
  (singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌ ≫
    J.map (seam k l (a T s) (b U t))

private theorem vertex_eq_parameterVertex (m : SimplexCategory)
    (u : (Δ[0] : SSet.{0}) ⟶ J.obj m) :
    u = parameterVertex m (parameterIndex m u) :=
  (parameterIndex_vertex m u).trans (simplexUnit_vertex m _)

private theorem connector_left :
    pointAt T (ULift.up (Fin.last T.len)) ≫ (s ≫ J.map (leftIn k l)) =
      pointAt E (ULift.up 0) ≫ connector T U s t := by
  unfold connector
  rw [← Category.assoc (pointAt T _) s, ← Category.assoc (pointAt E _) (singleIso 1).hom,
    JTNativeRowLabel.nativeVertex, ← Category.assoc,
    show JTMixedGraphEndpointLifts.vertex ⦋1⦌ 0 =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0) from rfl,
    simplexUnit_vertex, seam_left_parameter_endpoint]
  exact congrArg (fun f ↦ f ≫ J.map (leftIn k l)) (vertex_eq_parameterVertex k _)

private theorem connector_right :
    pointAt E (ULift.up (Fin.last E.len)) ≫ connector T U s t =
      pointAt U (ULift.up 0) ≫ (t ≫ J.map (rightIn k l)) := by
  unfold connector
  rw [← Category.assoc (pointAt U _) t, ← Category.assoc (pointAt E _) (singleIso 1).hom,
    JTNativeRowLabel.nativeVertex, ← Category.assoc,
    show JTMixedGraphEndpointLifts.vertex ⦋1⦌ (Fin.last E.len) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) from rfl,
    simplexUnit_vertex, seam_right_parameter_endpoint]
  exact congrArg (fun f ↦ f ≫ J.map (rightIn k l)) (vertex_eq_parameterVertex l _).symm

/-- The two entire parameter maps together with the original joint path. -/
def parameter : (C T U).toSSet ⟶ J.obj (common k l) :=
  tripleRightDesc T E U (s ≫ J.map (leftIn k l)) (connector T U s t)
    (t ≫ J.map (rightIn k l)) (connector_left T U s t) (connector_right T U s t)

theorem parameter_left : L T U ≫ parameter T U s t = s ≫ J.map (leftIn k l) :=
  tripleRightDesc_T _ _ _ _ _ _ _ _

theorem parameter_right : P T U ≫ parameter T U s t = t ≫ J.map (rightIn k l) :=
  tripleRightDesc_V _ _ _ _ _ _ _ _

private def terminal := SSet.stdSimplex.isTerminalObj₀.from E.toSSet

/-- The common joint of the unextended target wedge, regarded as a vertex map. -/
def joint : (Δ[0] : SSet.{0}) ⟶ (wedge T U).toSSet :=
  pointAt T (ULift.up (Fin.last T.len)) ≫ wedgeιLeft T U

private theorem point_terminal (v : Vertices.{0} E) :
    pointAt E v ≫ terminal = 𝟙 (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private def collapseMap : (C T U).toSSet ⟶ (wedge T U).toSSet :=
  tripleRightDesc T E U (wedgeιLeft T U) (terminal ≫ joint T U) (wedgeιRight T U)
    (by rw [← Category.assoc, point_terminal, Category.id_comp, joint])
    (by rw [← Category.assoc, point_terminal, Category.id_comp, joint, wedge_comm])

/-- Collapse only the connector, retaining both native codes in order. -/
def collapse : NecklaceCode.Hom.{0} (C T U) (wedge T U) where
  map := collapseMap T U
  first := first_of_point _ (by
    rw [← pointAt_first_left T (wedge E U), Category.assoc]
    change pointAt T (ULift.up 0) ≫ L T U ≫ collapseMap T U = _
    rw [collapseMap, tripleRightDesc_T, pointAt_first_left])
  last := last_of_point _ (by
    rw [← pointAt_last_right T (wedge E U), ← pointAt_last_right E U]
    change (pointAt U (ULift.up (Fin.last U.len)) ≫
      wedgeιRight E U) ≫ wedgeιRight T (wedge E U) ≫ collapseMap T U = _
    rw [Category.assoc]
    change pointAt U (ULift.up (Fin.last U.len)) ≫ P T U ≫ collapseMap T U = _
    rw [collapseMap, tripleRightDesc_V, pointAt_last_right])

theorem collapse_left : L T U ≫ (collapse T U).map = wedgeιLeft T U := by
  change L T U ≫ collapseMap T U = _
  rw [collapseMap, tripleRightDesc_T]

theorem collapse_middle : M T U ≫ (collapse T U).map = terminal ≫ joint T U := by
  change M T U ≫ collapseMap T U = _
  rw [collapseMap, tripleRightDesc_U]

theorem collapse_right : P T U ≫ (collapse T U).map = wedgeιRight T U := by
  change P T U ≫ collapseMap T U = _
  rw [collapseMap, tripleRightDesc_V]

end

end DaggerModels.PartII.JTGraphBinaryTraversal
