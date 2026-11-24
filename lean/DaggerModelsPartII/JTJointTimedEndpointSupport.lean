import DaggerModelsPartII.JTPrismJointCoefficient

/-!
# Full time support at a vertex of the joint inverse interval

An overlap vertex determines a degree-zero bead. Its parameter retains the
entire independent time simplex, and its row coefficient restricts to the
constant joint row on precisely the coefficient vertices used by that prism.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointTimedEndpointSupport

open JTParametrizedTargetFamilies (Family codes)
open JTJointRelativeGraphFamily (coefficient)
open JTTargetJointMarks (Joint)
open JTTargetIntervalPullback (sourceInterval)
open JTTargetIntervalGluing (middleInclusion)
open JTParametrizedBeadGraph (fullBeadParameter fullBeadSupport
  fullBeadSupportInclusion jointCoefficient fullBeadCoefficient_at_joint)
open JTPrismRectangle (supportedParameter supportedParameter_factor)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (j : Joint Q.code)

/-- An actual overlap vertex as a degree-zero native bead. -/
def vertexBead
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (NecklaceCode.single 0).toSSet ⟶
      (sourceInterval (F.collapse.app a) j j le_rfl).toSSet :=
  (NecklaceCode.singleIso 0).hom ≫ SSet.yonedaEquiv.symm u

/-- The canonical vertex of the native degree-zero bead. -/
def singleVertex : (NecklaceCode.single 0).toSSet.obj zero :=
  (NecklaceCode.singleIso 0).inv.app zero
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))

theorem vertexBead_vertex
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (vertexBead F a j u).app zero singleVertex = u := by
  change (SSet.yonedaEquiv.symm u).app zero
    ((NecklaceCode.singleIso 0).hom.app zero
      ((NecklaceCode.singleIso 0).inv.app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))))) = u
  have h := congrFun (NatTrans.congr_app (NecklaceCode.singleIso 0).inv_hom_id zero)
    (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))
  change (NecklaceCode.singleIso 0).hom.app zero
      ((NecklaceCode.singleIso 0).inv.app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) = _ at h
  rw [h]
  exact NecklaceCode.pointAt_vertex_apply u _

/-- Every original source vertex mapping to the target joint lies in the
full inverse interval, including vertices inside a bead. -/
theorem sourceVertex_lifts
    (v : ((codes L).obj a).toSSet.obj zero)
    (hv : (F.collapse.app a).map.app zero v =
      (NecklaceCode.pointAt Q.code (ULift.up j.val)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) :
    ∃ u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero,
      (middleInclusion (F.collapse.app a) j).app zero u = v := by
  let t := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))
  let sq := (JTTargetIntervalGluing.middlePB (F.collapse.app a) j).map
    ((evaluation _ _).obj zero)
  obtain ⟨u, hu, _⟩ := Types.exists_of_isPullback sq v t hv
  exact ⟨u, hu⟩

private abbrev originalBead (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :=
  vertexBead F a j u ≫ middleInclusion (F.collapse.app a) j

/-- The degree-zero bead can be chosen at every original source vertex over
the target joint. -/
theorem originalBead_for_sourceVertex
    (v : ((codes L).obj a).toSSet.obj zero)
    (hv : (F.collapse.app a).map.app zero v =
      (NecklaceCode.pointAt Q.code (ULift.up j.val)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) :
    ∃ u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero,
      (originalBead F a j u).app zero singleVertex = v := by
  obtain ⟨u, hu⟩ := sourceVertex_lifts F a j v hv
  refine ⟨u, ?_⟩
  change (middleInclusion (F.collapse.app a) j).app zero
    ((vertexBead F a j u).app zero singleVertex) = v
  rw [vertexBead_vertex, hu]

/-- The endpoint parameter on the whole independent time simplex. -/
def timedParameter
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶
      J.obj ((coefficient (L := L)).obj a) :=
  fullBeadParameter F a 0 (originalBead F a j u)

/-- All coefficient indices used by the entire timed endpoint prism. -/
abbrev timedSupport
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    SimplexCategory :=
  fullBeadSupport F a 0 (originalBead F a j u)

/-- The supported parameter retaining every time vertex of this endpoint. -/
def supportedTimedParameter
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶ J.obj (timedSupport F a j u) :=
  supportedParameter (timedParameter F a j u)

/-- The supported timed parameter recovers the original entire prism map. -/
theorem supportedTimedParameter_fac
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    supportedTimedParameter F a j u ≫
        J.map (fullBeadSupportInclusion F a 0 (originalBead F a j u)) =
      timedParameter F a j u :=
  supportedParameter_factor (timedParameter F a j u)

/-- The row coefficient of the degree-zero bead, before support restriction. -/
def rowCoefficient
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (Input W).obj (op (⦋0⦌, (coefficient (L := L)).obj a)) :=
  SSet.yonedaEquiv (X := JTProjectiveOrderedFiberComparison.row W ⦋0⦌)
    (JTParametrizedBeadGraph.coefficient (a := a) 0
    (originalBead F a j u))

/-- Restricting the endpoint row to its used coefficient indices gives the
constant row of the actual target joint. -/
theorem rowCoefficient_at_joint
    (u : (sourceInterval (F.collapse.app a) j j le_rfl).toSSet.obj zero) :
    (Input W).map
      (show (⦋0⦌, timedSupport F a j u) ⟶
        (⦋0⦌, (coefficient (L := L)).obj a) from
        (𝟙 ⦋0⦌, fullBeadSupportInclusion F a 0 (originalBead F a j u))).op
      (rowCoefficient F a j u) =
    (Input W).map
      (show (⦋0⦌, timedSupport F a j u) ⟶ (⦋0⦌, ⦋0⦌) from
        (SimplexCategory.isTerminalZero.from ⦋0⦌,
          SimplexCategory.isTerminalZero.from (timedSupport F a j u))).op
      (jointCoefficient (Q := Q) j) :=
  fullBeadCoefficient_at_joint F a 0 j (vertexBead F a j u)

end

end DaggerModels.PartII.JTJointTimedEndpointSupport
