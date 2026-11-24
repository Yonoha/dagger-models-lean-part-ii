import DaggerModelsPartII.JTThreePieceMiddleSupportDiagram
import DaggerModelsPartII.JTChosenSeamMiddleRaw
import DaggerModelsPartII.JTWhiskeredGraphEvaluation

/-!
The original full timed three-piece family supplies the natural support
diagram here. `JTThreePieceMiddleSupportDiagram.supported_row` identifies its
row, and `JTChosenSeamMiddleRaw.pieceEquations` combines the actual middle
support equation with the two old full-time outer equations. We then reuse
`JTWhiskeredGraphEvaluation` for the fixed-target evaluation and its weak
graph projection. No graph raw or additional support-factor premise is added.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTThreePieceMiddleSeamEvaluation

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (K : I ⥤ SimplexCategory)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (time : I ⥤ SimplexCategory)
variable (oldTimed : JTParametrizedTargetFamilies.Family Q
  (JTChosenSeamOldComparison.oldFamily W K f O).labels time)
variable (j : Joint Q.code)
variable (hj : ∀ a : I, orderMap (oldTimed.collapse.app a).map
  (JTThreePieceMiddleSupport.middleVertex P R a) = j.val)

/-- The naturally used full-time support, represented in simplicial sets. -/
abbrev support : I ⥤ SSet.{0} :=
  JTThreePieceMiddleSupportDiagram.support W K f O Q time oldTimed j hj ⋙ std

/-- Its literal inclusion in the original coefficient simplex diagram. -/
abbrev incl : support W K f O Q time oldTimed j hj ⟶ K ⋙ std :=
  Functor.whiskerRight
    (JTThreePieceMiddleSupportDiagram.u W K f O Q time oldTimed j hj) std

/-- The original middle row is stationary on exactly this used support. -/
theorem supported_row (a : I) :
    (incl W K f O Q time oldTimed j hj).app a ≫ f.app a =
      term ((support W K f O Q time oldTimed j hj).obj a) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient j) :=
  JTThreePieceMiddleSupportDiagram.supported_row
    W K f O Q time oldTimed j hj a

variable (e s : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I,
  e.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
    JTJointSubcomplexRelativeLift.boundaryPair W (f.app a)
      (JTParametrizedBeadGraph.jointCoefficient j))
variable (hs : ∀ a : I,
  s.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
    JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app a)
      (JTParametrizedBeadGraph.jointCoefficient j))
variable (heU : ∀ a : I,
  (incl W K f O Q time oldTimed j hj).app a ≫ e.app a =
    JTJointSubcomplexRelativeLift.identityOnU W
      (JTParametrizedBeadGraph.jointCoefficient j))
variable (hsU : ∀ a : I,
  (incl W K f O Q time oldTimed j hj).app a ≫ s.app a =
    JTJointSubcomplexRelativeLift.identityOnU W
      (JTParametrizedBeadGraph.jointCoefficient j))

private abbrev z (j : Joint Q.code) := JTParametrizedBeadGraph.jointCoefficient j
private abbrev C := JTChosenSeamChainDiagram.Index
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU
private abbrev base := JTChosenSeamChainDiagram.toOriginal
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU
private abbrev chosen := JTChosenSeamChainDiagram.seamFamily
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU O
private abbrev graph := JTChosenSeamGraphCover.graph
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU O time Q oldTimed
private abbrev π := JTChosenSeamGraphCover.projection
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU O time Q oldTimed
private abbrev θ := JTChosenSeamGraphCover.parameter
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU O time Q oldTimed
private abbrev target := JTChosenSeamGraphCover.triangleTarget
  W (z W Q j) (support W K f O Q time oldTimed j hj) K
  (incl W K f O Q time oldTimed j hj) f e s he hs
  (supported_row W K f O Q time oldTimed j hj) heU hsU O time Q oldTimed

/-- Every chosen chain object has the three exact full-graph equations. The
actual used face is the chosen support itself, so its factor is the identity. -/
theorem pieceEquations (p : C W K f O Q time oldTimed j hj e s he hs heU hsU) :
    JTWhiskeredGraphRaw.PieceEquations W
      ((chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle.data p)
      (JTWhiskeredGraphEvaluation.nativeCoordinate Q
        (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
        (base W K f O Q time oldTimed j hj e s he hs heU hsU ⋙ time)
        (target W K f O Q time oldTimed j hj e s he hs heU hsU)
        (π W K f O Q time oldTimed j hj e s he hs heU hsU) p)
      ((θ W K f O Q time oldTimed j hj e s he hs heU hsU).app p)
      (JTWhiskeredGraphEvaluation.rawTarget Q
        (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
        (target W K f O Q time oldTimed j hj e s he hs heU hsU) p) := by
  let b := (base W K f O Q time oldTimed j hj e s he hs heU hsU).obj p
  have hU : std.map (JTActualSourceJointSupport.usedInclusion oldTimed b j
        (JTThreePieceMiddleSupport.middleVertex P R b) (hj b)) =
      (𝟙 (std.obj (JTActualSourceJointSupport.usedDegree oldTimed b j
        (JTThreePieceMiddleSupport.middleVertex P R b) (hj b)))) ≫
        (incl W K f O Q time oldTimed j hj).app b := by
    rw [Category.id_comp]
    rfl
  exact JTChosenSeamMiddleRaw.pieceEquations W (z W Q j)
    (support W K f O Q time oldTimed j hj) K
    (incl W K f O Q time oldTimed j hj) f e s he hs
    (supported_row W K f O Q time oldTimed j hj) heU hsU
    O time Q oldTimed p j rfl (hj b) (𝟙 _) hU

/-- Keep the original full time on every higher-choice chain. -/
abbrev chainTime : C W K f O Q time oldTimed j hj e s he hs heU hsU ⥤
    SimplexCategory :=
  base W K f O Q time oldTimed j hj e s he hs heU hsU ⋙ time

/-- The complete reduced graph retains every internal necklace. -/
abbrev reduced : C W K f O Q time oldTimed j hj e s he hs heU hsU ⥤
    Under JTXiEndpointCollapse.boundary :=
  JTWhiskeredGraphEvaluation.reduced Q
    (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
    (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
    (target W K f O Q time oldTimed j hj e s he hs heU hsU)
    (π W K f O Q time oldTimed j hj e s he hs heU hsU)

/-- Evaluate every internal necklace in the literal original target comma
category `Q`, using the derived three-piece raw equations. -/
def evaluation : BoundaryNecklaceComma.Presentation
    (reduced W K f O Q time oldTimed j hj e s he hs heU hsU) ⥤
      JTGraphFactoredPresentation.TargetComma Q :=
  JTWhiskeredGraphEvaluation.evaluation Q
    (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
    (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
    (target W K f O Q time oldTimed j hj e s he hs heU hsU)
    (π W K f O Q time oldTimed j hj e s he hs heU hsU)
    (θ W K f O Q time oldTimed j hj e s he hs heU hsU)
    (pieceEquations W K f O Q time oldTimed j hj e s he hs heU hsU)

/-- The graph presentation weakly covers the higher-choice chain index. -/
theorem toChain_weak :
    WeakEquivalence (nerveMap
      (JTWhiskeredGraphEvaluation.toOriginal Q
        (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
        (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
        (target W K f O Q time oldTimed j hj e s he hs heU hsU)
        (π W K f O Q time oldTimed j hj e s he hs heU hsU))) :=
  JTWhiskeredGraphEvaluation.toOriginal_weak Q
    (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
    (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
    (target W K f O Q time oldTimed j hj e s he hs heU hsU)
    (π W K f O Q time oldTimed j hj e s he hs heU hsU)
    (JTChosenSeamGraphCover.projection_trivialFibration W (z W Q j)
      (support W K f O Q time oldTimed j hj) K
      (incl W K f O Q time oldTimed j hj) f e s he hs
      (supported_row W K f O Q time oldTimed j hj) heU hsU O time Q oldTimed)

/-- The same complete presentation weakly covers the original supplied
three-piece index, provided the ambient row diagram is fibrant. -/
theorem toOriginal_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap
      (JTWhiskeredGraphEvaluation.toOriginal Q
        (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
        (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
        (target W K f O Q time oldTimed j hj e s he hs heU hsU)
        (π W K f O Q time oldTimed j hj e s he hs heU hsU) ⋙
      base W K f O Q time oldTimed j hj e s he hs heU hsU)) := by
  have hi : ∀ a : I,
      Mono ((incl W K f O Q time oldTimed j hj).app a) := fun a ↦
    JTThreePieceMiddleSupportDiagram.std_u_mono
      W K f O Q time oldTimed j hj a
  have hw : ∀ a : I,
      WeakEquivalence ((incl W K f O Q time oldTimed j hj).app a) := fun a ↦
    JTThreePieceMiddleSupportDiagram.u_weak
      W K f O Q time oldTimed j hj a
  haveI : WeakEquivalence (nerveMap
      (JTWhiskeredGraphEvaluation.toOriginal Q
        (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
        (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
        (target W K f O Q time oldTimed j hj e s he hs heU hsU)
        (π W K f O Q time oldTimed j hj e s he hs heU hsU))) :=
    toChain_weak W K f O Q time oldTimed j hj e s he hs heU hsU
  haveI : WeakEquivalence (nerveMap
      (base W K f O Q time oldTimed j hj e s he hs heU hsU)) :=
    JTChosenSeamChainDiagram.toOriginal_weak W (z W Q j)
      (support W K f O Q time oldTimed j hj) K
      (incl W K f O Q time oldTimed j hj) f e s he hs
      (supported_row W K f O Q time oldTimed j hj) heU hsU hi hw hW
  change WeakEquivalence (nerveMap
    (JTWhiskeredGraphEvaluation.toOriginal Q
      (chosen W K f O Q time oldTimed j hj e s he hs heU hsU).triangle
      (chainTime W K f O Q time oldTimed j hj e s he hs heU hsU)
      (target W K f O Q time oldTimed j hj e s he hs heU hsU)
      (π W K f O Q time oldTimed j hj e s he hs heU hsU)) ≫
        nerveMap (base W K f O Q time oldTimed j hj e s he hs heU hsU))
  infer_instance

end
end DaggerModels.PartII.JTThreePieceMiddleSeamEvaluation
