import DaggerModelsPartII.JTThreePieceMiddleSupport
import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.JTInterleavedParameter

/-!
The supplied natural three-piece old family has an exactly transported
canonical middle vertex. We pull its full timed used-face support from
`JTExactlyMarkedSourceDiagram`, retaining the original degree and time.
The row calculation is `JTThreePieceMiddleSupport.middleVertex_row` and the
parameter transport is `JTActualSourceJointSupportTransport`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTThreePieceMiddleSupportDiagram

open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTParametrizedTargetFamilies (codes Family)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I] (W : Source)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (K : I ⥤ SimplexCategory)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (time : I ⥤ SimplexCategory)
variable (oldTimed : Family Q (JTChosenSeamOldComparison.oldFamily W K f O).labels time)
variable (j : Joint Q.code)
variable (hj : ∀ a : I, orderMap (oldTimed.collapse.app a).map
  (JTThreePieceMiddleSupport.middleVertex P R a) = j.val)

private theorem middlePoint_left (a : I) :
    pointAt (wedge (P.obj a) (wedge (single 0) (R.obj a)))
        (ULift.up (JTThreePieceMiddleSupport.middleVertex P R a)) =
      pointAt (P.obj a) (ULift.up (Fin.last (P.obj a).len)) ≫
        wedgeιLeft (P.obj a) (wedge (single 0) (R.obj a)) := by
  rw [pointAt_comp, wedgeιLeft_vertices]
  congr 1

/-- Every original native operator carries the middle vertex exactly. -/
theorem middleVertex_map {a b : I} (g : a ⟶ b) :
    orderMap ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).map g).map
      (JTThreePieceMiddleSupport.middleVertex P R a) =
        JTThreePieceMiddleSupport.middleVertex P R b := by
  have hp : pointAt ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).obj a)
      (ULift.up (JTThreePieceMiddleSupport.middleVertex P R a)) ≫
      ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).map g).map =
      pointAt ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).obj b)
        (ULift.up (JTThreePieceMiddleSupport.middleVertex P R b)) := by
    change pointAt (wedge (P.obj a) (wedge (single 0) (R.obj a)))
        (ULift.up (JTThreePieceMiddleSupport.middleVertex P R a)) ≫
          (wedgeMap (P.map g) (wedgeMap (𝟙 (single 0)) (R.map g))).map =
      pointAt (wedge (P.obj b) (wedge (single 0) (R.obj b)))
        (ULift.up (JTThreePieceMiddleSupport.middleVertex P R b))
    rw [middlePoint_left (P := P) (R := R) a,
      middlePoint_left (P := P) (R := R) b]
    rw [Category.assoc, wedgeMap_left, ← Category.assoc, pointAt_last_comp]
  rw [pointAt_comp] at hp
  have h := congrArg (fun t : (Δ[0] : SSet.{0}) ⟶
      ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).obj b).toSSet ↦
        ((codes ((JTChosenSeamOldComparison.oldFamily W K f O).labels)).obj b).verticesEquiv
          (SSet.yonedaEquiv t)) hp
  simp only [pointAt_vertex, Equiv.apply_symm_apply] at h
  exact congrArg ULift.down h

/-- The supplied canonical middle point defines a section of the exact
source-cut category over the unchanged original index. -/
def marked : I ⥤ JTExactlyMarkedSourceDiagram.Index oldTimed j where
  obj a := ⟨a, ⟨JTThreePieceMiddleSupport.middleVertex P R a, hj a⟩⟩
  map {a b} g := ⟨g, by
    apply Subtype.ext
    exact middleVertex_map W K f O g⟩
  map_id a := Subtype.ext rfl
  map_comp g h := Subtype.ext rfl

/-- Forgetting the mark recovers the literal original object and arrow. -/
theorem marked_base : marked W K f O Q time oldTimed j hj ⋙
    JTExactlyMarkedSourceDiagram.base oldTimed j = 𝟭 I := rfl

/-- The actual used timed faces, naturally in the original three-piece family. -/
abbrev support : I ⥤ SimplexCategory :=
  marked W K f O Q time oldTimed j hj ⋙ JTExactlyMarkedSourceDiagram.supports oldTimed j

/-- The used face includes in the unchanged old coefficient degree `K`. -/
def u : support W K f O Q time oldTimed j hj ⟶ K :=
  Functor.whiskerLeft (marked W K f O Q time oldTimed j hj)
    (JTExactlyMarkedSourceDiagram.incl oldTimed j)

/-- Every component is the original actual-source used inclusion. -/
theorem u_app (a : I) :
    (u W K f O Q time oldTimed j hj).app a =
      JTActualSourceJointSupport.usedInclusion oldTimed a j
        (JTThreePieceMiddleSupport.middleVertex P R a) (hj a) := rfl

/-- The transported old endpoint row is the supplied row `f` at every index. -/
theorem endpointRow_eq (a : I) :
    (JTExactlyMarkedSourceDiagram.endpointRows oldTimed j).app
      ((marked W K f O Q time oldTimed j hj).obj a) = f.app a :=
  JTThreePieceMiddleSupport.middleVertex_row W P R K f O a

/-- The supplied row is stationary on the entire naturally used face. -/
theorem supported_row (a : I) :
    std.map ((u W K f O Q time oldTimed j hj).app a) ≫ f.app a =
      term (std.obj ((support W K f O Q time oldTimed j hj).obj a)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient j) := by
  rw [← endpointRow_eq W K f O Q time oldTimed j hj a]
  exact JTExactlyMarkedSourceDiagram.supported_endpoint oldTimed j
    ((marked W K f O Q time oldTimed j hj).obj a)

/-- The chosen support inclusion is monic at every original object. -/
theorem u_mono (a : I) : Mono ((u W K f O Q time oldTimed j hj).app a) :=
  JTExactlyMarkedSourceDiagram.incl_mono oldTimed j
    ((marked W K f O Q time oldTimed j hj).obj a)

/-- The corresponding map of standard simplices is a monomorphism. -/
theorem std_u_mono (a : I) :
    Mono (std.map ((u W K f O Q time oldTimed j hj).app a)) := by
  letI := u_mono W K f O Q time oldTimed j hj a
  exact JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono _

/-- Every standard-simplex map of a used support is Kan weak. -/
theorem u_weak (a : I) :
    WeakEquivalence (std.map ((u W K f O Q time oldTimed j hj).app a)) :=
  JTInterleavedParameter.standardMap_weak _

/-- The original complete time parameter at the canonical middle point. -/
abbrev oldParameter (a : I) :
    (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶ J.obj (K.obj a) :=
  JTActualSourceJointSupport.timeParameter oldTimed a
    (JTThreePieceMiddleSupport.middleVertex P R a)

/-- The same full time parameter, confined to its natural used face. -/
abbrev supportedParameter (a : I) :
    (Δ[0] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶
      J.obj ((support W K f O Q time oldTimed j hj).obj a) :=
  JTJointTimedEndpointSupport.supportedTimedParameter oldTimed a j
    (JTActualSourceJointSupport.liftedOverlapVertex oldTimed a j
      (JTThreePieceMiddleSupport.middleVertex P R a) (hj a))

/-- The old full time parameter factors through the identical natural used face. -/
theorem supportedParameter_factor (a : I) :
    supportedParameter W K f O Q time oldTimed j hj a ≫
      J.map ((u W K f O Q time oldTimed j hj).app a) =
        oldParameter W K f O Q time oldTimed a :=
  JTThreePieceMiddleSupport.middleVertex_timeParameter_factor
    W P R K f O Q time oldTimed a j (hj a)

/-- Transport of the original complete time parameter along every old arrow. -/
theorem oldParameter_natural {a b : I} (g : a ⟶ b) :
    (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map g)) ≫
      oldParameter W K f O Q time oldTimed b =
    oldParameter W K f O Q time oldTimed a ≫ J.map (K.map g) :=
  JTActualSourceJointSupportTransport.timeParameter_map oldTimed g
    (JTThreePieceMiddleSupport.middleVertex P R a)
    (JTThreePieceMiddleSupport.middleVertex P R b)
    (middleVertex_map W K f O g)

/-- Transport of the supported parameter along every natural used-face arrow. -/
theorem supportedParameter_natural {a b : I} (g : a ⟶ b) :
    (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ J.map (time.map g)) ≫
      supportedParameter W K f O Q time oldTimed j hj b =
    supportedParameter W K f O Q time oldTimed j hj a ≫
      J.map ((support W K f O Q time oldTimed j hj).map g) :=
  JTActualSourceJointSupportTransport.supportedTimedParameter_map
    oldTimed j g (JTThreePieceMiddleSupport.middleVertex P R a)
      (JTThreePieceMiddleSupport.middleVertex P R b) (hj a) (hj b)
      (middleVertex_map W K f O g)

end
end DaggerModels.PartII.JTThreePieceMiddleSupportDiagram
