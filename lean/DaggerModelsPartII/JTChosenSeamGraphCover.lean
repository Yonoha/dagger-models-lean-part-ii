import DaggerModelsPartII.JTChosenSeamOldComparison
import DaggerModelsPartII.JTWhiskeredSeamTarget
import DaggerModelsPartII.JTWhiskeredGraphEvaluation
import DaggerModelsPartII.JTPrismChainGraphCover

/-! The full timed graph cover for a chosen triangle seam. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChosenSeamGraphCover

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (codes)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
variable (incl : U ⟶ K ⋙ std)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
  JTJointSubcomplexRelativeLift.boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
  JTJointSubcomplexRelativeLift.reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a =
  SSet.stdSimplex.isTerminalObj₀.from (U.obj a) ≫
    JTProjectiveOrderedFiberComparison.vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a =
  JTJointSubcomplexRelativeLift.identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a =
  JTJointSubcomplexRelativeLift.identityOnU W z)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)
variable (time : I ⥤ SimplexCategory)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (oldTimed : JTParametrizedTargetFamilies.Family Q
  (JTChosenSeamOldComparison.oldFamily W K f O).labels time)

private abbrev C := JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hfU heU hsU
private abbrev base := JTChosenSeamChainDiagram.toOriginal
  W z U K incl f e s he hs hfU heU hsU
private abbrev degree := JTChosenSeamChainDiagram.ordinals
  W z U K incl f e s he hs hfU heU hsU
private def oldDegree : C W z U K incl f e s he hs hfU heU hsU ⥤ SimplexCategory :=
  base W z U K incl f e s he hs hfU heU hsU ⋙ K
private def alpha : degree W z U K incl f e s he hs hfU heU hsU ⟶
    oldDegree W z U K incl f e s he hs hfU heU hsU :=
  JTChosenSeamChainDiagram.toOld W z U K incl f e s he hs hfU heU hsU
private abbrev chosen := JTChosenSeamChainDiagram.seamFamily
  W z U K incl f e s he hs hfU heU hsU O
private abbrev old := JTChosenSeamOldComparison.oldFamily W K f O

/-- The chosen collapsed native code maps to the original native code. -/
def collapsedNative :
    codes (JTWhiskeredSeamDiagram.collapsedFamily
      (chosen W z U K incl f e s he hs hfU heU hsU O)).labels ⟶
      base W z U K incl f e s he hs hfU heU hsU ⋙
        codes (old W K f O).labels :=
  JTWhiskeredSeamTarget.nativeOf
    (JTChosenSeamOldComparison.comparison W z U K incl f e s he hs hfU heU hsU O)

/-- The original fixed-target collapse on the chosen collapsed phase. -/
def collapsedTarget :
    codes (JTWhiskeredSeamDiagram.collapsedFamily
      (chosen W z U K incl f e s he hs hfU heU hsU O)).labels ⟶
      (Functor.const (C W z U K incl f e s he hs hfU heU hsU)).obj Q.code :=
  collapsedNative W z U K incl f e s he hs hfU heU hsU O ≫
    Functor.whiskerLeft (base W z U K incl f e s he hs hfU heU hsU)
      oldTimed.collapse

/-- The full triangle phase still collapses into the original fixed target. -/
def triangleTarget : codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels ⟶
    (Functor.const (C W z U K incl f e s he hs hfU heU hsU)).obj Q.code :=
  JTWhiskeredSeamTarget.triangleTarget
    (chosen W z U K incl f e s he hs hfU heU hsU O) Q
    (collapsedTarget W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)

/-- Collapse the entire triangle native code to the literal old native code. -/
def wholeNative : codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels ⟶
    base W z U K incl f e s he hs hfU heU hsU ⋙ codes (old W K f O).labels :=
  JTWhiskeredSeamTarget.triangleToCollapsed
    (chosen W z U K incl f e s he hs hfU heU hsU O) ≫
      collapsedNative W z U K incl f e s he hs hfU heU hsU O

/-- The original time is unchanged on every higher-choice chain. -/
abbrev newTime : C W z U K incl f e s he hs hfU heU hsU ⥤ SimplexCategory :=
  base W z U K incl f e s he hs hfU heU hsU ⋙ time

/-- Whole triangle native coordinate paired with the original time coordinate. -/
abbrev X : C W z U K incl f e s he hs hfU heU hsU ⥤ SSet.{0} :=
  JTWhiskeredGraphEvaluation.productDiagram Q
    (chosen W z U K incl f e s he hs hfU heU hsU O).triangle
    (newTime W z U K incl f e s he hs hfU heU hsU time)
    (triangleTarget W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)

/-- Parameter on the whole triangle and unchanged original time. -/
def coarseParameter : X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed ⟶
    oldDegree W z U K incl f e s he hs hfU heU hsU ⋙ J where
  app p := (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map
    ⊗ₘ 𝟙 (J.obj (time.obj ((base W z U K incl f e s he hs hfU heU hsU).obj p)))) ≫
      oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj p)
  naturality {p q} g := by
    have hn := (wholeNative W z U K incl f e s he hs hfU heU hsU O).naturality g
    have hp := oldTimed.parameter_map
      ((base W z U K incl f e s he hs hfU heU hsU).map g)
    have hn' := congrArg
      (fun h : (codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels).obj p ⟶
        (base W z U K incl f e s he hs hfU heU hsU ⋙ codes (old W K f O).labels).obj q ↦
          h.map) hn
    change ((codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels).map g).map ≫
        ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app q).map =
      ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ≫
        ((codes (old W K f O).labels).map
          ((base W z U K incl f e s he hs hfU heU hsU).map g)).map at hn'
    change (((codes (old W K f O).labels).map
        ((base W z U K incl f e s he hs hfU heU hsU).map g)).map ⊗ₘ
        J.map (time.map ((base W z U K incl f e s he hs hfU heU hsU).map g))) ≫
      oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj q) =
      oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj p) ≫
        J.map (K.map ((base W z U K incl f e s he hs hfU heU hsU).map g)) at hp
    change (((codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels).map g).map
        ⊗ₘ J.map (time.map ((base W z U K incl f e s he hs hfU heU hsU).map g))) ≫
      (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app q).map ⊗ₘ 𝟙 _)
        ≫ oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj q) =
      (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ⊗ₘ 𝟙 _)
        ≫ oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj p) ≫
          J.map (K.map ((base W z U K incl f e s he hs hfU heU hsU).map g))
    calc
      _ = ((((codes (chosen W z U K incl f e s he hs hfU heU hsU O).triangle.labels).map g).map ≫
          ((wholeNative W z U K incl f e s he hs hfU heU hsU O).app q).map) ⊗ₘ
            J.map (time.map ((base W z U K incl f e s he hs hfU heU hsU).map g))) ≫
          oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj q) := by
            rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (((wholeNative W z U K incl f e s he hs hfU heU hsU O).app p).map ⊗ₘ 𝟙 _) ≫
          (((codes (old W K f O).labels).map
            ((base W z U K incl f e s he hs hfU heU hsU).map g)).map ⊗ₘ
              J.map (time.map ((base W z U K incl f e s he hs hfU heU hsU).map g))) ≫
            oldTimed.parameter ((base W z U K incl f e s he hs hfU heU hsU).obj q) := by
              rw [hn', ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      _ = _ := by rw [hp]

/-- All coefficient lifts from the original full timed triangle graph. -/
abbrev graph : C W z U K incl f e s he hs hfU heU hsU ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover
    (X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (alpha W z U K incl f e s he hs hfU heU hsU)

/-- Projection to every point of the whole native and original-time product. -/
abbrev projection : graph W z U K incl f e s he hs hfU heU hsU O time Q oldTimed ⟶
    X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed :=
  JTPrismChainGraphCover.projection
    (X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (alpha W z U K incl f e s he hs hfU heU hsU)

/-- The lifted parameter on the actual chosen coefficient degree. -/
abbrev parameter : graph W z U K incl f e s he hs hfU heU hsU O time Q oldTimed ⟶
    degree W z U K incl f e s he hs hfU heU hsU ⋙ J :=
  JTPrismChainGraphCover.parameter
    (X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (alpha W z U K incl f e s he hs hfU heU hsU)

/-- The lifted parameter retains exactly the old full timed parameter. -/
theorem parameter_projection :
    parameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed ≫
      Functor.whiskerRight (alpha W z U K incl f e s he hs hfU heU hsU) J =
    projection W z U K incl f e s he hs hfU heU hsU O time Q oldTimed ≫
      coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed :=
  JTPrismChainGraphCover.parameter_projection
    (X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (alpha W z U K incl f e s he hs hfU heU hsU)

/-- The graph projection is objectwise a trivial fibration. -/
theorem projection_trivialFibration
    (p : C W z U K incl f e s he hs hfU heU hsU) :
    trivialFibrations SSet.{0}
      ((projection W z U K incl f e s he hs hfU heU hsU O time Q oldTimed).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration
    (X W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (coarseParameter W z U K incl f e s he hs hfU heU hsU O time Q oldTimed)
    (alpha W z U K incl f e s he hs hfU heU hsU)
    (fun q ↦ by
      change Function.Surjective
        ((JTChosenSeamChainDiagram.toOld W z U K incl f e s he hs hfU heU hsU).app q).toOrderHom
      exact TimePrismChainDiagram.coeffProjection_surjective
        (JTChosenSeamChainDiagram.coefficient W z U K incl f e s he hs hfU heU hsU)
        (JTChosenSeamChainDiagram.choiceTime W z U K incl f e s he hs hfU heU hsU) q) p

end
end DaggerModels.PartII.JTChosenSeamGraphCover
