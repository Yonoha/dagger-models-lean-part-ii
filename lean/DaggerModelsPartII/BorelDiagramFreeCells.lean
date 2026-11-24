import DaggerModelsPartII.BorelDiagonalFreeAction
import DaggerModelsPartII.DiagramMappingSpace
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Strict orbits of diagonal free cells in simplicial-set diagrams

An action on a simplicial-set diagram can be evaluated objectwise as a diagram of
actions. Colimits of actions and colimits of diagrams are computed objectwise,
which transports the simplicial free-cell cancellation to strict orbits in
`Action (C ⥤ SSet) C2`. The resulting isomorphism is natural in both the action
and the simplicial cell. In particular its cell naturality applies to boundary
inclusions and supplies the attaching-map comparison for a later filtration.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
open DaggerOriginalDaggerRealizationC2Action
open DaggerOriginalSimplicialActionFreeGenerators
universe u

namespace DaggerModels.PartII.BorelDiagramFreeCells

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- Evaluate a group action on a diagram at every diagram object. -/
def actionDiagram : Action (C ⥤ SSet.{u}) C2.{u} ⥤ C ⥤ Action SSet.{u} C2.{u} :=
  (Action.functorCategoryEquivalence (C ⥤ SSet.{u}) C2.{u}).functor ⋙
    flipFunctor _ _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj
        (Action.functorCategoryEquivalence SSet.{u} C2.{u}).inverse

/-- The constant diagram carrying the native free action on a simplicial cell. -/
def diagramFreeCellAction (K : SSet.{u}) : Action (C ⥤ SSet.{u}) C2.{u} :=
  ((Functor.const C).mapAction C2.{u}).obj (free.obj K)

/-- Functoriality of a constant free cell in its simplicial-set variable. -/
def diagramFreeCellMap {K L : SSet.{u}} (f : K ⟶ L) :
    diagramFreeCellAction C K ⟶ diagramFreeCellAction C L :=
  ((Functor.const C).mapAction C2.{u}).map (free.map f)

/-- Objectwise diagonal free-cell cancellation after strict orbits. -/
def pointwiseOrbitFreeCellIso (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : SSet.{u}) :
    ((actionDiagram C).obj (V ⊗ diagramFreeCellAction C K)) ⋙
      ActionStrictOrbits.orbit SSet.{u} C2.{u} ≅
      (diagramTensor V.V).obj K :=
  NatIso.ofComponents
    (fun c => BorelDiagonalFreeAction.orbitDiagonalFreeIso
      (((actionDiagram C).obj V).obj c) K)
    (by
      intro c d f
      exact BorelDiagonalFreeAction.orbitDiagonalFreeIso_natural_action
        (((actionDiagram C).obj V).obj c) K (((actionDiagram C).obj V).map f))

/-- Colimits of actions in a diagram category are computed objectwise. -/
def orbitDiagramIso (V : Action (C ⥤ SSet.{u}) C2.{u}) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).obj V ≅
      ((actionDiagram C).obj V) ⋙ ActionStrictOrbits.orbit SSet.{u} C2.{u} := by
  let J := (Action.functorCategoryEquivalence (C ⥤ SSet.{u}) C2.{u}).functor.obj V
  let E := Action.functorCategoryEquivalence SSet.{u} C2.{u}
  exact (colimitIsoFlipCompColim J).trans
    (Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft J.flip E.counitIso.symm) colim)

/-- Strict orbits in a diagram category agree naturally with objectwise orbits. -/
def orbitDiagramNatIso :
    ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u} ≅
      actionDiagram C ⋙
        (Functor.whiskeringRight _ _ _).obj
          (ActionStrictOrbits.orbit SSet.{u} C2.{u}) :=
  by
    let F := (Action.functorCategoryEquivalence (C ⥤ SSet.{u}) C2.{u}).functor
    let E := Action.functorCategoryEquivalence SSet.{u} C2.{u}
    let δ : colim ≅ E.inverse ⋙ E.functor ⋙ colim :=
      (colim.leftUnitor).symm ≪≫
        Functor.isoWhiskerRight E.counitIso.symm colim
    exact (Functor.isoWhiskerLeft F colimIsoFlipCompWhiskerColim).trans
      (Functor.isoWhiskerLeft (F ⋙ flipFunctor _ _ _)
        ((Functor.whiskeringRight _ _ _).mapIso δ))

/-- Strict orbits cancel a diagonal constant free cell in a diagram category. -/
def orbitFreeCellIso (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : SSet.{u}) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).obj
      (V ⊗ diagramFreeCellAction C K) ≅
      (diagramTensor V.V).obj K :=
  ((orbitDiagramNatIso C).app (V ⊗ diagramFreeCellAction C K)).trans
    (pointwiseOrbitFreeCellIso C V K)

theorem pointwiseOrbitFreeCellIso_natural_cell
    (V : Action (C ⥤ SSet.{u}) C2.{u}) {K L : SSet.{u}}
    (f : K ⟶ L) :
    Functor.whiskerRight ((actionDiagram C).map
      (𝟙 V ⊗ₘ diagramFreeCellMap C f))
        (ActionStrictOrbits.orbit SSet.{u} C2.{u}) ≫
      (pointwiseOrbitFreeCellIso C V L).hom =
    (pointwiseOrbitFreeCellIso C V K).hom ≫ (diagramTensor V.V).map f := by
  apply NatTrans.ext
  funext c
  exact BorelDiagonalFreeAction.orbitDiagonalFreeIso_natural_cell
    (((actionDiagram C).obj V).obj c) K f

/-- Strict-orbit free-cell cancellation is natural in every simplicial cell map. -/
theorem orbitFreeCellIso_natural_cell
    (V : Action (C ⥤ SSet.{u}) C2.{u}) {K L : SSet.{u}}
    (f : K ⟶ L) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
        (𝟙 V ⊗ₘ diagramFreeCellMap C f) ≫
      (orbitFreeCellIso C V L).hom =
    (orbitFreeCellIso C V K).hom ≫ (diagramTensor V.V).map f := by
  dsimp [orbitFreeCellIso]
  rw [← Category.assoc,
    (orbitDiagramNatIso C).hom.naturality
      (𝟙 V ⊗ₘ diagramFreeCellMap C f)]
  rw [Category.assoc]
  exact congrArg ((orbitDiagramNatIso C).hom.app (V ⊗ diagramFreeCellAction C K) ≫ ·)
    (pointwiseOrbitFreeCellIso_natural_cell C V f)

theorem pointwiseOrbitFreeCellIso_natural_action
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (K : SSet.{u}) :
    Functor.whiskerRight ((actionDiagram C).map
      (φ ⊗ₘ 𝟙 (diagramFreeCellAction C K)))
        (ActionStrictOrbits.orbit SSet.{u} C2.{u}) ≫
      (pointwiseOrbitFreeCellIso C W K).hom =
    (pointwiseOrbitFreeCellIso C V K).hom ≫
      Functor.whiskerRight φ.hom (tensorRight K) := by
  apply NatTrans.ext
  funext c
  exact BorelDiagonalFreeAction.orbitDiagonalFreeIso_natural_action
    (((actionDiagram C).obj V).obj c) K (((actionDiagram C).map φ).app c)

/-- Strict-orbit free-cell cancellation is natural in equivariant diagram maps. -/
theorem orbitFreeCellIso_natural_action
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (K : SSet.{u}) :
    (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}).map
        (φ ⊗ₘ 𝟙 (diagramFreeCellAction C K)) ≫
      (orbitFreeCellIso C W K).hom =
    (orbitFreeCellIso C V K).hom ≫
      Functor.whiskerRight φ.hom (tensorRight K) := by
  dsimp [orbitFreeCellIso]
  rw [← Category.assoc,
    (orbitDiagramNatIso C).hom.naturality
      (φ ⊗ₘ 𝟙 (diagramFreeCellAction C K))]
  rw [Category.assoc]
  exact congrArg ((orbitDiagramNatIso C).hom.app (V ⊗ diagramFreeCellAction C K) ≫ ·)
    (pointwiseOrbitFreeCellIso_natural_action C φ K)

end

end DaggerModels.PartII.BorelDiagramFreeCells
