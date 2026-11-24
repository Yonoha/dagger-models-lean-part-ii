import DaggerModelsPartII.JTChosenSeamChainDiagram
import DaggerModelsPartII.JTSeamTriangleGraphRaw

/-! The supported middle graph of every actual higher chosen seam has the original joint value. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChosenSeamGraphRaw

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTJointSubcomplexRelativeLift (boundaryPair reverseBoundaryPair identityOnU)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
variable (incl : U ⟶ K ⋙ std)
variable (f : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : K ⋙ std ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ endpointArrow W = boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ endpointArrow W = reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a = term (U.obj a) ≫ vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a = identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a = identityOnU W z)

private abbrev Chain := JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hfU heU hsU
private abbrev ordinals :=
  JTChosenSeamChainDiagram.ordinals W z U K incl f e s he hs hfU heU hsU
private abbrev oldBase :=
  JTChosenSeamChainDiagram.toOriginal W z U K incl f e s he hs hfU heU hsU
private abbrev toOld :=
  JTChosenSeamChainDiagram.toOld W z U K incl f e s he hs hfU heU hsU
private abbrev triangle :=
  JTChosenSeamChainDiagram.triangle W z U K incl f e s he hs hfU heU hsU

/-- Every actual higher filler, on every full coefficient-choice chain, gives
the literal joint raw value on its supported graph. Stationarity is derived
from the old support factor, not supplied as a new triangle hypothesis. -/
theorem graph_raw (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (d : SimplexCategory)
    (u : d ⟶ (ordinals W z U K incl f e s he hs hfU heU hsU).obj p)
    (a : std.obj d ⟶ U.obj ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p))
    (ha : std.map u ≫ std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p) =
      a ≫ incl.app ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p))
    {X : SSet.{0}} (h : X ⟶ (single 2).toSSet) (q : X ⟶ J.obj d) :
    lift h (q ≫ J.map u) ≫
      JTNecklaceLabelRealization.realizedLabel (single 2).toSSet W
        ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p)
        (SSet.yonedaEquiv ((triangle W z U K incl f e s he hs hfU heU hsU).app p ≫
          JTNativeRowLabel.labelFromRow W 2)) =
      h ≫ term (single 2).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) :=
  JTSeamTriangleGraphRaw.graph_raw W z u
    ((triangle W z U K incl f e s he hs hfU heU hsU).app p)
    (JTChosenSeamChainDiagram.triangle_onSupport
      W z U K incl f e s he hs hfU heU hsU p d u a ha) h q

end

end DaggerModels.PartII.JTChosenSeamGraphRaw
