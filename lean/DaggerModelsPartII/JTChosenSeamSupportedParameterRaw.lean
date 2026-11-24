import DaggerModelsPartII.JTChosenSeamGraphRaw
import DaggerModelsPartII.JTOrdinalFaceParameterPullback

/-! Exact supported parameters on the full inverse-image face of a chosen seam. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChosenSeamSupportedParameterRaw

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

/-- If the old projection of a lifted parameter lies in an original supported
face, the actual chosen triangle has the joint raw value on that parameter.
The parameter itself is retained, including every lifted coefficient value. -/
theorem graph_raw_of_old_factor
    (p : Chain W z U K incl f e s he hs hfU heU hsU)
    (d : SimplexCategory)
    (u : d ⟶ K.obj ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p))
    (hu : Function.Injective u.toOrderHom)
    (a : std.obj d ⟶ U.obj ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p))
    (ha : std.map u = a ≫ incl.app
      ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p))
    {X : SSet.{0}} (h : X ⟶ (single 2).toSSet)
    (q : X ⟶ J.obj ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p))
    (g : X ⟶ J.obj d)
    (hq : q ≫ J.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p) =
      g ≫ J.map u) :
    lift h q ≫
      JTNecklaceLabelRealization.realizedLabel (single 2).toSSet W
        ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p)
        (SSet.yonedaEquiv ((triangle W z U K incl f e s he hs hfU heU hsU).app p ≫
          JTNativeRowLabel.labelFromRow W 2)) =
      h ≫ term (single 2).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  let α := (toOld W z U K incl f e s he hs hfU heU hsU).app p
  have hα : Function.Surjective α.toOrderHom :=
    TimePrismChainDiagram.coeffProjection_surjective
      (JTChosenSeamChainDiagram.coefficient W z U K incl f e s he hs hfU heU hsU)
      (JTChosenSeamChainDiagram.choiceTime W z U K incl f e s he hs hfU heU hsU) p
  let v := JTOrdinalFaceInverseImage.incl u α hα
  let b := JTOrdinalFaceInverseImage.toFace u α hα hu
  have hv : std.map v ≫ std.map α = (std.map b ≫ a) ≫ incl.app
      ((oldBase W z U K incl f e s he hs hfU heU hsU).obj p) := by
    rw [← std.map_comp, ← JTOrdinalFaceInverseImage.toFace_fac u α hα hu,
      std.map_comp, ha, Category.assoc]
  have hr := JTChosenSeamGraphRaw.graph_raw
    W z U K incl f e s he hs hfU heU hsU p
    (JTOrdinalFaceInverseImage.ordinal u α) v (std.map b ≫ a) hv h
    (JTOrdinalFaceParameterPullback.factor u α hα q g hq)
  rw [JTOrdinalFaceParameterPullback.factor_incl] at hr
  exact hr

end

end DaggerModels.PartII.JTChosenSeamSupportedParameterRaw
