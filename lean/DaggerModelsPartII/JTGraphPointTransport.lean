import DaggerModelsPartII.JTGraphPointLabel

/-!
# Degree-zero transport over the original raw target at a point label
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphPointTransport

open JTProjectiveOrderedFiberComparison OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open JTGraphLiftTransport

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev L := orderedNecklaceLabels W (boundaryPoint W x y)
private abbrev F := DecoratedCylinderNecklacePresentation.toTarget W x y

private def zeroBase (P : Pres (W := W) (x := x) (y := y))
    (z₀ : ((L (W := W) (x := x) (y := y)).obj (op (code P))).obj (op ⦋0⦌)) :
    OrderedLabelElements.Index W (boundaryPoint W x y) :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code P) ⦋0⦌ z₀

private def zeroBaseArrow (P : Pres (W := W) (x := x) (y := y))
    (z₀ : ((L (W := W) (x := x) (y := y)).obj (op (code P))).obj (op ⦋0⦌))
    (hz : ((L (W := W) (x := x) (y := y)).obj (op (code P))).map
        (SimplexCategory.isTerminalZero.from (degree P)).op z₀ =
      OrderedLabelElements.label W (boundaryPoint W x y) P.base) :
    P.base ⟶ zeroBase P z₀ := by
  let b := boundaryPoint W x y
  let A := OrderedLabelElements.labelPresheaf W b
  let j := SimplexCategory.isTerminalZero.from (degree P)
  let g : (code P, degree P) ⟶ (code P, ⦋0⦌) := (𝟙 (code P), j)
  refine (CategoryOfElements.homMk (A.elementsMk (op (code P, ⦋0⦌)) z₀)
    P.base.unop g.op ?_).op
  let L' := orderedNecklaceLabels W b
  change (L'.obj (op (code P))).map j.op
    ((L'.map (𝟙 (op (code P)))).app (op ⦋0⦌) z₀) = _
  rw [L'.map_id]
  exact hz

/-- A degenerate label admits transport to degree zero in the original
fixed-target comma, with the entire internal native necklace retained. -/
theorem exists_zero_transport (U : CostructuredArrow F Q)
    (h : NecklaceCode.first.{0} (code U.left) = NecklaceCode.last.{0} (code U.left)) :
    ∃ (V : CostructuredArrow F Q) (a : U ⟶ V),
      degree V.left = ⦋0⦌ ∧ code V.left = code U.left ∧
      V.left.fiber.left = U.left.fiber.left ∧
      ∀ (S : NecklaceCode) (D E : GraphLift U.left S),
        (D.transport a.left).parameter = (E.transport a.left).parameter := by
  let P := U.left
  let b := boundaryPoint W x y
  obtain ⟨z₀, hz⟩ := JTGraphPointLabel.descends_zero W (code P) h b (degree P)
    (OrderedLabelElements.label W b P.base)
  let j := zeroBaseArrow P z₀ hz
  let P' := Grothendieck.transport P j
  let f := Grothendieck.toTransport P j
  have hmap : ((F (W := W) (x := x) (y := y)).obj P').map =
      ((F (W := W) (x := x) (y := y)).obj P).map := by
    have hf := ((F (W := W) (x := x) (y := y)).map f).w
    change (𝟙 U.left.fiber.left.toSSet) ≫ _ = _ at hf
    simpa only [Category.id_comp] using hf
  let v : (F (W := W) (x := x) (y := y)).obj P' ⟶ Q :=
    ⟨U.hom.hom, by rw [hmap]; exact U.hom.w⟩
  let V := CostructuredArrow.mk v
  let a : U ⟶ V := CostructuredArrow.homMk f (by
    apply NecklacesOver.Hom.ext
    change 𝟙 U.left.fiber.left ≫ U.hom.hom = U.hom.hom
    exact Category.id_comp _)
  refine ⟨V, a, rfl, rfl, rfl, ?_⟩
  intro S D E
  exact JTParameterZero.parameterZeroIsTerminal.hom_ext _ _

end

end DaggerModels.PartII.JTGraphPointTransport
