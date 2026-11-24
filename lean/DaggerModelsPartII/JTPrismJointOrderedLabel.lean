import DaggerModelsPartII.JTPrismJointCoefficient
import DaggerModelsPartII.JTMixedGraphHorizontalLabel
import DaggerModelsPartII.JTConstantOrderedLabel

/-! The supported coefficient equality in the actual native label mapping space. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
namespace DaggerModels.PartII.JTParametrizedBeadGraph

open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints OrderedSimplexEndpointFiber

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTPrismJointNormalization (jointRaw)
open JTNativeRowLabel (labelFromRow)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Rows (W : Source) := JTRealizationDiagonal.ordinaryCurry.obj (Input W)
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := discreteFree.{0}
private abbrev terminal := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ) (j : Joint Q.code)
variable (r : (NecklaceCode.single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

private abbrev native := r ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j
private abbrev l := fullBeadSupport F a d (native F a d j r)
private abbrev incl := fullBeadSupportInclusion F a d (native F a d j r)
private abbrev z : Vertex W := jointCoefficient (Q := Q) j

set_option maxHeartbeats 650000 in
private theorem supported_row_coefficient :
    std.map (incl F a d j r) ≫ coefficient (a := a) d (native F a d j r) =
      terminal (std.obj (l F a d j r)) ≫ vertexPoint W (z (Q := Q) j) ≫
        (Rows W).map (SimplexCategory.isTerminalZero.from ⦋d⦌).op := by
  let m := l F a d j r
  let p := SimplexCategory.isTerminalZero.from m
  let o := SimplexCategory.isTerminalZero.from ⦋d⦌
  let v := z (Q := Q) j
  have hterm : terminal (std.obj m) = std.map p :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hterm]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_comp]
  have hx : SSet.yonedaEquiv (vertexPoint W v) = v := Equiv.apply_symm_apply _ _
  rw [hx]
  let vert : (⦋d⦌, m) ⟶ (⦋d⦌, ⦋0⦌) := (𝟙 ⦋d⦌, p)
  let horiz : (⦋d⦌, ⦋0⦌) ⟶ (⦋0⦌, ⦋0⦌) := (o, 𝟙 ⦋0⦌)
  have hcomp : vert ≫ horiz = ((o, p) : (⦋d⦌, m) ⟶ (⦋0⦌, ⦋0⦌)) := by
    ext <;> simp [vert, horiz]
  have h :=
    fullBeadCoefficient_at_joint F a d j r
  change _ = (Input W).map vert.op ((Input W).map horiz.op v)
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, hcomp]
  exact h

set_option maxHeartbeats 800000 in
/-- The literal restriction of the old bead label to the full parameter support
agrees in its mapping space with the pullback from the same original point. -/
theorem restrictedBeadLabel_at_joint :
    std.map (incl F a d j r) ≫ SSet.yonedaEquiv.symm (beadLabel (a := a) d (native F a d j r)) =
      terminal (std.obj (l F a d j r)) ≫ zeroPoint W (z (Q := Q) j) ≫
        diagramMappingPrecomp (free.map (terminal (NecklaceCode.single d).toSSet)) W := by
  let o := SimplexCategory.isTerminalZero.from ⦋d⦌
  let v := z (Q := Q) j
  let h₀ : o.toOrderHom 0 = 0 := @Subsingleton.elim (Fin 1) inferInstance _ _
  let h₁ : o.toOrderHom (Fin.last d) = Fin.last 0 :=
    @Subsingleton.elim (Fin 1) inferInstance _ _
  let collapse := JTMixedGraphHorizontalTraversal.singleOperator o h₀ h₁
  rw [← coefficient_label (a := a) d (native F a d j r), Equiv.symm_apply_apply,
    ← Category.assoc, supported_row_coefficient F a d j r, Category.assoc,
    Category.assoc,
    ← JTMixedGraphHorizontalLabel.labelFromRow_natural W o h₀ h₁]
  change terminal (std.obj (l F a d j r)) ≫ vertexPoint W v ≫
    labelFromRow W 0 ≫ diagramMappingPrecomp (free.map collapse.map) W = _
  rw [← freeSimplexRowIso_zeroPoint W v]
  unfold labelFromRow
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← diagramMappingPrecomp_comp, ← free.map_comp]
  have ht : collapse.map ≫ (NecklaceCode.singleIso 0).hom =
      terminal (NecklaceCode.single d).toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht]

/-- The original supported coefficient now determines an actual ordered label
with the literal joint vertex at both endpoints. -/
theorem supportedOverlapLabel_coefficient :
    JTOrderedLabelBinaryGlue.coefficient W (z (Q := Q) j) (z (Q := Q) j)
        (NecklaceCode.single d) (l F a d j r)
        (JTConstantOrderedLabel.constantLabel W (z (Q := Q) j)
          (NecklaceCode.single d) (l F a d j r)) =
      std.map (incl F a d j r) ≫ SSet.yonedaEquiv.symm (beadLabel (a := a) d (native F a d j r)) :=
  (JTConstantOrderedLabel.coefficient_constantLabel W (z (Q := Q) j)
    (NecklaceCode.single d) (l F a d j r)).trans (restrictedBeadLabel_at_joint F a d j r).symm

/-- The overlap bead, with the actual supported coefficient and both boundary
vertices equal to the target joint. -/
abbrev supportedOverlapIndex : DecoratedNecklaceHomDiagram.Index W (z (Q := Q) j) (z (Q := Q) j) :=
  JTConstantOrderedLabel.constantIndex W (z (Q := Q) j) (NecklaceCode.single d) (l F a d j r)

/-- The supported label has an actual decorated arrow to the one common
point label, using the native collapse and the terminal coefficient operator. -/
def supportedOverlapCollapse : supportedOverlapIndex F a d j r ⟶
    JTConstantOrderedLabel.constantIndex W (z (Q := Q) j) (NecklaceCode.single 0) ⦋0⦌ :=
  JTConstantOrderedLabel.constantIndexHom W (z (Q := Q) j)
    (JTMixedGraphHorizontalTraversal.singleOperator
      (SimplexCategory.isTerminalZero.from ⦋d⦌)
      (@Subsingleton.elim (Fin 1) inferInstance _ _)
      (@Subsingleton.elim (Fin 1) inferInstance _ _))
    (SimplexCategory.isTerminalZero.from (l F a d j r))

section Operators

variable {a d r} {b : A} {e : ℕ}
variable {r' : (NecklaceCode.single e).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app b) j j le_rfl).toSSet}
variable (f : a ⟶ b) (u : ⦋d⦌ ⟶ ⦋e⦌)
variable (h₀ : u.toOrderHom 0 = 0) (h₁ : u.toOrderHom (Fin.last d) = Fin.last e)
variable (h : (NecklaceCode.singleIso d).inv ≫ native F a d j r ≫ ((codes L).map f).map =
  std.map u ≫ (NecklaceCode.singleIso e).inv ≫ native F b e j r')

/-- A mixed operator preserving the two endpoints gives a decorated arrow
with the original native operator and the full supported coefficient operator. -/
def supportedOverlapMap : supportedOverlapIndex F a d j r ⟶ supportedOverlapIndex F b e j r' :=
  JTConstantOrderedLabel.constantIndexHom W (z (Q := Q) j)
    (JTMixedGraphHorizontalTraversal.singleOperator u h₀ h₁)
    (fullBeadSupportMap (i := native F a d j r) (i' := native F b e j r') F f u
      (by simpa only [Category.assoc] using h))

end Operators

end
end DaggerModels.PartII.JTParametrizedBeadGraph
