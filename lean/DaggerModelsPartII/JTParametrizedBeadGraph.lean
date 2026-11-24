import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTNativeRowLabel
import DaggerModelsPartII.JTRowGraphFiber
import DaggerModelsPartII.JTMixedGraphRawRefinement

/-! An arbitrary bead of a parametrized target family gives an actual row graph. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTProjectiveOrderedFiberComparison (row)
open DaggerModels.PartII.OrderedNecklaceVertexPoints (boundaryPoint)
open DaggerModels.PartII.JTRealizedLabelEndpoints (orderedLabel)
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.OrderedSimplexEndpointFiber
open DaggerModels.PartII.JTNativeRowLabel
open DaggerModels.PartII.JTMixedGraphEndpointLifts (rawGraph)
open DaggerModels.PartII.JTMixedGraphRawRefinement (nativeRawGraph)

namespace DaggerModels.PartII.JTParametrizedBeadGraph

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev K (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time)
variable (a : A) (d : ℕ)
variable (i : (NecklaceCode.single d).toSSet ⟶
  ((JTParametrizedTargetFamilies.codes L).obj a).toSSet)
variable (v : K ⦋0⦌ ⟶ J.obj (time.obj a))

private abbrev degree :=
  ((OrderedLabelElements.projection W (boundaryPoint W x y)).obj (L.obj a)).2

private abbrev label := OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a)

/-- The restricted coefficient in the diagram mapping space of the native bead. -/
def beadLabel :
    (diagramMappingSpace (discreteFree.obj (NecklaceCode.single d).toSSet) W).obj
      (op (degree (W := W) (x := x) (y := y) (L := L) a)) :=
  Functor.whiskerRight (discreteFree.map i)
    (tensorRight (K (degree (W := W) (x := x) (y := y) (L := L) a))) ≫
    orderedLabel W x y ((JTParametrizedTargetFamilies.codes L).obj a)
      (degree (W := W) (x := x) (y := y) (L := L) a)
      (label (W := W) (x := x) (y := y) (L := L) a)

private def rowFromLabel :
    diagramMappingSpace (discreteFree.obj (NecklaceCode.single d).toSSet) W ⟶
      row W ⦋d⦌ :=
  diagramMappingPrecomp (discreteFree.map (NecklaceCode.singleIso d).inv) W ≫
    (freeSimplexRowIso W d).hom

private theorem rowFromLabel_labelFromRow :
    rowFromLabel (W := W) d ≫ labelFromRow W d = 𝟙 _ := by
  unfold rowFromLabel labelFromRow
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← diagramMappingPrecomp_comp,
    ← discreteFree.map_comp, Iso.hom_inv_id, discreteFree.map_id,
    diagramMappingPrecomp_id]

/-- The actual row coefficient of this restricted bead. -/
def coefficient : K (degree (W := W) (x := x) (y := y) (L := L) a) ⟶ row W ⦋d⦌ :=
  SSet.yonedaEquiv.symm (beadLabel (a := a) d i) ≫ rowFromLabel (W := W) d

/-- Convert the restricted row coefficient back to the literal native bead label. -/
theorem coefficient_label :
    SSet.yonedaEquiv (coefficient (a := a) d i ≫ labelFromRow W d) =
      beadLabel (a := a) d i := by
  rw [coefficient, Category.assoc, rowFromLabel_labelFromRow, Category.comp_id]
  exact Equiv.apply_symm_apply _ _

/-- The graph parameter on the native single bead, using the chosen time vertex. -/
def beadParameter : (NecklaceCode.single d).toSSet ⟶
    J.obj (degree (W := W) (x := x) (y := y) (L := L) a) :=
  lift i (term (NecklaceCode.single d).toSSet ≫ v) ≫ F.parameter a

/-- The exact native raw target selected by the bead inclusion. -/
def beadRaw : (NecklaceCode.single d).toSSet ⟶ R W :=
  i ≫ (F.collapse.app a).map ≫ Q.map

private theorem nativeRawGraph_realized (k : SimplexCategory)
    (f : K k ⟶ row W ⦋d⦌) (s : (NecklaceCode.single d).toSSet ⟶ J.obj k) :
    nativeRawGraph W d k f ((NecklaceCode.singleIso d).inv ≫ s) =
      lift (𝟙 (NecklaceCode.single d).toSSet) s ≫
        JTNecklaceLabelRealization.realizedLabel (NecklaceCode.single d).toSSet W k
          (SSet.yonedaEquiv (f ≫ labelFromRow W d)) := by
  unfold nativeRawGraph rawGraph
  rw [realized_nativeLabel, ← Category.assoc]
  have h :
      lift (𝟙 (NecklaceCode.single d).toSSet) s ≫
        ((NecklaceCode.singleIso d).hom ⊗ₘ 𝟙 (J.obj k)) =
      (NecklaceCode.singleIso d).hom ≫
        lift (𝟙 (K ⦋d⦌)) ((NecklaceCode.singleIso d).inv ≫ s) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc,
        Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id,
        Iso.hom_inv_id_assoc]
  rw [← h, Category.assoc]

/-- The full simplicial time parameter on the selected native bead. -/
def beadParameterWithTime
    (s : (NecklaceCode.single d).toSSet ⟶ J.obj (time.obj a)) :
    (NecklaceCode.single d).toSSet ⟶
      J.obj (degree (W := W) (x := x) (y := y) (L := L) a) :=
  lift i s ≫ F.parameter a

@[simp] theorem beadParameterWithTime_vertex :
    beadParameterWithTime F a d i (term (NecklaceCode.single d).toSSet ≫ v) =
      beadParameter F a d i v := rfl

/-- Restrict the raw family equation along an arbitrary simplicial time map. -/
theorem nativeRawGraphWithTime_eq
    (s : (NecklaceCode.single d).toSSet ⟶ J.obj (time.obj a)) :
    nativeRawGraph W d (degree (W := W) (x := x) (y := y) (L := L) a)
      (coefficient (a := a) d i)
      ((NecklaceCode.singleIso d).inv ≫ beadParameterWithTime F a d i s) =
    beadRaw F a d i := by
  let T := (JTParametrizedTargetFamilies.codes L).obj a
  let k := degree (W := W) (x := x) (y := y) (L := L) a
  let η := orderedLabel W x y T k (label (W := W) (x := x) (y := y) (L := L) a)
  let ι : (NecklaceCode.single d).toSSet ⟶ T.toSSet ⊗ J.obj (time.obj a) :=
    lift i s
  let p := beadParameterWithTime F a d i s
  have hproduct :
      lift (𝟙 (NecklaceCode.single d).toSSet) p ≫ (i ⊗ₘ 𝟙 (J.obj k)) =
      ι ≫ lift (fst T.toSSet (J.obj (time.obj a))) (F.parameter a) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, Category.id_comp]
      rfl
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc]
      rfl
  calc
    _ = lift (𝟙 (NecklaceCode.single d).toSSet) p ≫
        JTNecklaceLabelRealization.realizedLabel (NecklaceCode.single d).toSSet W k
          (SSet.yonedaEquiv (coefficient (a := a) d i ≫ labelFromRow W d)) :=
      nativeRawGraph_realized d k (coefficient (a := a) d i) p
    _ = lift (𝟙 (NecklaceCode.single d).toSSet) p ≫
        (i ⊗ₘ 𝟙 (J.obj k)) ≫
          JTNecklaceLabelRealization.realizedLabel T.toSSet W k η := by
      rw [coefficient_label]
      exact (congrArg
        (fun q ↦ lift (𝟙 (NecklaceCode.single d).toSSet) p ≫ q)
        (JTNecklaceLabelRealization.realizedLabel_natural_X i W k η)).symm
    _ = ι ≫ JTBinaryPrismRealization.realizeProduct W k (F.parameter a) η := by
      rw [JTBinaryPrismRealization.realizeProduct, ← Category.assoc, hproduct]
      rfl
    _ = ι ≫ fst T.toSSet (J.obj (time.obj a)) ≫
        (F.collapse.app a).map ≫ Q.map := by
      have hraw := JTParametrizedTargetFamilies.rawProduct F a
      change JTBinaryPrismRealization.realizeProduct W k (F.parameter a) η =
        fst T.toSSet (J.obj (time.obj a)) ≫ (F.collapse.app a).map ≫ Q.map at hraw
      rw [hraw]
    _ = beadRaw F a d i := by
      change (lift i s ≫ fst T.toSSet (J.obj (time.obj a))) ≫
        (F.collapse.app a).map ≫ Q.map =
        i ≫ (F.collapse.app a).map ≫ Q.map
      rw [lift_fst]

/-- The arbitrary-time graph on the ordinary simplex has the exact raw value. -/
theorem rawGraphWithTime_eq
    (s : (NecklaceCode.single d).toSSet ⟶ J.obj (time.obj a)) :
    rawGraph W ⦋d⦌ (degree (W := W) (x := x) (y := y) (L := L) a)
      (coefficient (a := a) d i)
      ((NecklaceCode.singleIso d).inv ≫ beadParameterWithTime F a d i s) =
    (NecklaceCode.singleIso d).inv ≫ beadRaw F a d i := by
  have h := congrArg (fun q ↦ (NecklaceCode.singleIso d).inv ≫ q)
    (nativeRawGraphWithTime_eq F a d i s)
  unfold nativeRawGraph at h
  simpa only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h

/-- Every simplicial time map yields an actual graph in the fixed raw-value fiber. -/
def fiberGraphWithTime
    (s : (NecklaceCode.single d).toSSet ⟶ J.obj (time.obj a)) :
    JTRowGraphFiber.Fiber ((NecklaceCode.singleIso d).inv ≫ beadRaw F a d i) :=
  ⟨⟨degree (W := W) (x := x) (y := y) (L := L) a,
    SSet.yonedaEquiv (X := row W ⦋d⦌) (coefficient (a := a) d i),
    (NecklaceCode.singleIso d).inv ≫ beadParameterWithTime F a d i s⟩,
    rawGraphWithTime_eq F a d i s⟩

theorem nativeRawGraph_eq :
    nativeRawGraph W d (degree (W := W) (x := x) (y := y) (L := L) a)
      (coefficient (a := a) d i)
      ((NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v) =
    beadRaw F a d i :=
  nativeRawGraphWithTime_eq F a d i (term _ ≫ v)

/-- The same graph, expressed on the ordinary simplex rather than the native bead. -/
theorem rawGraph_eq :
    rawGraph W ⦋d⦌ (degree (W := W) (x := x) (y := y) (L := L) a)
      (coefficient (a := a) d i)
      ((NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v) =
    (NecklaceCode.singleIso d).inv ≫ beadRaw F a d i :=
  rawGraphWithTime_eq F a d i (term _ ≫ v)

/-- A graph in the exact raw-value fiber, extracted from the original family. -/
def fiberGraph : JTRowGraphFiber.Fiber
    ((NecklaceCode.singleIso d).inv ≫ beadRaw F a d i) :=
  ⟨⟨degree (W := W) (x := x) (y := y) (L := L) a,
    SSet.yonedaEquiv (X := row W ⦋d⦌) (coefficient (a := a) d i),
    (NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v⟩,
    rawGraph_eq F a d i v⟩

end

end DaggerModels.PartII.JTParametrizedBeadGraph
