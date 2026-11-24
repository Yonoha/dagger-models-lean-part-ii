import DaggerModelsPartII.JTParametrizedBeadGraph

/-! Mixed operators retain the exact raw simplex and its graph parameter on a transported bead. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes)
open JTRealizedLabelEndpoints (orderedLabel)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels necklaceBoundaryRestriction necklaceLabels
  orderedLabelDiagram)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) {a b : A} (f : a ⟶ b)
variable (d : ℕ) (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)
variable (v : (Δ[0] : SSet.{0}) ⟶ J.obj (time.obj a))

private abbrev coefficientOperator :=
  ((OrderedLabelElements.projection W (boundaryPoint W x y)).map (L.map f)).2

/-- Transporting the bead and its time vertex commutes with the entire graph parameter. -/
theorem beadParameter_map :
    beadParameter F a d i v ≫ J.map (coefficientOperator (L := L) f) =
      beadParameter F b d (i ≫ ((codes L).map f).map) (v ≫ J.map (time.map f)) := by
  let k := coefficientOperator (L := L) f
  let n := J.map (time.map f)
  let g := ((codes L).map f).map
  let ι := lift i (term (NecklaceCode.single d).toSSet ≫ v)
  change (ι ≫ F.parameter a) ≫ J.map k =
    lift (i ≫ g) (term (NecklaceCode.single d).toSSet ≫ (v ≫ n)) ≫ F.parameter b
  have h : (g ⊗ₘ n) ≫ F.parameter b = F.parameter a ≫ J.map k := F.parameter_map f
  rw [Category.assoc, ← h, ← Category.assoc, lift_map, Category.assoc]

/-- Transport along any actual arrow preserves the complete raw simplex of this bead. -/
theorem beadRaw_map :
    beadRaw F b d (i ≫ ((codes L).map f).map) = beadRaw F a d i := by
  let g := (codes L).map f
  have h : g ≫ F.collapse.app b = F.collapse.app a :=
    (F.collapse.naturality f).trans (Category.comp_id _)
  have hm : g.map ≫ (F.collapse.app b).map = (F.collapse.app a).map :=
    congrArg (fun u : (codes L).obj a ⟶ Q.code ↦ u.map) h
  change (i ≫ g.map) ≫ (F.collapse.app b).map ≫ Q.map = i ≫ (F.collapse.app a).map ≫ Q.map
  rw [Category.assoc, ← Category.assoc g.map, hm]

private abbrev P := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev k (a : A) := ((P (W := W) (x := x) (y := y)).obj (L.obj a)).2
private abbrev z (a : A) :=
  OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a)
private abbrev underlyingLabel (a : A) :=
  orderedLabel W x y ((codes L).obj a) (k (L := L) a) (z (L := L) a)
private abbrev mapping (W : Source) (X : SSet.{0}) := diagramMappingSpace (discreteFree.obj X) W
private abbrev restrict (W : Source) {X Y : SSet.{0}} (s : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map s) W

private theorem underlyingLabel_map :
    (mapping W ((codes L).obj a).toSSet).map (coefficientOperator (L := L) f).op
      ((restrict W ((codes L).map f).map).app (op (k (L := L) b))
        (underlyingLabel (L := L) b)) = underlyingLabel (L := L) a := by
  let O := orderedNecklaceLabels W (boundaryPoint W x y)
  let g := (codes L).map f
  let j := coefficientOperator (L := L) f
  let f₁ := pullback.fst ((necklaceBoundaryRestriction W).app (op ((codes L).obj a)))
    (boundaryPoint W x y)
  let f₂ := pullback.fst ((necklaceBoundaryRestriction W).app (op ((codes L).obj b)))
    (boundaryPoint W x y)
  let z' := (O.map g.op).app (op (k (L := L) b)) (z (L := L) b)
  have hv := congrFun (f₁.naturality j.op) z'
  have hh : O.map g.op ≫ f₁ = f₂ ≫ (necklaceLabels W).map g.op := by
    simp only [O, f₁, f₂, orderedNecklaceLabels, orderedLabelDiagram,
      pullback.map, pullback.lift_fst]
  have hx := congrFun (NatTrans.congr_app hh (op (k (L := L) b))) (z (L := L) b)
  have hy : (O.obj (op ((codes L).obj a))).map j.op z' = z (L := L) a :=
    OrderedLabelElements.label_map W (boundaryPoint W x y) (L.map f)
  have h₀ : (restrict W g.map).app (op (k (L := L) b))
      (underlyingLabel (L := L) b) = f₁.app (op (k (L := L) b)) z' :=
    hx.symm
  change (mapping W ((codes L).obj a).toSSet).map j.op
      ((restrict W g.map).app (op (k (L := L) b)) (underlyingLabel (L := L) b)) =
    f₁.app (op (k (L := L) a)) (z (L := L) a)
  rw [h₀]
  exact hv.symm.trans (congrArg (f₁.app (op (k (L := L) a))) hy)

/-- The complete restricted bead label transports along the original coefficient map. -/
theorem beadLabel_map :
    (mapping W (NecklaceCode.single d).toSSet).map (coefficientOperator (L := L) f).op
      (beadLabel (a := b) d (i ≫ ((codes L).map f).map)) =
    beadLabel (a := a) d i := by
  let g := ((codes L).map f).map
  let h := restrict W i
  let r := restrict W g
  let m := op (k (L := L) b)
  let n := op (k (L := L) a)
  let e := (coefficientOperator (L := L) f).op
  let l := underlyingLabel (L := L) b
  have hc : restrict W (i ≫ g) = r ≫ h := by
    unfold restrict
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  have hm : beadLabel (a := b) d (i ≫ g) = h.app m (r.app m l) :=
    congrFun (NatTrans.congr_app hc m) l
  change (mapping W (NecklaceCode.single d).toSSet).map e
    (beadLabel (a := b) d (i ≫ g)) = h.app n (underlyingLabel (L := L) a)
  rw [hm]
  exact (congrFun (h.naturality e) (r.app m l)).trans
    (congrArg (h.app n) (underlyingLabel_map (L := L) f))

/-- The actual row coefficient commutes with every source operator when the bead is transported. -/
theorem coefficient_map :
    SSet.stdSimplex.map (coefficientOperator (L := L) f) ≫
        coefficient (a := b) d (i ≫ ((codes L).map f).map) =
      coefficient (a := a) d i := by
  let g := ((codes L).map f).map
  let u := coefficientOperator (L := L) f
  let D := mapping W (NecklaceCode.single d).toSSet
  have h := congrArg (SSet.yonedaEquiv (X := D)).symm (beadLabel_map f d i)
  change SSet.yonedaEquiv.symm (D.map u.op (beadLabel (a := b) d (i ≫ g))) =
    SSet.yonedaEquiv.symm (beadLabel (a := a) d i) at h
  rw [SSet.yonedaEquiv_symm_map] at h
  unfold coefficient
  rw [← Category.assoc, h]

/-- The induced arrow of complete row graphs uses the original coefficient operator. -/
def fiberGraphArrow :
    (fiberGraph F a d i v).obj ⟶
      (fiberGraph F b d (i ≫ ((codes L).map f).map) (v ≫ J.map (time.map f))).obj where
  operator := coefficientOperator (L := L) f
  coefficient := by
    change (row W ⦋d⦌).map (coefficientOperator (L := L) f).op
        (SSet.yonedaEquiv (coefficient (a := b) d (i ≫ ((codes L).map f).map))) =
      SSet.yonedaEquiv (coefficient (a := a) d i)
    rw [← SSet.yonedaEquiv_map_comp, coefficient_map f d i]
  parameter := by
    change ((NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v) ≫
        J.map (coefficientOperator (L := L) f) =
      (NecklaceCode.singleIso d).inv ≫
        beadParameter F b d (i ≫ ((codes L).map f).map) (v ≫ J.map (time.map f))
    rw [Category.assoc, beadParameter_map F f d i v]

end

end DaggerModels.PartII.JTParametrizedBeadGraph
