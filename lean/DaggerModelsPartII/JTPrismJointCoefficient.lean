import DaggerModelsPartII.JTFullPrismSupport
import DaggerModelsPartII.JTPrismJointNormalization

/-! The full parameter support at a bead lying in the inverse image of a joint. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTPrismRectangle
open JTRowGraphParameterSupport
open JTRowGraphPointCoefficient
open JTRowGraphRelations
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ)
variable (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)

private abbrev k := ((OrderedLabelElements.projection W (boundaryPoint W x y)).obj (L.obj a)).2
private abbrev xmap := (NecklaceCode.singleIso d).inv ≫ i

/-- The actual parameter on the chosen horizontal bead and all time simplices. -/
def fullBeadParameter :
    (Δ[d] : SSet.{0}) ⊗ J.obj (time.obj a) ⟶ J.obj (k (L := L) a) :=
  (xmap a d i ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ F.parameter a

/-- The indices in the original coefficient that are used anywhere on this prism. -/
abbrev fullBeadSupport := supportOrdinal (sample ⦋d⦌ (time.obj a) ≫ fullBeadParameter F a d i)

/-- The literal inclusion of the full bead support in the original coefficient degree. -/
abbrev fullBeadSupportInclusion := inclusion
  (sample ⦋d⦌ (time.obj a) ≫ fullBeadParameter F a d i)

private abbrev inputCoefficient : (Input W).obj (op (⦋d⦌, k (L := L) a)) :=
  SSet.yonedaEquiv (X := row W ⦋d⦌) (coefficient (a := a) d i)

set_option maxHeartbeats 800000 in
/-- A raw point value on a bead forces its actual coefficient, restricted to
the vertices used by the whole prism, to be the degeneracy of that point. -/
theorem fullBeadCoefficient_of_point
    (v : (Input W).obj (op (⦋0⦌, ⦋0⦌)))
    (h : xmap a d i ≫ (F.collapse.app a).map ≫ Q.map =
      std.map (SimplexCategory.isTerminalZero.from ⦋d⦌) ≫ (pointGraph v).value) :
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (⦋d⦌, k (L := L) a) from
      (𝟙 ⦋d⦌, fullBeadSupportInclusion F a d i)).op (inputCoefficient a d i) =
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (⦋0⦌, ⦋0⦌) from
      (SimplexCategory.isTerminalZero.from ⦋d⦌,
        SimplexCategory.isTerminalZero.from (fullBeadSupport F a d i))).op v := by
  let t := time.obj a
  let D := code ⦋d⦌ t
  let n := D.len
  let u := horizontal ⦋d⦌ t
  let m := std.map u
  let i' := (NecklaceCode.singleIso n).hom ≫ m ≫ xmap a d i
  let s' := (NecklaceCode.singleIso n).hom ≫ timeMap ⦋d⦌ t
  let b := fullBeadParameter F a d i
  have hi' : (NecklaceCode.singleIso n).inv ≫ i' = m ≫ (NecklaceCode.singleIso d).inv ≫ i := by
    simp only [i', xmap, Iso.inv_hom_id_assoc]
  have hc := congrArg SSet.yonedaEquiv (coefficient_horizontal a i' i u hi')
  rw [SSet.yonedaEquiv_comp] at hc
  change SSet.yonedaEquiv (X := row W ⦋n⦌) (coefficient (a := a) n i') =
    (Input W).map (show (D, k (L := L) a) ⟶ (⦋d⦌, k (L := L) a) from
      (u, 𝟙 (k (L := L) a))).op (inputCoefficient a d i) at hc
  have hp : (NecklaceCode.singleIso n).inv ≫ beadParameterWithTime F a n i' s' =
      sample ⦋d⦌ t ≫ b := by
    have hq : (NecklaceCode.singleIso n).inv ≫ lift i' s' =
        sample ⦋d⦌ t ≫ (xmap a d i ⊗ₘ 𝟙 (J.obj t)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, hi', Category.assoc, tensorHom_fst, sample, lift_fst_assoc]
      · rw [Category.assoc, lift_snd, Category.assoc, tensorHom_snd, Category.comp_id,
          sample, lift_snd]
        simp only [s', Iso.inv_hom_id_assoc]
    change (NecklaceCode.singleIso n).inv ≫ lift i' s' ≫ F.parameter a = _
    rw [← Category.assoc, hq]
    exact Category.assoc _ _ _
  have hv := (fiberGraphWithTime F a n i' s').property
  change (Graph.mk (W := Input W) (d := D) (k (L := L) a)
      (SSet.yonedaEquiv (X := row W ⦋n⦌) (coefficient (a := a) n i'))
      ((NecklaceCode.singleIso n).inv ≫ beadParameterWithTime F a n i' s')).value =
    (NecklaceCode.singleIso n).inv ≫ beadRaw F a n i' at hv
  rw [hc, hp] at hv
  have hraw : (NecklaceCode.singleIso n).inv ≫ beadRaw F a n i' =
      std.map (SimplexCategory.isTerminalZero.from D) ≫ (pointGraph v).value := by
    change (NecklaceCode.singleIso n).inv ≫ i' ≫ (F.collapse.app a).map ≫ Q.map = _
    rw [← Category.assoc (NecklaceCode.singleIso n).inv, hi']
    simp only [Category.assoc]
    change m ≫ (xmap a d i ≫ (F.collapse.app a).map ≫ Q.map) = _
    rw [h, ← Category.assoc, ← Functor.map_comp]
    exact congrArg (fun f : D ⟶ ⦋0⦌ ↦ std.map f ≫ (pointGraph v).value)
      (SimplexCategory.isTerminalZero.hom_ext _ _)
  exact coefficient_of_sample ⦋d⦌ t b (inputCoefficient a d i) v (hv.trans hraw)

variable (j : JTTargetJointMarks.Joint Q.code)

private abbrev pointMapAtJoint := JTPrismJointNormalization.jointRaw (Q := Q) j

/-- The genuine zero coefficient mapping to the original native joint. -/
def jointCoefficient : (Input W).obj (op (⦋0⦌, ⦋0⦌)) :=
  (JTRawVertexRecovery.zeroVertexEquiv (Input W)).symm (SSet.yonedaEquiv (pointMapAtJoint j))

/-- Its raw realization is the literal joint map of the original target. -/
theorem pointGraph_jointCoefficient : (pointGraph (jointCoefficient j)).value =
    pointMapAtJoint j := by
  apply SSet.yonedaEquiv.injective
  rw [pointGraph_vertex]
  exact (JTRawVertexRecovery.zeroVertexEquiv (Input W)).apply_symm_apply _

private abbrev overlapInclusion := JTTargetIntervalGluing.middleInclusion (F.collapse.app a) j

variable (r : (NecklaceCode.single d).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app a) j j le_rfl).toSSet)

set_option maxHeartbeats 850000 in
/-- Every bead in the actual inverse image of the joint has the common joint
coefficient on the literal support of all its time and horizontal vertices. -/
theorem fullBeadCoefficient_at_joint :
    (Input W).map
      (show (⦋d⦌, fullBeadSupport F a d (r ≫ overlapInclusion F a j)) ⟶
        (⦋d⦌, k (L := L) a) from
        (𝟙 ⦋d⦌, fullBeadSupportInclusion F a d (r ≫ overlapInclusion F a j))).op
      (inputCoefficient a d (r ≫ overlapInclusion F a j)) =
    (Input W).map
      (show (⦋d⦌, fullBeadSupport F a d (r ≫ overlapInclusion F a j)) ⟶
        (⦋0⦌, ⦋0⦌) from
        (SimplexCategory.isTerminalZero.from ⦋d⦌,
          SimplexCategory.isTerminalZero.from
            (fullBeadSupport F a d (r ≫ overlapInclusion F a j)))).op
      (jointCoefficient j) := by
  apply fullBeadCoefficient_of_point F a d (r ≫ overlapInclusion F a j)
  let e := (NecklaceCode.singleIso d).inv ≫ r
  let f : (codes L).obj a ⟶ Q.code := F.collapse.app a
  let z := JTTargetIntervalGluing.middlePoint f j
  let q := NecklaceCode.pointAt Q.code (ULift.up j.val)
  have h : overlapInclusion F a j ≫ f.map = z ≫ q :=
    (JTTargetIntervalGluing.middlePB f j).w
  simp only [xmap, Category.assoc, pointGraph_jointCoefficient]
  rw [← Category.assoc (overlapInclusion F a j) f.map, h]
  change (NecklaceCode.singleIso d).inv ≫ r ≫ (z ≫ q) ≫ Q.map = _
  simp only [Category.assoc]
  change e ≫ z ≫ q ≫ Q.map = _
  rw [← Category.assoc e, ← Category.assoc (e ≫ z)]
  change (e ≫ z) ≫ (q ≫ Q.map) = _
  exact congrArg (fun t ↦ t ≫ (q ≫ Q.map))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)

section Operators

variable {a d i} {b : A} {e : ℕ}
variable {i' : (NecklaceCode.single e).toSSet ⟶ ((codes L).obj b).toSSet}
variable (f : a ⟶ b) (u : ⦋d⦌ ⟶ ⦋e⦌)
variable (h : xmap a d i ≫ ((codes L).map f).map = std.map u ≫ xmap b e i')

private abbrev coefficientOp :=
  ((OrderedLabelElements.projection W (boundaryPoint W x y)).map (L.map f)).2

include h in
set_option maxHeartbeats 500000 in
/-- Changing the native bead and time uses the original decorated label operator
on the entire parameter, in all degrees. -/
theorem fullBeadParameter_map :
    (std.map u ⊗ₘ J.map (time.map f)) ≫ fullBeadParameter F b e i' =
      fullBeadParameter F a d i ≫ J.map (coefficientOp (L := L) f) := by
  let v := J.map (time.map f)
  let c := ((codes L).map f).map
  let r := J.map (coefficientOp (L := L) f)
  have hF : (c ⊗ₘ v) ≫ F.parameter b = F.parameter a ≫ r := F.parameter_map f
  change (std.map u ⊗ₘ v) ≫ (xmap b e i' ⊗ₘ 𝟙 _) ≫ F.parameter b =
    ((xmap a d i ⊗ₘ 𝟙 _) ≫ F.parameter a) ≫ r
  rw [← Category.assoc (std.map u ⊗ₘ v), tensorHom_comp_tensorHom, Category.comp_id,
    ← h, ← Category.id_comp v, ← tensorHom_comp_tensorHom, Category.assoc, hF,
    Category.assoc]

/-- Each exact original mixed operator induces a map on the full bead support. -/
abbrev fullBeadSupportMap : fullBeadSupport F a d i ⟶ fullBeadSupport F b e i' :=
  JTPrismRectangle.supportMap (fullBeadParameter F a d i) (fullBeadParameter F b e i')
    (std.map u ⊗ₘ J.map (time.map f)) (coefficientOp (L := L) f)
    (fullBeadParameter_map F f u h)

/-- Both full supported time-dependent parameters retain the same mixed map. -/
theorem supportedFullBeadParameter_map :
    (std.map u ⊗ₘ J.map (time.map f)) ≫
        supportedParameter (fullBeadParameter F b e i') =
      supportedParameter (fullBeadParameter F a d i) ≫
        J.map (fullBeadSupportMap F f u h) :=
  supportedParameter_natural _ _ _ _ (fullBeadParameter_map F f u h)

end Operators

end

end DaggerModels.PartII.JTParametrizedBeadGraph
