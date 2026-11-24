import DaggerModelsPartII.JTParametrizedBeadGraphOperators
import DaggerModelsPartII.JTRowGraphResolution
import DaggerModelsPartII.JTMixedGraphHorizontalLabel

/-! Restriction of an extracted row graph along an arbitrary horizontal simplex map. -/

set_option autoImplicit false
set_option maxHeartbeats 220000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTProjectiveOrderedFiberComparison (row rowRestrictionIso)
open OrderedSimplexEndpointFiber (freeSimplexRowIso freeMappingIso
  freeSimplexMappingIso_natural)
open OrderedNecklaceVertexPoints (boundaryPoint)
open ReversalDiscreteFreeColimits (discreteFree)
open JTParametrizedTargetFamilies (Family codes)
open JTRealizedLabelEndpoints (orderedLabel)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map g) W

private theorem rowRestriction_natural (W : Source) {d e : ℕ} (u : ⦋d⦌ ⟶ ⦋e⦌) :
    (rowRestrictionIso W ⦋e⦌).inv ≫ (Rows W).map u.op =
      W.map (ReverseSimplex.inclusion.map u).op ≫ (rowRestrictionIso W ⦋d⦌).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [rowRestrictionIso, Rows, row, JTRealizationDiagonal.ordinaryCurry,
    JTReversalInput.ordinaryInput]
  simp

private theorem rowIso_natural (W : Source) {d e : ℕ} (u : ⦋d⦌ ⟶ ⦋e⦌) :
    pre W (SSet.stdSimplex.{0}.map u) ≫ (freeSimplexRowIso W d).hom =
      (freeSimplexRowIso W e).hom ≫ (Rows W).map u.op := by
  have h := freeSimplexMappingIso_natural W u
  change pre W (SSet.stdSimplex.{0}.map u) ≫ (freeMappingIso W d).hom =
    (freeMappingIso W e).hom ≫ W.map (ReverseSimplex.inclusion.map u).op at h
  simpa only [freeSimplexRowIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    rowRestriction_natural] using congrArg (· ≫ (rowRestrictionIso W ⦋d⦌).inv) h

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj
  (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (a : A) {d e : ℕ}
variable (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)
variable (j : (NecklaceCode.single e).toSSet ⟶ ((codes L).obj a).toSSet)
variable (u : ⦋d⦌ ⟶ ⦋e⦌)

private abbrev degree := ((OrderedLabelElements.projection W (boundaryPoint W x y)).obj
  (L.obj a)).2
private abbrev label :=
  orderedLabel W x y ((codes L).obj a) (degree (L := L) a)
    (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a))

private theorem coefficient_as_restriction :
    coefficient (a := a) d i =
      SSet.yonedaEquiv.symm (label (L := L) a) ≫
        pre W ((NecklaceCode.singleIso d).inv ≫ i) ≫ (freeSimplexRowIso W d).hom := by
  let z := label (L := L) a
  have he : beadLabel (a := a) d i = (pre W i).app (op (degree (L := L) a)) z := rfl
  unfold coefficient
  rw [he, ← SSet.yonedaEquiv_symm_comp]
  change (SSet.yonedaEquiv.symm z ≫ pre W i) ≫
    pre W (NecklaceCode.singleIso d).inv ≫ (freeSimplexRowIso W d).hom = _
  have hpre : pre W ((NecklaceCode.singleIso d).inv ≫ i) =
      pre W i ≫ pre W (NecklaceCode.singleIso d).inv := by
    unfold pre
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  rw [hpre]
  simp only [Category.assoc]
  rfl

variable (h : (NecklaceCode.singleIso d).inv ≫ i =
  SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j)

include h in
/-- The original row coefficient restricts along the same horizontal simplex operator. -/
theorem coefficient_horizontal :
    coefficient (a := a) d i = coefficient (a := a) e j ≫ (Rows W).map u.op := by
  have hi := coefficient_as_restriction a i
  have hj := coefficient_as_restriction a j
  rw [hi, hj, h]
  have hc : pre W (SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j) =
      pre W ((NecklaceCode.singleIso e).inv ≫ j) ≫ pre W (SSet.stdSimplex.map u) := by
    unfold pre
    rw [discreteFree.map_comp, diagramMappingPrecomp_comp]
  rw [hc]
  simp only [Category.assoc, rowIso_natural]

variable (F : Family Q L time) (v : (Δ[0] : SSet.{0}) ⟶ J.obj (time.obj a))

include h in
/-- The complete groupoid parameter obeys the same horizontal restriction. -/
theorem beadParameter_horizontal :
    (NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v =
      SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ beadParameter F a e j v := by
  let D := (NecklaceCode.singleIso d).inv
  let E := (NecklaceCode.singleIso e).inv
  let V := SSet.stdSimplex.{0}.map u
  have hs : D ≫ lift i (term _ ≫ v) = V ≫ E ≫ lift j (term _ ≫ v) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, lift_fst] using h
    · simp only [Category.assoc, lift_snd]
      have h₁ : D ≫ term _ = term _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      have h₂ : E ≫ term _ = term _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      have h₃ : V ≫ term _ = term _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simp only [← Category.assoc, h₁, h₂, h₃]
  unfold beadParameter
  calc
    _ = (D ≫ lift i (term _ ≫ v)) ≫ F.parameter a := (Category.assoc _ _ _).symm
    _ = (V ≫ E ≫ lift j (term _ ≫ v)) ≫ F.parameter a :=
      congrArg (· ≫ F.parameter a) hs
    _ = _ := by
      simp only [Category.assoc]
      rfl

include h in
/-- Restricting the complete extracted row graph gives the graph of the actual face. -/
theorem fiberGraph_horizontal :
    (fiberGraph F a d i v).obj =
      JTRowGraphResolution.restrictGraph u (fiberGraph F a e j v).obj := by
  have hc := congrArg SSet.yonedaEquiv (coefficient_horizontal a i j u h)
  rw [SSet.yonedaEquiv_comp] at hc
  have hp := beadParameter_horizontal a i j u h F v
  let k := degree (L := L) a
  let W₀ := JTReversalInput.ordinaryInput.obj W
  let x₀ := SSet.yonedaEquiv (X := row W ⦋d⦌) (n := k) (coefficient (a := a) d i)
  let x₁ := SSet.yonedaEquiv (X := row W ⦋e⦌) (n := k) (coefficient (a := a) e j)
  let u₀ : (⦋d⦌, k) ⟶ (⦋e⦌, k) := (u, 𝟙 k)
  change JTRowGraphRelations.Graph.mk k x₀
      ((NecklaceCode.singleIso d).inv ≫ beadParameter F a d i v) =
    JTRowGraphRelations.Graph.mk k (W₀.map u₀.op x₁)
      (SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ beadParameter F a e j v)
  rw [hp]
  have hc' : x₀ = W₀.map u₀.op x₁ := hc
  rw [hc']

section Mixed

variable {b : A} (f : a ⟶ b)
variable (j' : (NecklaceCode.single e).toSSet ⟶ ((codes L).obj b).toSSet)
variable (h' : (NecklaceCode.singleIso d).inv ≫ i ≫ ((codes L).map f).map =
  SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j')

/-- The original mixed arrow transports the whole row graph into its horizontal restriction. -/
def mixedFiberGraphArrow :
    (fiberGraph F a d i v).obj ⟶ JTRowGraphResolution.restrictGraph u
      (fiberGraph F b e j' (v ≫ J.map (time.map f))).obj :=
  fiberGraphArrow F f d i v ≫
    eqToHom (fiberGraph_horizontal b (i ≫ ((codes L).map f).map) j' u h'
      F (v ≫ J.map (time.map f)))

include h' in
/-- The underlying raw simplex gives the exact horizontal triangle in the original target. -/
theorem beadRaw_mixed :
    (NecklaceCode.singleIso d).inv ≫ beadRaw F a d i =
      SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ beadRaw F b e j' := by
  rw [← beadRaw_map F f d i]
  let q := (F.collapse.app b).map ≫ Q.map
  change (NecklaceCode.singleIso d).inv ≫ (i ≫ ((codes L).map f).map) ≫ q =
    SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j' ≫ q
  exact ((Category.assoc (NecklaceCode.singleIso d).inv
      (i ≫ ((codes L).map f).map) q).symm.trans
    (congrArg (· ≫ q) h')).trans (by simp only [Category.assoc])

end Mixed

end

end DaggerModels.PartII.JTParametrizedBeadGraph
