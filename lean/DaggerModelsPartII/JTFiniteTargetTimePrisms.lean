import DaggerModelsPartII.JTPaddedNormalizedGraphPrisms
import DaggerModelsPartII.JTFiniteNecklaceGraphRefinement
import DaggerModelsPartII.JTGraphLargePredecessor
import OriginalGateHomValueCollapseReconciledRecovered
import NativeOverNerveWeakContractibility
import OriginalSimplicialPiZeroWeakEquivalence

/-! Glue the actual padded time families along the original finite necklace. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open NecklaceCode DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFiniteTargetTimePrisms

open JTProjectiveOrderedFiberComparison (row)
open JTMixedGraphEndpointLifts (vertex)
open JTPaddedNormalizedGraphPrisms (time Padded)
open DaggerOriginalFlagFlankification
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y z : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

/-- A weakly contractible time space of complete comparisons over the
prescribed original native target. -/
structure Resolution where
  space : SSet.{0}
  source : NecklaceCode
  collapse : source ⟶ Q.code
  family : JTCompatibleTimePrisms.Family (time space) Q source collapse
  point : GW (pointMap space)

variable {Q}
variable {P : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W x)}

/-- Pair all time choices on both sides before gluing along the joint. -/
def Resolution.join (L : Resolution P) (R : Resolution Q) : Resolution (NecklacesOver.wedge P Q) where
  space := L.space ⊗ R.space
  source := JTOrderedLabelBinaryGlue.code L.source R.source
  collapse := JTBinaryPrismRealization.collapse L.collapse R.collapse
  family := JTCompatibleTimePrisms.join
    (L.family.precomp (NatTrans.mapElements (fst L.space R.space)).op)
    (R.family.precomp (NatTrans.mapElements (snd L.space R.space)).op)
  point := pointMap_tensor_GW L.point R.point

/-- The family is still over the same complete target map after native postcomposition. -/
def Resolution.postcomp {Q' : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
    (R : Resolution Q) (f : Q ⟶ Q') : Resolution Q' where
  space := R.space
  source := R.source
  collapse := R.collapse ≫ f.hom
  family := R.family.postcomp f
  point := R.point

/-- Include all original internal necklaces in the resolved time cylinders. -/
abbrev Resolution.Presentation (R : Resolution Q) :=
  BoundaryNecklaceComma.Presentation (time R.space ⋙ JTNecklaceEndpointCylinder.under R.source)

/-- The category of all such cylinders and necklaces has weakly contractible nerve. -/
theorem Resolution.presentation_point_GW (R : Resolution Q) :
    GW (pointMap (nerve R.Presentation)) :=
  (JTHomotopyTargetTimeResolution.point_GW_iff_at R.source (time R.space)).mpr R.point

/-- The entire comparison maps to the original fixed-target comma. -/
def Resolution.toComma (R : Resolution Q) : R.Presentation ⥤
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  JTTimePrismTargetComparison.toComma R.family

/-- One fixed decorated code cannot reach every original comma object by a
forward arrow. A large graph predecessor gives an empty actual comma. -/
theorem Resolution.exists_empty_forward_comma (R : Resolution Q) :
    ∃ V : TargetComma Q, IsEmpty (CostructuredArrow R.toComma V) := by
  let X := nerve R.Presentation
  let e := pointIsTerminal.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  let p := pointMap X ≫ e.hom
  have : WeakEquivalence (pointMap X) :=
    (weakEquivalence_iff_GW _).mpr R.presentation_point_GW
  have : WeakEquivalence p := by dsimp only [p]; infer_instance
  let v := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))
  obtain ⟨a, _⟩ := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero p).2
    (SSet.π₀.mk v)
  obtain ⟨P, _⟩ := SSet.π₀.mk_surjective a
  let U := R.toComma.obj (CategoryTheory.nerveEquiv P)
  obtain ⟨V, _, hV⟩ := JTGraphLargePredecessor.exists_large U R.source.joints.card
  exact ⟨V, ⟨fun P ↦ (Nat.not_lt_of_ge
    (JTTimePrismTargetComparison.target_joints_card_le R.family V P.left P.hom)) hV⟩⟩

/-- The data on the time parameters needed to compare the finite resolution
with an original comma object. Both equalities are of whole maps. -/
structure Resolution.ComparisonTo (R : Resolution Q) (U : TargetComma Q) where
  decorated : JTTimePrismTargetComparison.toLabels R.family ⟶ (Functor.const _).obj U.left.base
  native : R.source ⟶ U.left.fiber.left
  decorated_comm : ∀ a,
    JTTimePrismTargetComparison.cylinderAt R.family a ≫
        (DecoratedCylinderNecklacePresentation.underDiagram W x y).map (decorated.app a) =
      JTGraphInterpolatedCollapseOriginal.timeCollapse (n := (time R.space).obj a) native ≫
        U.left.fiber.hom
  native_comm : native ≫ U.hom.hom = R.collapse

/-- The compatible finite comparison lands in the actual slice over the
original comma object. -/
def Resolution.toSlice (R : Resolution Q) {U : TargetComma Q} (data : R.ComparisonTo U) :
    R.Presentation ⥤ Over U :=
  Over.lift R.toComma (JTTimePrismTargetComparison.comparisonToOriginal R.family U
    data.native data.decorated data.decorated_comm data.native_comm)

theorem Resolution.toSlice_forget (R : Resolution Q) {U : TargetComma Q}
    (data : R.ComparisonTo U) : R.toSlice data ⋙ Over.forget U = R.toComma := rfl

/-- Given the parameterwise comparison, the finite resolution and the
original slice have the same weak homotopy type. -/
theorem Resolution.toSlice_weak (R : Resolution Q) {U : TargetComma Q}
    (data : R.ComparisonTo U) : WeakEquivalence (nerveMap (R.toSlice data)) := by
  let p := pointMap (nerve (Over U))
  have : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr
    (DaggerNativeOverNerveWeakContractibility.point_GW U)
  apply (weakEquivalence_postcomp_iff (nerveMap (R.toSlice data)) p).mp
  rw [pointIsTerminal.hom_ext (nerveMap (R.toSlice data) ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr R.presentation_point_GW

/-- Contractibility of the exact target comma is equivalent to weakness
of the joined comparison on its whole resolved domain. -/
theorem Resolution.toComma_weak_iff (R : Resolution Q) :
    WeakEquivalence (nerveMap R.toComma) ↔
      GW (pointMap (nerve (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q))) := by
  let f := nerveMap R.toComma
  let t := pointMap (nerve (CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q))
  have h : f ≫ t = pointMap (nerve R.Presentation) := pointIsTerminal.hom_ext _ _
  have : WeakEquivalence (f ≫ t) :=
    (weakEquivalence_iff_GW _).mpr (h.symm ▸ R.presentation_point_GW)
  change WeakEquivalence f ↔ GW t
  rw [← weakEquivalence_iff_GW]
  constructor
  · intro hf
    letI : WeakEquivalence f := hf
    exact (weakEquivalence_precomp_iff f t).mp inferInstance
  · intro ht
    letI : WeakEquivalence t := ht
    exact (weakEquivalence_postcomp_iff f t).mp inferInstance

/-- The single-bead resolution has the prescribed padded source and the exact
collapse to its middle bead. -/
theorem single_resolution
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (d : ℕ) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (hQ : Q.code = single d) :
    ∃ (R : Resolution Q) (e : R.source = MixedGraphCylinderTraversal.code d),
      eqToHom e.symm ≫ R.collapse = MixedGraphCylinderTraversal.collapseOuter d ≫
        eqToHom hQ.symm := by
  obtain ⟨T, q, qx, qy⟩ := Q
  change T = single d at hQ
  subst T
  let g : (Δ[d] : SSet.{0}) ⟶ Raw W := (singleIso d).inv ≫ q
  let G := JTRowGraphFiber.center g
  have hmap : JTMixedGraphRawRefinement.nativeRawGraph W d G.obj.degree
      (JTRowGraphNormalizationDiagram.coefficient G) G.obj.parameter = q := by
    exact (congrArg (fun u ↦ (singleIso d).hom ≫ u)
      (JTRowGraphNormalizationDiagram.raw_eq G)).trans (Iso.hom_inv_id_assoc _ _)
  obtain ⟨hx, hy⟩ := JTMixedGraphRawRefinement.graph_endpoints_of_native_map hmap qx qy
  rw [JTRowGraphNormalizationDiagram.raw_eq G] at hx hy
  let e := (JTPaddedNormalizedGraphPrisms.edge_nonempty hx hy G hW).some
  let X := Padded hx hy G e
  let D : Resolution (JTNormalizedGraphTargetArrow.target hx hy) :=
    ⟨X, MixedGraphCylinderTraversal.code d, MixedGraphCylinderTraversal.collapseOuter d,
      JTPaddedNormalizedGraphPrisms.family hx hy G (𝟙 X),
      JTFixedEdgePaddedTime.point_GW _ e⟩
  let a : JTNormalizedGraphTargetArrow.target hx hy ⟶
      (⟨single d, q, qx, qy⟩ : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
    ⟨(𝟙 (single d) : single d ⟶ single d), by
      change (𝟙 (single d).toSSet) ≫ q = (singleIso d).hom ≫ (singleIso d).inv ≫ q
      exact (Category.id_comp _).trans (Iso.hom_inv_id_assoc _ _).symm⟩
  refine ⟨D.postcomp a, rfl, ?_⟩
  change eqToHom rfl ≫ (MixedGraphCylinderTraversal.collapseOuter d ≫ 𝟙 (single d)) =
    MixedGraphCylinderTraversal.collapseOuter d ≫ eqToHom _
  simp only [eqToHom_refl, Category.id_comp]

private theorem single_nonempty
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (d : ℕ) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (hQ : Q.code = single d) :
    Nonempty (Resolution Q) := by
  obtain ⟨R, _, _⟩ := single_resolution hW d Q hQ
  exact ⟨R⟩

open JTFiniteNecklaceGraphRefinement (atRaw)

private theorem prefix_nonempty
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    {a b : (Raw W).obj (op ⦋0⦌)} (Q : NecklacesOver (Raw W) a b)
    (n : ℕ) (hn : n ≤ beadCount Q.code)
    (hx : jointVertex Q 0 = rawVertex W x)
    (hy : jointVertex Q ⟨n, Nat.lt_succ_of_le hn⟩ = rawVertex W y) :
    Nonempty (Resolution (atRaw (orderedPrefix Q n hn).source hx hy)) := by
  induction n generalizing y with
  | zero =>
    exact single_nonempty hW 0 _ (code_zero_eq_point (single 0) rfl).symm
  | succ n ih =>
    let i : Fin (beadCount Q.code) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let c := jointBead Q.code i
    let u := jointVertex Q i.castSucc
    let e := JTRawVertexRecovery.zeroVertexEquiv (JTReversalInput.ordinaryInput.obj W)
    let z : Vertex W := e.symm u
    have hz : u = rawVertex W z := (e.apply_symm_apply u).symm
    obtain ⟨L⟩ := ih (Nat.le_of_succ_le hn) hz
    obtain ⟨R⟩ := single_nonempty hW c.length (atRaw (sourceBeadOver Q c) hz hy) rfl
    exact ⟨L.join R⟩

/-- Every actual finite native target has a weakly contractible resolution
obtained by joining its padded bead comparisons and retaining its exact map. -/
theorem resolution_nonempty
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    Nonempty (Resolution Q) := by
  obtain ⟨L⟩ := prefix_nonempty hW Q (beadCount Q.code) le_rfl
    (jointVertex_first Q) (jointVertex_last Q)
  let L' : Resolution (assembledSource Q) := L
  exact ⟨L'.postcomp (sourceAssemblyIso Q).hom⟩

end

end DaggerModels.PartII.JTFiniteTargetTimePrisms
