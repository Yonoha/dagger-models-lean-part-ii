import DaggerModelsPartII.JTNativeLiftRawComparison
import DaggerModelsPartII.JTGraphMultiBeadIdentityLift
import DaggerModelsPartII.JTOrderedLabelBinaryGlue
import DaggerModelsPartII.JTRowGraphCategory
import DaggerModelsPartII.JTMixedGraphRawRefinement

/-!
# Exact identity lifts of a native single bead

The whole coefficient has stationary ordered endpoints precisely when an
exact identity lift exists, after taking the canonical row-graph
representative of the original raw simplex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTStationarySingleLift

open ReversalDiscreteFreeColimits JTProjectiveOrderedFiberComparison
open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement
open JTNativeRowLabel JTRealizedLabelEndpoints
open NecklaceCode

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev K (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {d : ℕ} {k : SimplexCategory}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (f : K k ⟶ row W ⦋d⦌)
variable (s : K ⦋d⦌ ⟶ J.obj k)

private abbrev T := single d

private theorem pointAt_first :
    pointAt (T (d := d)) (ULift.up 0) = SSet.yonedaEquiv.symm (T (d := d)).first := by
  apply SSet.yonedaEquiv.injective
  rw [pointAt_vertex, Equiv.apply_symm_apply]
  rfl

private theorem pointAt_last :
    pointAt (T (d := d)) (ULift.up (Fin.last d)) =
      SSet.yonedaEquiv.symm (T (d := d)).last := by
  apply SSet.yonedaEquiv.injective
  rw [pointAt_vertex, Equiv.apply_symm_apply]
  rfl

private theorem coefficient_boundary
    (hx : f ≫ rowVertex W ⦋d⦌ 0 = term (K k) ≫ vertexPoint W x)
    (hy : f ≫ rowVertex W ⦋d⦌ (Fin.last d) = term (K k) ≫ vertexPoint W y) :
    (f ≫ labelFromRow W d) ≫ (necklaceBoundaryRestriction W).app (op (single d)) =
      term (K k) ≫ boundaryPoint W x y := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst, boundaryPoint_first]
    change f ≫ labelFromRow W d ≫ diagramMappingPrecomp (boundaryNecklace (single d)) W ≫
      diagramMappingPrecomp (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    rw [← diagramMappingPrecomp_comp, boundaryNecklace, coprod.inl_desc, ← pointAt_first,
      labelFromRow_vertex, ← Category.assoc f, hx]
    simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  · simp only [Category.assoc, boundaryMappingIso_snd, boundaryPoint_last]
    change f ≫ labelFromRow W d ≫ diagramMappingPrecomp (boundaryNecklace (single d)) W ≫
      diagramMappingPrecomp (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    rw [← diagramMappingPrecomp_comp, boundaryNecklace, coprod.inr_desc, ← pointAt_last,
      labelFromRow_vertex, ← Category.assoc f, hy]
    simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

variable (hx : f ≫ rowVertex W ⦋d⦌ 0 = term (K k) ≫ vertexPoint W x)
variable (hy : f ≫ rowVertex W ⦋d⦌ (Fin.last d) = term (K k) ≫ vertexPoint W y)

private def label :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (single d))).obj (op k) :=
  SSet.yonedaEquiv (pullback.lift (f ≫ labelFromRow W d) (term (K k)) (coefficient_boundary f hx hy))

private theorem label_coefficient :
    orderedLabel W x y (single d) k (label f hx hy) =
      SSet.yonedaEquiv (f ≫ labelFromRow W d) := by
  let b := boundaryPoint W x y
  let r := (necklaceBoundaryRestriction W).app (op (single d))
  let g : K k ⟶ pullback r b :=
    pullback.lift (f ≫ labelFromRow W d) (term (K k)) (coefficient_boundary f hx hy)
  change (pullback.fst r b).app (op k) (SSet.yonedaEquiv g) = _
  exact (SSet.yonedaEquiv_comp g (pullback.fst r b)).symm.trans
    (congrArg SSet.yonedaEquiv (pullback.lift_fst _ _ _))

private theorem graph_value :
    JTGraphRefinement.realizeGraph W k ((singleIso d).hom ≫ s)
        (SSet.yonedaEquiv (f ≫ labelFromRow W d)) = nativeRawGraph W d k f s := by
  unfold JTGraphRefinement.realizeGraph nativeRawGraph rawGraph
  rw [realized_nativeLabel, ← Category.assoc]
  have h : lift (𝟙 (single d).toSSet) ((singleIso d).hom ≫ s) ≫
        ((singleIso d).hom ⊗ₘ 𝟙 (J.obj k)) =
      (singleIso d).hom ≫ lift (𝟙 (K ⦋d⦌)) s := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc, Category.comp_id,
        Category.id_comp]
    · simp only [Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
  rw [h, Category.assoc]

include hx hy in
/-- A stationary row graph gives a lift with its original single bead as
both the native domain and the decorated code. -/
theorem identity_rawLift_nonempty
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d)
    (hq : nativeRawGraph W d k f s = (eqToHom (congrArg NecklaceCode.toSSet hQ.symm)) ≫ Q.map) :
    Nonempty (JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))).Elements := by
  obtain ⟨C, q, qx, qy⟩ := Q
  change C = single d at hQ
  subst C
  simp only [eqToHom_refl, Category.id_comp] at hq
  let Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) := ⟨single d, q, qx, qy⟩
  let z := label f hx hy
  let a := (singleIso d).hom ≫ s
  let P := JTGraphRefinement.presentation W x y (single d) k z a
  let R := JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))
  refine ⟨R.elementsMk P.base (Over.homMk P.fiber.hom ?_)⟩
  apply Under.UnderMorphism.ext
  change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj P).map =
    (𝟙 (single d).toSSet) ≫ q
  rw [Category.id_comp, JTGraphRefinement.presentation_target_map]
  rw [label_coefficient]
  exact (graph_value f s).trans hq


open OrderedSimplexEndpointFiber JTGraphLiftTransport

private def rowFromLabel (W : Source) (d : ℕ) :
    diagramMappingSpace (F.obj (single d).toSSet) W ⟶ row W ⦋d⦌ :=
  diagramMappingPrecomp (F.map (singleIso d).inv) W ≫ (freeSimplexRowIso W d).hom

private theorem rowFromLabel_labelFromRow (W : Source) (d : ℕ) :
    rowFromLabel W d ≫ labelFromRow W d = 𝟙 _ := by
  unfold rowFromLabel labelFromRow
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← diagramMappingPrecomp_comp,
    ← F.map_comp, Iso.hom_inv_id, F.map_id, diagramMappingPrecomp_id]

private def orderedRow
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (single d))).obj (op k)) :
    K k ⟶ row W ⦋d⦌ :=
  JTOrderedLabelBinaryGlue.coefficient W x y (single d) k z ≫ rowFromLabel W d

private theorem orderedRow_label
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (single d))).obj (op k)) :
    orderedRow z ≫ labelFromRow W d = JTOrderedLabelBinaryGlue.coefficient W x y (single d) k z := by
  rw [orderedRow, Category.assoc, rowFromLabel_labelFromRow]
  exact Category.comp_id _

private theorem orderedRow_first
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (single d))).obj (op k)) :
    orderedRow z ≫ rowVertex W ⦋d⦌ 0 = term (K k) ≫ vertexPoint W x := by
  let j := TwoBeadEndpointLabel.jointLabelFromRow W
  haveI : Mono j := by
    change Mono (freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono j).mp
  change (orderedRow z ≫ rowVertex W ⦋d⦌ 0) ≫ TwoBeadEndpointLabel.jointLabelFromRow W =
    (term (K k) ≫ vertexPoint W x) ≫ TwoBeadEndpointLabel.jointLabelFromRow W
  rw [Category.assoc, ← labelFromRow_vertex, ← Category.assoc, orderedRow_label,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  exact JTOrderedLabelBinaryGlue.coefficient_first W x y (single d) k z

private theorem orderedRow_last
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (single d))).obj (op k)) :
    orderedRow z ≫ rowVertex W ⦋d⦌ (Fin.last d) = term (K k) ≫ vertexPoint W y := by
  let j := TwoBeadEndpointLabel.jointLabelFromRow W
  haveI : Mono j := by
    change Mono (freeSimplexRowIso W 0).inv
    infer_instance
  apply (cancel_mono j).mp
  change (orderedRow z ≫ rowVertex W ⦋d⦌ (Fin.last d)) ≫ TwoBeadEndpointLabel.jointLabelFromRow W =
    (term (K k) ≫ vertexPoint W y) ≫ TwoBeadEndpointLabel.jointLabelFromRow W
  rw [Category.assoc, ← labelFromRow_vertex, ← Category.assoc, orderedRow_label,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
  exact JTOrderedLabelBinaryGlue.coefficient_last W x y (single d) k z

/-- An exact identity lift of a single bead yields a raw graph presentation
whose original row coefficient has both endpoints stationary. -/
theorem exists_stationary_graph_of_identity_rawLift
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d)
    (u : (JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))).Elements) :
    ∃ (k : SimplexCategory) (f : K k ⟶ row W ⦋d⦌) (s : K ⦋d⦌ ⟶ J.obj k),
      f ≫ rowVertex W ⦋d⦌ 0 = term (K k) ≫ vertexPoint W x ∧
      f ≫ rowVertex W ⦋d⦌ (Fin.last d) = term (K k) ≫ vertexPoint W y ∧
      nativeRawGraph W d k f s = eqToHom (congrArg NecklaceCode.toSSet hQ.symm) ≫ Q.map := by
  obtain ⟨C, q, qx, qy⟩ := Q
  change C = single d at hQ
  subst C
  let Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) := ⟨single d, q, qx, qy⟩
  obtain ⟨i, u⟩ := u
  let P : Pres (W := W) (x := x) (y := y) := ⟨i, CostructuredArrow.mk u.left⟩
  have hu : ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj P).map = q := by
    have h := congrArg (fun m ↦ m.right) (Over.w u)
    change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj P).map =
      (𝟙 (single d).toSSet) ≫ q at h
    exact h.trans (Category.id_comp q)
  obtain ⟨D, hD⟩ := JTGraphMultiBeadIdentityLift.exists_identity_lift P
  let a := D.collapse ≫ JTCommaGraphPredecessor.augmentationCode P
  let z := JTGraphToPresentationArrow.pulledLabel P (single d) a
  let s := (singleIso d).inv ≫ D.parameter
  let g := JTGraphToPresentationArrow.toPresentation P (single d) a D.collapse D.parameter D.comm
  let U := DecoratedCylinderNecklacePresentation.toTarget W x y
  have hg : ((U.map g).hom.map) = 𝟙 (single d).toSSet := by
    change D.collapse.map = _
    rw [hD]
    rfl
  have h := (U.map g).w
  rw [hg] at h
  have h := (Category.id_comp ((U.obj P).map)).symm.trans h
  change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj P).map = _ at h
  rw [hu] at h
  symm at h
  change ((DecoratedCylinderNecklacePresentation.toTarget W x y).obj
    (JTGraphRefinement.presentation W x y (single d) (degree P) z D.parameter)).map = q at h
  rw [JTGraphRefinement.presentation_target_map] at h
  refine ⟨degree P, orderedRow z, s, orderedRow_first z, orderedRow_last z, ?_⟩
  have ht : (singleIso d).hom ≫ s = D.parameter := Iso.hom_inv_id_assoc _ _
  have hm := graph_value (orderedRow z) s
  rw [ht, orderedRow_label] at hm
  have hz : SSet.yonedaEquiv (JTOrderedLabelBinaryGlue.coefficient W x y (single d) (degree P) z) =
      orderedLabel W x y (single d) (degree P) z :=
    Equiv.apply_symm_apply SSet.yonedaEquiv _
  have hz' := congrArg (JTGraphRefinement.realizeGraph W (degree P) D.parameter) hz
  have he : eqToHom (congrArg NecklaceCode.toSSet (rfl : single d = single d)) ≫ q = q :=
    Category.id_comp q
  exact hm.symm.trans (hz'.trans (h.trans he.symm))

end
end DaggerModels.PartII.JTStationarySingleLift

namespace DaggerModels.PartII.JTRowGraphEndpointCollapse
open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory JTRowGraphNormalForm
open DaggerChosenRigidificationNecklace.NecklaceCode JTMixedGraphRawRefinement
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev graph (W : Source) (d : SimplexCategory) := Graph (ordinaryInput.obj W) d
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {d : SimplexCategory}

/-- Read an original graph coefficient as a map of simplicial sets. -/
def coefficient (G : graph W d) : simplex G.degree ⟶ row W d :=
  SSet.yonedaEquiv.symm G.coefficient

private theorem coefficient_map {G H : graph W d} (u : G ⟶ H) :
    SSet.stdSimplex.map u.operator ≫ coefficient H = coefficient G := by
  unfold coefficient
  rw [← SSet.yonedaEquiv_symm_map]
  exact congrArg SSet.yonedaEquiv.symm u.coefficient

private theorem constant_iff_of_epi {G H : graph W d} (u : G ⟶ H)
    [Epi u.operator] (i : Fin (d.len + 1))
    (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    coefficient G ≫ rowVertex W d i = term (simplex G.degree) ≫ vertexPoint W x ↔
      coefficient H ≫ rowVertex W d i = term (simplex H.degree) ≫ vertexPoint W x := by
  let a := SSet.stdSimplex.{0}.map u.operator
  haveI : IsSplitEpi u.operator := isSplitEpi_of_epi _
  haveI : Epi a := by
    change Epi (SSet.stdSimplex.{0}.map u.operator)
    infer_instance
  have ha : a ≫ coefficient H = coefficient G := coefficient_map u
  have ht : a ≫ term (simplex H.degree) = term (simplex G.degree) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [← ha, Category.assoc, ← ht, Category.assoc]
  exact (cancel_epi a)

/-- Stationarity descends from the entire coefficient of a graph to the
coefficient of its canonical representative over the same raw simplex. -/
theorem normal_endpoint_constant (G : graph W d) (i : Fin (d.len + 1))
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (h : coefficient G ≫ rowVertex W d i = term (simplex G.degree) ≫ vertexPoint W x) :
    coefficient (normal G) ≫ rowVertex W d i =
      term (simplex (normal G).degree) ≫ vertexPoint W x := by
  let u := (supportInclusion (ordinaryInput.obj W) d).app G
  let v := supportToNormal G
  haveI : Epi v.operator := (reduction (support G)).epi
  apply (constant_iff_of_epi v i x).mp
  have hc : coefficient (support G) = SSet.stdSimplex.map u.operator ≫ coefficient G :=
    (coefficient_map u).symm
  rw [hc, Category.assoc, h, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ vertexPoint W x)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)


/-- If the graph uses every parameter vertex, its endpoint is stationary
exactly when that of its canonical representative is stationary. -/
theorem normal_endpoint_constant_iff (G : graph W d)
    (hs : Function.Surjective (JTRowGraphParameterSupport.label G.parameter))
    (i : Fin (d.len + 1)) (x : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    coefficient (normal G) ≫ rowVertex W d i =
      term (simplex (normal G).degree) ≫ vertexPoint W x ↔
    coefficient G ≫ rowVertex W d i = term (simplex G.degree) ≫ vertexPoint W x := by
  let u := (supportInclusion (ordinaryInput.obj W) d).app G
  let v := supportToNormal G
  haveI : Epi v.operator := (reduction (support G)).epi
  haveI : Epi u.operator := by
    apply SimplexCategory.epi_iff_surjective.mpr
    intro j
    obtain ⟨a, ha⟩ := hs j
    exact ⟨JTRowGraphParameterSupport.sourceLabel G.parameter a,
      (JTRowGraphParameterSupport.sourceLabel_inclusion G.parameter a).trans ha⟩
  exact ((constant_iff_of_epi v i x).symm).trans (constant_iff_of_epi u i x)


private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- A raw single bead with a moving endpoint on a representative using every
parameter vertex has no exact identity lift in the original presentation. -/
theorem no_identity_rawLift_of_moving_endpoint
    {W : Source} {d : ℕ}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (G : graph W ⦋d⦌)
    (hs : Function.Surjective (JTRowGraphParameterSupport.label G.parameter))
    (Q : NecklacesOver (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d)
    (hv : (singleIso d).hom ≫ G.value = eqToHom (congrArg NecklaceCode.toSSet hQ.symm) ≫ Q.map)
    (hm : coefficient G ≫ rowVertex W ⦋d⦌ 0 ≠
      term (simplex G.degree) ≫ vertexPoint W x) :
    IsEmpty (JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))).Elements := by
  constructor
  intro u
  obtain ⟨k, f, s, hf, _, he⟩ :=
    JTStationarySingleLift.exists_stationary_graph_of_identity_rawLift Q hQ u
  let H : graph W ⦋d⦌ := ⟨k, SSet.yonedaEquiv (X := row W ⦋d⦌) f, s⟩
  have hH : coefficient H = f := Equiv.symm_apply_apply _ _
  have hVal : (singleIso d).hom ≫ H.value = nativeRawGraph W d k f s := rfl
  have hGH : G.value = H.value := (cancel_epi (singleIso d).hom).mp
    (hv.trans (hVal.trans he).symm)
  have hn : normal G = normal H := (value_eq_iff_normal_eq G H).mp hGH
  apply hm
  apply (normal_endpoint_constant_iff G hs 0 x).mp
  rw [hn]
  exact normal_endpoint_constant H 0 x (hH.symm ▸ hf)


/-- The canonical row graph of the actual raw map of the single bead. -/
def canonicalOfSingle {W : Source} {d : ℕ}
    {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (Q : NecklacesOver (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d) : graph W ⦋d⦌ :=
  JTRowGraphCategory.canonical ((singleIso d).inv ≫
    eqToHom (congrArg NecklaceCode.toSSet hQ.symm) ≫ Q.map)

/-- Exact identity lifts of a single bead exist precisely when both entire
endpoint families of the canonical graph are constant at the ordered endpoints. -/
theorem identity_rawLift_nonempty_iff_canonical
    {W : Source} {d : ℕ} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
    (Q : NecklacesOver (realization.obj (ordinaryInput.obj W)) (rawVertex W x) (rawVertex W y))
    (hQ : Q.code = single d) :
    let G := canonicalOfSingle Q hQ
    Nonempty (JTNativeLiftRawComparison.rawLifts Q (Over.mk (𝟙 Q.code))).Elements ↔
      (coefficient G ≫ rowVertex W ⦋d⦌ 0 =
        term (simplex G.degree) ≫ vertexPoint W x) ∧
      (coefficient G ≫ rowVertex W ⦋d⦌ (Fin.last d) =
        term (simplex G.degree) ≫ vertexPoint W y) := by
  let q := eqToHom (congrArg NecklaceCode.toSSet hQ.symm) ≫ Q.map
  let G := canonicalOfSingle Q hQ
  have hG : G.value = (singleIso d).inv ≫ q := JTRowGraphCategory.canonical_value _
  constructor
  · rintro ⟨u⟩
    obtain ⟨k, f, s, hf₁, hf₂, hv⟩ :=
      JTStationarySingleLift.exists_stationary_graph_of_identity_rawLift Q hQ u
    let H : graph W ⦋d⦌ := ⟨k, SSet.yonedaEquiv (X := row W ⦋d⦌) f, s⟩
    have hc : coefficient H = f := Equiv.symm_apply_apply _ _
    have hh : (singleIso d).hom ≫ H.value = q := hv
    have h : normal H = G := by
      rw [JTRowGraphCategory.normal_eq_canonical]
      apply congrArg JTRowGraphCategory.canonical
      exact (Iso.inv_hom_id_assoc (singleIso d) H.value).symm.trans
        (congrArg ((singleIso d).inv ≫ ·) hh)
    change (coefficient G ≫ rowVertex W ⦋d⦌ 0 =
      term (simplex G.degree) ≫ vertexPoint W x) ∧
      (coefficient G ≫ rowVertex W ⦋d⦌ (Fin.last d) =
        term (simplex G.degree) ≫ vertexPoint W y)
    rw [← h]
    exact ⟨normal_endpoint_constant H 0 x (hc.symm ▸ hf₁),
      normal_endpoint_constant H (Fin.last d) y (hc.symm ▸ hf₂)⟩
  · rintro ⟨hx, hy⟩
    apply JTStationarySingleLift.identity_rawLift_nonempty (coefficient G) G.parameter hx hy Q hQ
    have he : nativeRawGraph W d G.degree (coefficient G) G.parameter =
        (singleIso d).hom ≫ G.value := by
      unfold nativeRawGraph rawGraph coefficient Graph.value
      rw [Equiv.apply_symm_apply]
    rw [he, hG]
    exact Iso.hom_inv_id_assoc _ _


end
end DaggerModels.PartII.JTRowGraphEndpointCollapse
