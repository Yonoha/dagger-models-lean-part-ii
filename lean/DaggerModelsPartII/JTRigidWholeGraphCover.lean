import DaggerModelsPartII.JTRigidJointGraphCover

/-!
# A pointwise trivial fibration of the whole graph source

The shared rigid coefficient tests control the joint. Outside the joint,
each actual side keeps its own reference parameter.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRigidWholeGraphCover

open JTJointRelativeParameters (withTime joint_vertices_injective joint_vertices_reflects)
open JTJointRelativeGraphFamily (RawOn native coefficient leftLeg rightLeg jointInclusion
  referenceParameter jointInclusion_left jointInclusion_right reference_left_away
  reference_right_away product_sides_cover)
open JTParametrizedTargetFamilies (Family codes)
open JTTargetIntervalOverMapping (left right whole)
open JTTargetJointMarks (Joint)
open JTNecklaceEndpointCylinder (cylinder)
open JTRigidJointGraphCover (overlapData)
open JTRigidOverlapDiagram (stableAllowed stableAllowed_mapsTo PairwiseFiberAgreement)
open JTCodiscreteParameterPairing (coord)
open JTGraphParameterSourceRestriction (RigidVertex)
open JTExactGraphRelativeExtension (rigidVertex_map exact_graph_of_rigid_agreement)
open JTVertexAssignmentCover (extendAllowed extendAllowed_mapsTo)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj zero
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)

private abbrev product := withTime Q.map J time (native F) (whole Q.code)
private abbrev D := overlapData F j s t

private abbrev allowed :=
  extendAllowed (jointInclusion F j) (referenceParameter F j s t) (stableAllowed (D F j s t))

private theorem allowed_mapsTo {p q : I} (a : p ⟶ q) (v : ((product F).obj p).obj zero) :
    Set.MapsTo ((coefficient (L := L)).map a).toOrderHom (allowed F j s t p v)
      (allowed F j s t q (((product F).map a).app zero v)) :=
  extendAllowed_mapsTo (jointInclusion F j) (referenceParameter F j s t) _
    (joint_vertices_injective Q.map J time (native F) j)
    (joint_vertices_reflects Q.map J time (native F) j)
    (stableAllowed_mapsTo (D F j s t)) a v

/-- The entire original product with all the compatible rigid coefficient choices. -/
abbrev cover := JTVertexAssignmentCover.cover (product F) (coefficient (L := L))
    (allowed F j s t) (allowed_mapsTo F j s t)

abbrev projection : cover F j s t ⟶ product F :=
  JTVertexAssignmentCover.projection _ _ (allowed F j s t) (allowed_mapsTo F j s t)

abbrev parameter : cover F j s t ⟶ coefficient (L := L) ⋙ J :=
  JTVertexAssignmentCover.trace _ _ (allowed F j s t) (allowed_mapsTo F j s t)

/-- The exact joint constraints give a pointwise trivial fibration of the whole source. -/
theorem projection_trivialFibration (h : PairwiseFiberAgreement (D F j s t)) (p : I) :
    trivialFibrations SSet.{0} ((projection F j s t).app p) :=
  JTVertexAssignmentCover.projection_trivialFibration _ _ _ (allowed_mapsTo F j s t)
    (JTVertexAssignmentCover.extendAllowed_nonempty _ _ _
      (joint_vertices_injective Q.map J time (native F) j)
      ((JTRigidOverlapDiagram.stableAllowed_nonempty_iff_pairwise (D F j s t)).mpr h)) p

private abbrev value {p : I} (v : ((product F).obj p).obj zero) :=
  coord ((coefficient (L := L)).obj p) zero (((referenceParameter F j s t).app p).app zero v) 0

section ExactChart

variable (p : I)
private abbrev k := (coefficient (L := L)).obj p
private abbrev T := (codes L).obj p
private abbrev n := time.obj p
private abbrev axis := fst ((T (L := L) p).toSSet) (J.obj (n (time := time) p))

set_option maxHeartbeats 450000 in
private theorem chart_exact {Y U : SSet.{0}}
    (a : (D F j s t).overlap.obj p ⟶ Y) (b : Y ⟶ (product F).obj p)
    (ρ : Y ⟶ J.obj (k (L := L) p))
    (hjoint : a ≫ b = (jointInclusion F j).app p)
    (hinj : Function.Injective (b.app zero))
    (outside : ∀ v, v ∉ Set.range (a.app zero) →
      value F j s t (b.app zero v) = coord (k (L := L) p) zero (ρ.app zero v) 0)
    (rigid : ∀ v c, c ∈ stableAllowed (D F j s t) p v →
      RigidVertex (T (L := L) p) (b ≫ axis (L := L) (time := time) p) (a.app zero v) →
        c = coord (k (L := L) p) zero (ρ.app zero (a.app zero v)) 0)
    (g : U ⟶ (cover F j s t).obj p) (i : U ⟶ Y)
    (h : g ≫ (projection F j s t).app p = i ≫ b) :
    g ≫ lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) =
    i ≫ lift (b ≫ axis (L := L) (time := time) p) ρ ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) := by
  rw [← Category.assoc g, ← Category.assoc i, comp_lift, comp_lift,
    ← Category.assoc g, h, Category.assoc i]
  apply exact_graph_of_rigid_agreement
  intro w hr
  let y := i.app zero w
  let z := ((projection F j s t).app p).app zero (g.app zero w)
  let c := coord (k (L := L) p) zero
    (((parameter F j s t).app p).app zero (g.app zero w)) 0
  change c = coord (k (L := L) p) zero (ρ.app zero y) 0
  have hz : z = b.app zero y := congrFun (NatTrans.congr_app h zero) w
  have hJ (x : (D F j s t).overlap.obj p |>.obj zero) :
      b.app zero (a.app zero x) = ((jointInclusion F j).app p).app zero x :=
    congrFun (NatTrans.congr_app hjoint zero) x
  have hc : c ∈ allowed F j s t p z :=
    JTVertexAssignmentCover.trace_allowed _ _ _ (allowed_mapsTo F j s t) p (g.app zero w)
  have hy : RigidVertex (T (L := L) p) (b ≫ axis (L := L) (time := time) p) y :=
    rigidVertex_map _ i _ w hr
  by_cases hmem : y ∈ Set.range (a.app zero)
  · obtain ⟨x, hx⟩ := hmem
    rw [← hx]
    have hv : ((jointInclusion F j).app p).app zero x = z := by
      rw [← hJ x, hx, hz]
    exact rigid x c (hc.1 x hv) (hx.symm ▸ hy)
  · have hnot : z ∉ Set.range (((jointInclusion F j).app p).app zero) := by
      rintro ⟨x, hx⟩
      exact hmem ⟨x, hinj ((hJ x).trans (hx.trans hz))⟩
    exact (hc.2 hnot).trans ((congrArg (value F j s t) hz).trans (outside y hmem))

private theorem leftChart_exact {U : SSet.{0}}
    (g : U ⟶ (cover F j s t).obj p) (i : U ⟶ (D F j s t).left.obj p)
    (h : g ≫ (projection F j s t).app p = i ≫ (leftLeg F j).app p) :
    g ≫ lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) =
    i ≫ lift ((leftLeg F j).app p ≫ axis (L := L) (time := time) p) (s.app p) ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) :=
  chart_exact F j s t p ((D F j s t).leftInclusion.app p) ((leftLeg F j).app p) (s.app p)
    (NatTrans.congr_app (jointInclusion_left F j) p)
    (JTJointRelativeParameters.left_vertices_injective Q.map J time (native F) j p)
    (reference_left_away F j s t (p := p)) (JTRigidOverlapDiagram.allowed_left_at_rigid (D F j s t) p) g i h

private theorem rightChart_exact {U : SSet.{0}}
    (g : U ⟶ (cover F j s t).obj p) (i : U ⟶ (D F j s t).right.obj p)
    (h : g ≫ (projection F j s t).app p = i ≫ (rightLeg F j).app p) :
    g ≫ lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) =
    i ≫ lift ((rightLeg F j).app p ≫ axis (L := L) (time := time) p) (t.app p) ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) :=
  chart_exact F j s t p ((D F j s t).rightInclusion.app p) ((rightLeg F j).app p) (t.app p)
    (NatTrans.congr_app (jointInclusion_right F j) p)
    (JTJointRelativeParameters.right_vertices_injective Q.map J time (native F) j p)
    (reference_right_away F j s t (p := p)) (JTRigidOverlapDiagram.allowed_right_at_rigid (D F j s t) p) g i h

private theorem mapped_chart {U Y V : SSet.{0}}
    (g : U ⟶ (cover F j s t).obj p) (i : U ⟶ Y)
    (b : Y ⟶ (product F).obj p) (ρ : Y ⟶ J.obj (k (L := L) p))
    (h : g ≫ (projection F j s t).app p = i ≫ b)
    (d : (JTNecklaceEndpointCylinder.value (T (L := L) p)).obj (k (L := L) p) ⟶ V)
    (q : (product F).obj p ⟶ V)
    (hGraph : g ≫ lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) =
      i ≫ lift (b ≫ axis (L := L) (time := time) p) ρ ≫
        (cylinder (T (L := L) p)).app (k (L := L) p))
    (hImage : lift (b ≫ axis (L := L) (time := time) p) ρ ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d = b ≫ q) :
    g ≫ lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d =
        g ≫ (projection F j s t).app p ≫ q := by
  calc
    _ = i ≫ lift (b ≫ axis (L := L) (time := time) p) ρ ≫
        (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d := by
      simpa only [Category.assoc] using congrArg (· ≫ d) hGraph
    _ = i ≫ b ≫ q := congrArg (i ≫ ·) hImage
    _ = _ := by rw [← Category.assoc i, ← h, Category.assoc]

set_option maxHeartbeats 900000 in
/-- If both references have the prescribed image after a common postcomposition,
the full covered graph has precisely that image after its projection. -/
theorem preservesImage {V : SSet.{0}}
    (d : (JTNecklaceEndpointCylinder.value (T (L := L) p)).obj (k (L := L) p) ⟶ V)
    (q : (product F).obj p ⟶ V)
    (hs : lift ((leftLeg F j).app p ≫ axis (L := L) (time := time) p) (s.app p) ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d = (leftLeg F j).app p ≫ q)
    (ht : lift ((rightLeg F j).app p ≫ axis (L := L) (time := time) p) (t.app p) ≫
      (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d = (rightLeg F j).app p ≫ q) :
    lift ((projection F j s t).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j s t).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) ≫ d =
        (projection F j s t).app p ≫ q := by
  apply NatTrans.ext
  funext u w
  induction u using Opposite.rec with
  | op u =>
    induction u using SimplexCategory.rec with
    | h n =>
      let u := op ⦋n⦌
      let π := (projection F j s t).app p
      let v := π.app u w
      let g : (Δ[n] : SSet.{0}) ⟶ (cover F j s t).obj p := SSet.yonedaEquiv.symm w
      rcases product_sides_cover F j p u v with ⟨a, ha⟩ | ⟨a, ha⟩
      · let z : (Δ[n] : SSet.{0}) ⟶ (D F j s t).left.obj p := SSet.yonedaEquiv.symm a
        have hz : g ≫ π = z ≫ (leftLeg F j).app p := by
          apply SSet.yonedaEquiv.injective
          simpa only [SSet.yonedaEquiv_comp, g, z, Equiv.apply_symm_apply] using ha.symm
        have hImage := mapped_chart F j s t p g z _ (s.app p) hz d q
          (leftChart_exact F j s t p g z hz) hs
        simpa only [SSet.yonedaEquiv_comp, g, Equiv.apply_symm_apply] using
          congrArg SSet.yonedaEquiv hImage
      · let z : (Δ[n] : SSet.{0}) ⟶ (D F j s t).right.obj p := SSet.yonedaEquiv.symm a
        have hz : g ≫ π = z ≫ (rightLeg F j).app p := by
          apply SSet.yonedaEquiv.injective
          simpa only [SSet.yonedaEquiv_comp, g, z, Equiv.apply_symm_apply] using ha.symm
        have hImage := mapped_chart F j s t p g z _ (t.app p) hz d q
          (rightChart_exact F j s t p g z hz) ht
        simpa only [SSet.yonedaEquiv_comp, g, Equiv.apply_symm_apply] using
          congrArg SSet.yonedaEquiv hImage

end ExactChart

/-- The whole covered graph retains the exact fixed raw image of both references. -/
theorem rawOn (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t) :
    RawOn F (projection F j s t) (parameter F j s t) := by
  intro p
  exact preservesImage F j s t p
    ((DecoratedCylinderNecklacePresentation.underCocone W x y).app (L.obj p)).right
    (axis (L := L) (time := time) p ≫ (F.collapse.app p).map ≫ Q.map) (hs p) (ht p)

open JTJointRelativeGraphFamily (originalLeft originalRight)

section Original

local notation "S" => originalLeft F j
local notation "R" => originalRight F j

/-- If both references are the actual restrictions of the original graph,
the full cover preserves that graph in the original reduced label itself. -/
theorem originalGraph (p : I) :
    lift ((projection F j S R).app p ≫ axis (L := L) (time := time) p)
      ((parameter F j S R).app p) ≫ (cylinder (T (L := L) p)).app (k (L := L) p) =
        (projection F j S R).app p ≫ lift (axis (L := L) (time := time) p) (F.parameter p) ≫
          (cylinder (T (L := L) p)).app (k (L := L) p) := by
  let v := lift (axis (L := L) (time := time) p) (F.parameter p) ≫
    (cylinder (T (L := L) p)).app (k (L := L) p)
  have h := preservesImage F j S R p (𝟙 _) v
    (by simp only [Category.comp_id, v, ← Category.assoc, comp_lift]; rfl)
    (by simp only [Category.comp_id, v, ← Category.assoc, comp_lift]; rfl)
  simpa only [Category.comp_id, v] using h

end Original

end

end DaggerModels.PartII.JTRigidWholeGraphCover
