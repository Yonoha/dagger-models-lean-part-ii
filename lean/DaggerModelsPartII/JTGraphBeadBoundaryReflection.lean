import DaggerModelsPartII.JTGraphBoundaryReflection
import ChosenNecklaceBeadMaps

/-!
# Boundary reflection on full beads of the graph source
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphBeadBoundaryReflection

open JTNecklaceEndpointCylinder
open JTGraphBoundaryReflection

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter

/-- Boundary reflection is required only on the full bead generators of the source. -/
def ReflectsBeadBoundary {S T L : NecklaceCode} (g : S ⟶ T) (f : T ⟶ L) : Prop :=
  ∀ b : S.Bead,
    (∃ a : B.obj (op ⦋b.length⦌),
      (endpointInclusion L).app (op ⦋b.length⦌) a =
        SSet.yonedaEquiv (S.beadSimplex b ≫ (g ≫ f).map)) →
      ∃ a : B.obj (op ⦋b.length⦌),
        (endpointInclusion T).app (op ⦋b.length⦌) a =
          SSet.yonedaEquiv (S.beadSimplex b ≫ g.map)

theorem reflectsBeadBoundary_of_reflectsBoundary {S T L : NecklaceCode}
    (g : S ⟶ T) (f : T ⟶ L) (hf : ReflectsBoundary f) :
    ReflectsBeadBoundary g f := by
  intro b h
  have hx : SSet.yonedaEquiv (S.beadSimplex b ≫ (g ≫ f).map) =
      f.map.app (op ⦋b.length⦌)
        (SSet.yonedaEquiv (S.beadSimplex b ≫ g.map)) := by
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
    rfl
  obtain ⟨a, ha⟩ := h
  exact hf _ _ ⟨a, ha.trans hx⟩

private theorem boundary_value (T : NecklaceCode) (k : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (a : B.obj q) (u : (J.obj k).obj q) :
    ((cylinder T).app k).app q ((endpointInclusion T).app q a, u) =
      ((boundary T).app k).app q a := by
  exact congrFun (NatTrans.congr_app (isPushout T k).w q) (a, u)

private def firstPieceIso (S : NecklaceCode) :
    (Δ[0] : SSet.{0}) ≅ (S.pieces none).toSSet :=
  SSet.stdSimplex.faceSingletonIso 0

private theorem firstPiece_eq_first (S : NecklaceCode) :
    (firstPieceIso S).hom ≫ S.pieceι none =
      pointAt S (ULift.up 0) := by
  apply SSet.yonedaEquiv.injective
  let u := SSet.yonedaEquiv (firstPieceIso S).hom
  have hu : SSet.stdSimplex.obj₀Equiv u.val = 0 := by
    have h := (SSet.stdSimplex.mem_face_iff {0} u.val).mp u.property 0
    simpa using h
  have hi : S.inclusion.app (op ⦋0⦌) ((S.pieceι none).app (op ⦋0⦌) u) =
      u.val := congrFun (NatTrans.congr_app (S.pieceι_inclusion none) (op ⦋0⦌)) u
  have hv : S.verticesEquiv ((S.pieceι none).app (op ⦋0⦌) u) = ULift.up 0 := by
    apply ULift.ext
    rw [S.verticesEquiv_down, hi]
    exact hu
  rw [SSet.yonedaEquiv_comp, pointAt_vertex]
  exact S.verticesEquiv.injective (hv.trans (S.verticesEquiv.apply_symm_apply _).symm)

private theorem eq_on_bead {S T L : NecklaceCode} (g : S ⟶ T) (f : T ⟶ L)
    (hf : ReflectsBeadBoundary g f) (k : SimplexCategory)
    (s t : S.toSSet ⟶ J.obj k)
    (hEq : lift (g ≫ f).map s ≫ (cylinder L).app k =
      lift (g ≫ f).map t ≫ (cylinder L).app k) (b : S.Bead) :
    S.beadSimplex b ≫ lift g.map s ≫ (cylinder T).app k =
      S.beadSimplex b ≫ lift g.map t ≫ (cylinder T).app k := by
  let q := op ⦋b.length⦌
  let l := S.beadSimplex b
  let zs := SSet.yonedaEquiv (l ≫ lift (g ≫ f).map s)
  let zt := SSet.yonedaEquiv (l ≫ lift (g ≫ f).map t)
  have hz : ((cylinder L).app k).app q zs = ((cylinder L).app k).app q zt := by
    simpa only [zs, zt, SSet.yonedaEquiv_comp, Category.assoc] using
      congrArg SSet.yonedaEquiv (congrArg (fun u ↦ l ≫ u) hEq)
  obtain hs | ⟨a, ha⟩ :=
    JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary L k b.length zs zt hz
  · have hs' : l ≫ s = l ≫ t := by
      apply SSet.yonedaEquiv.injective
      simpa only [zs, zt, SSet.yonedaEquiv_comp, Category.assoc, lift_snd] using hs
    have he : l ≫ lift g.map s = l ≫ lift g.map t := by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst]
      · simpa only [Category.assoc, lift_snd] using hs'
    simpa only [Category.assoc] using congrArg (fun u ↦ u ≫ (cylinder T).app k) he
  · have ha' : (endpointInclusion L).app q a =
        SSet.yonedaEquiv (l ≫ (g ≫ f).map) := by
      simpa only [zs, SSet.yonedaEquiv_comp, Category.assoc, lift_fst] using ha
    obtain ⟨c, hc⟩ := hf b ⟨a, ha'⟩
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp] at hc ⊢
    change ((cylinder T).app k).app q
        (g.map.app q (SSet.yonedaEquiv l), s.app q (SSet.yonedaEquiv l)) =
      ((cylinder T).app k).app q
        (g.map.app q (SSet.yonedaEquiv l), t.app q (SSet.yonedaEquiv l))
    rw [← hc]
    change ((cylinder T).app k).app q
        ((endpointInclusion T).app q c, SSet.yonedaEquiv (l ≫ s)) =
      ((cylinder T).app k).app q
        ((endpointInclusion T).app q c, SSet.yonedaEquiv (l ≫ t))
    exact (boundary_value T k q c (SSet.yonedaEquiv (l ≫ s))).trans
      (boundary_value T k q c (SSet.yonedaEquiv (l ≫ t))).symm

private theorem eq_on_first {S T : NecklaceCode} (g : S ⟶ T)
    (k : SimplexCategory) (s t : S.toSSet ⟶ J.obj k) :
    (firstPieceIso S).hom ≫ S.pieceι none ≫ lift g.map s ≫ (cylinder T).app k =
      (firstPieceIso S).hom ≫ S.pieceι none ≫ lift g.map t ≫ (cylinder T).app k := by
  have hfirst (U : NecklaceCode) :
      SSet.boundary₁.ι₀ ≫ endpointInclusion U = pointAt U (ULift.up 0) := by
    change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc U.first U.last = _
    rw [SSet.boundary₁.ι₀_desc]
    rfl
  have hG : (firstPieceIso S).hom ≫ S.pieceι none ≫ g.map =
      SSet.boundary₁.ι₀ ≫ endpointInclusion T := by
    rw [← Category.assoc, firstPiece_eq_first, ← hfirst S,
      Category.assoc, endpointInclusion_natural]
  apply NatTrans.ext
  funext q
  funext z
  let x := ((firstPieceIso S).hom ≫ S.pieceι none).app q z
  have hx : g.map.app q x =
      (endpointInclusion T).app q (SSet.boundary₁.ι₀.app q z) := by
    exact congrFun (NatTrans.congr_app hG q) z
  change ((cylinder T).app k).app q (g.map.app q x, s.app q x) =
    ((cylinder T).app k).app q (g.map.app q x, t.app q x)
  rw [hx]
  exact (boundary_value T k q _ (s.app q x)).trans
    (boundary_value T k q _ (t.app q x)).symm

/-- Full-bead reflection suffices to reflect equality of the complete reduced
graph maps, including sources with repeated endpoint vertices. -/
theorem graph_eq_of_reflectsBeadBoundary {S T L : NecklaceCode} (g : S ⟶ T)
    (f : T ⟶ L) (hf : ReflectsBeadBoundary g f) (k : SimplexCategory)
    (s t : S.toSSet ⟶ J.obj k)
    (hEq : lift (g ≫ f).map s ≫ (cylinder L).app k =
      lift (g ≫ f).map t ≫ (cylinder L).app k) :
    lift g.map s ≫ (cylinder T).app k =
      lift g.map t ≫ (cylinder T).app k := by
  let A := lift g.map s ≫ (cylinder T).app k
  let A' := lift g.map t ≫ (cylinder T).app k
  apply NatTrans.ext
  funext q
  induction q using Opposite.rec with | op q =>
  induction q using SimplexCategory.rec with | h d =>
    funext z
    let F := SSet.yonedaEquiv.symm z
    obtain ⟨i, h, hfac⟩ := S.simplex_factors_piece F
    have hF : F ≫ A = F ≫ A' := by
      cases i with
      | none =>
        let r := h ≫ (firstPieceIso S).inv
        have hr : r ≫ (firstPieceIso S).hom ≫ S.pieceι none = F := by
          simp only [r, Category.assoc, Iso.inv_hom_id_assoc]
          exact hfac
        have he := eq_on_first g k s t
        have he' := congrArg (fun u ↦ r ≫ u) he
        simpa only [Category.assoc, ← hr, A, A'] using he'
      | some b =>
        let r := h ≫ b.faceIso.inv
        have hr : r ≫ S.beadSimplex b = F := by
          simp only [r, NecklaceCode.beadSimplex, Category.assoc,
            Iso.inv_hom_id_assoc]
          rw [← S.pieceι_some]
          exact hfac
        have he := eq_on_bead g f hf k s t hEq b
        have he' := congrArg (fun u ↦ r ≫ u) he
        simpa only [Category.assoc, ← hr, A, A'] using he'
    have hz := congrArg SSet.yonedaEquiv hF
    simpa only [SSet.yonedaEquiv_comp, F, Equiv.apply_symm_apply, A, A'] using hz

end

end DaggerModels.PartII.JTGraphBeadBoundaryReflection
