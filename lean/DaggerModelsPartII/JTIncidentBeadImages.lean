import ChosenNecklaceBeadCoordinates
import ChosenNecklacePointMaps

/-!
An arbitrary simplicial map sends each full source bead simplex into an actual
target bead or the initial point. The factor retains the exact image of every
specified incident source vertex. No endpoint or flag condition is used, and
no functorial choice of target bead is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTIncidentBeadImages

noncomputable section

private abbrev std := SSet.stdSimplex.{0}

private instance : std.Full :=
  inferInstanceAs (uliftYoneda.{0} (C := SimplexCategory)).Full

private theorem bead_vertex {T : NecklaceCode} (B : T.Bead)
    (w : Fin (B.length + 1)) :
    std.map (SimplexCategory.const ⦋0⦌ ⦋B.length⦌ w) ≫ T.beadSimplex B =
      pointAt T (ULift.up (B.embedding w)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map, pointAt_vertex]
  apply T.verticesEquiv.injective
  rw [T.verticesEquiv.apply_symm_apply]
  exact B.beadSimplex_vertex w

private theorem point_piece (U : NecklaceCode) :
    U.pieceι (none : Option U.Bead) =
      SSet.stdSimplex.isTerminalObj₀.from (U.pieces none).toSSet ≫
        pointAt U (ULift.up 0) := by
  apply (cancel_mono U.inclusion).mp
  rw [U.pieceι_inclusion, Category.assoc, pointAt_inclusion]
  apply NatTrans.ext
  funext q x
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with | _ n
  apply SSet.stdSimplex.ext
  intro i
  change x.val i = 0
  have hx := (SSet.stdSimplex.mem_face_iff _ _).mp x.property
  exact Finset.mem_singleton.mp (hx i)

private theorem full_factor {T U : NecklaceCode}
    (f : (T.toSSet : SSet.{0}) ⟶ U.toSSet) (B : T.Bead) :
    (∃ C : U.Bead, ∃ u : ⦋B.length⦌ ⟶ ⦋C.length⦌,
      std.map u ≫ U.beadSimplex C = T.beadSimplex B ≫ f) ∨
    (∃ u : ⦋B.length⦌ ⟶ ⦋0⦌,
      std.map u ≫ pointAt U (ULift.up 0) = T.beadSimplex B ≫ f) := by
  obtain ⟨i, g, hg⟩ := T.map_bead_factors f B
  cases i with
  | none =>
      right
      let u := std.preimage (g ≫ SSet.stdSimplex.isTerminalObj₀.from (U.pieces none).toSSet)
      refine ⟨u, ?_⟩
      rw [show std.map u = _ from std.map_preimage _, Category.assoc, ← point_piece]
      exact hg
  | some C =>
      left
      let u := std.preimage (g ≫ C.faceIso.inv)
      refine ⟨C, u, ?_⟩
      rw [show std.map u = _ from std.map_preimage _]
      change (g ≫ C.faceIso.inv) ≫ (C.faceIso.hom ≫ U.beadι C) = _
      rw [Category.assoc, Iso.inv_hom_id_assoc, ← U.pieceι_some]
      exact hg

/-- An exact full bead factor carries every bead coordinate to the same target coordinate. -/
theorem operator_vertex {T U : NecklaceCode}
    (f : (T.toSSet : SSet.{0}) ⟶ U.toSSet) (B : T.Bead) (C : U.Bead)
    (u : ⦋B.length⦌ ⟶ ⦋C.length⦌)
    (h : std.map u ≫ U.beadSimplex C = T.beadSimplex B ≫ f)
    (w : Fin (B.length + 1)) :
    orderMap f (B.embedding w) = C.embedding (u.toOrderHom w) := by
  have hp : pointAt T (ULift.up (B.embedding w)) ≫ f =
      pointAt U (ULift.up (C.embedding (u.toOrderHom w))) := by
    rw [← bead_vertex B w, Category.assoc, ← h, ← Category.assoc,
      ← std.map_comp, SimplexCategory.const_comp, bead_vertex]
  rw [pointAt_comp] at hp
  have hv := congrArg (fun p : (Δ[0] : SSet.{0}) ⟶ U.toSSet ↦
    (U.verticesEquiv (SSet.yonedaEquiv p)).down) hp
  simpa only [pointAt_vertex, Equiv.apply_symm_apply] using hv

private theorem point_operator_vertex {T U : NecklaceCode}
    (f : (T.toSSet : SSet.{0}) ⟶ U.toSSet) (B : T.Bead)
    (u : ⦋B.length⦌ ⟶ ⦋0⦌)
    (h : std.map u ≫ pointAt U (ULift.up 0) = T.beadSimplex B ≫ f)
    (w : Fin (B.length + 1)) : orderMap f (B.embedding w) = 0 := by
  have hp : pointAt T (ULift.up (B.embedding w)) ≫ f = pointAt U (ULift.up 0) := by
    rw [← bead_vertex B w, Category.assoc, ← h, ← Category.assoc, ← std.map_comp]
    have hu : SimplexCategory.const ⦋0⦌ ⦋B.length⦌ w ≫ u = 𝟙 ⦋0⦌ :=
      Subsingleton.elim _ _
    rw [hu, std.map_id, Category.id_comp]
  rw [pointAt_comp] at hp
  have hv := congrArg (fun p : (Δ[0] : SSet.{0}) ⟶ U.toSSet ↦
    (U.verticesEquiv (SSet.yonedaEquiv p)).down) hp
  simpa only [pointAt_vertex, Equiv.apply_symm_apply] using hv

/-- The full image factor retains the image of the specified incident vertex.
The point alternative is based at that exact image, with no extra map hypotheses. -/
theorem incident_image {T U : NecklaceCode}
    (f : (T.toSSet : SSet.{0}) ⟶ U.toSSet) (B : T.Bead)
    (v : Fin (T.len + 1)) (hv : v ∈ B.interval) :
    (∃ C : U.Bead, ∃ u : ⦋B.length⦌ ⟶ ⦋C.length⦌,
      orderMap f v ∈ C.interval ∧
        std.map u ≫ U.beadSimplex C = T.beadSimplex B ≫ f) ∨
    (∃ u : ⦋B.length⦌ ⟶ ⦋0⦌,
      std.map u ≫ pointAt U (ULift.up (orderMap f v)) = T.beadSimplex B ≫ f) := by
  have hv' : v ∈ Set.range B.embedding := by
    simpa only [Bead.embedding, Finset.range_orderEmbOfFin] using hv
  obtain ⟨w, hw⟩ := hv'
  rcases full_factor f B with ⟨C, u, h⟩ | ⟨u, h⟩
  · left
    refine ⟨C, u, ?_, h⟩
    rw [← hw, operator_vertex f B C u h w]
    exact Finset.orderEmbOfFin_mem C.interval C.card_interval _
  · right
    refine ⟨u, ?_⟩
    have he : orderMap f v = 0 := hw ▸ point_operator_vertex f B u h w
    rw [he]
    exact h

end
end DaggerModels.PartII.JTIncidentBeadImages
