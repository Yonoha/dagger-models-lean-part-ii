import DaggerModelsPartII.JTGraphJointSeparation
import DaggerModelsPartII.JTNecklaceCylinderConnector
import Mathlib.CategoryTheory.Limits.Types.Pushouts

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphNondegenerateBead

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter
private abbrev term (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

theorem bead_length_pos {T : NecklaceCode} (b : T.Bead) : 0 < b.length := by
  have h := b.lt
  simp only [Bead.length, Bead.interval, Fin.card_Icc]
  change b.left.val < b.right.val at h
  omega

private theorem endpoint_first (T : NecklaceCode) :
    SSet.boundary₁.ι₀ ≫ endpointInclusion T = pointAt T (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₀_desc]
  rfl

private theorem endpoint_last (T : NecklaceCode) :
    SSet.boundary₁.ι₁ ≫ endpointInclusion T =
      pointAt T (ULift.up (Fin.last T.len)) := by
  change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last = _
  rw [SSet.boundary₁.ι₁_desc]
  rfl

/-- In every degree, the ordered boundary contains exactly the two constant
endpoint simplices. -/
theorem boundary_iff_constant (T : NecklaceCode) (d : ℕ)
    (p : (Δ[d] : SSet.{0}) ⟶ T.toSSet) :
    (∃ a : B.obj (op ⦋d⦌),
      (endpointInclusion T).app (op ⦋d⦌) a = SSet.yonedaEquiv p) ↔
      (p = term (Δ[d] : SSet.{0}) ≫ pointAt T (ULift.up 0) ∨
        p = term (Δ[d] : SSet.{0}) ≫
          pointAt T (ULift.up (Fin.last T.len))) := by
  constructor
  · rintro ⟨a, ha⟩
    have sq := (SSet.boundary₁.isPushout.{0}).map
      (SSet.evaluation.obj (op ⦋d⦌))
    obtain ⟨v, hv⟩ | ⟨v, hv⟩ := Types.eq_or_eq_of_isPushout sq a
    · left
      change SSet.boundary₁.ι₀.app (op ⦋d⦌) v = a at hv
      apply SSet.yonedaEquiv.injective
      calc
        SSet.yonedaEquiv p = (endpointInclusion T).app (op ⦋d⦌) a := ha.symm
        _ = (endpointInclusion T).app (op ⦋d⦌)
            (SSet.boundary₁.ι₀.app (op ⦋d⦌) v) := by rw [hv]
        _ = SSet.yonedaEquiv
            (SSet.yonedaEquiv.symm v ≫ SSet.boundary₁.ι₀ ≫ endpointInclusion T) := by
          rw [← Category.assoc, SSet.yonedaEquiv_comp,
            SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        _ = SSet.yonedaEquiv
            (term (Δ[d] : SSet.{0}) ≫ pointAt T (ULift.up 0)) := by
          rw [endpoint_first,
            show SSet.yonedaEquiv.symm v = term (Δ[d] : SSet.{0}) from
              SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
    · right
      change SSet.boundary₁.ι₁.app (op ⦋d⦌) v = a at hv
      apply SSet.yonedaEquiv.injective
      calc
        SSet.yonedaEquiv p = (endpointInclusion T).app (op ⦋d⦌) a := ha.symm
        _ = (endpointInclusion T).app (op ⦋d⦌)
            (SSet.boundary₁.ι₁.app (op ⦋d⦌) v) := by rw [hv]
        _ = SSet.yonedaEquiv
            (SSet.yonedaEquiv.symm v ≫ SSet.boundary₁.ι₁ ≫ endpointInclusion T) := by
          rw [← Category.assoc, SSet.yonedaEquiv_comp,
            SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
        _ = SSet.yonedaEquiv
            (term (Δ[d] : SSet.{0}) ≫
              pointAt T (ULift.up (Fin.last T.len))) := by
          rw [endpoint_last,
            show SSet.yonedaEquiv.symm v = term (Δ[d] : SSet.{0}) from
              SSet.stdSimplex.isTerminalObj₀.hom_ext _ _]
  · intro h
    rcases h with h | h
    · refine ⟨SSet.yonedaEquiv (term (Δ[d] : SSet.{0}) ≫ SSet.boundary₁.ι₀), ?_⟩
      rw [← SSet.yonedaEquiv_comp, Category.assoc, endpoint_first, ← h]
    · refine ⟨SSet.yonedaEquiv (term (Δ[d] : SSet.{0}) ≫ SSet.boundary₁.ι₁), ?_⟩
      rw [← SSet.yonedaEquiv_comp, Category.assoc, endpoint_last, ← h]

/-- A positive-dimensional nondegenerate simplex cannot be a constant point. -/
theorem nondegenerate_not_constant {X : SSet.{0}} {d : ℕ}
    (hd : 0 < d) (p : (Δ[d] : SSet.{0}) ⟶ X)
    (hp : SSet.yonedaEquiv p ∈ X.nonDegenerate d)
    (x : (Δ[0] : SSet.{0}) ⟶ X) :
    p ≠ term (Δ[d] : SSet.{0}) ≫ x := by
  intro h
  haveI : Mono x := SSet.stdSimplex.isTerminalObj₀.mono_from x
  have hzero : SSet.yonedaEquiv (term (Δ[d] : SSet.{0})) ∈
      (Δ[0] : SSet.{0}).nonDegenerate d := by
    apply (SSet.nonDegenerate_iff_of_mono x _).mp
    rw [h] at hp
    simpa only [SSet.yonedaEquiv_comp] using hp
  have hstrict := (SSet.stdSimplex.mem_nonDegenerate_iff_strictMono _).mp hzero
  have h01 : (0 : Fin (d + 1)) < 1 := by
    have hm : 1 % (d + 1) = 1 := Nat.mod_eq_of_lt (by omega)
    simp [Fin.lt_def, hm]
  have hbad := hstrict h01
  have heq : (SSet.yonedaEquiv (term (Δ[d] : SSet.{0}))) 0 =
      (SSet.yonedaEquiv (term (Δ[d] : SSet.{0}))) 1 :=
    by apply Fin.ext; omega
  exact (lt_irrefl _ (heq ▸ hbad))

/-- A positive nondegenerate reduced-cylinder bead has horizontal value
outside the ordered endpoint boundary. -/
theorem graph_nondegenerate_bead_not_boundary {T L : NecklaceCode}
    (f : T ⟶ L) (k : SimplexCategory) (s : T.toSSet ⟶ J.obj k)
    (b : T.Bead) (hd : 0 < b.length)
    (hnd : SSet.yonedaEquiv
        (T.beadSimplex b ≫ (lift f.map s ≫ (cylinder L).app k)) ∈
      ((value L).obj k).nonDegenerate b.length) :
    ¬ ∃ a : B.obj (op ⦋b.length⦌),
      (endpointInclusion L).app (op ⦋b.length⦌) a =
        SSet.yonedaEquiv (T.beadSimplex b ≫ f.map) := by
  intro hboundary
  let q := T.beadSimplex b
  let z := q ≫ (lift f.map s ≫ (cylinder L).app k)
  have hLift : q ≫ lift f.map s = lift (q ≫ f.map) (q ≫ s) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst]
    · simp only [Category.assoc, lift_snd]
  have hz : SSet.yonedaEquiv z ∈ ((value L).obj k).nonDegenerate b.length := hnd
  rcases (boundary_iff_constant L b.length (q ≫ f.map)).mp hboundary with
    hfirst | hlast
  · let a : (Δ[b.length] : SSet.{0}) ⟶ B :=
      term (Δ[b.length] : SSet.{0}) ≫ SSet.boundary₁.ι₀
    have ha : a ≫ endpointInclusion L = q ≫ f.map := by
      dsimp only [a]
      rw [Category.assoc, endpoint_first]
      exact hfirst.symm
    have hcollapse := JTNecklaceCylinderConnector.boundary_collapse L k a (q ≫ s)
    have hconstant : z =
        term (Δ[b.length] : SSet.{0}) ≫
          (SSet.boundary₁.ι₀ ≫ (boundary L).app k) := by
      calc
        z = lift (q ≫ f.map) (q ≫ s) ≫ (cylinder L).app k := by
          dsimp only [z]
          rw [← Category.assoc, hLift]
        _ = lift (a ≫ endpointInclusion L) (q ≫ s) ≫ (cylinder L).app k := by
          rw [ha]
        _ = a ≫ (boundary L).app k := hcollapse
        _ = _ := by dsimp only [a]; rw [Category.assoc]
    exact nondegenerate_not_constant hd z hz _ hconstant
  · let a : (Δ[b.length] : SSet.{0}) ⟶ B :=
      term (Δ[b.length] : SSet.{0}) ≫ SSet.boundary₁.ι₁
    have ha : a ≫ endpointInclusion L = q ≫ f.map := by
      dsimp only [a]
      rw [Category.assoc, endpoint_last]
      exact hlast.symm
    have hcollapse := JTNecklaceCylinderConnector.boundary_collapse L k a (q ≫ s)
    have hconstant : z =
        term (Δ[b.length] : SSet.{0}) ≫
          (SSet.boundary₁.ι₁ ≫ (boundary L).app k) := by
      calc
        z = lift (q ≫ f.map) (q ≫ s) ≫ (cylinder L).app k := by
          dsimp only [z]
          rw [← Category.assoc, hLift]
        _ = lift (a ≫ endpointInclusion L) (q ≫ s) ≫ (cylinder L).app k := by
          rw [ha]
        _ = a ≫ (boundary L).app k := hcollapse
        _ = _ := by dsimp only [a]; rw [Category.assoc]
    exact nondegenerate_not_constant hd z hz _ hconstant

end

end DaggerModels.PartII.JTGraphNondegenerateBead
