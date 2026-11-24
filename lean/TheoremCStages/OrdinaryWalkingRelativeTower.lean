import OrdinaryWalkingRelativeExtension
import OrdinaryWalkingFirstEdgeCalibration
import NatSubcomplexGluing

/-!
# Relative extension across the entire alternating walking filtration

The first edge of every attaching horn is the original first-stage edge.
Selected relative left outer-horn fillers therefore extend a compatible
lift one stage at a time. The checked increasing-subcomplex colimit glues
these choices to one map on the original walking parameter. Both the
initial-stage restriction and the prescribed base map are exact equations.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerOriginalInnerHornFillers
open DaggerOriginalOrdinaryKanCoreEdgeMembership

namespace DaggerModels.PartII.OrdinaryWalkingRelativeTower

open OrdinaryWalkingAlternatingFiltration
open OrdinaryWalkingAlternatingExhaustion
open OrdinaryWalkingAlternatingPushout
open OrdinaryWalkingRelativeExtension
open OrdinaryWalkingFirstEdgeCalibration

noncomputable section

private abbrev Walking := GroupoidSimplex.parameter.obj ⦋1⦌

private def S (n : ℕ) : Walking.Subcomplex := stage (n + 1)

private theorem S_monotone : Monotone S :=
  fun _ _ h ↦ stage_monotone (Nat.add_le_add_right h 1)

private theorem S_cover : (⨆ n : ℕ, S n) = ⊤ :=
  (stage_monotone.iSup_nat_add 1).trans iSup_stage_eq_top

private def chainMap (n m : ℕ) (h : n ≤ m) :
    (S n : SSet) ⟶ (S m : SSet) :=
  SSet.Subcomplex.homOfLE (S_monotone h)

private def firstMap (n : ℕ) : (stage 1 : SSet) ⟶ (S n : SSet) :=
  chainMap 0 n (Nat.zero_le n)

private theorem firstMap_zero : firstMap 0 = 𝟙 _ := by
  simp only [firstMap, chainMap, S, SSet.Subcomplex.homOfLE_refl]

private theorem firstMap_succ (n : ℕ) :
    firstMap (n + 1) = firstMap n ≫ stageInclusion n := rfl

private structure Partial {C D : SSet} (p : C ⟶ D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D) (n : ℕ) where
  map : (S n : SSet) ⟶ C
  restrict : firstMap n ≫ map = u
  base : map ≫ p = (S n).ι ≫ β

private def partialZero {C D : SSet} (p : C ⟶ D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (w : u ≫ p = (stage 1).ι ≫ β) : Partial p u β 0 where
  map := u
  restrict := by rw [firstMap_zero, Category.id_comp]
  base := w

private noncomputable def partialStep {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u)))
    (n : ℕ) (a : Partial p u β n) :
    {b : Partial p u β (n + 1) // stageInclusion n ≫ b.map = a.map} := by
  have hfirst :
      DaggerModels.PartII.RelativeLeftOuterHornGeometry.firstEdgeInclusion n ≫
        (hornToPrevious n ≫ a.map) = stageAttachmentLift 1 ≫ u := by
    calc
      _ = (DaggerModels.PartII.RelativeLeftOuterHornGeometry.firstEdgeInclusion n ≫
            hornToPrevious n) ≫ a.map := (Category.assoc _ _ _).symm
      _ = (stageAttachmentLift 1 ≫ firstMap n) ≫ a.map := by
        exact congrArg (fun z ↦ z ≫ a.map) (firstEdge_hornToPrevious n)
      _ = stageAttachmentLift 1 ≫ (firstMap n ≫ a.map) :=
        Category.assoc _ _ _
      _ = stageAttachmentLift 1 ≫ u := by rw [a.restrict]
  have he' : edgeIsInvertible C
      (SSet.yonedaEquiv
        (DaggerModels.PartII.RelativeLeftOuterHornGeometry.firstEdgeInclusion n ≫
          (hornToPrevious n ≫ a.map))) := by
    rw [hfirst]
    exact he
  have wstep : a.map ≫ p = stageInclusion n ≫
      ((stage (n + 2)).ι ≫ β) := by
    calc
      a.map ≫ p = (S n).ι ≫ β := a.base
      _ = (stageInclusion n ≫ (stage (n + 2)).ι) ≫ β := by
        rw [stageInclusion, SSet.Subcomplex.homOfLE_ι]
        rfl
      _ = stageInclusion n ≫ ((stage (n + 2)).ι ≫ β) :=
        Category.assoc _ _ _
  let hex := extend_one_stage p hp hC hD n a.map
    ((stage (n + 2)).ι ≫ β) wstep he'
  let g := Classical.choose hex
  have hg := (Classical.choose_spec hex).1
  have hbase := (Classical.choose_spec hex).2
  have hrestrict : firstMap (n + 1) ≫ g = u := by
    calc
      firstMap (n + 1) ≫ g =
          (firstMap n ≫ stageInclusion n) ≫ g := by
        rw [firstMap_succ]
      _ = firstMap n ≫ (stageInclusion n ≫ g) := Category.assoc _ _ _
      _ = firstMap n ≫ a.map := by rw [hg]
      _ = u := a.restrict
  exact ⟨⟨g, hrestrict, hbase⟩, hg⟩

private noncomputable def partialLift {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (w : u ≫ p = (stage 1).ι ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u)))
    (n : ℕ) : Partial p u β n :=
  Nat.rec (partialZero p u β w)
    (fun j a ↦ (partialStep p hp hC hD u β he j a).val) n

private theorem partial_compat {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (w : u ≫ p = (stage 1).ι ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u)))
    (n : ℕ) :
    stageInclusion n ≫ (partialLift p hp hC hD u β w he (n + 1)).map =
      (partialLift p hp hC hD u β w he n).map :=
  (partialStep p hp hC hD u β he n
    (partialLift p hp hC hD u β w he n)).property

private theorem compatible {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (w : u ≫ p = (stage 1).ι ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u))) :
    ∀ n m (h : n ≤ m),
      chainMap n m h ≫ (partialLift p hp hC hD u β w he m).map =
        (partialLift p hp hC hD u β w he n).map := by
  intro n m h
  induction m, h using Nat.le_induction with
  | base =>
      simp only [chainMap, SSet.Subcomplex.homOfLE_refl,
        Category.id_comp]
  | succ m h ih =>
      calc
        chainMap n (m + 1) (Nat.le_succ_of_le h) ≫
            (partialLift p hp hC hD u β w he (m + 1)).map =
          (chainMap n m h ≫ stageInclusion m) ≫
            (partialLift p hp hC hD u β w he (m + 1)).map := by rfl
        _ = chainMap n m h ≫
            (stageInclusion m ≫
              (partialLift p hp hC hD u β w he (m + 1)).map) :=
          Category.assoc _ _ _
        _ = chainMap n m h ≫
            (partialLift p hp hC hD u β w he m).map := by
          rw [partial_compat p hp hC hD u β w he m]
        _ = (partialLift p hp hC hD u β w he n).map := ih

private theorem hom_ext_of_cover {X Y : SSet} (T : ℕ → X.Subcomplex)
    (hcover : (⨆ n, T n) = ⊤) {f g : X ⟶ Y}
    (h : ∀ n, (T n).ι ≫ f = (T n).ι ≫ g) : f = g := by
  apply NatTrans.ext
  funext q
  funext x
  have hx : x ∈ (⨆ n, T n).obj q := by
    rw [hcover]
    trivial
  simp only [SSet.Subcomplex.iSup_obj, Set.mem_iUnion] at hx
  obtain ⟨n, hn⟩ := hx
  have hpoint := congrFun (NatTrans.congr_app (h n) q) ⟨x, hn⟩
  change f.app q x = g.app q x at hpoint
  exact hpoint

/-- A relative extension over the entire original walking parameter,
starting from its literal first alternating stage. -/
theorem extend_entire_walking {C D : SSet} (p : C ⟶ D)
    (hp : DaggerNativeInnerHornFactorization.innerFibrations p)
    (hC : innerHornFillers C) (hD : innerHornFillers D)
    (u : (stage 1 : SSet) ⟶ C) (β : Walking ⟶ D)
    (w : u ≫ p = (stage 1).ι ≫ β)
    (he : edgeIsInvertible C
      (SSet.yonedaEquiv (stageAttachmentLift 1 ≫ u))) :
    ∃ l : Walking ⟶ C, (stage 1).ι ≫ l = u ∧ l ≫ p = β := by
  let F : ∀ n, (S n : SSet) ⟶ C :=
    fun n ↦ (partialLift p hp hC hD u β w he n).map
  have hcompat : ∀ n m (h : n ≤ m),
      SSet.Subcomplex.homOfLE (S_monotone h) ≫ F m = F n :=
    compatible p hp hC hD u β w he
  let l : Walking ⟶ C :=
    NatSubcomplexGluing.desc S S_monotone S_cover F hcompat
  refine ⟨l, ?_, ?_⟩
  · have h₀ := NatSubcomplexGluing.ι_desc
      S S_monotone S_cover F hcompat 0
    change (stage 1).ι ≫ l = u at h₀
    exact h₀
  · apply hom_ext_of_cover S S_cover
    intro n
    calc
      (S n).ι ≫ (l ≫ p) = ((S n).ι ≫ l) ≫ p :=
        (Category.assoc _ _ _).symm
      _ = F n ≫ p := by
        exact congrArg (fun z ↦ z ≫ p)
          (NatSubcomplexGluing.ι_desc S S_monotone S_cover F hcompat n)
      _ = (S n).ι ≫ β := (partialLift p hp hC hD u β w he n).base

#print axioms extend_entire_walking

end

end DaggerModels.PartII.OrdinaryWalkingRelativeTower
