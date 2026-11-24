import DaggerModelsPartII.OrdinaryFilteredDwyerKanComparison
import DaggerModelsPartII.OrdinaryCofibrationLocalComparison
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Transfinite propagation of an ordinary comparison

For a natural transformation between colimit-preserving functors, a source
cofibration carries the comparison's weak equivalence from its source to its
target. The resulting intersection property is transfinite stable under the
explicit hypotheses below. No retract or cobase stability of that property
is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty DaggerModels
open DaggerModels.OrdinaryDwyerKanCore

universe v u

namespace DaggerModels.PartII.FunctorComparisonTransfinite

noncomputable section

variable {C : Type u} [Category.{v} C]
variable (F G : C ⥤ SimplicialCat.{0, 0}) (α : F ⟶ G)
variable (Co : MorphismProperty C)
variable [MorphismProperty.IsStableUnderTransfiniteComposition.{0} Co]
variable (hFco : ∀ {X Y : C} (f : X ⟶ Y), Co f →
  DaggerOrdinaryRigidificationCof.ordinaryCofibrations (F.map f))
variable (hGco : ∀ {X Y : C} (f : X ⟶ Y), Co f →
  DaggerOrdinaryRigidificationCof.ordinaryCofibrations (G.map f))

/-- A source cofibration along which comparison weakness propagates. -/
def Q : MorphismProperty C :=
  fun X Y f ↦ Co f ∧ (W (α.app X) → W (α.app Y))

omit [MorphismProperty.IsStableUnderTransfiniteComposition.{0} Co] in
private theorem Q_le_Co : Q F G α Co ≤ Co :=
  fun _ _ _ h ↦ h.1

variable {J : Type} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : C} {i : X ⟶ Y}

include hFco in
private theorem transition_hom_mono_F
    (h : (Q F G α Co).TransfiniteCompositionOfShape J i)
    {j k : J} (β : j ⟶ k) (a b : (F.obj (h.F.obj j)).Obj) :
    Mono ((F.map (h.F.map β)).map a b) := by
  have hCo : Co (h.F.map β) := (h.ofLE (Q_le_Co F G α Co)).mem_map β
  exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
    _ (hFco (h.F.map β) hCo) a b

include hGco in
private theorem transition_hom_mono_G
    (h : (Q F G α Co).TransfiniteCompositionOfShape J i)
    {j k : J} (β : j ⟶ k) (a b : (G.obj (h.F.obj j)).Obj) :
    Mono ((G.map (h.F.map β)).map a b) := by
  have hCo : Co (h.F.map β) := (h.ofLE (Q_le_Co F G α Co)).mem_map β
  exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
    _ (hGco (h.F.map β) hCo) a b

variable [PreservesColimitsOfSize.{0, 0} F] [PreservesColimitsOfSize.{0, 0} G]

include hFco hGco in
/-- Actual comparison weakness propagates from the bottom object to the
colimit of a supplied transfinite Q-diagram. -/
theorem weak_target_of_transfinite
    (h : (Q F G α Co).TransfiniteCompositionOfShape J i)
    (hX : W (α.app X)) : W (α.app Y) := by
  let hmonoF : ∀ {j k : J} (β : j ⟶ k)
      (a b : (F.obj (h.F.obj j)).Obj),
      Mono ((F.map (h.F.map β)).map a b) :=
    fun β a b ↦ transition_hom_mono_F F G α Co hFco h β a b
  let hmonoG : ∀ {j k : J} (β : j ⟶ k)
      (a b : (G.obj (h.F.obj j)).Obj),
      Mono ((G.map (h.F.map β)).map a b) :=
    fun β a b ↦ transition_hom_mono_G F G α Co hGco h β a b
  have hstage : ∀ j : J, W (α.app (h.F.obj j)) := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl := hj.eq_bot
      let e : Arrow.mk (α.app (h.F.obj ⊥)) ≅ Arrow.mk (α.app X) :=
        Arrow.isoMk (F.mapIso h.isoBot) (G.mapIso h.isoBot)
          (α.naturality h.isoBot.hom)
      exact (W.arrow_mk_iso_iff e).2 hX
    | succ j hj hprev =>
      exact (h.map_mem j hj).2 hprev
    | isSuccLimit m hm hprev =>
      let R := (Set.principalSegIio m).monotone.functor
      let c := (Set.principalSegIio m).cocone h.F
      let cF := F.mapCocone c
      let cG := G.mapCocone c
      let η : R ⋙ h.F ⋙ F ⟶ R ⋙ h.F ⋙ G :=
        Functor.whiskerLeft (R ⋙ h.F) α
      have hc : IsColimit c := h.F.isColimitOfIsWellOrderContinuous m hm
      have hlegs : ∀ k : Set.Iio m,
          cF.ι.app k ≫ α.app (h.F.obj m) = η.app k ≫ cG.ι.app k := by
        intro k
        exact α.naturality (h.F.map (homOfLE k.2.le))
      have hmF : ∀ {k l : Set.Iio m} (β : k ⟶ l)
          (a b : ((R ⋙ h.F ⋙ F).obj k).Obj),
          Mono (((R ⋙ h.F ⋙ F).map β).map a b) := by
        intro k l β a b
        exact hmonoF (R.map β) a b
      have hmG : ∀ {k l : Set.Iio m} (β : k ⟶ l)
          (a b : ((R ⋙ h.F ⋙ G).obj k).Obj),
          Mono (((R ⋙ h.F ⋙ G).map β).map a b) := by
        intro k l β a b
        exact hmonoG (R.map β) a b
      letI : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
      exact OrdinaryFilteredDwyerKanComparison.filtered_W_of_colimits η
        (isColimitOfPreserves F hc) (isColimitOfPreserves G hc)
        (α.app (h.F.obj m)) hlegs hmF hmG
        (fun k ↦ hprev k.val k.property)
  let c := Cocone.mk Y h.incl
  let cF := F.mapCocone c
  let cG := G.mapCocone c
  let η : h.F ⋙ F ⟶ h.F ⋙ G := Functor.whiskerLeft h.F α
  have hlegs : ∀ j : J,
      cF.ι.app j ≫ α.app Y = η.app j ≫ cG.ι.app j := by
    intro j
    exact α.naturality (h.incl.app j)
  exact OrdinaryFilteredDwyerKanComparison.filtered_W_of_colimits η
    (isColimitOfPreserves F h.isColimit)
    (isColimitOfPreserves G h.isColimit)
    (α.app Y) hlegs hmonoF hmonoG hstage

include hFco hGco in
/-- The Q-property is closed under every common-universe transfinite shape
provided the original source cofibration class is. -/
theorem Q_transfiniteOfShape :
    (Q F G α Co).IsStableUnderTransfiniteCompositionOfShape J where
  le X Y i hi := by
    obtain ⟨h⟩ := hi
    let hCo : Co.TransfiniteCompositionOfShape J i :=
      h.ofLE (Q_le_Co F G α Co)
    refine ⟨Co.transfiniteCompositionsOfShape_le J i ⟨hCo⟩, ?_⟩
    intro hX
    exact weak_target_of_transfinite F G α Co hFco hGco h hX

include hFco hGco in
/-- Common-universe transfinite stability of Q. This does not assert
retract or cobase stability of Q. -/
theorem Q_transfinite :
    MorphismProperty.IsStableUnderTransfiniteComposition.{0} (Q F G α Co) where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ :=
    Q_transfiniteOfShape F G α Co hFco hGco

end

end DaggerModels.PartII.FunctorComparisonTransfinite
