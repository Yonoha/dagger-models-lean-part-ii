import DaggerModelsPartII.OrdinaryUniversalLocalCobase
import DaggerModelsPartII.OrdinaryFilteredLocalComparison
import DaggerModelsPartII.OrdinaryTransfiniteHomMonicity
import DaggerModelsPartII.OrdinaryLocalCobaseRetract
import OriginalTransfinitePushoutDataRecovered
import TransfinitePushoutColimit

/-!
# Transfinite closure of the universal ordinary local cobase class

The actual basechange transfinite record gives the second diagram and every
pushout transition square. Successor local comparisons follow from the
universal cobase property. At proper limits and at the final colimit, the
ordinary filtered Hom comparison applies to the actual supplied cocones;
all transition Hom monomorphisms come from the previously proved transfinite
closure of the original local Hom monomorphism class.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryTransfiniteLocalCobase

noncomputable section

open OrdinaryUniversalLocalCobase

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {C B : SimplicialCat.{u, u}} {i : C ⟶ B}

/-- Every transition of a transfinite `U` record has monic original Hom maps,
including non-successor transitions. -/
private theorem transition_localHomMono
    (h : U.TransfiniteCompositionOfShape J i)
    {j k : J} (α : j ⟶ k) :
    localHomMono (h.F.map α) :=
  (h.ofLE U_le_localHomMono).mem_map α

/-- The generic actual basechange record retains `U` on every successor
transition because each target transition is a supplied cobase square. -/
private def basechangeU
    {C' B' : SimplicialCat.{u, u}}
    (h : U.TransfiniteCompositionOfShape J i)
    (F : C ⟶ C') [HasPushoutsAlong F]
    (f' : B ⟶ B') (i' : C' ⟶ B')
    (sq : IsPushout F i i' f') :
    U.TransfiniteCompositionOfShape J i' where
  __ := DaggerTransfinitePushoutData.basechange
    h.toTransfiniteCompositionOfShape F f' i' sq
  map_mem j hj := by
    have hs := DaggerTransfinitePushoutData.basechange_transitionSquare
      h.toTransfiniteCompositionOfShape F f' i' sq
      j (Order.succ j) (Order.le_succ j)
    exact U.of_isPushout hs (h.map_mem j hj)

/-- A supplied cobase of the full ordinary transfinite arrow preserves the
local geometric comparison on every Hom, with the actual final map `f'`. -/
theorem cobase_local_of_transfinite
    {C' B' : SimplicialCat.{u, u}}
    (h : U.TransfiniteCompositionOfShape J i)
    (F : C ⟶ C') (f' : B ⟶ B') (i' : C' ⟶ B')
    (sq : IsPushout F i i' f')
    (hF : LocalGeometric F) : LocalGeometric f' := by
  letI : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  let h0 : CategoryTheory.TransfiniteCompositionOfShape J i :=
    h.toTransfiniteCompositionOfShape
  let h' : U.TransfiniteCompositionOfShape J i' :=
    basechangeU h F f' i' sq
  have hdiagram : h'.F = DaggerTransfinitePushoutData.diagram h0 F :=
    DaggerTransfinitePushoutData.basechange_diagram h0 F f' i' sq
  have hmonoSource : ∀ {j k : J} (α : j ⟶ k)
      (a b : (h.F.obj j).Obj), Mono ((h.F.map α).map a b) := by
    intro j k α a b
    exact transition_localHomMono h α a b
  have hmonoTarget : ∀ {j k : J} (α : j ⟶ k)
      (a b : ((DaggerTransfinitePushoutData.diagram h0 F).obj j).Obj),
      Mono (((DaggerTransfinitePushoutData.diagram h0 F).map α).map a b) := by
    intro j k α a b
    have hm : localHomMono (h'.F.map α) := transition_localHomMono h' α
    rw [hdiagram] at hm
    exact hm a b
  have hstage : ∀ j : J, LocalGeometric
      ((DaggerTransfinitePushoutData.eta h0 F).app j) := by
    intro j
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl := hj.eq_bot
      let e : Arrow.mk ((DaggerTransfinitePushoutData.eta h0 F).app ⊥) ≅
          Arrow.mk F :=
        Arrow.isoMk h.isoBot (DaggerTransfinitePushoutData.botIso h0 F)
          (DaggerTransfinitePushoutData.bot_eta h0 F).symm
      exact OrdinaryLocalCobaseRetract.local_of_retract (Retract.ofIso e) hF
    | succ j hj hprev =>
      have hs := DaggerTransfinitePushoutData.transitionSquare h0 F
        (homOfLE (Order.le_succ j))
      exact (U_le_BaseLocal _ (h.map_mem j hj))
        ((DaggerTransfinitePushoutData.eta h0 F).app j)
        ((DaggerTransfinitePushoutData.diagram h0 F).map
          (homOfLE (Order.le_succ j)))
        ((DaggerTransfinitePushoutData.eta h0 F).app (Order.succ j))
        hs hprev
    | isSuccLimit m hm hprev =>
      let R := (Set.principalSegIio m).monotone.functor
      let c := (Set.principalSegIio m).cocone h.F
      let d := (Set.principalSegIio m).cocone
        (DaggerTransfinitePushoutData.diagram h0 F)
      let ηm : R ⋙ h.F ⟶ R ⋙ DaggerTransfinitePushoutData.diagram h0 F :=
        Functor.whiskerLeft R (DaggerTransfinitePushoutData.eta h0 F)
      have hc : IsColimit c := h.F.isColimitOfIsWellOrderContinuous m hm
      have hd : IsColimit d := DaggerTransfinitePushoutData.limitIsColimit h0 F m hm
      have hlegs : ∀ k : Set.Iio m,
          c.ι.app k ≫ (DaggerTransfinitePushoutData.eta h0 F).app m =
            ηm.app k ≫ d.ι.app k := by
        intro k
        exact (DaggerTransfinitePushoutData.eta h0 F).naturality
          (homOfLE k.2.le)
      have hmonoC : ∀ {k l : Set.Iio m} (α : k ⟶ l)
          (a b : ((R ⋙ h.F).obj k).Obj),
          Mono (((R ⋙ h.F).map α).map a b) := by
        intro k l α a b
        exact hmonoSource (R.map α) a b
      have hmonoD : ∀ {k l : Set.Iio m} (α : k ⟶ l)
          (a b : ((R ⋙ DaggerTransfinitePushoutData.diagram h0 F).obj k).Obj),
          Mono (((R ⋙ DaggerTransfinitePushoutData.diagram h0 F).map α).map a b) := by
        intro k l α a b
        exact hmonoTarget (R.map α) a b
      letI : Nonempty (Set.Iio m) := ⟨⟨⊥, hm.bot_lt⟩⟩
      intro a b
      exact OrdinaryFilteredLocalComparison.filtered_local_of_colimits
        ηm hc hd ((DaggerTransfinitePushoutData.eta h0 F).app m)
        hlegs hmonoC hmonoD
        (fun k p q ↦ hprev k.val k.property p q) a b
  have hlegsFinal : ∀ j : J,
      h.incl.app j ≫ f' =
        (DaggerTransfinitePushoutData.eta h0 F).app j ≫
          (DaggerTransfinitePushoutData.incl h0 F f' i' sq).app j := by
    intro j
    exact (DaggerTransfinitePushoutData.eta_incl h0 F f' i' sq j).symm
  intro a b
  exact OrdinaryFilteredLocalComparison.filtered_local_of_colimits
    (DaggerTransfinitePushoutData.eta h0 F)
    h.isColimit
    (DaggerTransfinitePushoutData.finalIsColimit h0 F f' i' sq)
    f' hlegsFinal hmonoSource hmonoTarget
    (fun j p q ↦ hstage j p q) a b

/-- The universal ordinary local cobase class is closed under each actual
common-universe transfinite shape. -/
instance U_transfiniteOfShape :
    U.{u}.IsStableUnderTransfiniteCompositionOfShape J where
  le C B i hi := by
    let h := hi.some
    apply (DaggerICellLocalComparison.universalCobase_iff _ i).2
    intro C' B' F f' i' sq
    letI : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
      SimplicialCat.SemanticColimit.simplicialCatHasColimits
    let h' : U.TransfiniteCompositionOfShape J i' :=
      basechangeU h F f' i' sq
    constructor
    · exact OriginalOrdinaryHomTransfinite.localHomMono_of_transfinite
        h'.toTransfiniteCompositionOfShape
        (fun j hj ↦ U_le_localHomMono _ (h'.map_mem j hj))
    · intro D PD G j Gplus sqG hG
      exact cobase_local_of_transfinite h' G Gplus j sqG hG

/-- The universal ordinary local cobase class is transfinite-stable at the
common universe. -/
instance U_transfinite :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u} U.{u} where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ := inferInstance

end

end DaggerModels.OrdinaryTransfiniteLocalCobase
