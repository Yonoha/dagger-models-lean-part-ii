import DaggerModelsPartII.OrdinaryRigidificationTensorWeak
import DaggerModelsPartII.OrdinaryRigidifiedLatchingWeak
import DaggerModelsPartII.OrdinaryDwyerKanPushoutComparison
import DaggerModelsPartII.OrdinaryFilteredDwyerKanComparison
import DaggerModelsPartII.OrdinaryCofibrationLocalComparison
import OriginalDiagonalFiltration
import DiagonalSuccessorPushout
import DiagonalAttachingData
import OrdinaryRigidificationCof
import Mathlib.CategoryTheory.Category.ULift

/-!
# Ordinary rigidified diagonal weakness from every literal row

The proof uses the original subcomplex filtration of the actual diagonal,
the actual latching-boundary attaching union, and the original successor
pushouts. It concludes the original ordinary DK predicate for the literal
rigidification image of `diagMap`, without a Joyal-reflection or ordinary
model-category hypothesis.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MorphismProperty
open DaggerModels DaggerOrdinaryRigidificationCof
open DaggerModels.OrdinaryDwyerKanCore
open DaggerBisimplicialDiagonal
open DaggerOriginalDiagonalStages

universe u

namespace DaggerModels.OrdinaryRigidifiedDiagonalWeak

noncomputable section

private local instance : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits

private local instance : PreservesColimitsOfSize.{u, u} C.{u} :=
  OrdinaryRigidification.rigidificationCoherentNerveAdjunction.leftAdjoint_preservesColimits

private local instance : BraidedCategory SSet.{u} :=
  BraidedCategory.ofCartesianMonoidalCategory

/-- Braiding moves the original ordinary DK product theorem to the
right simplicial factor, preserving the literal arrow. -/
theorem rigidification_whiskerRight_W
    {A B : SSet.{u}} (f : A ⟶ B)
    (hf : W (C.map f)) (K : SSet.{u}) :
    W (C.map (f ▷ K)) := by
  let e : Arrow.mk (C.map (f ▷ K)) ≅ Arrow.mk (C.map (K ◁ f)) :=
    Arrow.isoMk (C.mapIso (β_ A K)) (C.mapIso (β_ B K)) (by
      change C.map (β_ A K).hom ≫ C.map (K ◁ f) =
        C.map (f ▷ K) ≫ C.map (β_ B K).hom
      rw [← C.map_comp, ← C.map_comp]
      exact congrArg C.map (BraidedCategory.braiding_naturality_left f K).symm)
  exact (W.arrow_mk_iso_iff e).2
    (DaggerModels.PartII.OrdinaryRigidificationTensorWeak.rigidification_whiskerLeft_W
      K f hf)

private theorem tensorRight_W {A B : SSet.{u}} (f : A ⟶ B)
    (hf : W (C.map f)) (K : SSet.{u}) :
    W (C.map (f ⊗ₘ 𝟙 K)) := by
  simpa [tensorHom_def] using
    rigidification_whiskerRight_W f hf K

/-- The exact latching-times-simplex union row-times-boundary comparison
is weak after rigidification. -/
theorem attaching_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ m : ℕ, W (C.map (η.app (op ⦋m⦌))))
    (n : ℕ) :
    W (C.map (attachingMap η n)) := by
  let S := latching B n
  let S' := latching B' n
  let T := SSet.boundary n
  let f := η.app (op ⦋n⦌)
  let l := latchingMap η n
  have hl : W (C.map l) :=
    OrdinaryRigidifiedLatchingWeak.latching_W η hrow n
  have hA : W (C.map (l ⊗ₘ 𝟙 (T : SSet.{u}))) :=
    tensorRight_W l hl T
  have hB : W (C.map (f ⊗ₘ 𝟙 (T : SSet.{u}))) :=
    tensorRight_W f (hrow n) T
  have hD : W (C.map (l ⊗ₘ 𝟙 (Δ[n] : SSet.{u}))) :=
    tensorRight_W l hl (Δ[n] : SSet.{u})
  have sq : IsPushout
      (C.map (S.ι ▷ (T : SSet.{u})))
      (C.map ((S : SSet.{u}) ◁ T.ι))
      (C.map (SSet.Subcomplex.unionProd.ι₁ S T))
      (C.map (SSet.Subcomplex.unionProd.ι₂ S T)) :=
    (SSet.Subcomplex.unionProd.isPushout S T).map C
  have sq' : IsPushout
      (C.map (S'.ι ▷ (T : SSet.{u})))
      (C.map ((S' : SSet.{u}) ◁ T.ι))
      (C.map (SSet.Subcomplex.unionProd.ι₁ S' T))
      (C.map (SSet.Subcomplex.unionProd.ι₂ S' T)) :=
    (SSet.Subcomplex.unionProd.isPushout S' T).map C
  have hmono : Mono (S.ι ▷ (T : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    rw [mono_iff_injective]
    rintro ⟨x, k⟩ ⟨y, l⟩ h
    change (x.val, k) = (y.val, l) at h
    have hk : k = l :=
      congrArg (fun p : (B.obj (op ⦋n⦌)).obj q × (T : SSet.{u}).obj q ↦ p.2) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) hk
  have hmono' : Mono (S'.ι ▷ (T : SSet.{u})) := by
    rw [NatTrans.mono_iff_mono_app]
    intro q
    rw [mono_iff_injective]
    rintro ⟨x, k⟩ ⟨y, l⟩ h
    change (x.val, k) = (y.val, l) at h
    have hk : k = l :=
      congrArg (fun p : (B'.obj (op ⦋n⦌)).obj q × (T : SSet.{u}).obj q ↦ p.2) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) hk
  letI : Mono (S.ι ▷ (T : SSet.{u})) := hmono
  letI : Mono (S'.ι ▷ (T : SSet.{u})) := hmono'
  have hcof : ordinaryCofibrations (C.map (S.ι ▷ (T : SSet.{u}))) :=
    mono_rigidification_cofibration _
  have hcof' : ordinaryCofibrations (C.map (S'.ι ▷ (T : SSet.{u}))) :=
    mono_rigidification_cofibration _
  have h₁ : C.map (S.ι ▷ (T : SSet.{u})) ≫
      C.map (f ⊗ₘ 𝟙 (T : SSet.{u})) =
      C.map (l ⊗ₘ 𝟙 (T : SSet.{u})) ≫
        C.map (S'.ι ▷ (T : SSet.{u})) := by
    simp only [← C.map_comp]
    congr 1
  have h₂ : C.map ((S : SSet.{u}) ◁ T.ι) ≫
      C.map (l ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) =
      C.map (l ⊗ₘ 𝟙 (T : SSet.{u})) ≫
        C.map ((S' : SSet.{u}) ◁ T.ι) := by
    simp only [← C.map_comp]
    congr 1
  have h₃ : C.map (SSet.Subcomplex.unionProd.ι₁ S T) ≫
      C.map (attachingMap η n) =
      C.map (f ⊗ₘ 𝟙 (T : SSet.{u})) ≫
        C.map (SSet.Subcomplex.unionProd.ι₁ S' T) := by
    simp only [← C.map_comp]
    congr 1
  have h₄ : C.map (SSet.Subcomplex.unionProd.ι₂ S T) ≫
      C.map (attachingMap η n) =
      C.map (l ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫
        C.map (SSet.Subcomplex.unionProd.ι₂ S' T) := by
    simp only [← C.map_comp]
    congr 1
  exact OrdinaryDwyerKanPushoutComparison.weak_of_pushoutComparison
    sq sq' hcof hcof'
    (C.map (l ⊗ₘ 𝟙 (T : SSet.{u})))
    (C.map (f ⊗ₘ 𝟙 (T : SSet.{u})))
    (C.map (l ⊗ₘ 𝟙 (Δ[n] : SSet.{u})))
    (C.map (attachingMap η n))
    h₁ h₂ h₃ h₄ hA hB hD

/-- The exact zero stage is initial, so its comparison is an isomorphism. -/
theorem stage_zero_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B') :
    W (C.map (stageMap η 0)) := by
  have hB : IsInitial (stage B 0 : SSet.{u}) :=
    (SSet.Subcomplex.isInitialBot
      (X := DaggerBisimplicialDiagonal.diag B)).ofIso
      (DaggerOriginalDiagonalStages.stageZeroIso B).symm
  have hB' : IsInitial (stage B' 0 : SSet.{u}) :=
    (SSet.Subcomplex.isInitialBot
      (X := DaggerBisimplicialDiagonal.diag B')).ofIso
      (DaggerOriginalDiagonalStages.stageZeroIso B').symm
  have h : stageMap η 0 = (hB.uniqueUpToIso hB').hom :=
    hB.hom_ext _ _
  rw [h]
  exact W.of_isIso _

/-- Every original finite diagonal stage comparison is ordinary DK weak.
The successor step uses the literal cell-first pushout. -/
theorem stage_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ m : ℕ, W (C.map (η.app (op ⦋m⦌))))
    (n : ℕ) :
    W (C.map (stageMap η n)) := by
  induction n with
  | zero => exact stage_zero_W η
  | succ n ih =>
      have sq : IsPushout
          (C.map (attaching B n).ι)
          (C.map (DaggerOriginalDiagonalSuccessor.attachingToStage B n))
          (C.map (DaggerOriginalDiagonalSuccessor.rowEvalStage B n))
          (C.map (DaggerOriginalDiagonalSuccessor.transition B n)) :=
        (DaggerOriginalDiagonalSuccessor.successorIsPushout B n).map C
      have sq' : IsPushout
          (C.map (attaching B' n).ι)
          (C.map (DaggerOriginalDiagonalSuccessor.attachingToStage B' n))
          (C.map (DaggerOriginalDiagonalSuccessor.rowEvalStage B' n))
          (C.map (DaggerOriginalDiagonalSuccessor.transition B' n)) :=
        (DaggerOriginalDiagonalSuccessor.successorIsPushout B' n).map C
      have hcof : ordinaryCofibrations (C.map (attaching B n).ι) :=
        mono_rigidification_cofibration _
      have hcof' : ordinaryCofibrations (C.map (attaching B' n).ι) :=
        mono_rigidification_cofibration _
      have h₁ : C.map (attaching B n).ι ≫
          C.map (η.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) =
          C.map (attachingMap η n) ≫ C.map (attaching B' n).ι := by
        simpa only [← C.map_comp] using
          congrArg C.map (attachingMap_ι η n)
      have h₂ : C.map (DaggerOriginalDiagonalSuccessor.attachingToStage B n) ≫
          C.map (stageMap η n) =
          C.map (attachingMap η n) ≫
            C.map (DaggerOriginalDiagonalSuccessor.attachingToStage B' n) := by
        simpa only [← C.map_comp] using
          congrArg C.map (DaggerOriginalDiagonalSuccessor.attachingToStage_naturality η n)
      have h₃ : C.map (DaggerOriginalDiagonalSuccessor.rowEvalStage B n) ≫
          C.map (stageMap η (n + 1)) =
          C.map (η.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})) ≫
            C.map (DaggerOriginalDiagonalSuccessor.rowEvalStage B' n) := by
        simpa only [← C.map_comp] using
          congrArg C.map (DaggerOriginalDiagonalSuccessor.rowEvalStage_naturality η n)
      have h₄ : C.map (DaggerOriginalDiagonalSuccessor.transition B n) ≫
          C.map (stageMap η (n + 1)) =
          C.map (stageMap η n) ≫
            C.map (DaggerOriginalDiagonalSuccessor.transition B' n) := by
        simpa only [← C.map_comp] using
          congrArg C.map (DaggerOriginalDiagonalSuccessor.transition_naturality η n)
      exact OrdinaryDwyerKanPushoutComparison.weak_of_pushoutComparison
        sq sq' hcof hcof'
        (C.map (attachingMap η n))
        (C.map (η.app (op ⦋n⦌) ⊗ₘ 𝟙 (Δ[n] : SSet.{u})))
        (C.map (stageMap η n))
        (C.map (stageMap η (n + 1)))
        h₁ h₂ h₃ h₄
        (attaching_W η hrow n)
        (tensorRight_W (η.app (op ⦋n⦌)) (hrow n) (Δ[n] : SSet.{u}))
        ih

/-- The literal diagonal comparison is ordinary DK weak after the original
rigidification whenever every horizontal row comparison is. -/
theorem diagonal_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ n : ℕ, W (C.map (η.app (op ⦋n⦌)))) :
    W (C.map (DaggerBisimplicialDiagonal.diagMap η)) := by
  let J := AsSmall.{u} ℕ
  let e : J ≌ ℕ := (AsSmall.equiv (C := ℕ)).symm
  let R : J ⥤ ℕ := AsSmall.down
  let F := R ⋙ DaggerOriginalDiagonalStages.filtration B
  let F' := R ⋙ DaggerOriginalDiagonalStages.filtration B'
  let c₀ := (DaggerOriginalDiagonalStages.filtrationCocone B).whisker R
  let c₀' := (DaggerOriginalDiagonalStages.filtrationCocone B').whisker R
  let c := C.mapCocone c₀
  let c' := C.mapCocone c₀'
  let θ₀ : F ⟶ F' :=
    Functor.whiskerLeft R (DaggerOriginalDiagonalStages.filtrationNatTrans η)
  let θ : F ⋙ C ⟶ F' ⋙ C := Functor.whiskerRight θ₀ C
  have hc₀ : IsColimit c₀ :=
    (DaggerOriginalDiagonalStages.filtrationIsColimit B).whiskerEquivalence e
  have hc₀' : IsColimit c₀' :=
    (DaggerOriginalDiagonalStages.filtrationIsColimit B').whiskerEquivalence e
  have hlegs : ∀ r : J,
      c.ι.app r ≫ C.map (DaggerBisimplicialDiagonal.diagMap η) =
        θ.app r ≫ c'.ι.app r := by
    intro r
    change C.map ((DaggerOriginalDiagonalStages.filtrationCocone B).ι.app (ULift.down r)) ≫
        C.map (DaggerBisimplicialDiagonal.diagMap η) =
      C.map ((DaggerOriginalDiagonalStages.filtrationNatTrans η).app (ULift.down r)) ≫
        C.map ((DaggerOriginalDiagonalStages.filtrationCocone B').ι.app (ULift.down r))
    rw [← C.map_comp, ← C.map_comp]
    exact congrArg C.map (DaggerOriginalDiagonalStages.filtration_leg η (ULift.down r))
  have hmF : ∀ {r s : J} (φ : r ⟶ s)
      (a b : ((F ⋙ C).obj r).Obj),
      Mono (((F ⋙ C).map φ).map a b) := by
    intro r s φ a b
    haveI : Mono (F.map φ) :=
      DaggerOriginalDiagonalStages.filtration_map_mono B (R.map φ)
    exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
      _ (mono_rigidification_cofibration (F.map φ)) a b
  have hmF' : ∀ {r s : J} (φ : r ⟶ s)
      (a b : ((F' ⋙ C).obj r).Obj),
      Mono (((F' ⋙ C).map φ).map a b) := by
    intro r s φ a b
    haveI : Mono (F'.map φ) :=
      DaggerOriginalDiagonalStages.filtration_map_mono B' (R.map φ)
    exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
      _ (mono_rigidification_cofibration (F'.map φ)) a b
  exact OrdinaryFilteredDwyerKanComparison.filtered_W_of_colimits θ
    (isColimitOfPreserves C hc₀)
    (isColimitOfPreserves C hc₀')
    (C.map (DaggerBisimplicialDiagonal.diagMap η))
    hlegs hmF hmF' (fun r ↦ stage_W η hrow (ULift.down r))

end

end DaggerModels.OrdinaryRigidifiedDiagonalWeak
