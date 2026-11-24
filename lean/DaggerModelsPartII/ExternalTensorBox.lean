import DaggerModelsPartII.ReedyBoundaryLifting
import DaggerModelsPartII.RelativeDiagramHom
import DaggerModelsPartII.LocalPushout

/-! Pushout-products of coefficient maps with arbitrary outer simplicial inclusions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

noncomputable section

local instance externalBoxLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance externalBoxColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance externalBoxCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance externalBoxReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

variable {A B : DaggerSSet.{u}} (i : A ⟶ B)

/-- Vary the coefficient of the external tensor along a given coefficient map. -/
def externalTensorCoefficientMap : externalTensor A ⟶ externalTensor B :=
  { app := fun K ↦ (externalTensorWith K).map i
    naturality := by
      intro K L j
      apply NatTrans.ext
      funext n
      exact (sigmaConst.map i).naturality (j.app n) }

private def mappingCoefficientMap : mappingSimplicialSet B ⟶ mappingSimplicialSet A :=
  { app := diagramHomPrecomp i
    naturality := by
      intro W V f
      ext n x : 2
      exact (Category.assoc i x (f.app n)).symm }

private def coefficientParameterLeft : WalkingParallelPair ⥤ SSet.{u} ⥤ ResolutionDiagram.{u} :=
  parallelPair (externalTensorCoefficientMap i) (externalTensorCoefficientMap i)

private def coefficientParameterRight :
    WalkingParallelPairᵒᵖ ⥤ ResolutionDiagram.{u} ⥤ SSet.{u} :=
  walkingParallelPairOpEquiv.inverse ⋙ parallelPair (mappingCoefficientMap i) (mappingCoefficientMap i)

private def coefficientParameterAdjunctionAt (s : WalkingParallelPair) :
    (coefficientParameterLeft i).obj s ⊣ (coefficientParameterRight i).obj (op s) :=
  match s with
  | .zero => externalTensorAdjunction A
  | .one => externalTensorAdjunction B

private def coefficientParameterAdjunction :
    coefficientParameterLeft i ⊣₂ coefficientParameterRight i :=
  ParametrizedAdjunction.mk' (coefficientParameterAdjunctionAt i) (by
    intro s t g K W q
    change WalkingParallelPairHom s t at g
    cases g with
    | left =>
      ext n x : 2
      exact externalTensorAdjunction_natural_in_dagger i K W q n x
    | right =>
      ext n x : 2
      exact externalTensorAdjunction_natural_in_dagger i K W q n x
    | id s =>
      cases s <;>
        change _ = _ ≫ 𝟙 _ <;>
        simp [coefficientParameterLeft, coefficientParameterRight, Category.comp_id])

variable {K L : SSet.{u}} (j : K ⟶ L)

private def externalBoxPushout :
    (coefficientParameterLeft i).PushoutObjObj WalkingParallelPairHom.left j :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The pushout-product of a coefficient map and a map of test simplicial sets. -/
def externalTensorBox := (externalBoxPushout i j).ι

private def externalBoxPullback {W V : ResolutionDiagram.{u}} (f : W ⟶ V) :
    (coefficientParameterRight i).PullbackObjObj WalkingParallelPairHom.left f :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

private theorem externalBoxPullback_π {W V : ResolutionDiagram.{u}} (f : W ⟶ V) :
    (externalBoxPullback i f).π = diagramHomCorner i f := by
  apply pullback.hom_ext
  · exact ((externalBoxPullback i f).π_fst).trans (pullback.lift_fst _ _ _).symm
  · exact ((externalBoxPullback i f).π_snd).trans (pullback.lift_snd _ _ _).symm

/-- Lifts against the external pushout-product are the relative mapping-space lifts. -/
theorem externalTensorBox_hasLiftingProperty_iff {W V : ResolutionDiagram.{u}} (f : W ⟶ V) :
    HasLiftingProperty (externalTensorBox i j) f ↔ HasLiftingProperty j (diagramHomCorner i f) := by
  rw [← externalBoxPullback_π]
  exact (coefficientParameterAdjunction i).hasLiftingProperty_iff
    (externalBoxPushout i j) (externalBoxPullback i f)

/-- An external pushout-product of a dagger cofibration and a simplicial monomorphism
is a Reedy cofibration. -/
theorem externalTensorBox_cofibration [Mono j] (hi : cofibrations DaggerSSet.{u} i) :
    reedyCofibrations (externalTensorBox i j) := by
  change cofibrations ResolutionDiagram.{u} _
  rw [← llp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u})]
  intro W V f hf
  apply (externalTensorBox_hasLiftingProperty_iff i j f).mpr
  apply diagramHomCorner_mono_lifting
  change (reedyFibrations ⊓ reedyWeakEquivalences) f at hf
  rw [reedyFibrations_inf_weakEquivalences] at hf
  exact fun n ↦ hasLiftingProperty_of_wfs i _ hi (hf n)

/-- Tensoring a simplicial monomorphism with a cofibrant coefficient gives a Reedy cofibration. -/
theorem externalTensor_map_cofibration [Mono j] [IsCofibrant A] :
    reedyCofibrations ((externalTensor A).map j) := by
  change cofibrations ResolutionDiagram.{u} _
  rw [← llp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u})]
  intro W V f hf
  apply ((externalTensorAdjunction A).hasLiftingProperty_iff j f).mpr
  have hI : SSet.modelCategoryQuillen.I.rlp ((mappingSimplicialSet A).map f) := by
    intro X Y k hk
    obtain ⟨n⟩ := hk
    apply diagramHomPostcomp_boundary_lifting
    change (reedyFibrations ⊓ reedyWeakEquivalences) f at hf
    rw [reedyFibrations_inf_weakEquivalences] at hf
    exact hasLiftingProperty_of_wfs _ _ (mem_cofibrations (initial.to A)) (hf n)
  rw [SSet.modelCategoryQuillen.I_rlp_eq_monomorphisms_rlp] at hI
  exact hI j (show Mono j from inferInstance)

/-- If tensoring the outer map with both coefficients gives local equivalences,
so does its pushout-product with the coefficient map, provided the first tensor
map is a Reedy cofibration. -/
theorem externalTensorBox_localEquivalence
    (hA : (reedyCofibrations ⊓ resolutionLocalEquivalences) ((externalTensor A).map j))
    (hB : resolutionLocalEquivalences ((externalTensor B).map j)) :
    resolutionLocalEquivalences (externalTensorBox i j) := by
  let sq := externalBoxPushout i j
  have hl : (reedyCofibrations ⊓ resolutionLocalEquivalences) sq.inl :=
    (reedyCofibrations ⊓ resolutionLocalEquivalences).of_isPushout sq.isPushout hA
  apply resolutionLocalEquivalences.of_precomp sq.inl _ hl.2
  rw [externalTensorBox, Functor.PushoutObjObj.inl_ι]
  exact hB

private theorem evaluationHomEquiv_outer {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌)
    {D : DaggerSSet.{u}} {W : ResolutionDiagram.{u}}
    (f : (externalTensor D).obj Δ[n] ⟶ W) :
    (evaluationAdjunction m).homEquiv D W ((externalTensor D).map (SSet.stdSimplex.map s) ≫ f) =
      (evaluationAdjunction n).homEquiv D W f ≫ W.map s.op := by
  simp only [evaluationAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  change SSet.yonedaEquiv ((externalTensorAdjunction D).homEquiv Δ[m] W
    ((externalTensor D).map (SSet.stdSimplex.map s) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  let z := (externalTensorAdjunction D).homEquiv Δ[n] W f
  exact (uliftYonedaEquiv_naturality z s.op).symm

/-- Lifting against the terminal map tests lifting against the actual evaluation
operator when the outer map is a map of representables. -/
theorem externalTensorBox_hasLiftingProperty_terminal_iff {m n : ℕ} (s : ⦋m⦌ ⟶ ⦋n⦌)
    (W : ResolutionDiagram.{u}) :
    HasLiftingProperty (externalTensorBox i (SSet.stdSimplex.map s)) (terminal.from W) ↔
      HasLiftingProperty i (W.map s.op) := by
  let sq := externalBoxPushout i (SSet.stdSimplex.map s)
  let eₘA := (evaluationAdjunction m).homEquiv A W
  let eₘB := (evaluationAdjunction m).homEquiv B W
  let eₙA := (evaluationAdjunction n).homEquiv A W
  let eₙB := (evaluationAdjunction n).homEquiv B W
  have coeffₘ (f : (externalTensor B).obj Δ[m] ⟶ W) :
      eₘA ((externalTensorWith Δ[m]).map i ≫ f) = i ≫ eₘB f :=
    (evaluationAdjunction m).homEquiv_naturality_left i f
  have coeffₙ (f : (externalTensor B).obj Δ[n] ⟶ W) :
      eₙA ((externalTensorWith Δ[n]).map i ≫ f) = i ≫ eₙB f :=
    (evaluationAdjunction n).homEquiv_naturality_left i f
  change HasLiftingProperty sq.ι (terminal.from W) ↔ _
  constructor
  · intro h
    letI := h
    constructor
    intro a b w
    let a' := eₙA.symm a
    let b' := eₘB.symm b
    have comm : (externalTensorWith Δ[m]).map i ≫ b' =
        (externalTensor A).map (SSet.stdSimplex.map s) ≫ a' := by
      apply eₘA.injective
      rw [coeffₘ, show eₘA ((externalTensor A).map (SSet.stdSimplex.map s) ≫ a') =
        eₙA a' ≫ W.map s.op from evaluationHomEquiv_outer s a']
      simpa only [a', b', Equiv.apply_symm_apply] using w.w.symm
    let c := sq.isPushout.desc b' a' comm
    have w' : CommSq c sq.ι (terminal.from W) (terminal.from _) :=
      ⟨terminal.hom_ext _ _⟩
    have hl : (externalTensor B).map (SSet.stdSimplex.map s) ≫ w'.lift = b' := by
      change ((coefficientParameterLeft i).obj WalkingParallelPair.one).map
        (SSet.stdSimplex.map s) ≫ w'.lift = _
      rw [← sq.inl_ι, Category.assoc, w'.fac_left]
      exact sq.isPushout.inl_desc _ _ _
    have hr : (externalTensorWith Δ[n]).map i ≫ w'.lift = a' := by
      change ((coefficientParameterLeft i).map WalkingParallelPairHom.left).app Δ[n] ≫ w'.lift = _
      rw [← sq.inr_ι, Category.assoc, w'.fac_left]
      exact sq.isPushout.inr_desc _ _ _
    refine CommSq.HasLift.mk' ⟨eₙB w'.lift, ?_, ?_⟩
    · rw [← coeffₙ, hr]
      exact Equiv.apply_symm_apply eₙA a
    · change (evaluationAdjunction n).homEquiv B W w'.lift ≫ W.map s.op = b
      rw [← evaluationHomEquiv_outer s, hl]
      exact Equiv.apply_symm_apply eₘB b
  · intro h
    letI := h
    constructor
    intro a b w
    let a' := eₙA (sq.inr ≫ a)
    let b' := eₘB (sq.inl ≫ a)
    have w' : CommSq a' i (W.map s.op) b' := by
      constructor
      change eₙA (sq.inr ≫ a) ≫ W.map s.op = i ≫ eₘB (sq.inl ≫ a)
      rw [show eₙA (sq.inr ≫ a) ≫ W.map s.op =
        eₘA ((externalTensor A).map (SSet.stdSimplex.map s) ≫ sq.inr ≫ a) from
          (evaluationHomEquiv_outer s _).symm, ← coeffₘ, ← Category.assoc, ← Category.assoc]
      exact congrArg eₘA (congrArg (fun f ↦ f ≫ a) sq.isPushout.w.symm)
    let d := eₙB.symm w'.lift
    refine CommSq.HasLift.mk' ⟨d, ?_, terminal.hom_ext _ _⟩
    apply sq.isPushout.hom_ext
    · change sq.inl ≫ sq.ι ≫ d = _
      rw [sq.inl_ι_assoc]
      apply eₘB.injective
      change (evaluationAdjunction m).homEquiv B W
        ((externalTensor B).map (SSet.stdSimplex.map s) ≫ d) = b'
      rw [evaluationHomEquiv_outer]
      change eₙB (eₙB.symm w'.lift) ≫ W.map s.op = b'
      rw [Equiv.apply_symm_apply]
      exact w'.fac_right
    · change sq.inr ≫ sq.ι ≫ d = _
      rw [sq.inr_ι_assoc]
      apply eₙA.injective
      change eₙA ((externalTensorWith Δ[n]).map i ≫ d) = _
      rw [coeffₙ, show eₙB d = w'.lift from Equiv.apply_symm_apply _ _]
      exact w'.fac_left

end

end DaggerModels.PartII
