import DaggerModelsPartII.SourceResolutionTower
import DaggerModelsPartII.TransfiniteCommaIteration

/-! Existence of compatible source resolutions for every continuous well-ordered diagram. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe u

namespace DaggerModels.PartII

noncomputable section

local instance towerConstructionLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance towerConstructionColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance towerConstructionCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance towerConstructionReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

private abbrev Frames := SimplexCategoryᵒᵖ ⥤ ResolutionDiagram.{u}ᵒᵖ

local instance towerConstructionFrameModel : ModelCategory Frames.{u} :=
  simplicialReedyModelCategory ResolutionDiagram.{u}ᵒᵖ

private theorem degreewise_of_reedy_trivialCofibration {W V : Frames.{u}} {f : W ⟶ V}
    (hf : trivialCofibrations Frames.{u} f) (j : SimplexCategoryᵒᵖ) :
    trivialFibrations ResolutionDiagram.{u} (f.app j).unop := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
    ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  change (reedyLatchingProperty (cofibrations ResolutionDiagram.{u}ᵒᵖ) ⊓
    simplicialReedyWeakEquivalences ResolutionDiagram.{u}ᵒᵖ) f at hf
  rw [simplicialReedyCofibrations_inf_weakEquivalences] at hf
  have h := reedyTrivialLatching_eval f hf n
  rw [trivialCofibrations_op] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- Any continuous diagram of Part II objects admits a continuous inverse
tower of pointwise source resolutions, with Reedy fibration successors. -/
theorem sourceResolutionTower_exists {J : Type u} [LinearOrder J] [SuccOrder J]
    [OrderBot J] [WellFoundedLT J] (X : J ⥤ ResolutionDiagram.{u})
    [X.IsWellOrderContinuous] : Nonempty (SourceResolutionTower X) := by
  let K : J ⥤ Frames.{u}ᵒᵖ := (X.op ⋙ Functor.const SimplexCategoryᵒᵖ).rightOp
  let P : MorphismProperty Frames.{u}ᵒᵖ := (trivialCofibrations Frames.{u}).op
  let Q : MorphismProperty Frames.{u}ᵒᵖ := (fibrations Frames.{u}).op
  letI : P.RespectsIso := inferInstanceAs ((trivialCofibrations Frames.{u}).op.RespectsIso)
  letI : Q.RespectsIso := inferInstanceAs ((fibrations Frames.{u}).op.RespectsIso)
  let R := cosimplicialResolution (X.obj ⊥)
  have hs (j : J) (_ : ¬IsMax j) (A : Frames.{u}ᵒᵖ) (a : A ⟶ K.obj j) :
      ∃ (B : Frames.{u}ᵒᵖ) (i : A ⟶ B) (b : B ⟶ K.obj (Order.succ j)),
        i ≫ b = a ≫ K.map (homOfLE (Order.le_succ j)) ∧ Q i ∧ P b := by
    let d := factorizationData (trivialCofibrations Frames.{u}) (fibrations Frames.{u})
      (a ≫ K.map (homOfLE (Order.le_succ j))).unop
    exact ⟨op d.Z, d.p.op, d.i.op, Quiver.Hom.unop_inj d.fac, d.hp, d.hi⟩
  let ε : K ⟶ (Functor.const J).obj (⊤_ Frames.{u}ᵒᵖ) :=
    { app := fun j ↦ terminal.from (K.obj j)
      naturality := fun _ _ _ ↦ terminal.hom_ext _ _ }
  obtain ⟨F, a, hcont, ⟨e₀⟩, ha₀, ha⟩ :=
    exists_continuous_over K ε P Q R.augmentationOp.op R.augmentationOp_mem hs
  let G := F.leftOp
  let a' : X.op ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ G := a.leftOp
  letI : F.IsWellOrderContinuous := hcont
  letI : G.rightOp.IsWellOrderContinuous := hcont
  have hfib (j : J) : IsFibrant (G.obj (op j)) := by
    have h₀' : IsFibrant (G.obj (op ⊥)) := by
      letI := R.fibrantOp
      let e : G.obj (op ⊥) ≅ R.oppositeDiagram := e₀.unop.symm
      letI : Fibration e.hom := (fibration_iff _).mpr ((fibrations Frames.{u}).of_isIso _)
      exact isFibrant_of_fibration e.hom
    letI := h₀'
    have hp : fibrations Frames.{u} (G.map (homOfLE (bot_le : ⊥ ≤ j)).op) := by
      rw [← rlp_eq_of_wfs (trivialCofibrations Frames.{u}) (fibrations Frames.{u})]
      apply rlp_toBottom_of_inverseTower
      intro k hk
      rw [rlp_eq_of_wfs (trivialCofibrations Frames.{u}) (fibrations Frames.{u})]
      exact (ha k hk).1
    letI : Fibration (G.map (homOfLE (bot_le : ⊥ ≤ j)).op) := (fibration_iff _).mpr hp
    exact isFibrant_of_fibration (G.map (homOfLE (bot_le : ⊥ ≤ j)).op)
  have hdeg (j : J) (n : SimplexCategoryᵒᵖ) :
      trivialFibrations ResolutionDiagram.{u} ((a'.app (op j)).app n).unop := by
    induction j using SuccOrder.limitRecOn generalizing n with
    | isMin j hj =>
      obtain rfl : j = ⊥ := le_antisymm (hj bot_le) bot_le
      exact degreewise_of_reedy_trivialCofibration ha₀ n
    | succ j hj _ =>
      exact degreewise_of_reedy_trivialCofibration (ha j hj).2 n
    | isSuccLimit j hj ih =>
      let I := (Set.principalSegIio j).monotone.functor
      let cX := (Set.principalSegIio j).cocone X
      let cF := (Set.principalSegIio j).cocone F
      let G' := I.op ⋙ G
      let cG : Cone G' := coneOfCoconeRightOp cF
      let hG : IsLimit cG := isLimitConeOfCoconeRightOp G' (F.isColimitOfIsWellOrderContinuous j hj)
      let b : (I ⋙ X).op ⋙ Functor.const SimplexCategoryᵒᵖ ⟶ G' :=
        Functor.whiskerLeft I.op a'
      have haug : sourceResolutionLimitAugmentation (I ⋙ X) G' b cX cG hG = a'.app (op j) := by
        apply hG.hom_ext
        intro k
        obtain ⟨k⟩ := k
        rw [sourceResolutionLimitAugmentation_fac]
        exact a'.naturality (homOfLE k.2.le).op
      rw [← haug]
      letI : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
      have hprev (k : Set.Iio j) (m : SimplexCategoryᵒᵖ) :
          trivialFibrations ResolutionDiagram.{u} ((b.app (op k)).app m).unop := by
        change trivialFibrations ResolutionDiagram.{u} ((a'.app (op k.1)).app m).unop
        exact ih k.1 k.2 m
      exact sourceResolutionLimitAugmentation_degreewise (I ⋙ X) G' b cX cG hG
        (X.isColimitOfIsWellOrderContinuous j hj) hprev n
  exact ⟨⟨G, a', hdeg, hfib, hcont, fun j hj ↦ (ha j hj).1⟩⟩

/-- The exact local weak-equivalence class is closed under transfinite composition. -/
instance resolutionLocalEquivalences_transfinite :
    IsStableUnderTransfiniteComposition.{u} resolutionLocalEquivalences.{u} where
  isStableUnderTransfiniteCompositionOfShape J := by
    intro _ _ _ _
    constructor
    intro A B f hf
    obtain ⟨c⟩ := hf
    letI := c.isWellOrderContinuous
    obtain ⟨S⟩ := sourceResolutionTower_exists c.F
    exact S.localEquivalence_of_transfiniteComposition c.toTransfiniteCompositionOfShape c.map_mem

/-- The intersection of Reedy cofibrations and local equivalences is closed
under transfinite composition. -/
instance resolutionLocalTrivialCofibrations_transfinite :
    IsStableUnderTransfiniteComposition.{u} (reedyCofibrations.{u} ⊓ resolutionLocalEquivalences) where
  isStableUnderTransfiniteCompositionOfShape J := by
    intro _ _ _ _
    constructor
    intro A B f hf
    letI : IsStableUnderTransfiniteComposition.{u} reedyCofibrations.{u} := by
      change IsStableUnderTransfiniteComposition.{u} (cofibrations ResolutionDiagram.{u})
      rw [← llp_eq_of_wfs (cofibrations ResolutionDiagram.{u}) (trivialFibrations ResolutionDiagram.{u})]
      infer_instance
    exact ⟨reedyCofibrations.transfiniteCompositionsOfShape_le J _
        (transfiniteCompositionsOfShape_monotone J inf_le_left _ hf),
      resolutionLocalEquivalences.transfiniteCompositionsOfShape_le J _
        (transfiniteCompositionsOfShape_monotone J inf_le_right _ hf)⟩

end

end DaggerModels.PartII
