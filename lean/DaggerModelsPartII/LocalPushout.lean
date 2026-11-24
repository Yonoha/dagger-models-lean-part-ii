import DaggerModelsPartII.SourceResolutionFibration
import DaggerModelsPartII.LeftProperPushoutComparison
import DaggerModelsPartII.ResolutionLocality
import DaggerModelsPartII.ReedyModelComparison
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Cobase change for the literal local trivial cofibrations. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

section Generic

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, v} C]

local instance localPushoutOppositeReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

local instance localPushoutFibrationsBaseChange :
    (fibrations (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ)).IsStableUnderBaseChange := by
  rw [← rlp_eq_of_wfs (trivialCofibrations _) (fibrations (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ))]
  infer_instance

local instance localPushoutKanTrivialFibrationsBaseChange :
    (trivialFibrations SSet.{v}).IsStableUnderBaseChange := by
  rw [← SSet.modelCategoryQuillen.rlp_I_eq_trivialFibrations]
  infer_instance

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, v} C] in
private theorem mapping_preservesPullback (Z : C)
    {P T S R : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ}
    {p : P ⟶ T} {q : P ⟶ S} {h : T ⟶ R} {g : S ⟶ R}
    (sq : IsPullback p q h g) :
    IsPullback ((CosimplicialResolution.mappingFromOppositeDiagram Z).map p)
      ((CosimplicialResolution.mappingFromOppositeDiagram Z).map q)
      ((CosimplicialResolution.mappingFromOppositeDiagram Z).map h)
      ((CosimplicialResolution.mappingFromOppositeDiagram Z).map g) := by
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  letI : PreservesLimitsOfShape WalkingCospan F := by
    dsimp only [F, CosimplicialResolution.mappingFromOppositeDiagram]
    letI : HasLimitsOfShape WalkingCospan Cᵒᵖ := inferInstance
    let G := coyoneda.obj (op (op Z))
    letI : PreservesLimitsOfShape WalkingCospan G := coyonedaPreservesLimitsOfShape _ _
    exact CategoryTheory.whiskeringRight_preservesLimitsOfShape G
  exact sq.map F

/-- In a left proper model category, the derived mapping-space weak-equivalence
test into a fibrant object is preserved by cobase change of cofibrations. -/
theorem homotopyMappingWeakEquivalences_of_pushout
    (leftProper : ∀ {A B D P : C} {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P},
      IsPushout i k l r → cofibrations C i → weakEquivalences C k → weakEquivalences C l)
    {A B D E : C} {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ E} {r : D ⟶ E}
    (sq : IsPushout i k l r) (hi : cofibrations C i) (Z : C) [IsFibrant Z]
    (hw : homotopyMappingWeakEquivalences Z i) : homotopyMappingWeakEquivalences Z r := by
  let R := cosimplicialResolution A
  let T := cosimplicialResolution D
  let h := R.comparison T k
  obtain ⟨S, g, hg⟩ := R.exists_comparison_reedyFibration i
  let p := pullback.fst h.mapOp g.mapOp
  let q := pullback.snd h.mapOp g.mapOp
  let P := pullback h.mapOp g.mapOp
  let sqP : IsPullback p q h.mapOp g.mapOp := IsPullback.of_hasPullback _ _
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  have hp : trivialFibrations SSet.{v} (F.map p) :=
    (trivialFibrations SSet.{v}).of_isPullback (mapping_preservesPullback Z sqP.flip)
      (g.precomp_trivialFibration_of_test hg Z hw)
  letI := T.fibrantOp
  letI : Fibration p := (fibration_iff _).mpr ((fibrations _).of_isPullback sqP.flip hg)
  letI : IsFibrant P := isFibrant_of_fibration p
  let K : Cᵒᵖ ⥤ (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) := Functor.const SimplexCategoryᵒᵖ
  let a := K.map r.op ≫ T.augmentationOp
  let b := K.map l.op ≫ S.augmentationOp
  have comm : a ≫ h.mapOp = b ≫ g.mapOp := by
    dsimp only [a, b]
    rw [Category.assoc, h.comm, Category.assoc, g.comm, ← Category.assoc, ← Category.assoc,
      ← K.map_comp, ← K.map_comp, ← op_comp, ← op_comp, sq.w]
  let aug := pullback.lift a b comm
  have ap : aug ≫ p = a := pullback.lift_fst _ _ _
  have aq : aug ≫ q = b := pullback.lift_snd _ _ _
  have haug : weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) aug := by
    intro n
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, op ⦋m⦌ = n :=
      ⟨n.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
    let ev := (evaluation SimplexCategoryᵒᵖ Cᵒᵖ).obj (op ⦋m⦌)
    have hgn := reedyMatchingFibration_eval g.mapOp hg m
    rw [fibrations_op] at hgn
    change weakEquivalences C (aug.app (op ⦋m⦌)).unop
    exact weak_of_pushoutComparison leftProper ((sqP.map ev).unop) sq hgn hi
      (R.augmentationOp.app _).unop (S.augmentationOp.app _).unop
      (T.augmentationOp.app _).unop (aug.app _).unop
      (congrArg Quiver.Hom.unop (congr_app g.comm _))
      (congrArg Quiver.Hom.unop (congr_app h.comm _))
      (congrArg Quiver.Hom.unop (congr_app aq _))
      (congrArg Quiver.Hom.unop (congr_app ap _))
      (R.augmentation_weak _) (S.augmentation_weak _) (T.augmentation_weak _)
  let U := cosimplicialResolution E
  letI := U.fibrantOp
  have liftSq : CommSq aug U.augmentationOp (terminal.from P) (terminal.from U.oppositeDiagram) :=
    ⟨terminal.hom_ext _ _⟩
  letI := hasLiftingProperty_of_wfs U.augmentationOp (terminal.from P)
    U.augmentationOp_mem (mem_fibrations _)
  let e := liftSq.lift
  have he : weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) e :=
    (weakEquivalences _).of_precomp _ _ U.augmentationOp_mem.2 (liftSq.fac_left.symm ▸ haug)
  have hef := map_weak_of_trivialFibration F
    (fun f hf ↦ (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z f hf).2) e he
  let d : T.Comparison U r :=
    ⟨e ≫ p, by rw [← Category.assoc, liftSq.fac_left, ap]⟩
  apply (homotopyMappingWeakEquivalences_iff Z d).mpr
  change weakEquivalences SSet.{v} (F.map (e ≫ p))
  rw [F.map_comp]
  exact (weakEquivalences SSet.{v}).comp_mem _ _ hef hp.2

end Generic

local instance localPushoutLimits : HasLimits DaggerSSet.{u} := daggerSSetHasLimits
local instance localPushoutColimits : HasColimits DaggerSSet.{u} := daggerSSetHasColimits
local instance localPushoutCoefficientModel : ModelCategory DaggerSSet.{u} :=
  DaggerOriginalJoyalModel.standardModelCategory
local instance localPushoutReedyModel : ModelCategory ResolutionDiagram.{u} :=
  resolutionReedyModelCategory

/-- Reedy cofibrations that are (S_h)-local equivalences are stable under pushout. -/
instance resolutionLocalTrivialCofibrations_cobaseChange :
    (reedyCofibrations.{u} ⊓ resolutionLocalEquivalences).IsStableUnderCobaseChange where
  of_isPushout sq hi := by
    refine ⟨(cofibrations ResolutionDiagram.{u}).of_isPushout sq hi.1, ?_⟩
    intro W hW
    letI := hW.1
    letI : HasColimitsOfSize.{0, u} ResolutionDiagram.{u} := hasColimitsOfSizeShrink.{0, u} _
    exact homotopyMappingWeakEquivalences_of_pushout
      (fun sq hc hw ↦ resolutionReedy_leftProper sq.flip hw hc) sq.flip hi.1 W (hi.2 W hW)

end

end DaggerModels.PartII
