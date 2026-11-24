import DaggerModelsPartII.SourceResolutionFibration

/-! Source frames whose augmentation is specified degreewise, for limit stages. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance pointwiseSourceReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

omit [HasLimitsOfSize.{0, 0} C] in
/-- Relative trivial latching maps give degreewise trivial cofibrations. -/
theorem reedyTrivialLatching_eval {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)
    (hf : reedyLatchingProperty (trivialCofibrations C) f) (n : ℕ) :
    trivialCofibrations C (f.app (op ⦋n⦌)) := by
  let P := trivialCofibrations C
  letI : P.IsStableUnderCobaseChange := by
    dsimp [P]
    rw [← llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    infer_instance
  have hm : P ((latchingFunctor n).map f) := by
    change trivialCofibrations C _
    rw [← llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    apply latchingFunctor_map_llp
    intro m _
    rw [llp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    exact hf m
  rw [← inl_comp_relativeLatchingMap f n]
  exact P.comp_mem _ _ (P.pushout_inl _ _ hm) (hf n)

namespace CosimplicialResolution

/-- The augmentation of a source resolution is a trivial fibration in each degree
after reversing the arrows. -/
theorem augmentation_degreewise_trivialFibration {X : C} (R : CosimplicialResolution X)
    (j : SimplexCategoryᵒᵖ) : trivialFibrations C (R.augmentationOp.app j).unop := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
    ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  have h := R.augmentationOp_mem
  change (reedyLatchingProperty (cofibrations Cᵒᵖ) ⊓ simplicialReedyWeakEquivalences Cᵒᵖ)
    R.augmentationOp at h
  rw [simplicialReedyCofibrations_inf_weakEquivalences] at h
  have h₀ := reedyTrivialLatching_eval _ h n
  rw [trivialCofibrations_op] at h₀
  exact h₀

end CosimplicialResolution

/-- A Reedy fibrant opposite source diagram with a degreewise trivial augmentation. -/
structure PointwiseSourceResolution (X : C) where
  diagram : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ
  augmentation : (Functor.const SimplexCategoryᵒᵖ).obj (op X) ⟶ diagram
  degreewise : ∀ j, trivialFibrations C (augmentation.app j).unop
  fibrant : IsFibrant diagram

namespace PointwiseSourceResolution

/-- A cosimplicial resolution is in particular a pointwise source resolution. -/
def ofResolution {X : C} (R : CosimplicialResolution X) : PointwiseSourceResolution X :=
  ⟨R.oppositeDiagram, R.augmentationOp, R.augmentation_degreewise_trivialFibration, R.fibrantOp⟩

variable {X Y : C}

/-- A compatible map of pointwise source resolutions, in the opposite direction. -/
structure Comparison (R : PointwiseSourceResolution X) (S : PointwiseSourceResolution Y)
    (f : X ⟶ Y) where
  map : S.diagram ⟶ R.diagram
  comm : S.augmentation ≫ map =
    (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ R.augmentation

/-- The successor step chooses an ordinary resolution with a Reedy fibration
comparison to any pointwise source resolution. -/
theorem exists_comparison_reedyFibration (R : PointwiseSourceResolution X) (f : X ⟶ Y) :
    ∃ (S : CosimplicialResolution Y) (g : R.Comparison (ofResolution S) f),
      reedyMatchingProperty (fibrations Cᵒᵖ) g.map := by
  let a := (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ R.augmentation
  let d := factorizationData (trivialCofibrations _) (fibrations _) a
  letI := R.fibrant
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  let S : CosimplicialResolution Y := ⟨d.Z, d.i, d.hi, isFibrant_of_fibration d.p⟩
  exact ⟨S, ⟨d.p, d.fac⟩, d.hp⟩

variable (R : PointwiseSourceResolution X)

private theorem augmentation_weak :
    weakEquivalences (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) R.augmentation :=
  fun j ↦ (R.degreewise j).2

private theorem structureMap_weak {s t : SimplexCategoryᵒᵖ} (f : s ⟶ t) :
    weakEquivalences Cᵒᵖ (R.diagram.map f) := by
  have h := R.augmentation.naturality f
  change 𝟙 _ ≫ R.augmentation.app t = R.augmentation.app s ≫ R.diagram.map f at h
  rw [Category.id_comp] at h
  exact (weakEquivalences Cᵒᵖ).of_precomp _ _ (R.augmentation_weak s)
    (h ▸ R.augmentation_weak t)

private theorem exists_trivialFibration_fromResolution :
    ∃ (T : CosimplicialResolution X) (a : T.oppositeDiagram ⟶ R.diagram),
      T.augmentationOp ≫ a = R.augmentation ∧ trivialFibrations _ a := by
  let d := factorizationData (trivialCofibrations _) (fibrations _) R.augmentation
  letI := R.fibrant
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  let T : CosimplicialResolution X := ⟨d.Z, d.i, d.hi, isFibrant_of_fibration d.p⟩
  exact ⟨T, d.p, d.fac, d.hp,
    (weakEquivalences _).of_precomp _ _ d.hi.2 (d.fac.symm ▸ R.augmentation_weak)⟩

variable {R} {S : PointwiseSourceResolution Y} {f : X ⟶ Y}

/-- The derived mapping test can be computed using any compatible pointwise source resolutions. -/
theorem Comparison.mapping_weak_iff (g : R.Comparison S f) (Z : C) [IsFibrant Z] :
    homotopyMappingWeakEquivalences Z f ↔
      weakEquivalences SSet.{v} ((CosimplicialResolution.mappingFromOppositeDiagram Z).map g.map) := by
  obtain ⟨R', a, ha, hta⟩ := R.exists_trivialFibration_fromResolution
  obtain ⟨S', b, hb, htb⟩ := S.exists_trivialFibration_fromResolution
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  let k := (Functor.const SimplexCategoryᵒᵖ).map f.op
  have sq : CommSq (k ≫ R'.augmentationOp) S'.augmentationOp a (b ≫ g.map) := by
    constructor
    rw [Category.assoc, ha, ← Category.assoc, hb, g.comm]
  letI := hasLiftingProperty_of_wfs S'.augmentationOp a S'.augmentationOp_mem hta.1
  let d : R'.Comparison S' f := ⟨sq.lift, sq.fac_left⟩
  have he : d.precomp Z ≫ F.map a = F.map b ≫ F.map g.map := by
    change F.map sq.lift ≫ F.map a = F.map b ≫ F.map g.map
    rw [← F.map_comp, ← F.map_comp, sq.fac_right]
  have hwa := (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z a hta).2
  have hwb := (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z b htb).2
  rw [homotopyMappingWeakEquivalences_iff Z d]
  exact ⟨fun h ↦ (weakEquivalences SSet.{v}).of_precomp _ _ hwb
      (he ▸ (weakEquivalences SSet.{v}).comp_mem _ _ h hwa),
    fun h ↦ (weakEquivalences SSet.{v}).of_postcomp _ _ hwa
      (he.symm ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hwb h)⟩

/-- An opposite Reedy fibration comparison which passes the derived mapping test
induces a Kan trivial fibration. -/
theorem Comparison.mapping_trivialFibration [HasColimitsOfSize.{0, v} C]
    (g : R.Comparison S f) (hg : reedyMatchingProperty (fibrations Cᵒᵖ) g.map)
    (Z : C) [IsFibrant Z] (hf : homotopyMappingWeakEquivalences Z f) :
    trivialFibrations SSet.{v} ((CosimplicialResolution.mappingFromOppositeDiagram Z).map g.map) := by
  letI := S.fibrant
  letI := R.fibrant
  letI : IsCofibrant (op Z) :=
    (isCofibrant_iff_of_isInitial (terminal.from Z).op (initialOpOfTerminal terminalIsTerminal)).mpr
      ((cofibration_op_iff _).mpr inferInstance)
  exact ⟨(fibration_iff _).mp (diagramHomPostcomp_kan_fibration (op Z)
    S.structureMap_weak R.structureMap_weak g.map hg), (g.mapping_weak_iff Z).mp hf⟩

end PointwiseSourceResolution

end

end DaggerModels.PartII
