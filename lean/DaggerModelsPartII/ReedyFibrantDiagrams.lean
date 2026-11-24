import DaggerModelsPartII.SimplicialReedyModel
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-! Fibrancy and change of coefficients for simplicial Reedy diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial

universe v u v' u'

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

omit [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C] in
/-- Reversing arrows sends a cofibrant object to a fibrant object. -/
theorem isFibrant_op_of_isCofibrant (A : C) [IsCofibrant A] : IsFibrant (op A) := by
  apply (isFibrant_iff_of_isTerminal (initial.to A).op (terminalOpOfInitial initialIsInitial)).mpr
  apply (fibration_iff _).mpr
  rw [fibrations_op]
  exact mem_cofibrations (initial.to A)

local instance fibrantDiagramsReedyModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ C) :=
  simplicialReedyModelCategory C

private theorem matchingComparison_mem_fibrations_iff (W : SimplexCategoryᵒᵖ ⥤ C)
    (n : ℕ) :
    fibrations C ((matchingComparison n).app W) ↔
      fibrations C (relativeMatchingMap n (terminal.from W)) := by
  let T := ⊤_ (SimplexCategoryᵒᵖ ⥤ C)
  let f := terminal.from W
  letI : PreservesLimit (Functor.empty.{0} _) (matchingFunctor (C := C) n) := by
    unfold matchingFunctor
    infer_instance
  have hT : IsTerminal ((matchingFunctor n).obj T) :=
    terminalIsTerminal.isTerminalObj (matchingFunctor n) T
  have hTn : IsTerminal (T.obj (op ⦋n⦌)) :=
    terminalIsTerminal.isTerminalObj ((evaluation _ C).obj (op ⦋n⦌)) T
  letI : IsIso ((matchingComparison n).app T) :=
    isIso_of_isTerminal hTn hT _
  let π := pullback.fst ((matchingFunctor n).map f) ((matchingComparison n).app T)
  haveI : IsIso π := pullback_fst_iso_of_right_iso _ _
  have hπ : relativeMatchingMap n f ≫ π = (matchingComparison n).app W :=
    pullback.lift_fst _ _ _
  rw [← hπ]
  exact (fibrations C).cancel_right_of_respectsIso _ π


/-- A simplicial diagram is Reedy fibrant exactly when its matching maps are fibrations. -/
theorem reedyFibrant_iff_matchingComparison (W : SimplexCategoryᵒᵖ ⥤ C) :
    IsFibrant W ↔ ∀ n, fibrations C ((matchingComparison n).app W) := by
  rw [isFibrant_iff, fibration_iff]
  change (∀ n, fibrations C (relativeMatchingMap n (terminal.from W))) ↔ _
  exact forall_congr' (fun n ↦ (matchingComparison_mem_fibrations_iff W n).symm)

omit [HasColimitsOfSize.{0, 0} C] in
/-- Every component of a map with fibration relative matching maps is a fibration. -/
theorem reedyMatchingFibration_eval {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V)
    (hf : reedyMatchingProperty (fibrations C) f) (n : ℕ) :
    fibrations C (f.app (op ⦋n⦌)) := by
  let P := fibrations C
  have hm : P ((matchingFunctor n).map f) := by
    change fibrations C ((matchingFunctor n).map f)
    rw [← rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    apply matchingFunctor_map_rlp
    intro m _
    rw [rlp_eq_of_wfs (trivialCofibrations C) (fibrations C)]
    exact hf m
  rw [← relativeMatchingMap_comp_snd f n]
  exact P.comp_mem _ _ (hf n) (P.pullback_snd _ _ hm)

/-- The value of a Reedy fibrant diagram at every degree is fibrant. -/
theorem reedyFibrant_obj (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W]
    (j : SimplexCategoryᵒᵖ) : IsFibrant (W.obj j) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, op ⦋n⦌ = j :=
    ⟨j.unop.len, congrArg op (SimplexCategory.ext _ _ rfl)⟩
  let f := terminal.from W
  have hT := terminalIsTerminal.isTerminalObj ((evaluation _ C).obj (op ⦋n⦌)) _
  exact (isFibrant_iff_of_isTerminal (f.app _) hT).mpr
    ((fibration_iff _).mpr (reedyMatchingFibration_eval f (mem_fibrations f) n))

variable {D : Type u'} [Category.{v'} D] [ModelCategory D]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]

/-- A limit-preserving functor which preserves fibrations preserves Reedy fibrant objects. -/
theorem reedyFibrant_comp (W : SimplexCategoryᵒᵖ ⥤ C) [IsFibrant W] (G : C ⥤ D)
    [PreservesLimitsOfSize.{0, 0} G]
    (hG : ∀ {X Y : C} (f : X ⟶ Y), fibrations C f → fibrations D (G.map f)) :
    IsFibrant (W ⋙ G) := by
  apply (reedyFibrant_iff_matchingComparison (W ⋙ G)).mpr
  intro n
  let e := preservesLimitIso G (matchingProjection n ⋙ W)
  have h : G.map ((matchingComparison n).app W) ≫ e.hom =
      (matchingComparison n).app (W ⋙ G) := by
    apply limit.hom_ext
    intro s
    change (_ ≫ e.hom) ≫ limit.π ((matchingProjection n ⋙ W) ⋙ G) s =
      limit.lift _ (matchingCone n (W ⋙ G)) ≫ limit.π (matchingProjection n ⋙ (W ⋙ G)) s
    rw [Category.assoc, preservesLimitIso_hom_π, ← G.map_comp, limit.lift_π]
    change G.map (limit.lift _ (matchingCone n W) ≫ limit.π _ s) = G.map (W.map s.obj.hom)
    rw [limit.lift_π]
    rfl
  rw [← h]
  exact ((fibrations D).cancel_right_of_respectsIso _ e.hom).mpr
    (hG _ ((reedyFibrant_iff_matchingComparison W).mp inferInstance n))

end

end DaggerModels.PartII
