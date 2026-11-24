import DaggerModelsPartII.JTOrderedLabelPaddingPrism
import DaggerModelsPartII.JTCommonCoefficientNormalization

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismBoundary

open JTOrderedLabelPaddingSpace (embedding square extensionSpace)
open JTOrderedLabelPaddingPrism (blocks Realizations)
open JTCommonCoefficientParameter (prism)
open JTFixedLiftSpaceTimeEquiv (timeMap timeEquiv)
open SemiSimplexBoundaryLifting

noncomputable section

private abbrev simplex (n : SimplexCategory) := SSet.stdSimplex.{0}.obj n
private abbrev inc := SemiSimplexCategory.toSimplexCategory

variable (Y : SSet.{0}) (k : SimplexCategory) (a : Y.obj (op k))

private def terminalSquare : CommSq (SSet.yonedaEquiv.symm a) (embedding k)
    (SSet.stdSimplex.isTerminalObj₀.from Y)
    (SSet.stdSimplex.map (blocks k) ≫
      SSet.stdSimplex.isTerminalObj₀.from (simplex ⦋2⦌)) :=
  ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩

private theorem terminalSquare_eq : terminalSquare Y k a = square Y k a := by
  have h : SSet.stdSimplex.map (blocks k) ≫
      SSet.stdSimplex.isTerminalObj₀.from (simplex ⦋2⦌) =
      SSet.stdSimplex.isTerminalObj₀.from (simplex (JTPaddedTimeOperators.pad k)) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  cases h
  rfl

private abbrev sq := terminalSquare Y k a
private abbrev normalized (n : SimplexCategory) :=
  JTCommonCoefficientLiftChoices.Extension (sq Y k a) n

private def toPair (n : SimplexCategory) (E : normalized Y k a n) :
    Σ v : (extensionSpace Y k a).obj (op n), Realizations v := by
  let v : (extensionSpace Y k a).obj (op n) := by
    simpa only [terminalSquare_eq] using
      (JTCommonCoefficientLiftChoices.underlying (sq Y k a) E)
  refine ⟨v, E.map, ?_⟩
  have h := JTCommonCoefficientLiftChoices.underlying_timeMap (sq Y k a) E
  change timeMap (sq Y k a) n _ = prism (blocks k) n ≫ E.map at h
  simpa only [terminalSquare_eq] using h.symm

private def fromPair (n : SimplexCategory)
    (z : Σ v : (extensionSpace Y k a).obj (op n), Realizations v) :
    normalized Y k a n := by
  obtain ⟨v, s⟩ := z
  have hstat := (JTFixedLiftSpaceTimeEquiv.timeMap_conditions (square Y k a) n v).1
  refine ⟨s.val, ?_, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  change (embedding k ▷ simplex n) ≫ prism (blocks k) n ≫ s.val =
    fst (simplex k) (simplex n) ≫ SSet.yonedaEquiv.symm a
  calc
    (embedding k ▷ simplex n) ≫ prism (blocks k) n ≫ s.val =
        (embedding k ▷ simplex n) ≫ timeMap (square Y k a) n v := by
      rw [s.property]
    _ = _ := hstat

private theorem pair_ext {n : SimplexCategory}
    {v w : (extensionSpace Y k a).obj (op n)} (s : Realizations v)
    (t : Realizations w) (hv : v = w) (hs : s.val = t.val) :
    (⟨v, s⟩ : Σ v, Realizations v) = ⟨w, t⟩ := by
  apply Sigma.ext hv
  apply (Subtype.heq_iff_coe_eq (fun x ↦ ?_)).2 hs
  have hmap := congrArg (timeMap (square Y k a) n) hv
  exact ⟨fun h ↦ h.trans hmap, fun h ↦ h.trans hmap.symm⟩

private theorem toPair_first (n : SimplexCategory) (E : normalized Y k a n) :
    timeMap (square Y k a) n (toPair Y k a n E).fst =
      prism (blocks k) n ≫ E.map :=
  (toPair Y k a n E).snd.property.symm

private theorem fromPair_first (n : SimplexCategory)
    (v : (extensionSpace Y k a).obj (op n)) (s : Realizations v) :
    (toPair Y k a n (fromPair Y k a n ⟨v, s⟩)).fst = v := by
  apply (timeEquiv (square Y k a) n).injective
  apply Subtype.ext
  exact (toPair_first Y k a n (fromPair Y k a n ⟨v, s⟩)).trans s.property

private theorem fromPair_map (n : SimplexCategory)
    (v : (extensionSpace Y k a).obj (op n)) (s : Realizations v) :
    (fromPair Y k a n ⟨v, s⟩).map = s.val := rfl

private theorem toPair_fromPair (n : SimplexCategory)
    (z : Σ v : (extensionSpace Y k a).obj (op n), Realizations v) :
    toPair Y k a n (fromPair Y k a n z) = z := by
  rcases z with ⟨v, s⟩
  have hs : (toPair Y k a n (fromPair Y k a n ⟨v, s⟩)).snd.val = s.val := by
    exact fromPair_map Y k a n v s
  exact pair_ext Y k a _ _ (fromPair_first Y k a n v s) hs

private theorem fromPair_toPair (n : SimplexCategory)
    (E : normalized Y k a n) :
    fromPair Y k a n (toPair Y k a n E) = E := by
  apply JTCommonCoefficientLiftChoices.Extension.ext
  simp only [fromPair, toPair]

/-- Exact objectwise identification with literal ordered realizations. -/
def pairEquiv (n : SimplexCategory) :
    normalized Y k a n ≃
      Σ v : (extensionSpace Y k a).obj (op n), Realizations v where
  toFun := toPair Y k a n
  invFun := fromPair Y k a n
  left_inv := fromPair_toPair Y k a n
  right_inv := toPair_fromPair Y k a n

/-- The realized label is exactly the enlargement map. -/
theorem pairEquiv_apply_val (n : SimplexCategory) (E : normalized Y k a n) :
    ((pairEquiv Y k a n) E).snd.val = E.map := rfl

/-- Exact enlargement choices over the terminal coefficient base. -/
def choices : SemiSimplexCategoryᵒᵖ ⥤ Type :=
  JTCommonCoefficientNormalization.choices (sq Y k a)

/-- Every choice is a literal ordered-prism realization. -/
def realization {n : SimplexCategory} (E : normalized Y k a n) :
    Σ v : (extensionSpace Y k a).obj (op n), Realizations v :=
  toPair Y k a n E

/-- Forget the ordered realization and retain the original padded extension. -/
def forget : choices Y k a ⟶ inc.op ⋙ extensionSpace Y k a := by
  simpa only [choices, extensionSpace, terminalSquare_eq] using
    (JTCommonCoefficientNormalization.forget (sq Y k a))


/-- The actual time-face operator acts on the enlarged label map. -/
theorem choices_map_val {m n : SemiSimplexCategory} (j : m ⟶ n)
    (E : (choices Y k a).obj (op n)) :
    ((choices Y k a).map j.op E).map =
      SSet.stdSimplex.map (JTCommonCoefficientParameter.timeOperator (blocks k)
        (n.len) (inc.map j) (SemiSimplexCategory.homEquiv j).injective) ≫ E.map := rfl

/-- The simplex in a realization is the value of the forgetful map. -/
theorem realization_forget (n : SemiSimplexCategory)
    (E : (choices Y k a).obj (op n)) :
    (realization Y k a E).fst = (forget Y k a).app (op n) E := by
  rfl

/-- The terminal-base enlargement has exact compatible boundary lifting. -/
theorem hasBoundaryLifting [IsFibrant Y] : HasBoundaryLifting (forget Y k a) := by
  haveI : Fibration (SSet.stdSimplex.isTerminalObj₀.from Y) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  simpa only [forget, terminalSquare_eq] using
    (JTCommonCoefficientNormalization.hasBoundaryLifting (sq Y k a))

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismBoundary
