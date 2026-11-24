import DaggerModelsPartII.JTOrderedLabelPaddingDiagram
import DaggerModelsPartII.JTCommonCoefficientTimeBoundary

/-! Realize higher padded extensions on ordered prisms with the original mixed operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrism

open JTPaddedTimeOperators (pad inside)
open JTOrderedLabelPaddingSpace (embedding square)
open JTCommonCoefficientParameter (prism)
open JTFixedLiftSpaceTimeEquiv (timeMap timeMap_conditions timeMap_map)

noncomputable section

private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k

/-- The two added positions and the original interior form three distinct blocks. -/
def blocks (k : SimplexCategory) : pad k ⟶ ⦋2⦌ :=
  JTPaddedTimeOperators.extend (OrderHom.const _ 1)

/-- Arbitrary original coefficient operators respect the same three blocks. -/
theorem map_blocks {k l : SimplexCategory} (f : k ⟶ l) :
    JTPaddedTimeOperators.map f ≫ blocks l = blocks k := by
  apply JTPaddedTimeOperators.hom_ext (n := k)
  · change (blocks l).toOrderHom ((JTPaddedTimeOperators.map f).toOrderHom 0) = _
    rw [JTPaddedTimeOperators.map_first]
    rfl
  · intro i
    change (blocks l).toOrderHom ((JTPaddedTimeOperators.map f).toOrderHom (inside k i)) = _
    rw [JTPaddedTimeOperators.map_inside]
    unfold blocks
    rw [JTPaddedTimeOperators.extend_inside, JTPaddedTimeOperators.extend_inside]
    rfl
  · change (blocks l).toOrderHom
      ((JTPaddedTimeOperators.map f).toOrderHom (Fin.last (pad k).len)) = _
    rw [JTPaddedTimeOperators.map_last]
    unfold blocks
    rw [JTPaddedTimeOperators.extend_last, JTPaddedTimeOperators.extend_last]

variable {Y Y' : SSet.{0}} {k l n m : SimplexCategory}
variable {a : Y.obj (op k)} {a' : Y'.obj (op l)}

/-- A label on an ordered simplex extending the entire chosen padded prism. -/
def Realizations (v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n)) :=
  {s : simplex (JTHigherInterleavedParameter.common (pad k) n) ⟶ Y //
    prism (blocks k) n ≫ s = timeMap (square Y k a) n v}

/-- The realized label is stationary on the whole original coefficient
simplex throughout the prescribed time prism. -/
theorem interior_fixed
    {v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n)}
    (s : Realizations v) :
    (embedding k ▷ simplex n) ≫ prism (blocks k) n ≫ s.val =
      fst (simplex k) (simplex n) ≫ SSet.yonedaEquiv.symm a := by
  rw [s.property]
  exact (timeMap_conditions (square Y k a) n v).1

/-- Every higher extension of a label in a Kan complex has such an ordered realization. -/
theorem nonempty_realizations [IsFibrant Y]
    (v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n)) :
    Nonempty (Realizations v) := by
  let p := SSet.stdSimplex.isTerminalObj₀.from Y
  haveI : Fibration p :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  let i := prism (blocks k) n
  haveI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono _
  haveI : WeakEquivalence i := JTCommonCoefficientParameter.prism_weak _ _
  let sq : CommSq (timeMap (square Y k a) n v) i p
      (SSet.stdSimplex.isTerminalObj₀.from _) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨⟨sq.lift, sq.fac_left⟩⟩

/-- A prescribed enlarged time boundary can be held fixed during realization. -/
theorem exists_realization_relative [IsFibrant Y] (d : ℕ)
    (v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op ⦋d⦌))
    (G : (JTCommonCoefficientParameter.timeBoundary (blocks k) d).toSSet ⟶ Y)
    (hG : ((JTCommonCoefficientParameter.timeBoundary (blocks k) d).preimage
          (prism (blocks k) ⦋d⦌)).ι ≫ timeMap (square Y k a) ⦋d⦌ v =
      (JTCommonCoefficientParameter.timeBoundary (blocks k) d).fromPreimage
        (prism (blocks k) ⦋d⦌) ≫ G) :
    ∃ s : Realizations v, (JTCommonCoefficientParameter.timeBoundary (blocks k) d).ι ≫ s.val = G := by
  let p := SSet.stdSimplex.isTerminalObj₀.from Y
  haveI : Fibration p :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  let i := prism (blocks k) ⦋d⦌
  haveI : WeakEquivalence i := JTCommonCoefficientParameter.prism_weak _ _
  obtain ⟨s, hs, hB, _⟩ := JTPrismSubcomplexExtension.exists_extension i
    (JTCommonCoefficientParameter.timeBoundary (blocks k) d)
    (JTCommonCoefficientParameter.timeBoundary_fromPreimage_weak (blocks k) d)
    (SSet.stdSimplex.isTerminalObj₀.from (simplex _)) (timeMap (square Y k a) ⦋d⦌ v) G
    (p := p) (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _) hG
  exact ⟨⟨s, hs⟩, hB⟩

/-- Restriction of a chosen realization along the original coefficient map,
an injective time map, and the actual map of ordered label spaces. -/
def restrict (f : k ⟶ l) (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) (u : Y' ⟶ Y)
    (v : (JTOrderedLabelPaddingSpace.extensionSpace Y k a).obj (op n))
    (v' : (JTOrderedLabelPaddingSpace.extensionSpace Y' l a').obj (op m))
    (h : timeMap (square Y k a) n v =
      (SSet.stdSimplex.map (JTPaddedTimeOperators.map f) ⊗ₘ SSet.stdSimplex.map j) ≫
        timeMap (square Y' l a') m v' ≫ u)
    (s : Realizations v') : Realizations v :=
  ⟨SSet.stdSimplex.map (JTCommonCoefficientParameter.map
      (JTPaddedTimeOperators.map f) (map_blocks f) j hj) ≫ s.val ≫ u, by
    rw [← Category.assoc (prism (blocks k) n), JTCommonCoefficientParameter.prism_map,
      Category.assoc, ← Category.assoc (prism (blocks l) m), s.property, h]⟩

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)

private abbrev labels := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b
private abbrev code := OrderedLabelElements.necklace W b
private abbrev degree := OrderedLabelElements.degree W b
private abbrev label := OrderedLabelElements.label W b

private abbrev sq (i : OrderedLabelElements.Index W b) :=
  square ((labels W b).obj (op (code W b i))) (degree W b i) (label W b i)

/-- On each higher simplex the mixed operator acts on the actual prism
by the padded coefficient map, the simplex map, and the native label map. -/
theorem timeMap_restriction {i i' : OrderedLabelElements.Index W b} (f : i ⟶ i')
    {n m : SimplexCategory} (j : n ⟶ m)
    (v : (JTOrderedLabelPaddingDiagram.fiberAt W b i').obj (op m)) :
    timeMap (sq W b i) n
        ((JTOrderedLabelPaddingDiagram.fiberAt W b i).map j.op
          ((JTOrderedLabelPaddingDiagram.restriction W b f).app (op m) v)) =
      (SSet.stdSimplex.map (JTPaddedTimeOperators.map ((OrderedLabelElements.projection W b).map f).2)
        ⊗ₘ SSet.stdSimplex.map j) ≫
        timeMap (sq W b i') m v ≫ (labels W b).map
          ((OrderedLabelElements.projection W b).map f).1.op := by
  change timeMap (sq W b i) n
    ((SSet.ihomToPullbackFiber (sq W b i) : SSet.{0}).map j.op _) = _
  rw [timeMap_map]
  unfold timeMap
  rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, JTOrderedLabelPaddingDiagram.restriction_ι,
    ← Category.assoc, ← Category.assoc, uncurry_natural_right, uncurry_pre_app]
  simp only [Category.assoc, tensorHom_def']
  rfl

end

end DaggerModels.PartII.JTOrderedLabelPaddingPrism
