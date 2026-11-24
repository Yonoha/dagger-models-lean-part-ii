import DaggerModelsPartII.JTCoarseCoefficientRegrouping
import DaggerModelsPartII.JTCorrectedCoarseIntervalComparison

/-!
# Regroup the five complete pieces over their original target

The existing regrouping isomorphism preserves all five native inclusions.
Pushout uniqueness therefore identifies the complete assembly BEFORE any
postcomposition with Q. This adds no actual-family raw or evaluation premise.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCoarseRegroupingAssembly

noncomputable section

private abbrev R := JTCoarseCoefficientRegrouping.sourceCode

private theorem five_ext {A e B f D : NecklaceCode} {X : SSet.{0}}
    {g h : (R A e B f D).toSSet ⟶ X}
    (hA : JTCoarseCoefficientRegrouping.sourceA A e B f D ≫ g =
      JTCoarseCoefficientRegrouping.sourceA A e B f D ≫ h)
    (he : JTCoarseCoefficientRegrouping.sourceE A e B f D ≫ g =
      JTCoarseCoefficientRegrouping.sourceE A e B f D ≫ h)
    (hB : JTCoarseCoefficientRegrouping.sourceB A e B f D ≫ g =
      JTCoarseCoefficientRegrouping.sourceB A e B f D ≫ h)
    (hf : JTCoarseCoefficientRegrouping.sourceF A e B f D ≫ g =
      JTCoarseCoefficientRegrouping.sourceF A e B f D ≫ h)
    (hD : JTCoarseCoefficientRegrouping.sourceD A e B f D ≫ g =
      JTCoarseCoefficientRegrouping.sourceD A e B f D ≫ h) : g = h := by
  apply (wedgeIsPushout A (wedge (wedge e (wedge B f)) D)).hom_ext
  · exact hA
  · apply (wedgeIsPushout (wedge e (wedge B f)) D).hom_ext
    · apply (wedgeIsPushout e (wedge B f)).hom_ext
      · simpa only [JTCoarseCoefficientRegrouping.sourceE, Category.assoc] using he
      · apply (wedgeIsPushout B f).hom_ext
        · simpa only [JTCoarseCoefficientRegrouping.sourceB, Category.assoc] using hB
        · simpa only [JTCoarseCoefficientRegrouping.sourceF, Category.assoc] using hf
    · simpa only [JTCoarseCoefficientRegrouping.sourceD, Category.assoc] using hD

variable {X : SSet.{0}} {a₀ a₁ a₂ a₃ a₄ a₅ : X.obj (op ⦋0⦌)}
variable (A : NecklacesOver X a₀ a₁) (e : NecklacesOver X a₁ a₂)
variable (B : NecklacesOver X a₂ a₃) (f : NecklacesOver X a₃ a₄)
variable (D : NecklacesOver X a₄ a₅)

/-- The five pieces with the exact original coarse parenthesization. -/
def sourceOver : NecklacesOver X a₀ a₅ :=
  NecklacesOver.wedge A (NecklacesOver.wedge
    (NecklacesOver.wedge e (NecklacesOver.wedge B f)) D)

/-- The same complete pieces grouped for the left and right raw equations. -/
def groupedOver : NecklacesOver X a₀ a₅ :=
  NecklacesOver.wedge (NecklacesOver.wedge A (NecklacesOver.wedge e B))
    (NecklacesOver.wedge f D)

/-- The complete regrouping square holds before postcomposition into any Q. -/
theorem delta_assembly :
    (JTCoarseCoefficientRegrouping.delta A.code e.code B.code f.code D.code).hom ≫
        (groupedOver A e B f D).map = (sourceOver A e B f D).map := by
  apply five_ext
  · rw [← Category.assoc, JTCoarseCoefficientRegrouping.delta_A]
    simp only [JTCoarseCoefficientRegrouping.groupedA,
      JTCoarseCoefficientRegrouping.sourceA, sourceOver, groupedOver,
      Category.assoc, NecklacesOver.wedge, wedgeDesc_left]
  · rw [← Category.assoc, JTCoarseCoefficientRegrouping.delta_e]
    simp only [JTCoarseCoefficientRegrouping.groupedE,
      JTCoarseCoefficientRegrouping.sourceE, sourceOver, groupedOver,
      Category.assoc, NecklacesOver.wedge, wedgeDesc_left, wedgeDesc_right]
  · rw [← Category.assoc, JTCoarseCoefficientRegrouping.delta_B]
    simp only [JTCoarseCoefficientRegrouping.groupedB,
      JTCoarseCoefficientRegrouping.sourceB, sourceOver, groupedOver,
      Category.assoc, NecklacesOver.wedge, wedgeDesc_left, wedgeDesc_right]
  · rw [← Category.assoc, JTCoarseCoefficientRegrouping.delta_f]
    simp only [JTCoarseCoefficientRegrouping.groupedF,
      JTCoarseCoefficientRegrouping.sourceF, sourceOver, groupedOver,
      Category.assoc, NecklacesOver.wedge, wedgeDesc_left, wedgeDesc_right]
  · rw [← Category.assoc, JTCoarseCoefficientRegrouping.delta_D]
    simp only [JTCoarseCoefficientRegrouping.groupedD,
      JTCoarseCoefficientRegrouping.sourceD, sourceOver, groupedOver,
      Category.assoc, NecklacesOver.wedge, wedgeDesc_right]

/-- The existing native regrouping is an actual morphism over the original target. -/
def regroupOver : sourceOver A e B f D ⟶ groupedOver A e B f D where
  hom := (JTCoarseCoefficientRegrouping.deltaCodeIso A.code e.code B.code f.code D.code).hom
  w := delta_assembly A e B f D


section Corrected

variable (T : NecklaceCode) (a c : Fin (T.len + 1)) (hac : a ≤ c)

private abbrev vertex (v : Fin (T.len + 1)) := T.verticesEquiv.symm (ULift.up v)
private abbrev correction (v : Fin (T.len + 1)) :=
  JTCorrectedIntervalAssembly.constantOver (single 1) (vertex T v)
private abbrev outerLeft := NecklacesOver.wedge (intervalOver T 0 a (Fin.zero_le a))
  (correction T a)
private abbrev outerRight := NecklacesOver.wedge (correction T c)
  (intervalOver T c (Fin.last T.len) (Fin.le_last c))

/-- The complete right piece after restricting away only the diagonal old interval. -/
def correctedRight := NecklacesOver.wedge (correction T c) (outerRight T c)

/-- Group the actual corrected coarse necklace into its complete left and right pieces. -/
def correctedGrouped :
    NecklacesOver T.toSSet (vertex T 0) (vertex T (Fin.last T.len)) :=
  NecklacesOver.wedge (JTCorrectedIntervalAssembly.leftOver T a c hac)
    (correctedRight T c)

/-- Apply the existing regrouping to the exact corrected coarse native object. -/
def correctedRegroup : JTCorrectedCoarseIntervalComparison.coarseOver T a c hac ⟶
    correctedGrouped T a c hac :=
  regroupOver (outerLeft T a) (correction T a) (intervalOver T a c hac)
    (correction T c) (outerRight T c)

/-- The exact corrected coarse assembly square holds in the original necklace T. -/
theorem corrected_assembly :
    (correctedRegroup T a c hac).hom.map ≫ (correctedGrouped T a c hac).map =
      (JTCorrectedCoarseIntervalComparison.assembly T a c hac).map :=
  (correctedRegroup T a c hac).w

/-- Restricting the grouped assembly to its whole left piece recovers leftOver. -/
theorem corrected_left :
    wedgeιLeft (JTCorrectedIntervalAssembly.leftOver T a c hac).code
        (correctedRight T c).code ≫ (correctedGrouped T a c hac).map =
      (JTCorrectedIntervalAssembly.leftOver T a c hac).map :=
  NecklacesOver.wedge_left _ _

/-- Restricting the grouped assembly to its whole right piece retains both later edges. -/
theorem corrected_right :
    wedgeιRight (JTCorrectedIntervalAssembly.leftOver T a c hac).code
        (correctedRight T c).code ≫ (correctedGrouped T a c hac).map =
      (correctedRight T c).map :=
  NecklacesOver.wedge_right _ _

/-- Restriction of the existing diagonal right assembly removes only its old point piece. -/
theorem diagonal_right :
    wedgeιRight (intervalOver T c c le_rfl).code (correctedRight T c).code ≫
        (JTCorrectedIntervalAssembly.rightOver T c c le_rfl).map =
      (correctedRight T c).map :=
  NecklacesOver.wedge_right (intervalOver T c c le_rfl) (correctedRight T c)

end Corrected

end
end DaggerModels.PartII.JTCoarseRegroupingAssembly
