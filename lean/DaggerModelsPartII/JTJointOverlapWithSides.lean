import DaggerModelsPartII.JTActualJointMarkedEvaluation
import DaggerModelsPartII.JTJointPaddedOverlapEvaluation

/-!
# Inserting the full overlap between two families on the actual sides
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointOverlapWithSides

open JTTargetJointMarks (Joint)
open JTParametrizedTargetFamilies (Family codes)
open JTJointOverlapPrismDiagram (overlapSimplices)
open JTParametrizedProductSimplices (Index base)
open JTMarkedFiniteParametrizedTargetFamilies (Synchronized)
open JTMarkedParametrizedTargetFamilyJoin (degree)
open JTActualJointMarkedEvaluation (left right targetIso)
open JTParameterBlocks (common leftIn rightIn)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {A : Type} [SmallCategory A]
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev X := overlapSimplices F j
private abbrev t := base (X F j) ⋙ time
private abbrev M := JTJointPaddedOverlapEvaluation.synchronized j F

variable (S : Synchronized (t F j) (left Q j)) (R : Synchronized (t F j) (right Q j))

private abbrev rightWithMiddle := (M F j).join R
private abbrev withMiddle := S.join (rightWithMiddle F j R)

set_option maxHeartbeats 900000 in
/-- Attach the original overlap between compatible marked families on the two
actual sides, then evaluate over the unchanged target. -/
def glued : Synchronized (t F j) Q :=
  (withMiddle F j S R).postcomp
    (NecklacesOver.wedgeHom (𝟙 (left Q j)) (NecklacesOver.wedgeLeftUnitOver (right Q j)) ≫
      (targetIso Q j).hom)

private abbrev nativeCode {B : Type} [SmallCategory B] {t₀ : B ⥤ SimplexCategory}
    {u v : Vertex W} {P : NecklacesOver (Raw W) (rawVertex W u) (rawVertex W v)}
    (G : Synchronized t₀ P) (a : B) := (codes G.labels).obj a

private abbrev s (a : Index (X F j)) := (degree S.labels).obj a
private abbrev m (a : Index (X F j)) := (degree (M F j).labels).obj a
private abbrev r (a : Index (X F j)) := (degree R.labels).obj a

/-- The native inclusion of the full padded middle in the twice joined label. -/
def middleInclusion (a : Index (X F j)) :
    (nativeCode (M F j) a).toSSet ⟶ (nativeCode (glued F j S R) a).toSSet :=
  tripleRightT (nativeCode (M F j) a) (single 1) (nativeCode R a) ≫
    tripleRightV (nativeCode S a) (single 1) (nativeCode (rightWithMiddle F j R) a)

/-- The coefficient operator of the middle in the two ordered joins. -/
def middleCoefficient (a : Index (X F j)) :
    m F j a ⟶ (degree (glued F j S R).labels).obj a :=
  leftIn (m F j a) (r F j R a) ≫ rightIn (s F j S a) (common (m F j a) (r F j R a))

set_option maxHeartbeats 1500000 in
/-- The joined graph restricts to the complete padded middle parameter. -/
theorem middle_parameter (a : Index (X F j)) :
    (middleInclusion F j S R a ⊗ₘ 𝟙 (J.obj ((t F j).obj a))) ≫
      (glued F j S R).family.parameter a =
    (M F j).family.parameter a ≫ J.map (middleCoefficient F j S R a) := by
  let I := J.obj ((t F j).obj a)
  let X₁ := nativeCode S a
  let X₂ := nativeCode (M F j) a
  let X₃ := nativeCode R a
  let X₂₃ := nativeCode (rightWithMiddle F j R) a
  let k := s F j S a
  let l := m F j a
  let n := r F j R a
  let p := (M F j).family.parameter a
  let q := (rightWithMiddle F j R).family.parameter a
  have h₁ : (tripleRightT X₂ (single 1) X₃ ⊗ₘ 𝟙 I) ≫ q =
      p ≫ J.map (leftIn l n) :=
    JTBinaryPrismParameter.parameter_left X₂ X₃ (common l n) I
      (p ≫ J.map (leftIn l n)) (R.family.parameter a ≫ J.map (rightIn l n))
  have h₂ : (tripleRightV X₁ (single 1) X₂₃ ⊗ₘ 𝟙 I) ≫
        (glued F j S R).family.parameter a = q ≫ J.map (rightIn k (common l n)) :=
    JTBinaryPrismParameter.parameter_right X₁ X₂₃ (common k (common l n)) I
      (S.family.parameter a ≫ J.map (leftIn k (common l n)))
      (q ≫ J.map (rightIn k (common l n)))
  change ((tripleRightT X₂ (single 1) X₃ ≫ tripleRightV X₁ (single 1) X₂₃) ⊗ₘ
      𝟙 I) ≫ (glued F j S R).family.parameter a =
    p ≫ J.map (leftIn l n ≫ rightIn k (common l n))
  rw [J.map_comp, ← Category.assoc p, ← h₁, Category.assoc, ← h₂,
    ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]

private abbrev originalDegree :=
  base (X F j) ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

set_option maxHeartbeats 1500000 in
/-- The entire original parameter occurs on the interior of the glued family,
including all time simplices and the two ordered coefficient embeddings. -/
theorem original_overlap_parameter (a : Index (X F j)) :
    ((JTPaddedPointTargetFamily.interior
        (D := JTParametrizedProductSimplices.degree (X F j)) a ≫
      middleInclusion F j S R a) ⊗ₘ 𝟙 (J.obj ((t F j).obj a))) ≫
        (glued F j S R).family.parameter a =
    (JTJointOverlapPrismDiagram.parameter F j).app a ≫
      J.map (JTOrderedLabelCoefficientPadding.embedding ((originalDegree F j).obj a) ≫
        middleCoefficient F j S R a) := by
  let i := JTPaddedPointTargetFamily.interior
    (D := JTParametrizedProductSimplices.degree (X F j)) a
  let m := middleInclusion F j S R a
  let V := J.obj ((t F j).obj a)
  have h : (i ⊗ₘ 𝟙 V) ≫ (m ⊗ₘ 𝟙 V) = (i ≫ m) ⊗ₘ 𝟙 V := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [← h, Category.assoc, middle_parameter, ← Category.assoc, J.map_comp]
  exact congrArg (fun g ↦ g ≫ J.map (middleCoefficient F j S R a))
    (JTJointPaddedOverlapEvaluation.interior_parameter j F a)

end
end DaggerModels.PartII.JTJointOverlapWithSides
