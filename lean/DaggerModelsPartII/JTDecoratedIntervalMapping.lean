import DaggerModelsPartII.JTTargetIntervalOverMapping
import DaggerModelsPartII.JTDecoratedCylinderOverMapping

/-!
# Gluing full lifts in the actual decorated cylinder

The restriction square of the cylinder lift spaces is a pullback. Each
degree gives unique gluing with the exact raw target equation, and the
two ordered endpoints are enforced on the left and right respectively.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTDecoratedIntervalMapping

open NecklaceCode JTTargetJointMarks JTTargetIntervalPullback
open JTTargetIntervalGluing (leftInclusion rightInclusion)
open JTDecoratedCylinderOverMapping
open DecoratedCylinderNecklacePresentation (underDiagram)

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (K : SimplexCategory ⥤ SSet.{0})


variable (P : Over Q.code) (j : Joint Q.code) (i : DecoratedNecklaceHomDiagram.Index W x y)

abbrev whole : SSet.{0} := rawMapping W x y Q K ((JTTargetIntervalOverMapping.whole Q.code).obj P) i
abbrev left : SSet.{0} := rawMapping W x y Q K ((JTTargetIntervalOverMapping.left Q.code j).obj P) i
abbrev right : SSet.{0} := rawMapping W x y Q K ((JTTargetIntervalOverMapping.right Q.code j).obj P) i
abbrev overlap : SSet.{0} := rawMapping W x y Q K ((JTTargetIntervalOverMapping.overlap Q.code j).obj P) i

abbrev toLeft := rawPrecomp W x y Q K ((JTTargetIntervalOverMapping.leftToWhole Q.code j).app P) i
abbrev toRight := rawPrecomp W x y Q K ((JTTargetIntervalOverMapping.rightToWhole Q.code j).app P) i
abbrev leftToOverlap := rawPrecomp W x y Q K ((JTTargetIntervalOverMapping.overlapToLeft Q.code j).app P) i
abbrev rightToOverlap := rawPrecomp W x y Q K ((JTTargetIntervalOverMapping.overlapToRight Q.code j).app P) i

/-- The cylinder lifts with the exact raw equation are glued by a strict
pullback over the full overlap, in the entire parameter simplicial set. -/
theorem isPullback :
    IsPullback (toLeft W x y Q K P j i) (toRight W x y Q K P j i)
      (leftToOverlap W x y Q K P j i) (rightToOverlap W x y Q K P j i) := by
  apply (JTTargetIntervalOverMapping.mapping_isPullback Q.code j K P ((decoratedTarget W x y Q).obj i)).of_iso
    (mappingIso W x y Q K ((JTTargetIntervalOverMapping.whole Q.code).obj P) i)
    (mappingIso W x y Q K ((JTTargetIntervalOverMapping.left Q.code j).obj P) i)
    (mappingIso W x y Q K ((JTTargetIntervalOverMapping.right Q.code j).obj P) i)
    (mappingIso W x y Q K ((JTTargetIntervalOverMapping.overlap Q.code j).obj P) i)
  · exact mappingIso_precomp W x y Q K ((JTTargetIntervalOverMapping.leftToWhole Q.code j).app P) i
  · exact mappingIso_precomp W x y Q K ((JTTargetIntervalOverMapping.rightToWhole Q.code j).app P) i
  · exact mappingIso_precomp W x y Q K ((JTTargetIntervalOverMapping.overlapToLeft Q.code j).app P) i
  · exact mappingIso_precomp W x y Q K ((JTTargetIntervalOverMapping.overlapToRight Q.code j).app P) i

private abbrev leftCode {T : NecklaceCode} (P : Over T) (j : Joint T) :=
  sourceInterval P.hom ⟨0, T.first_mem⟩ j (Fin.zero_le j.val)

private abbrev rightCode {T : NecklaceCode} (P : Over T) (j : Joint T) :=
  sourceInterval P.hom j ⟨Fin.last T.len, T.last_mem⟩ (Fin.le_last j.val)

/-- The original first vertex on the left inverse-image interval. -/
abbrev firstLeft {T : NecklaceCode} (P : Over T) (j : Joint T) :=
  pointAt (leftCode P j) (ULift.up 0)

/-- The original last vertex on the right inverse-image interval. -/
abbrev lastRight {T : NecklaceCode} (P : Over T) (j : Joint T) :=
  pointAt (rightCode P j) (ULift.up (Fin.last (rightCode P j).len))

/-- The actual specified first endpoint of the decorated cylinder. -/
def cylinderFirst : Δ[0] ⟶ ((rawTarget W x y).obj i).left :=
  SSet.boundary₁.ι₀ ≫ ((underDiagram W x y).obj i).hom

/-- The actual specified last endpoint of the decorated cylinder. -/
def cylinderLast : Δ[0] ⟶ ((rawTarget W x y).obj i).left :=
  SSet.boundary₁.ι₁ ≫ ((underDiagram W x y).obj i).hom

theorem cylinderFirst_natural {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i') :
    cylinderFirst W x y i ≫ ((rawTarget W x y).map u).left = cylinderFirst W x y i' := by
  change (SSet.boundary₁.ι₀ ≫ ((underDiagram W x y).obj i).hom) ≫
    ((underDiagram W x y).map u).right = SSet.boundary₁.ι₀ ≫ ((underDiagram W x y).obj i').hom
  rw [Category.assoc, Under.w ((underDiagram W x y).map u)]

theorem cylinderLast_natural {i i' : DecoratedNecklaceHomDiagram.Index W x y} (u : i ⟶ i') :
    cylinderLast W x y i ≫ ((rawTarget W x y).map u).left = cylinderLast W x y i' := by
  change (SSet.boundary₁.ι₁ ≫ ((underDiagram W x y).obj i).hom) ≫
    ((underDiagram W x y).map u).right = SSet.boundary₁.ι₁ ≫ ((underDiagram W x y).obj i').hom
  rw [Category.assoc, Under.w ((underDiagram W x y).map u)]

/-- The first endpoint of a full lift is its first endpoint on the left. -/
theorem first_restrict (k : SimplexCategory)
    (m : (whole W x y Q K P i).obj (op k)) :
    (firstLeft P j ⊗ₘ 𝟙 (K.obj k)) ≫ ((toLeft W x y Q K P j i).app (op k) m).left =
      (pointAt P.left (ULift.up 0) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left := by
  change (firstLeft P j ⊗ₘ 𝟙 (K.obj k)) ≫
    ((leftInclusion P.hom j ⊗ₘ 𝟙 (K.obj k)) ≫ m.left) = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, JTTargetIntervalOverMapping.left_first]

/-- The last endpoint of a full lift is its last endpoint on the right. -/
theorem last_restrict (k : SimplexCategory)
    (m : (whole W x y Q K P i).obj (op k)) :
    (lastRight P j ⊗ₘ 𝟙 (K.obj k)) ≫ ((toRight W x y Q K P j i).app (op k) m).left =
      (pointAt P.left (ULift.up (Fin.last P.left.len)) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left := by
  change (lastRight P j ⊗ₘ 𝟙 (K.obj k)) ≫
    ((rightInclusion P.hom j ⊗ₘ 𝟙 (K.obj k)) ≫ m.left) = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, JTTargetIntervalOverMapping.right_last]

/-- Compatible side lifts with the actual ordered endpoints glue uniquely,
with their whole maps and both endpoint values retained in every degree. -/
theorem existsUnique_glue (k : SimplexCategory)
    (mL : (left W x y Q K P j i).obj (op k)) (mR : (right W x y Q K P j i).obj (op k))
    (h : (leftToOverlap W x y Q K P j i).app (op k) mL =
      (rightToOverlap W x y Q K P j i).app (op k) mR)
    (hL : (firstLeft P j ⊗ₘ 𝟙 (K.obj k)) ≫ mL.left =
      fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderFirst W x y i)
    (hR : (lastRight P j ⊗ₘ 𝟙 (K.obj k)) ≫ mR.left =
      fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderLast W x y i) :
    ∃! m : (whole W x y Q K P i).obj (op k),
      (toLeft W x y Q K P j i).app (op k) m = mL ∧
      (toRight W x y Q K P j i).app (op k) m = mR ∧
      (pointAt P.left (ULift.up 0) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left =
        fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderFirst W x y i ∧
      (pointAt P.left (ULift.up (Fin.last P.left.len)) ⊗ₘ 𝟙 (K.obj k)) ≫ m.left =
        fst (Δ[0] : SSet.{0}) (K.obj k) ≫ cylinderLast W x y i := by
  have hp : IsPullback ((toLeft W x y Q K P j i).app (op k))
      ((toRight W x y Q K P j i).app (op k)) ((leftToOverlap W x y Q K P j i).app (op k))
      ((rightToOverlap W x y Q K P j i).app (op k)) :=
    (isPullback W x y Q K P j i).map ((evaluation SimplexCategoryᵒᵖ (Type)).obj (op k))
  obtain ⟨m, hmL, hmR⟩ := Types.exists_of_isPullback hp mL mR h
  refine ⟨m, ⟨hmL, hmR, ?_, ?_⟩, ?_⟩
  · rw [← first_restrict W x y Q K P j i k m, hmL]
    exact hL
  · rw [← last_restrict W x y Q K P j i k m, hmR]
    exact hR
  · intro n hn
    exact Types.ext_of_isPullback hp (hn.1.trans hmL.symm) (hn.2.1.trans hmR.symm)

end

end DaggerModels.PartII.JTDecoratedIntervalMapping
