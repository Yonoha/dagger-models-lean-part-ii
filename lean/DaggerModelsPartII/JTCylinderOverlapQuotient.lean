import DaggerModelsPartII.JTCylinderPrismEmbedding
import DaggerModelsPartII.JTCylinderOverlapChains
import DaggerModelsPartII.JTCylinderCellQuotient
import DaggerModelsPartII.JTCylinderQuotientIntersections

/-!
# The actual adjacent cylinder overlap is the smaller block quotient

The original cell in the smaller cylinder is followed by the actual
first-coordinate-preserving gap embedding. Its range is the intersection
of the two specified quotient cells in the larger cylinder. The resulting
isomorphism preserves the same block projection as interval augmentation.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTCylinderOverlapQuotient

open JTCylinderPrismEmbedding JTCylinderOverlapChains
open JTCylinderCellQuotient JTCylinderBlockQuotient
open JTCylinderStaircase JTCylinderQuotientImages JTCylinderQuotientIntersections

noncomputable section

/-- The common chain is exactly the smaller staircase under the actual gap map. -/
theorem overlapSimplex_eq_staircase_gap (n : ℕ) (t : Fin (n + 1)) :
    overlapSimplex n t = staircaseSimplex n t ≫ gapPrism n := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  apply SSet.prodStdSimplex.objEquiv.injective
  rw [gapPrism_objEquiv]
  apply OrderHom.ext
  funext i
  change overlapOrder n t i = gapOrder n (staircaseOrder n t i)
  apply Prod.ext
  · apply Fin.ext
    dsimp [overlapOrder, gapOrder, staircaseOrder]
    split_ifs <;> simp
  · apply Fin.ext
    dsimp [overlapOrder, gapOrder, staircaseOrder]
    split_ifs <;> simp
    omega

/-- The independently defined smaller block quotient maps into the actual
larger cylinder by the previously constructed smaller cell and gap map. -/
def overlapToCylinder (n : ℕ) (t : Fin (n + 1)) :
    blockQuotient t.val (n - t.val) ⟶ JTCylinderFrame.value.obj ⦋n + 1⦌ :=
  cellToCylinder n t ≫ gapReduced n

theorem overlapToCylinder_mono (n : ℕ) (t : Fin (n + 1)) :
    Mono (overlapToCylinder n t) := by
  letI : Mono (cellToCylinder n t) := cellToCylinder_mono n t
  letI : Mono (gapReduced n) := gapReduced_mono n
  dsimp only [overlapToCylinder]
  infer_instance

/-- The actual overlap has the same independently defined block projection. -/
theorem overlapToCylinder_augmentation (n : ℕ) (t : Fin (n + 1)) :
    overlapToCylinder n t ≫ JTCylinderFrame.augmentation.app ⦋n + 1⦌ =
      blockProjection t.val (n - t.val) := by
  rw [overlapToCylinder, Category.assoc, gapReduced_augmentation,
    cellToCylinder_augmentation]

private theorem range_precomp_epi {A B C : SSet.{0}} (e : A ⟶ B) [Epi e]
    (f : B ⟶ C) :
    SSet.Subcomplex.range (e ≫ f) = SSet.Subcomplex.range f := by
  rw [SSet.Subcomplex.range_comp, SSet.Subcomplex.range_eq_top,
    SSet.Subcomplex.image_top]

/-- The actual overlap map has exactly the intersection of the specified
adjacent quotient cells as its range, including the edge overlap at n=0. -/
theorem overlapToCylinder_range (n : ℕ) (t : Fin (n + 1)) :
    SSet.Subcomplex.range (overlapToCylinder n t) =
      quotientImage (n + 1) (Fin.succ t) ⊓
        quotientImage (n + 1) (Fin.castSucc t) := by
  letI : Epi (simplexToBlock t.val (n - t.val)) := simplexToBlock_epi _ _
  calc
    SSet.Subcomplex.range (overlapToCylinder n t) =
        SSet.Subcomplex.range
          (simplexToBlock t.val (n - t.val) ≫ overlapToCylinder n t) :=
      (range_precomp_epi _ _).symm
    _ = SSet.Subcomplex.range (blockSimplexToCylinder n t ≫ gapReduced n) := by
      rw [overlapToCylinder, ← Category.assoc, simplexToBlock_cellToCylinder]
    _ = SSet.Subcomplex.range
        ((blockSimplexIso n t).hom ≫
          staircaseSimplex n t ≫ gapPrism n ≫ JTCylinderFrame.cylinder ⦋n + 1⦌) := by
      simp only [blockSimplexToCylinder, Category.assoc, cylinder_gapReduced]
    _ = SSet.Subcomplex.range
        (staircaseSimplex n t ≫ gapPrism n ≫ JTCylinderFrame.cylinder ⦋n + 1⦌) :=
      range_precomp_epi _ _
    _ = SSet.Subcomplex.range
        (overlapSimplex n t ≫ JTCylinderFrame.cylinder ⦋n + 1⦌) := by
      rw [← Category.assoc, ← overlapSimplex_eq_staircase_gap]
    _ = (overlapImage n t).image (JTCylinderFrame.cylinder ⦋n + 1⦌) := by
      rw [SSet.Subcomplex.range_comp]
      rfl
    _ = quotientImage (n + 1) (Fin.succ t) ⊓
        quotientImage (n + 1) (Fin.castSucc t) := by
      rw [overlapImage_eq_inf, quotientImage_inf, inf_comm]

private theorem eqToIso_ι {X : SSet.{0}} {A B : X.Subcomplex} (h : A = B) :
    (eqToIso (congrArg (fun S : X.Subcomplex ↦ S.toSSet) h)).hom ≫ B.ι = A.ι := by
  subst h
  simp

/-- The original smaller block quotient is isomorphic to the actual
adjacent intersection; it is not a newly substituted quotient object. -/
def overlapRangeIso (n : ℕ) (t : Fin (n + 1)) :
    blockQuotient t.val (n - t.val) ≅
      (quotientImage (n + 1) (Fin.succ t) ⊓
        quotientImage (n + 1) (Fin.castSucc t)).toSSet := by
  letI : Mono (overlapToCylinder n t) := overlapToCylinder_mono n t
  exact asIso (SSet.Subcomplex.toRange (overlapToCylinder n t)) ≪≫
    eqToIso (congrArg (fun S : (JTCylinderFrame.value.obj ⦋n + 1⦌).Subcomplex ↦
      S.toSSet) (overlapToCylinder_range n t))

theorem overlapRangeIso_hom_ι (n : ℕ) (t : Fin (n + 1)) :
    (overlapRangeIso n t).hom ≫
        (quotientImage (n + 1) (Fin.succ t) ⊓
          quotientImage (n + 1) (Fin.castSucc t)).ι =
      overlapToCylinder n t := by
  change (SSet.Subcomplex.toRange (overlapToCylinder n t) ≫
    (eqToIso (congrArg (fun S : (JTCylinderFrame.value.obj ⦋n + 1⦌).Subcomplex ↦
      S.toSSet) (overlapToCylinder_range n t))).hom) ≫ _ = _
  rw [Category.assoc, eqToIso_ι (overlapToCylinder_range n t),
    SSet.Subcomplex.toRange_ι]

theorem overlapRangeIso_augmentation (n : ℕ) (t : Fin (n + 1)) :
    (overlapRangeIso n t).hom ≫
        (quotientImage (n + 1) (Fin.succ t) ⊓
          quotientImage (n + 1) (Fin.castSucc t)).ι ≫
        JTCylinderFrame.augmentation.app ⦋n + 1⦌ =
      blockProjection t.val (n - t.val) := by
  rw [← Category.assoc, overlapRangeIso_hom_ι, overlapToCylinder_augmentation]

/-- The SAME interval augmentation is original Joyal weak on every actual
adjacent overlap, including zero-length blocks and n=0. -/
theorem adjacent_augmentation_weak (n : ℕ) (t : Fin (n + 1)) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      ((quotientImage (n + 1) (Fin.succ t) ⊓
        quotientImage (n + 1) (Fin.castSucc t)).ι ≫
          JTCylinderFrame.augmentation.app ⦋n + 1⦌) := by
  have hIso : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (overlapRangeIso n t).hom :=
    MorphismProperty.of_isIso DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (overlapRangeIso n t).hom
  apply DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.of_precomp
    (overlapRangeIso n t).hom _ hIso
  rw [overlapRangeIso_augmentation]
  exact blockProjection_weak _ _

end

end DaggerModels.PartII.JTCylinderOverlapQuotient
