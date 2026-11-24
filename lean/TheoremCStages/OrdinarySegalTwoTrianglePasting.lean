import OrdinarySegalUnitMiddleFibrations
import OrdinarySegalUnitPullbackWeak

/-!
# Pasting the two literal unit triangles

The strict two-triangle pullback is also the pullback of the two unit
triangle spaces over their common middle face. The first common-face map
is a Kan fibration by the checked outer-horn base change. Its section is
the first literal unit comparison, so the Segal condition makes it a
trivial fibration. Base change and the second literal unit comparison
then prove that the exact two-triangle comparison is Kan weak.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalTwoTrianglePasting

open OrdinaryCSSLocalization (Space)
open OrdinarySegalTwoTriangleUnitWeak
open OrdinarySegalUnitMiddleFibrations

noncomputable section

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory SimplexCategoryᵒᵖ

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)
private abbrev d₀ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (0 : Fin 3)).op
private abbrev d₁ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (1 : Fin 3)).op
private abbrev d₂ (W : Space) : row W 2 ⟶ row W 1 :=
  W.map (SimplexCategory.δ (Fin.last 2)).op
private abbrev d₁₀ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (1 : Fin 2)).op
private abbrev d₀₀ (W : Space) : row W 1 ⟶ row W 0 :=
  W.map (SimplexCategory.δ (0 : Fin 2)).op
private abbrev s (W : Space) : row W 0 ⟶ row W 1 :=
  W.map (SimplexCategory.σ (0 : Fin 1)).op

private abbrev firstUnit (W : Space) := pullback (d₂ W) (s W)
private abbrev secondUnit (W : Space) := pullback (d₀ W) (s W)
private abbrev largePullback (W : Space) :=
  pullback (outerPair W) (degeneratePair W)

/-- The second unit triangle's common middle face. -/
def secondCommonFace (W : Space) : secondUnit W ⟶ row W 1 :=
  pullback.fst (d₀ W) (s W) ≫ d₁ W

private def lowerUnit (W : Space) : largePullback W ⟶ firstUnit W :=
  pullback.lift
    (pullback.fst (outerPair W) (degeneratePair W) ≫
      pullback.fst (d₁ W) (d₁ W))
    (pullback.snd (outerPair W) (degeneratePair W) ≫ prod.fst) (by
      have h := congrArg (fun z ↦ z ≫ prod.fst)
        (pullback.condition (f := outerPair W) (g := degeneratePair W))
      simpa only [Category.assoc, outerPair, prod.lift_fst,
        degeneratePair, prod.map_fst] using h)

private def upperUnit (W : Space) : largePullback W ⟶ secondUnit W :=
  pullback.lift
    (pullback.fst (outerPair W) (degeneratePair W) ≫
      pullback.snd (d₁ W) (d₁ W))
    (pullback.snd (outerPair W) (degeneratePair W) ≫ prod.snd) (by
      have h := congrArg (fun z ↦ z ≫ prod.snd)
        (pullback.condition (f := outerPair W) (g := degeneratePair W))
      simpa only [Category.assoc, outerPair, prod.lift_snd,
        degeneratePair, prod.map_snd] using h)

private theorem lowerUnit_fst (W : Space) :
    lowerUnit W ≫ pullback.fst (d₂ W) (s W) =
      pullback.fst (outerPair W) (degeneratePair W) ≫
        pullback.fst (d₁ W) (d₁ W) := by
  simp only [lowerUnit, pullback.lift_fst]

private theorem lowerUnit_snd (W : Space) :
    lowerUnit W ≫ pullback.snd (d₂ W) (s W) =
      pullback.snd (outerPair W) (degeneratePair W) ≫ prod.fst := by
  simp only [lowerUnit, pullback.lift_snd]

private theorem upperUnit_fst (W : Space) :
    upperUnit W ≫ pullback.fst (d₀ W) (s W) =
      pullback.fst (outerPair W) (degeneratePair W) ≫
        pullback.snd (d₁ W) (d₁ W) := by
  simp only [upperUnit, pullback.lift_fst]

private theorem upperUnit_snd (W : Space) :
    upperUnit W ≫ pullback.snd (d₀ W) (s W) =
      pullback.snd (outerPair W) (degeneratePair W) ≫ prod.snd := by
  simp only [upperUnit, pullback.lift_snd]

private theorem lower_upper_common (W : Space) :
    lowerUnit W ≫ firstCommonFace W =
      upperUnit W ≫ secondCommonFace W := by
  have h := congrArg
    (fun z ↦ pullback.fst (outerPair W) (degeneratePair W) ≫ z)
    (pullback.condition (f := d₁ W) (g := d₁ W))
  rw [firstCommonFace, secondCommonFace,
    ← Category.assoc, ← Category.assoc,
    lowerUnit_fst, upperUnit_fst]
  simpa only [Category.assoc] using h

private def gluing (W : Space) {X : SSet.{0}}
    (a : X ⟶ firstUnit W) (b : X ⟶ secondUnit W)
    (h : a ≫ firstCommonFace W = b ≫ secondCommonFace W) :
    X ⟶ largePullback W := by
  let t : X ⟶ twoTriangles W :=
    pullback.lift (a ≫ pullback.fst (d₂ W) (s W))
      (b ≫ pullback.fst (d₀ W) (s W)) (by
        simpa only [firstCommonFace, secondCommonFace, Category.assoc] using h)
  let v : X ⟶ row W 0 ⨯ row W 0 :=
    prod.lift (a ≫ pullback.snd (d₂ W) (s W))
      (b ≫ pullback.snd (d₀ W) (s W))
  have hv : t ≫ outerPair W = v ≫ degeneratePair W := by
    apply prod.hom_ext
    · simp only [Category.assoc, outerPair, prod.lift_fst,
        degeneratePair, prod.map_fst, t, v,
        pullback.lift_fst_assoc, prod.lift_fst_assoc]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ a ≫ z)
          (pullback.condition (f := d₂ W) (g := s W))
    · simp only [Category.assoc, outerPair, prod.lift_snd,
        degeneratePair, prod.map_snd, t, v,
        pullback.lift_snd_assoc, prod.lift_snd_assoc]
      simpa only [Category.assoc] using
        congrArg (fun z ↦ b ≫ z)
          (pullback.condition (f := d₀ W) (g := s W))
  exact pullback.lift t v hv

private theorem gluing_lower (W : Space) {X : SSet.{0}}
    (a : X ⟶ firstUnit W) (b : X ⟶ secondUnit W)
    (h : a ≫ firstCommonFace W = b ≫ secondCommonFace W) :
    gluing W a b h ≫ lowerUnit W = a := by
  apply pullback.hom_ext
  · rw [Category.assoc, lowerUnit_fst, ← Category.assoc]
    dsimp only [gluing]
    erw [pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, lowerUnit_snd, ← Category.assoc]
    dsimp only [gluing]
    erw [pullback.lift_snd, prod.lift_fst]

private theorem gluing_upper (W : Space) {X : SSet.{0}}
    (a : X ⟶ firstUnit W) (b : X ⟶ secondUnit W)
    (h : a ≫ firstCommonFace W = b ≫ secondCommonFace W) :
    gluing W a b h ≫ upperUnit W = b := by
  apply pullback.hom_ext
  · rw [Category.assoc, upperUnit_fst, ← Category.assoc]
    dsimp only [gluing]
    erw [pullback.lift_fst, pullback.lift_snd]
  · rw [Category.assoc, upperUnit_snd, ← Category.assoc]
    dsimp only [gluing]
    erw [pullback.lift_snd, prod.lift_snd]

/-- The exact two-triangle pullback is the pullback of the two unit
triangle spaces over their common d₁ edge. -/
theorem twoTriangle_isPullback (W : Space) :
    IsPullback (lowerUnit W) (upperUnit W)
      (firstCommonFace W) (secondCommonFace W) := by
  refine {
    w := lower_upper_common W
    isLimit' := ?_ }
  refine ⟨PullbackCone.IsLimit.mk _
    (fun t ↦ gluing W t.fst t.snd t.condition)
    (fun t ↦ gluing_lower W t.fst t.snd t.condition)
    (fun t ↦ gluing_upper W t.fst t.snd t.condition)
    (fun t m hm₀ hm₁ ↦ ?_)⟩
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · have h := congrArg
        (fun z ↦ z ≫ pullback.fst (d₂ W) (s W)) hm₀
      simpa [Category.assoc, lowerUnit_fst, gluing] using h
    · have h := congrArg
        (fun z ↦ z ≫ pullback.fst (d₀ W) (s W)) hm₁
      simpa [Category.assoc, upperUnit_fst, gluing] using h
  · apply prod.hom_ext
    · have h := congrArg
        (fun z ↦ z ≫ pullback.snd (d₂ W) (s W)) hm₀
      simpa [Category.assoc, lowerUnit_snd, gluing] using h
    · have h := congrArg
        (fun z ↦ z ≫ pullback.snd (d₀ W) (s W)) hm₁
      simpa [Category.assoc, upperUnit_snd, gluing] using h

private theorem firstUnit_common (W : Space) :
    OrdinarySegalUnitPullbackWeak.firstUnitComparison W ≫
      firstCommonFace W = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫
      SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  rw [firstCommonFace, OrdinarySegalUnitPullbackWeak.firstUnitComparison,
    KanBinaryUnitPullback.unitComparison, ← Category.assoc,
    pullback.lift_fst]
  change W.map (SimplexCategory.σ (0 : Fin 2)).op ≫ d₁ W = 𝟙 _
  rw [← W.map_comp, ← op_comp, h, op_id, W.map_id]

private theorem secondUnit_common (W : Space) :
    OrdinarySegalUnitPullbackWeak.secondUnitComparison W ≫
      secondCommonFace W = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫
      SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  rw [secondCommonFace, OrdinarySegalUnitPullbackWeak.secondUnitComparison,
    KanBinaryUnitPullback.unitComparison, ← Category.assoc,
    pullback.lift_fst]
  change W.map (SimplexCategory.σ (1 : Fin 2)).op ≫ d₁ W = 𝟙 _
  rw [← W.map_comp, ← op_comp, h, op_id, W.map_id]

private theorem comparison_lower (W : Space) :
    twoTriangleUnitComparison W ≫ lowerUnit W =
      OrdinarySegalUnitPullbackWeak.firstUnitComparison W := by
  apply pullback.hom_ext
  · calc
      (twoTriangleUnitComparison W ≫ lowerUnit W) ≫
          pullback.fst (d₂ W) (s W) =
        (twoTriangleUnitComparison W ≫
          pullback.fst (outerPair W) (degeneratePair W)) ≫
            pullback.fst (d₁ W) (d₁ W) := by
              rw [Category.assoc, lowerUnit_fst, ← Category.assoc]
      _ = insertedTriangles W ≫ pullback.fst (d₁ W) (d₁ W) := by
        rw [twoTriangleUnitComparison_fst]
      _ = W.map (SimplexCategory.σ (0 : Fin 2)).op := by
        unfold insertedTriangles
        erw [pullback.lift_fst]
        rfl
      _ = OrdinarySegalUnitPullbackWeak.firstUnitComparison W ≫
          pullback.fst (d₂ W) (s W) := by
        simp only [OrdinarySegalUnitPullbackWeak.firstUnitComparison,
          KanBinaryUnitPullback.unitComparison, pullback.lift_fst]
  · calc
      (twoTriangleUnitComparison W ≫ lowerUnit W) ≫
          pullback.snd (d₂ W) (s W) =
        (twoTriangleUnitComparison W ≫
          pullback.snd (outerPair W) (degeneratePair W)) ≫ prod.fst := by
            rw [Category.assoc, lowerUnit_snd, ← Category.assoc]
      _ = OrdinarySegalOrderedMappingFibres.endpointArrow W ≫ prod.fst := by
        rw [twoTriangleUnitComparison_snd]
      _ = d₁₀ W := OrdinarySegalOrderedMappingFibres.endpointArrow_fst W
      _ = OrdinarySegalUnitPullbackWeak.firstUnitComparison W ≫
          pullback.snd (d₂ W) (s W) := by
        simp only [OrdinarySegalUnitPullbackWeak.firstUnitComparison,
          KanBinaryUnitPullback.unitComparison, pullback.lift_snd]

private theorem comparison_upper (W : Space) :
    twoTriangleUnitComparison W ≫ upperUnit W =
      OrdinarySegalUnitPullbackWeak.secondUnitComparison W := by
  apply pullback.hom_ext
  · calc
      (twoTriangleUnitComparison W ≫ upperUnit W) ≫
          pullback.fst (d₀ W) (s W) =
        (twoTriangleUnitComparison W ≫
          pullback.fst (outerPair W) (degeneratePair W)) ≫
            pullback.snd (d₁ W) (d₁ W) := by
              rw [Category.assoc, upperUnit_fst, ← Category.assoc]
      _ = insertedTriangles W ≫ pullback.snd (d₁ W) (d₁ W) := by
        rw [twoTriangleUnitComparison_fst]
      _ = W.map (SimplexCategory.σ (1 : Fin 2)).op := by
        unfold insertedTriangles
        erw [pullback.lift_snd]
        rfl
      _ = OrdinarySegalUnitPullbackWeak.secondUnitComparison W ≫
          pullback.fst (d₀ W) (s W) := by
        simp only [OrdinarySegalUnitPullbackWeak.secondUnitComparison,
          KanBinaryUnitPullback.unitComparison, pullback.lift_fst]
  · calc
      (twoTriangleUnitComparison W ≫ upperUnit W) ≫
          pullback.snd (d₀ W) (s W) =
        (twoTriangleUnitComparison W ≫
          pullback.snd (outerPair W) (degeneratePair W)) ≫ prod.snd := by
            rw [Category.assoc, upperUnit_snd, ← Category.assoc]
      _ = OrdinarySegalOrderedMappingFibres.endpointArrow W ≫ prod.snd := by
        rw [twoTriangleUnitComparison_snd]
      _ = d₀₀ W := OrdinarySegalOrderedMappingFibres.endpointArrow_snd W
      _ = OrdinarySegalUnitPullbackWeak.secondUnitComparison W ≫
          pullback.snd (d₀ W) (s W) := by
        simp only [OrdinarySegalUnitPullbackWeak.secondUnitComparison,
          KanBinaryUnitPullback.unitComparison, pullback.lift_snd]

/-- The exact original two-triangle comparison is a Kan weak
equivalence for every injectively Kan fibrant ordinary Segal space. -/
theorem twoTriangleUnitComparison_weak (W : Space) [IsFibrant W]
    (hSegal : OrdinaryCSSConditions.segalCondition W) :
    WeakEquivalence (twoTriangleUnitComparison W) := by
  haveI : Fibration (firstCommonFace W) := firstCommonFace_fibration W
  haveI : WeakEquivalence
      (OrdinarySegalUnitPullbackWeak.firstUnitComparison W) :=
    OrdinarySegalUnitPullbackWeak.firstUnitComparison_weak W hSegal
  haveI : WeakEquivalence (firstCommonFace W) :=
    weakEquivalence_of_precomp_of_fac (firstUnit_common W)
  haveI : WeakEquivalence (upperUnit W) :=
    SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
      (twoTriangle_isPullback W)
  haveI : WeakEquivalence
      (OrdinarySegalUnitPullbackWeak.secondUnitComparison W) :=
    OrdinarySegalUnitPullbackWeak.secondUnitComparison_weak W hSegal
  exact weakEquivalence_of_postcomp_of_fac (comparison_upper W)

#print axioms twoTriangle_isPullback
#print axioms twoTriangleUnitComparison_weak

end

end DaggerModels.PartII.OrdinarySegalTwoTrianglePasting
