import DaggerModelsPartII.HomotopyMappingEquivalence

/-! Comparing weakly augmented Reedy fibrant frames with chosen cosimplicial resolutions. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite
open scoped SSet.modelCategoryQuillen

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

local instance frameNormalizationModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ Cᵒᵖ) :=
  simplicialReedyModelCategory Cᵒᵖ

local notation "constOp" => Functor.const SimplexCategoryᵒᵖ

private structure FrameNormalization {X : C} {D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ}
    (a : (constOp).obj (op X) ⟶ D) where
  frame : CosimplicialResolution X
  projection : frame.oppositeDiagram ⟶ D
  fac : frame.augmentationOp ≫ projection = a
  projection_mem : trivialFibrations _ projection

private def normalizeFrame {X : C} {D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} [IsFibrant D]
    (a : (constOp).obj (op X) ⟶ D) (ha : weakEquivalences _ a) : FrameNormalization a := by
  let d := factorizationData (trivialCofibrations _) (fibrations _) a
  letI : Fibration d.p := (fibration_iff _).mpr d.hp
  refine ⟨⟨d.Z, d.i, d.hi, isFibrant_of_fibration d.p⟩, d.p, d.fac, ⟨d.hp, ?_⟩⟩
  exact (weakEquivalences _).of_precomp _ _ d.hi.2 (d.fac.symm ▸ ha)

/-- To compute the derived test it suffices to use weakly augmented Reedy fibrant frames. -/
theorem homotopyMappingWeakEquivalences_iff_of_frames {X Y Z : C} [IsFibrant Z]
    (f : X ⟶ Y) {D E : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} [IsFibrant D] [IsFibrant E]
    (a : (constOp).obj (op X) ⟶ D) (b : (constOp).obj (op Y) ⟶ E)
    (ha : weakEquivalences _ a) (hb : weakEquivalences _ b) (g : E ⟶ D)
    (comm : b ≫ g = (constOp).map f.op ≫ a) :
    homotopyMappingWeakEquivalences Z f ↔
      weakEquivalences SSet.{v} ((CosimplicialResolution.mappingFromOppositeDiagram Z).map g) := by
  let A := normalizeFrame a ha
  let B := normalizeFrame b hb
  have sq : CommSq ((constOp).map f.op ≫ A.frame.augmentationOp)
      B.frame.augmentationOp A.projection (B.projection ≫ g) := by
    constructor
    rw [Category.assoc, A.fac, ← Category.assoc, B.fac, comm]
  letI : HasLiftingProperty B.frame.augmentationOp A.projection :=
    hasLiftingProperty_of_wfs _ _ B.frame.augmentationOp_mem A.projection_mem.1
  let h : A.frame.Comparison B.frame f := ⟨sq.lift, sq.fac_left⟩
  rw [homotopyMappingWeakEquivalences_iff Z h]
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  have ha' : weakEquivalences SSet.{v} (F.map A.projection) :=
    (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z _
      A.projection_mem).2
  have hb' : weakEquivalences SSet.{v} (F.map B.projection) :=
    (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z _
      B.projection_mem).2
  have w := congrArg (fun k ↦ F.map k) sq.fac_right
  simp only [F.map_comp] at w
  change weakEquivalences SSet.{v} (F.map sq.lift) ↔ weakEquivalences SSet.{v} (F.map g)
  constructor
  · intro h₁
    exact (weakEquivalences SSet.{v}).of_precomp _ _ hb'
      (w ▸ (weakEquivalences SSet.{v}).comp_mem _ _ h₁ ha')
  · intro h₂
    exact (weakEquivalences SSet.{v}).of_postcomp _ _ ha'
      (w.symm ▸ (weakEquivalences SSet.{v}).comp_mem _ _ hb' h₂)

/-- A weakly augmented Reedy fibrant frame computes the chosen homotopy
mapping object after Kan localization. The isomorphism uses the existing
normalization and an actual comparison of cosimplicial resolutions. -/
def frameMappingLocalizationIso (Z : C) [IsFibrant Z]
    {X : C} {D : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ} [IsFibrant D]
    (a : (constOp).obj (op X) ⟶ D) (ha : weakEquivalences _ a) :
    (weakEquivalences SSet.{v}).Q.obj
        ((CosimplicialResolution.mappingFromOppositeDiagram Z).obj D) ≅
      (homotopyMappingFunctor Z).obj (op X) := by
  let A := normalizeFrame a ha
  let R := cosimplicialResolution X
  let r : R.Comparison A.frame (𝟙 X) := R.comparison A.frame (𝟙 X)
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  let Q := (weakEquivalences SSet.{v}).Q
  have hp : weakEquivalences SSet.{v} (F.map A.projection) :=
    (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z
      A.projection A.projection_mem).2
  have hr : weakEquivalences SSet.{v} (r.precomp Z) :=
    r.precomp_weak ((weakEquivalences C).id_mem X) Z
  letI : IsIso (Q.map (F.map A.projection)) :=
    (weakEquivalences SSet.{v}).Q_inverts _ hp
  letI : IsIso (Q.map (r.precomp Z)) :=
    (weakEquivalences SSet.{v}).Q_inverts _ hr
  exact (asIso (Q.map (F.map A.projection))).symm ≪≫
    asIso (Q.map (r.precomp Z))

/-- The localization isomorphisms respect an actual map of weakly
augmented Reedy fibrant frames over the specified source map. -/
theorem frameMappingLocalizationIso_naturality (Z : C) [IsFibrant Z]
    {X Y : C} {D E : SimplexCategoryᵒᵖ ⥤ Cᵒᵖ}
    [IsFibrant D] [IsFibrant E]
    (f : X ⟶ Y)
    (a : (constOp).obj (op X) ⟶ D)
    (b : (constOp).obj (op Y) ⟶ E)
    (ha : weakEquivalences _ a) (hb : weakEquivalences _ b)
    (g : E ⟶ D)
    (comm : b ≫ g = (constOp).map f.op ≫ a) :
    (weakEquivalences SSet.{v}).Q.map
        ((CosimplicialResolution.mappingFromOppositeDiagram Z).map g) ≫
      (frameMappingLocalizationIso Z a ha).hom =
    (frameMappingLocalizationIso Z b hb).hom ≫
      (homotopyMappingFunctor Z).map f.op := by
  let A := normalizeFrame a ha
  let B := normalizeFrame b hb
  let RX := cosimplicialResolution X
  let RY := cosimplicialResolution Y
  let rA : RX.Comparison A.frame (𝟙 X) := RX.comparison A.frame (𝟙 X)
  let rB : RY.Comparison B.frame (𝟙 Y) := RY.comparison B.frame (𝟙 Y)
  let c : RX.Comparison RY f := RX.comparison RY f
  let F := CosimplicialResolution.mappingFromOppositeDiagram Z
  let Q := (weakEquivalences SSet.{v}).Q
  have sq : CommSq ((constOp).map f.op ≫ A.frame.augmentationOp)
      B.frame.augmentationOp A.projection (B.projection ≫ g) := by
    constructor
    rw [Category.assoc, A.fac, ← Category.assoc, B.fac, comm]
  letI : HasLiftingProperty B.frame.augmentationOp A.projection :=
    hasLiftingProperty_of_wfs _ _ B.frame.augmentationOp_mem A.projection_mem.1
  let h : A.frame.Comparison B.frame f := ⟨sq.lift, sq.fac_left⟩
  let pA := Q.map (F.map A.projection)
  let pB := Q.map (F.map B.projection)
  let uA := Q.map (rA.precomp Z)
  let uB := Q.map (rB.precomp Z)
  let t := Q.map (c.precomp Z)
  have hpA : weakEquivalences SSet.{v} (F.map A.projection) :=
    (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z
      A.projection A.projection_mem).2
  have hpB : weakEquivalences SSet.{v} (F.map B.projection) :=
    (CosimplicialResolution.mappingFromOppositeDiagram_map_trivialFibration Z
      B.projection B.projection_mem).2
  have hrA : weakEquivalences SSet.{v} (rA.precomp Z) :=
    rA.precomp_weak ((weakEquivalences C).id_mem X) Z
  have hrB : weakEquivalences SSet.{v} (rB.precomp Z) :=
    rB.precomp_weak ((weakEquivalences C).id_mem Y) Z
  letI : IsIso pA := (weakEquivalences SSet.{v}).Q_inverts _ hpA
  letI : IsIso pB := (weakEquivalences SSet.{v}).Q_inverts _ hpB
  letI : IsIso uA := (weakEquivalences SSet.{v}).Q_inverts _ hrA
  letI : IsIso uB := (weakEquivalences SSet.{v}).Q_inverts _ hrB
  have hA : pA ≫ (frameMappingLocalizationIso Z a ha).hom = uA := by
    change pA ≫ ((asIso pA).symm.hom ≫
      (asIso uA).hom) = uA
    rw [← Category.assoc]
    have hcancel : pA ≫ (asIso pA).symm.hom = 𝟙 _ :=
      (asIso pA).hom_inv_id
    rw [hcancel, Category.id_comp, asIso_hom]
  have hB : pB ≫ (frameMappingLocalizationIso Z b hb).hom = uB := by
    change pB ≫ ((asIso pB).symm.hom ≫
      (asIso uB).hom) = uB
    rw [← Category.assoc]
    have hcancel : pB ≫ (asIso pB).symm.hom = 𝟙 _ :=
      (asIso pB).hom_inv_id
    rw [hcancel, Category.id_comp, asIso_hom]
  let hc₁ : RX.Comparison B.frame f :=
    { mapOp := h.mapOp ≫ rA.mapOp
      comm := by
        calc
          B.frame.augmentationOp ≫ (h.mapOp ≫ rA.mapOp) =
              (B.frame.augmentationOp ≫ h.mapOp) ≫ rA.mapOp := by
                rw [Category.assoc]
          _ = ((constOp).map f.op ≫ A.frame.augmentationOp) ≫ rA.mapOp := by
                rw [h.comm]
          _ = (constOp).map f.op ≫
                (A.frame.augmentationOp ≫ rA.mapOp) := Category.assoc _ _ _
          _ = (constOp).map f.op ≫ RX.augmentationOp := by
                rw [rA.comm]
                rw [op_id]
                rw [← Category.assoc, ← (constOp).map_comp,
                  Category.comp_id] }
  let hc₂ : RX.Comparison B.frame f :=
    { mapOp := rB.mapOp ≫ c.mapOp
      comm := by
        calc
          B.frame.augmentationOp ≫ (rB.mapOp ≫ c.mapOp) =
              (B.frame.augmentationOp ≫ rB.mapOp) ≫ c.mapOp := by
                rw [Category.assoc]
          _ = RY.augmentationOp ≫ c.mapOp := by
                rw [rB.comm]
                rw [op_id, (constOp).map_id, Category.id_comp]
          _ = (constOp).map f.op ≫ RX.augmentationOp := c.comm }
  have hchoice : Q.map (F.map h.mapOp) ≫ uA = uB ≫ t := by
    have hc := hc₁.precomp_localized_eq hc₂ Z
    change Q.map (F.map hc₁.mapOp) = Q.map (F.map hc₂.mapOp) at hc
    have hm₁ : hc₁.mapOp = h.mapOp ≫ rA.mapOp := rfl
    have hm₂ : hc₂.mapOp = rB.mapOp ≫ c.mapOp := rfl
    rw [hm₁, hm₂] at hc
    simpa only [F.map_comp, Q.map_comp] using hc
  have hsq : pB ≫ Q.map (F.map g) =
      Q.map (F.map h.mapOp) ≫ pA := by
    have hc := congrArg (fun k ↦ Q.map (F.map k)) sq.fac_right
    simpa only [F.map_comp, Q.map_comp] using hc.symm
  apply (cancel_epi pB).1
  calc
    pB ≫ (Q.map (F.map g) ≫ (frameMappingLocalizationIso Z a ha).hom) =
        (pB ≫ Q.map (F.map g)) ≫
          (frameMappingLocalizationIso Z a ha).hom := by
            rw [Category.assoc]
    _ = (Q.map (F.map h.mapOp) ≫ pA) ≫
          (frameMappingLocalizationIso Z a ha).hom := by rw [hsq]
    _ = Q.map (F.map h.mapOp) ≫ uA := by
          rw [Category.assoc, hA]
    _ = uB ≫ t := hchoice
    _ = pB ≫ ((frameMappingLocalizationIso Z b hb).hom ≫
          (homotopyMappingFunctor Z).map f.op) := by
          change uB ≫ t = pB ≫
            ((frameMappingLocalizationIso Z b hb).hom ≫ t)
          rw [← Category.assoc, hB]

end

end DaggerModels.PartII
