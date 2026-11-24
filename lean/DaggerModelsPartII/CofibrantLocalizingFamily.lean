import DaggerModelsPartII.CosimplicialQuillenComparison

/-! Cofibrant resolutions of the maps in an indexed localization family. -/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Limits MorphismProperty

universe v u t

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- A cofibration between cofibrant objects with a weak equivalence of arrows to
the original localizing map. -/
structure CofibrantArrowResolution {A B : C} (s : A ⟶ B) where
  source : C
  target : C
  hom : source ⟶ target
  comparison : Arrow.mk hom ⟶ Arrow.mk s
  cofibration : Cofibration hom
  source_cofibrant : IsCofibrant source
  target_cofibrant : IsCofibrant target
  source_weak : WeakEquivalence comparison.left
  target_weak : WeakEquivalence comparison.right

/-- First replace the source by a cofibrant object, and then factor its
composite into the original target. -/
def cofibrantArrowResolution {A B : C} (s : A ⟶ B) : CofibrantArrowResolution s := by
  let source := factorizationData (cofibrations C) (trivialFibrations C) (initial.to A)
  let target := factorizationData (cofibrations C) (trivialFibrations C) (source.p ≫ s)
  have hA : IsCofibrant source.Z := by
    rw [isCofibrant_iff_of_isInitial source.i initialIsInitial, cofibration_iff]
    exact source.hi
  have h : Cofibration target.i := (cofibration_iff _).mpr target.hi
  exact {
    source := source.Z
    target := target.Z
    hom := target.i
    comparison := Arrow.homMk source.p target.p target.fac.symm
    cofibration := h
    source_cofibrant := hA
    target_cofibrant := isCofibrant_of_cofibration target.i
    source_weak := (weakEquivalence_iff _).mpr source.hp.2
    target_weak := (weakEquivalence_iff _).mpr target.hp.2 }

/-- Passing a derived locality test is invariant under a cofibrant resolution
of its testing map. -/
theorem CofibrantArrowResolution.homotopyMappingWeakEquivalences_iff {A B : C}
    {s : A ⟶ B} (R : CofibrantArrowResolution s) (Z : C) [IsFibrant Z] :
    homotopyMappingWeakEquivalences Z R.hom ↔ homotopyMappingWeakEquivalences Z s := by
  let W := homotopyMappingWeakEquivalences Z
  have hleft : W R.comparison.left := weakEquivalences_le_homotopyMappingWeakEquivalences Z _
    ((weakEquivalence_iff _).mp R.source_weak)
  have hright : W R.comparison.right := weakEquivalences_le_homotopyMappingWeakEquivalences Z _
    ((weakEquivalence_iff _).mp R.target_weak)
  have square : R.hom ≫ R.comparison.right = R.comparison.left ≫ s := (Arrow.w R.comparison).symm
  constructor
  · intro hs
    apply W.of_precomp _ _ hleft
    rw [← square]
    exact W.comp_mem _ _ hs hright
  · intro hs
    apply W.of_postcomp _ _ hright
    rw [square]
    exact W.comp_mem _ _ hleft hs

variable {ι : Type t} {A B : ι → C} (s : ∀ i, A i ⟶ B i)

/-- The resolved family keeps one cofibrant resolution for each original index. -/
def cofibrantLocalizingFamily : MorphismProperty C :=
  ofHoms (fun i ↦ (cofibrantArrowResolution (s i)).hom)

instance : IsSmall.{t} (cofibrantLocalizingFamily s) := isSmall_ofHoms _

omit [HasLimitsOfSize.{0, 0} C] in
/-- Every member of the resolved family is a cofibration with cofibrant endpoints. -/
theorem cofibrantLocalizingFamily_cofibrancy {X Y : C} {f : X ⟶ Y}
    (hf : cofibrantLocalizingFamily s f) :
    Cofibration f ∧ IsCofibrant X ∧ IsCofibrant Y := by
  change ofHoms (fun i ↦ (cofibrantArrowResolution (s i)).hom) f at hf
  obtain ⟨i⟩ := hf
  let R := cofibrantArrowResolution (s i)
  exact ⟨R.cofibration, R.source_cofibrant, R.target_cofibrant⟩

/-- Any family of cofibrant resolutions gives the same derived tests as the
original family on every fibrant target. -/
theorem resolvedFamily_le_iff (R : ∀ i, CofibrantArrowResolution (s i))
    (Z : C) [IsFibrant Z] :
    ofHoms (fun i ↦ (R i).hom) ≤ homotopyMappingWeakEquivalences Z ↔
      ofHoms s ≤ homotopyMappingWeakEquivalences Z := by
  constructor
  · intro h X Y f hf
    obtain ⟨i⟩ := hf
    exact ((R i).homotopyMappingWeakEquivalences_iff Z).mp (h _ ⟨i⟩)
  · intro h X Y f hf
    obtain ⟨i⟩ := hf
    exact ((R i).homotopyMappingWeakEquivalences_iff Z).mpr (h _ ⟨i⟩)

/-- The original and resolved families impose the same derived tests on every
fibrant target. -/
theorem cofibrantLocalizingFamily_le_iff (Z : C) [IsFibrant Z] :
    cofibrantLocalizingFamily s ≤ homotopyMappingWeakEquivalences Z ↔
      ofHoms s ≤ homotopyMappingWeakEquivalences Z :=
  resolvedFamily_le_iff s (fun i ↦ cofibrantArrowResolution (s i)) Z

variable {D : Type u} [Category.{v} D] [ModelCategory D]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)

/-- For cofibrant source and target at each index, locality at the image of
the family under a left Quillen functor is locality after restriction. -/
theorem leftQuillen_imageLocality_iff [adj.IsQuillenAdjunction]
    [∀ i, IsCofibrant (A i)] [∀ i, IsCofibrant (B i)] (Z : D)
    [IsFibrant Z] [IsFibrant (G.obj Z)] :
    ofHoms (fun i ↦ L.map (s i)) ≤ homotopyMappingWeakEquivalences Z ↔
      ofHoms s ≤ homotopyMappingWeakEquivalences (G.obj Z) := by
  constructor
  · intro h X Y f hf
    obtain ⟨i⟩ := hf
    exact (homotopyMappingWeakEquivalences_leftQuillen_iff adj (s i) Z).mp (h _ ⟨i⟩)
  · intro h X Y f hf
    obtain ⟨i⟩ := hf
    exact (homotopyMappingWeakEquivalences_leftQuillen_iff adj (s i) Z).mpr (h _ ⟨i⟩)

/-- The family obtained by applying the left adjoint to the chosen cofibrant
resolutions of the original localizing maps. -/
def imageCofibrantLocalizingFamily : MorphismProperty D :=
  ofHoms (fun i ↦ L.map (cofibrantArrowResolution (s i)).hom)

instance : IsSmall.{t} (imageCofibrantLocalizingFamily (L := L) s) := isSmall_ofHoms _

omit [HasLimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} D] in
/-- The left Quillen images are again cofibrations between cofibrant objects. -/
theorem imageCofibrantLocalizingFamily_cofibrancy [adj.IsQuillenAdjunction]
    {X Y : D} {f : X ⟶ Y} (hf : imageCofibrantLocalizingFamily (L := L) s f) :
    Cofibration f ∧ IsCofibrant X ∧ IsCofibrant Y := by
  change ofHoms (fun i ↦ L.map (cofibrantArrowResolution (s i)).hom) f at hf
  obtain ⟨i⟩ := hf
  let R := cofibrantArrowResolution (s i)
  letI : L.PreservesCofibrations := Adjunction.IsQuillenAdjunction.preservesCofibrations adj
  letI : PreservesColimitsOfSize.{0, 0} L := adj.leftAdjoint_preservesColimits
  letI := R.cofibration
  letI := R.source_cofibrant
  letI := R.target_cofibrant
  refine ⟨inferInstance, ?_, ?_⟩
  · exact (isCofibrant_iff_of_isInitial (L.map (initial.to R.source))
      (initialIsInitial.isInitialObj L)).mpr inferInstance
  · exact (isCofibrant_iff_of_isInitial (L.map (initial.to R.target))
      (initialIsInitial.isInitialObj L)).mpr inferInstance

/-- Locality for the image of the resolved family is tested by the original
family on the right-adjoint target. -/
theorem leftQuillen_imageCofibrantLocality_iff [adj.IsQuillenAdjunction] (Z : D)
    [IsFibrant Z] [IsFibrant (G.obj Z)] :
    imageCofibrantLocalizingFamily (L := L) s ≤ homotopyMappingWeakEquivalences Z ↔
      ofHoms s ≤ homotopyMappingWeakEquivalences (G.obj Z) := by
  let R := fun i ↦ cofibrantArrowResolution (s i)
  letI : ∀ i, IsCofibrant ((R i).source) := fun i ↦ (R i).source_cofibrant
  letI : ∀ i, IsCofibrant ((R i).target) := fun i ↦ (R i).target_cofibrant
  exact (leftQuillen_imageLocality_iff (fun i ↦ (R i).hom) adj Z).trans
    (cofibrantLocalizingFamily_le_iff s (G.obj Z))

end

end DaggerModels.PartII
