import DaggerModelsPartII.CofibrantLocalizingFamily
import DaggerModelsPartII.ResolutionMappingComponents

/-! Derived local objects and local equivalences for an arbitrary specified family. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u t

namespace DaggerModels.PartII.Localization

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- Fibrant objects passing the derived mapping test at the specified family. -/
def localObject (S : MorphismProperty C) (Z : C) : Prop :=
  IsFibrant Z ∧ S ≤ homotopyMappingWeakEquivalences Z

/-- The maps inducing weak equivalences on derived mapping spaces into all local objects. -/
def localEquivalences (S : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f ↦ ∀ Z, localObject S Z → homotopyMappingWeakEquivalences Z f

variable (S : MorphismProperty C)

/-- Equivalent local-object tests define exactly the same local-equivalence class. -/
theorem localEquivalences_eq_of_localObjects (T : MorphismProperty C)
    (h : ∀ Z, localObject S Z ↔ localObject T Z) :
    localEquivalences S = localEquivalences T := by
  ext X Y f
  exact ⟨fun hf Z hZ ↦ hf Z ((h Z).mpr hZ), fun hf Z hZ ↦ hf Z ((h Z).mp hZ)⟩

theorem weakEquivalences_le_localEquivalences :
    weakEquivalences C ≤ localEquivalences S := by
  intro X Y f hf Z hZ
  letI := hZ.1
  exact weakEquivalences_le_homotopyMappingWeakEquivalences Z f hf

theorem family_le_localEquivalences : S ≤ localEquivalences S :=
  fun _ _ f hf _ hZ ↦ hZ.2 f hf

instance : (localEquivalences S).ContainsIdentities where
  id_mem X := weakEquivalences_le_localEquivalences S _ ((weakEquivalences C).id_mem X)

instance : (localEquivalences S).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg Z hZ := by
    letI := hZ.1
    exact (homotopyMappingWeakEquivalences Z).comp_mem _ _ (hf Z hZ) (hg Z hZ)
  of_precomp f g hf hfg Z hZ := by
    letI := hZ.1
    exact (homotopyMappingWeakEquivalences Z).of_precomp _ _ (hf Z hZ) (hfg Z hZ)
  of_postcomp f g hg hfg Z hZ := by
    letI := hZ.1
    exact (homotopyMappingWeakEquivalences Z).of_postcomp _ _ (hg Z hZ) (hfg Z hZ)

instance : (localEquivalences S).IsStableUnderRetracts where
  of_retract r hg Z hZ := by
    letI := hZ.1
    exact (homotopyMappingWeakEquivalences Z).of_retract r (hg Z hZ)

/-- Weak equivalences between fibrant targets preserve locality. -/
theorem localObject_iff_of_weak {X Y : C} [IsFibrant X] [IsFibrant Y]
    (f : X ⟶ Y) (hf : weakEquivalences C f) :
    localObject S X ↔ localObject S Y := by
  constructor
  · rintro ⟨_, hX⟩
    refine ⟨inferInstance, fun A B s hs ↦ ?_⟩
    exact (homotopyMappingWeakEquivalences_target_iff f hf s).mp (hX s hs)
  · rintro ⟨_, hY⟩
    refine ⟨inferInstance, fun A B s hs ↦ ?_⟩
    exact (homotopyMappingWeakEquivalences_target_iff f hf s).mpr (hY s hs)

/-- On local fibrant objects, a local equivalence is an original weak equivalence. -/
theorem localEquivalence_iff_weak_of_local {X Y : C} (f : X ⟶ Y)
    (hX : localObject S X) (hY : localObject S Y) :
    localEquivalences S f ↔ weakEquivalences C f := by
  letI := hX.1
  letI := hY.1
  exact ⟨fun h ↦ CosimplicialResolution.weak_of_mappingTests_self f (h X hX) (h Y hY),
    weakEquivalences_le_localEquivalences S f⟩

/-- A functorial local replacement whose unit is locally weak computes the exact
local-equivalence class as the inverse image of the original weak class. -/
theorem localEquivalences_eq_inverseImage (R : C ⥤ C) (η : 𝟭 C ⟶ R)
    (hR : ∀ X, localObject S (R.obj X)) (hη : ∀ X, localEquivalences S (η.app X)) :
    localEquivalences S = (weakEquivalences C).inverseImage R := by
  ext X Y f
  change localEquivalences S f ↔ weakEquivalences C (R.map f)
  have naturality : f ≫ η.app Y = η.app X ≫ R.map f := η.naturality f
  refine Iff.trans ?_ (localEquivalence_iff_weak_of_local S _ (hR X) (hR Y))
  constructor
  · intro hf
    apply (localEquivalences S).of_precomp _ _ (hη X)
    rw [← naturality]
    exact (localEquivalences S).comp_mem _ _ hf (hη Y)
  · intro hf
    apply (localEquivalences S).of_postcomp _ _ (hη Y)
    rw [naturality]
    exact (localEquivalences S).comp_mem _ _ (hη X) hf

variable {ι : Type t} {A B : ι → C} (s : ∀ i, A i ⟶ B i)

/-- The original family and the chosen cofibrant resolutions have exactly the same local objects. -/
theorem cofibrantFamily_localObject_iff (Z : C) :
    localObject (cofibrantLocalizingFamily s) Z ↔ localObject (ofHoms s) Z := by
  constructor
  · rintro ⟨hZ, h⟩
    letI := hZ
    exact ⟨hZ, (cofibrantLocalizingFamily_le_iff s Z).mp h⟩
  · rintro ⟨hZ, h⟩
    letI := hZ
    exact ⟨hZ, (cofibrantLocalizingFamily_le_iff s Z).mpr h⟩

/-- Consequently both families specify the same local-equivalence class. -/
theorem cofibrantFamily_localEquivalences :
    localEquivalences (cofibrantLocalizingFamily s) = localEquivalences (ofHoms s) := by
  ext X Y f
  constructor
  · intro h Z hZ
    exact h Z ((cofibrantFamily_localObject_iff s Z).mpr hZ)
  · intro h Z hZ
    exact h Z ((cofibrantFamily_localObject_iff s Z).mp hZ)

end

end DaggerModels.PartII.Localization
