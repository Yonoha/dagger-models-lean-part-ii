import DaggerModelsPartII.ProjectiveKanDiagram
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import SSetGluing

/-!
# Kan and projective left properness

The existing gluing theorem for two supplied simplicial-set pushouts gives
ordinary Kan left properness. Pointwise evaluation then gives projective left
properness for simplicial-set diagrams.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII

/-- The ordinary Kan model on simplicial sets is left proper. -/
theorem kanLeftProper {A B D P : SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : cofibrations SSet.{u} i)
    (hk : HomotopicalAlgebra.weakEquivalences SSet.{u} k) :
    HomotopicalAlgebra.weakEquivalences SSet.{u} l := by
  haveI : Cofibration i := (cofibration_iff i).mpr hi
  haveI : Mono i := (SSet.modelCategoryQuillen.cofibration_iff i).mp inferInstance
  have hA : DaggerSSetGluing.GW (𝟙 A) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mp (by infer_instance)
  have hB : DaggerSSetGluing.GW (𝟙 B) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mp (by infer_instance)
  have hD : DaggerSSetGluing.GW k :=
    (DaggerSSetGluing.weakEquivalence_iff_GW k).mp
      ((weakEquivalence_iff k).mpr hk)
  have hl : DaggerSSetGluing.GW l :=
    DaggerSSetGluing.geometric_of_pushout_cube i (𝟙 A) (𝟙 B) i
      i k l r (IsPushout.of_id_snd) sq (𝟙 A) (𝟙 B) k l
      (by simp) (by simp) (by simp) (by simpa using sq.w) hA hB hD
  exact (weakEquivalence_iff l).mp
    ((DaggerSSetGluing.weakEquivalence_iff_GW l).mpr hl)

end DaggerModels.PartII

namespace DaggerModels.PartII.ProjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

/-- A Kan left-properness theorem transports pointwise to projective diagrams. -/
theorem leftProper_of_kanLeftProper
    (hKan : ∀ {A B D P : SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
      {l : B ⟶ P} {r : D ⟶ P}, IsPushout i k l r →
        cofibrations SSet.{u} i → HomotopicalAlgebra.weakEquivalences SSet.{u} k →
          HomotopicalAlgebra.weakEquivalences SSet.{u} l)
    {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (boundaryGenerators C).rlp.llp i) (hk : weakEquivalences C k) :
    weakEquivalences C l := by
  intro c
  let E := (evaluation C SSet.{u}).obj c
  have hs : IsPushout (E.map i) (E.map k) (E.map l) (E.map r) := sq.map E
  exact hKan hs (boundaryCofibrations_levelwiseCofibrations C i hi c) (hk c)

/-- The projective Kan model structure on simplicial-set diagrams is left proper. -/
theorem leftProper {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (boundaryGenerators C).rlp.llp i) (hk : weakEquivalences C k) :
    weakEquivalences C l :=
  leftProper_of_kanLeftProper C (fun sq hi hk ↦ DaggerModels.PartII.kanLeftProper sq hi hk)
    sq hi hk

/-- Left properness stated using the classes of the constructed model category. -/
theorem model_leftProper {A B D P : C ⥤ SSet.{u}} {i : A ⟶ B} {k : A ⟶ D}
    {l : B ⟶ P} {r : D ⟶ P} (sq : IsPushout i k l r)
    (hi : (@cofibrations (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithCofibrations) i)
    (hk : (@HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithWeakEquivalences) k) :
    (@HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) _
      (modelCategory C).categoryWithWeakEquivalences) l := by
  rw [model_cofibrations C] at hi
  rw [model_weakEquivalences C] at hk ⊢
  exact leftProper C sq hi hk

end DaggerModels.PartII.ProjectiveKanDiagram
