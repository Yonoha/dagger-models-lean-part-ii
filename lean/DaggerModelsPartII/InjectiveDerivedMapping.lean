import DaggerModelsPartII.InjectiveTensorMapping
import DaggerModelsPartII.CosimplicialFrameNormalization
import NativeContractibleSimplexParameter

/-!
# Strict and derived mapping spaces for injective simplicial-set diagrams

The standard simplex tensor gives the literal mapping space of diagrams.
The remaining comparison with a chosen cosimplicial resolution is controlled
by its Reedy fibrancy and its levelwise weak augmentation.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite MonoidalCategory
open CartesianMonoidalCategory
open Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.InjectiveKanDiagram

variable (C : Type u) [Category.{u} C] [hgen : Fact (GeneratorsAreAllMonos C)]

noncomputable section

local instance injectiveModel : ModelCategory (C ⥤ SSet.{u}) :=
  modelOfGeneratorDensity C hgen.out

local instance frameModel : ModelCategory (SimplexCategoryᵒᵖ ⥤ (C ⥤ SSet.{u})ᵒᵖ) :=
  simplicialReedyModelCategory (C ⥤ SSet.{u})ᵒᵖ

/-- The ordinary standard-simplex tensor, regarded as an opposite simplicial diagram. -/
def standardFrame (A : C ⥤ SSet.{u}) :
    SimplexCategoryᵒᵖ ⥤ (C ⥤ SSet.{u})ᵒᵖ :=
  (SSet.stdSimplex ⋙ diagramTensor A).op

/-- Projection of a levelwise product to the fixed diagram. -/
def diagramTensorProjection (A : C ⥤ SSet.{u}) (K : SSet.{u}) :
    (diagramTensor A).obj K ⟶ A where
  app c :=
    { app := fun _ x ↦ x.1
      naturality := by intros; rfl }
  naturality := by
    intros
    ext n x
    rfl

/-- Removing a standard-simplex factor is an injective weak equivalence. -/
theorem diagramTensorProjection_weak (A : C ⥤ SSet.{u}) (n : ℕ) :
    HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u})
      (diagramTensorProjection C A (SSet.stdSimplex.obj ⦋n⦌)) := by
  change (modelOfGeneratorDensity C hgen.out).categoryWithWeakEquivalences.weakEquivalences _
  rw [(modelOfGeneratorDensity_exactClasses C hgen.out).2]
  intro c
  have hs : HomotopicalAlgebra.weakEquivalences SSet.{u}
      (snd (SSet.stdSimplex.obj ⦋n⦌) (A.obj c)) :=
    (weakEquivalence_iff _).mp
      (DaggerNativeContractibleSimplexParameter.simplexProjection_weakEquivalence n (A.obj c))
  have hb : HomotopicalAlgebra.weakEquivalences SSet.{u}
      (β_ (A.obj c) (SSet.stdSimplex.obj ⦋n⦌)).hom :=
    (HomotopicalAlgebra.weakEquivalences SSet.{u}).of_isIso _
  have heq : (diagramTensorProjection C A (SSet.stdSimplex.obj ⦋n⦌)).app c =
      (β_ (A.obj c) (SSet.stdSimplex.obj ⦋n⦌)).hom ≫
        snd (SSet.stdSimplex.obj ⦋n⦌) (A.obj c) := by
    ext m x
    rfl
  rw [heq]
  exact (HomotopicalAlgebra.weakEquivalences SSet.{u}).comp_mem _ _ hb hs

/-- The levelwise product projections give the standard augmentation. -/
def standardAugmentation (A : C ⥤ SSet.{u}) :
    (Functor.const SimplexCategoryᵒᵖ).obj (op A) ⟶ standardFrame C A where
  app n := (diagramTensorProjection C A (SSet.stdSimplex.obj n.unop)).op
  naturality := by
    intros
    apply Quiver.Hom.unop_inj
    ext c n x
    rfl

/-- The standard frame augmentation is levelwise weak, hence Reedy weak. -/
theorem standardAugmentation_weak (A : C ⥤ SSet.{u}) :
    HomotopicalAlgebra.weakEquivalences _ (standardAugmentation C A) := by
  change simplicialReedyWeakEquivalences (C ⥤ SSet.{u})ᵒᵖ (standardAugmentation C A)
  intro n
  change HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u})ᵒᵖ
    ((diagramTensorProjection C A (SSet.stdSimplex.obj n.unop)).op)
  rw [weakEquivalences_op]
  exact diagramTensorProjection_weak C A n.unop.len

/-- The standard frame is contravariant in the fixed diagram. -/
def standardFrameMap {A B : C ⥤ SSet.{u}} (f : A ⟶ B) :
    standardFrame C B ⟶ standardFrame C A := by
  let α : diagramTensor A ⟶ diagramTensor B :=
    { app := fun K ↦ Functor.whiskerRight f (tensorRight K)
      naturality := by
        intro K L g
        ext c n x
        rfl }
  exact NatTrans.op (Functor.whiskerLeft SSet.stdSimplex α)

omit hgen in
theorem standardAugmentation_naturality {A B : C ⥤ SSet.{u}} (f : A ⟶ B) :
    standardAugmentation C B ≫ standardFrameMap C f =
      (Functor.const SimplexCategoryᵒᵖ).map f.op ≫ standardAugmentation C A := by
  apply NatTrans.ext
  funext n
  apply Quiver.Hom.unop_inj
  ext c m x
  rfl

/-- Mapping from the standard frame is naturally isomorphic to the literal mapping space. -/
def standardFrameMappingIso (A W : C ⥤ SSet.{u}) :
    (CosimplicialResolution.mappingFromOppositeDiagram W).obj (standardFrame C A) ≅
      diagramMappingSpace A W :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun := fun f ↦ f.unop
      invFun := fun f ↦ f.op
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by
        intros
        rfl)

omit hgen in
/-- The frame comparison acts by literal precomposition on diagram mapping spaces. -/
theorem standardFrameMap_mapping {A B : C ⥤ SSet.{u}} (f : A ⟶ B)
    (W : C ⥤ SSet.{u}) :
    (standardFrameMappingIso C B W).inv ≫
        (CosimplicialResolution.mappingFromOppositeDiagram W).map (standardFrameMap C f) ≫
        (standardFrameMappingIso C A W).hom = diagramMappingPrecomp f W := by
  ext n η
  rfl

/-- Reedy fibrancy of the standard tensor frames identifies the derived mapping
test with the literal simplicial mapping-space test. -/
theorem homotopyMappingWeakEquivalences_iff_strict_of_reedyFibrant
    {A B W : C ⥤ SSet.{u}} [IsFibrant W] (f : A ⟶ B)
    (hA : IsFibrant (standardFrame C A))
    (hB : IsFibrant (standardFrame C B)) :
    homotopyMappingWeakEquivalences W f ↔
      HomotopicalAlgebra.weakEquivalences SSet.{u} (diagramMappingPrecomp f W) := by
  letI := hA
  letI := hB
  rw [homotopyMappingWeakEquivalences_iff_of_frames f
    (standardAugmentation C A) (standardAugmentation C B)
    (standardAugmentation_weak C A) (standardAugmentation_weak C B)
    (standardFrameMap C f) (standardAugmentation_naturality C f)]
  rw [← standardFrameMap_mapping C f W]
  simp only [(HomotopicalAlgebra.weakEquivalences SSet.{u}).cancel_left_of_respectsIso,
    (HomotopicalAlgebra.weakEquivalences SSet.{u}).cancel_right_of_respectsIso]

end

end DaggerModels.PartII.InjectiveKanDiagram
