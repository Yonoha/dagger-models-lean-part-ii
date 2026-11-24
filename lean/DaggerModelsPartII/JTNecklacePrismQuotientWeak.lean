import DaggerModelsPartII.NecklaceCylinderJointDiagram
import DaggerModelsPartII.KanLeftProper
import DaggerModelsPartII.TotalElementsWeakComparison
import DaggerModelsPartII.JTFrameProjection
import OriginalSimplicialTrivialFibrationTensor

/-! Kan weakness of the original prism quotient in native code and time. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNecklacePrismQuotientWeak

noncomputable section

private abbrev NCode := NecklaceCode
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

private theorem mono_tensor_id {S T : SSet.{0}} (i : S ⟶ T) (K : SSet.{0})
    (hi : Mono i) : Mono (i ⊗ₘ 𝟙 K) := by
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro d
  apply (mono_iff_injective _).mpr
  intro z z' h
  change (i.app d z.1, z.2) = (i.app d z'.1, z'.2) at h
  have inj := (mono_iff_injective (i.app d)).mp ((NatTrans.mono_iff_mono_app _).mp hi d)
  exact Prod.ext (inj (congrArg Prod.fst h))
    (congrArg (@Prod.snd (T.obj d) (K.obj d)) h)

private theorem fst_trivialFibration (X : SSet.{0}) (k : SimplexCategory) :
    trivialFibrations SSet.{0} (fst X (J.obj k)) := by
  let P := trivialFibrations SSet.{0}
  let q := terminal.from (J.obj k)
  have hq : P q := GroupoidSimplex.augmentation_trivialFibration k
  have htensor : P (𝟙 X ⊗ₘ q) :=
    DaggerOriginalSimplicialTrivialFibrationTensor.tensorHom_trivialFibration
      (𝟙 X) q (P.of_isIso _) hq
  haveI : IsIso (fst X (⊤_ SSet.{0})) :=
    (BinaryFan.isLimit_iff_isIso_fst terminalIsTerminal
      (BinaryFan.mk (fst X (⊤_ SSet.{0}))
        (snd X (⊤_ SSet.{0})))).1
      ⟨tensorProductIsBinaryProduct X (⊤_ SSet.{0})⟩
  have hc : P ((𝟙 X ⊗ₘ q) ≫ fst X (⊤_ SSet.{0})) :=
    P.comp_mem _ _ htensor (P.of_isIso _)
  have he : (𝟙 X ⊗ₘ q) ≫ fst X (⊤_ SSet.{0}) = fst X (J.obj k) := by
    simpa only [Category.comp_id] using tensorHom_fst (𝟙 X) q
  rwa [he] at hc

/-- The unreduced product prism, covariant in every native code and time map. -/
def prismDiagram : NCode × SimplexCategory ⥤ SSet.{0} :=
  ((CategoryTheory.Prod.fst NCode SimplexCategory ⋙ NecklaceCode.simplicialFunctor).prod'
    (CategoryTheory.Prod.snd NCode SimplexCategory ⋙ J)) ⋙
      MonoidalCategory.tensor SSet.{0}

/-- The literal quotient from the full prism onto its endpoint-reduced cylinder. -/
def quotient : prismDiagram ⟶ NecklaceCylinderJointDiagram.cylinderDiagram where
  app p := (JTNecklaceEndpointCylinder.cylinder p.1).app p.2
  naturality := by
    intro p q f
    change (f.1.map ⊗ₘ J.map f.2) ≫
        (JTNecklaceEndpointCylinder.cylinder q.1).app q.2 =
      (JTNecklaceEndpointCylinder.cylinder p.1).app p.2 ≫
        (JTNecklaceEndpointCylinder.nativeMap f.1 p.2 ≫
          (JTNecklaceEndpointCylinder.value q.1).map f.2)
    calc
      _ = ((f.1.map ⊗ₘ 𝟙 (J.obj p.2)) ≫
          (𝟙 q.1.toSSet ⊗ₘ J.map f.2)) ≫
          (JTNecklaceEndpointCylinder.cylinder q.1).app q.2 := by
            rw [tensorHom_comp_tensorHom]
            simp
      _ = (f.1.map ⊗ₘ 𝟙 (J.obj p.2)) ≫
          ((JTNecklaceEndpointCylinder.cylinder q.1).app p.2 ≫
            (JTNecklaceEndpointCylinder.value q.1).map f.2) := by
            rw [Category.assoc]
            exact congrArg (fun h ↦ (f.1.map ⊗ₘ 𝟙 (J.obj p.2)) ≫ h)
              ((JTNecklaceEndpointCylinder.cylinder q.1).naturality f.2)
      _ = _ := by
        rw [← Category.assoc, ← JTNecklaceEndpointCylinder.nativeMap_cylinder]
        rfl

/-- Positive-length necklace quotient legs are Kan weak equivalences. -/
theorem quotient_app_weak (p : NCode × SimplexCategory) (h : 0 < p.1.len) :
    WeakEquivalence (quotient.app p) := by
  have hmono : Mono (JTNecklaceEndpointCylinder.endpointInclusion p.1) :=
    NecklaceCylinderAugmentation.endpointInclusion_mono_of_pos p.1 h
  haveI : Mono (JTNecklaceEndpointCylinder.endpointInclusion p.1 ⊗ₘ 𝟙 (J.obj p.2)) :=
    mono_tensor_id _ _ hmono
  have hcof : cofibrations SSet.{0}
      (JTNecklaceEndpointCylinder.endpointInclusion p.1 ⊗ₘ 𝟙 (J.obj p.2)) := by
    haveI : Cofibration
        (JTNecklaceEndpointCylinder.endpointInclusion p.1 ⊗ₘ 𝟙 (J.obj p.2)) :=
      (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
    exact (cofibration_iff _).mp inferInstance
  have htriv := fst_trivialFibration B p.2
  haveI : WeakEquivalence (fst B (J.obj p.2)) :=
    ((mem_trivialFibrations_iff _).mp htriv).2
  have hweak : weakEquivalences SSet.{0} (fst B (J.obj p.2)) :=
    (weakEquivalence_iff _).mp inferInstance
  exact (weakEquivalence_iff _).mpr
    (kanLeftProper (JTNecklaceEndpointCylinder.isPushout p.1 p.2) hcof hweak)

/-- The opposite simplex-indexing functor is weak in each positive native code. -/
theorem quotient_app_elements_weak (p : NCode × SimplexCategory) (h : 0 < p.1.len) :
    WeakEquivalence (nerveMap (NatTrans.mapElements (quotient.app p)).op) :=
  (TotalElementsWeakComparison.elementsOpposite_weak_iff _).mpr (quotient_app_weak p h)

/-- Every positive-code restriction of the quotient is weak on total elements. -/
theorem total_weak {C : Type} [SmallCategory C]
    (D : C ⥤ NCode × SimplexCategory)
    (h : ∀ c : C, 0 < (D.obj c).1.len) :
    WeakEquivalence (nerveMap
      (TotalElementsWeakComparison.totalMap (Functor.whiskerLeft D quotient))) :=
  TotalElementsWeakComparison.totalMap_weak _ (fun c ↦ quotient_app_weak (D.obj c) (h c))

end

end DaggerModels.PartII.JTNecklacePrismQuotientWeak
