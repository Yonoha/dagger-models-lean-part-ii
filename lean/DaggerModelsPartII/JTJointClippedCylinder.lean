import DaggerModelsPartII.JTJointClippedGluing
import DaggerModelsPartII.JTNecklacePrismQuotientWeak

/-! The clipped native comparison acts on the full endpoint-reduced cylinders. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointClippedCylinder

open JTTargetJointMarks (Joint)
open JTJointClippedGluing (nativeGlued nativeComparison wedgeIso fromOriginal_app_weak)
open JTJointIntervalQuotient (wholeCollapse)
open JTNecklaceEndpointCylinder (endpointInclusion nativeMap value)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_native_natural)
open JTNecklacePrismQuotientWeak (quotient quotient_app_weak)

noncomputable section

private theorem timeProjection_weak (X : SSet.{0}) (k : SimplexCategory) :
    WeakEquivalence (fst X (GroupoidSimplex.parameter.obj k)) := by
  let K := GroupoidSimplex.parameter.obj k
  let q := terminal.from K
  letI : WeakEquivalence q :=
    (weakEquivalence_iff _).mpr (GroupoidSimplex.augmentation_trivialFibration k).2
  letI : WeakEquivalence (𝟙 X ⊗ₘ q) :=
    (weakEquivalence_iff_GW _).mpr (DaggerSSetProductGeometric.tensorMap_geometric _ _
      (DaggerSSetProductGeometric.identity_geometric _)
      ((weakEquivalence_iff_GW _).mp inferInstance))
  letI : IsIso (fst X (⊤_ SSet.{0})) :=
    (BinaryFan.isLimit_iff_isIso_fst terminalIsTerminal
      (BinaryFan.mk (fst X (⊤_ SSet.{0})) (snd X (⊤_ SSet.{0})))).1
      ⟨tensorProductIsBinaryProduct X (⊤_ SSet.{0})⟩
  have he : (𝟙 X ⊗ₘ q) ≫ fst X (⊤_ SSet.{0}) = fst X K := by
    simpa only [Category.id_comp] using tensorHom_fst (𝟙 X) q
  rw [← he]
  infer_instance

/-- The actual cylinder augmentation is also Kan weak, including point necklaces. -/
theorem augmentation_kanWeak (T : NecklaceCode) (k : SimplexCategory) :
    WeakEquivalence (augmentation T k) := by
  by_cases h : T.len = 0
  · have hT := NecklaceCode.code_eq_point_of_zero T h
    subst T
    have hs : SSet.boundary₁.ι₀ ≫ endpointInclusion NecklaceCode.point =
        𝟙 (NecklaceCode.point).toSSet :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    letI := ReducedGroupoidCylinderAugmentation.augmentation_isIso_of_split_epi
      (endpointInclusion NecklaceCode.point) k SSet.boundary₁.ι₀ hs
    exact inferInstanceAs (WeakEquivalence
      (ReducedGroupoidCylinderAugmentation.augmentation (endpointInclusion NecklaceCode.point) k))
  · letI := quotient_app_weak (T, k) (Nat.pos_of_ne_zero h)
    letI := timeProjection_weak T.toSSet k
    exact weakEquivalence_of_precomp_of_fac
      (show quotient.app (T, k) ≫ augmentation T k = _ from augmentation_cylinder T k)

/-- For a Kan weak native map, the full endpoint-reduced cylinder map is Kan weak. -/
theorem nativeMap_weak {T V : NecklaceCode} (f : T ⟶ V)
    (h : WeakEquivalence f.map) (k : SimplexCategory) :
    WeakEquivalence (nativeMap f k) := by
  letI := h
  letI := augmentation_kanWeak T k
  letI := augmentation_kanWeak V k
  exact weakEquivalence_of_postcomp_of_fac (augmentation_native_natural f k)

variable (U : NecklaceCode) (j : Joint U)

theorem nativeComparison_app_weak (P : Over U) :
    WeakEquivalence ((nativeComparison U j).app P).left.map := by
  change WeakEquivalence (((wholeCollapse U j ≫ JTJointClippedGluing.compare U j).app P).left ≫
    (wedgeIso U j P).hom)
  letI := fromOriginal_app_weak U j P
  infer_instance

variable {I : Type} [SmallCategory I] (D : I ⥤ Over U) (time : I ⥤ SimplexCategory)

private abbrev before := (D ⋙ Over.forget U).prod' time
private abbrev after := (D ⋙ nativeGlued U j ⋙ Over.forget U).prod' time

private def indexComparison : before U D time ⟶ after U j D time :=
  NatTrans.prod'
    (Functor.whiskerRight (Functor.whiskerLeft D (nativeComparison U j)) (Over.forget U))
    (𝟙 time)

/-- Compare the complete reduced cylinders, naturally in the native and time operators. -/
def reducedComparison :
    before U D time ⋙ NecklaceCylinderJointDiagram.cylinderDiagram ⟶
      after U j D time ⋙ NecklaceCylinderJointDiagram.cylinderDiagram :=
  Functor.whiskerRight (indexComparison U j D time) NecklaceCylinderJointDiagram.cylinderDiagram

theorem reducedComparison_app (p : I) :
    (reducedComparison U j D time).app p =
      nativeMap ((nativeComparison U j).app (D.obj p)).left (time.obj p) := by
  change nativeMap ((nativeComparison U j).app (D.obj p)).left (time.obj p) ≫
    (value ((nativeGlued U j).obj (D.obj p)).left).map (𝟙 (time.obj p)) = _
  rw [(value ((nativeGlued U j).obj (D.obj p)).left).map_id, Category.comp_id]

/-- Both exact maps from the reduced cylinders to the original target agree. -/
theorem reducedComparison_native (p : I) :
    (reducedComparison U j D time).app p ≫
      augmentation ((nativeGlued U j).obj (D.obj p)).left (time.obj p) ≫
        ((nativeGlued U j).obj (D.obj p)).hom.map =
    augmentation (D.obj p).left (time.obj p) ≫ (D.obj p).hom.map := by
  rw [← Category.assoc, reducedComparison_app, augmentation_native_natural, Category.assoc]
  exact congrArg (augmentation (D.obj p).left (time.obj p) ≫ ·)
    (congrArg NecklaceCode.Hom.map (Over.w ((nativeComparison U j).app (D.obj p))))

/-- The whole endpoint-reduced cylinder comparison gives a nerve weak
equivalence on its total category of simplices. -/
theorem reducedComparison_total_weak :
    WeakEquivalence (nerveMap (TotalElementsWeakComparison.totalMap
      (reducedComparison U j D time))) := by
  apply TotalElementsWeakComparison.totalMap_weak
  intro p
  rw [reducedComparison_app]
  exact nativeMap_weak _ (nativeComparison_app_weak U j (D.obj p)) (time.obj p)

end
end DaggerModels.PartII.JTJointClippedCylinder
