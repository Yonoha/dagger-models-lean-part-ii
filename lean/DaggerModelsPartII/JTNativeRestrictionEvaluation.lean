import DaggerModelsPartII.JTNativeRestrictionFamily
import DaggerModelsPartII.JTParametrizedTargetFamilyReindexEvaluation
import DaggerModelsPartII.GrothendieckContractiblePreWeak
import DaggerModelsPartII.JTNativePulledComparisonComposition

/-!
Compare the whole evaluation over all native restrictions, including every
original base operator, to the original full family evaluation. Both actual
presentation changes are weak. Existing full-family comparison and reindexing
constructors retain all internal necklaces and the exact original fixed target.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNativeRestrictionEvaluation

open JTProjectiveOrderedFiberComparison (row)
open JTParametrizedTargetFamilies (Family codes Presentation evaluate cylinders liftNatural)
open JTNativeRestrictionLabels (labels Index toOriginal)
open JTNativeRestrictionFamily (family pulledTime compatible)

noncomputable section

private theorem weak_nerve_comp {C D E : Type}
    [SmallCategory C] [SmallCategory D] [SmallCategory E]
    (a : C ⥤ D) (b : D ⥤ E)
    (ha : WeakEquivalence (nerveMap a)) (hb : WeakEquivalence (nerveMap b)) :
    WeakEquivalence (nerveMap (a ⋙ b)) := by
  haveI := ha
  haveI := hb
  change WeakEquivalence (nerveFunctor.map (a.toCatHom ≫ b.toCatHom))
  rw [nerveFunctor.map_comp]
  change WeakEquivalence (nerveMap a ≫ nerveMap b)
  infer_instance

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}

private abbrev π := JTNativeRestrictionIndex.projection (codes L)
private abbrev t := pulledTime (L := L) (time := time)

private abbrev toReindexed : Presentation (L := labels L) (time := t (L := L) (time := time)) ⥤
    Presentation (L := π (L := L) ⋙ L) (time := π (L := L) ⋙ time) :=
  JTParametrizedTargetFamilyComparison.presentation
    (L := labels L) (M := π (L := L) ⋙ L)
    (toOriginal L) (𝟙 (t (L := L) (time := time)))

/-- Retain all complete original necklaces through both actual source changes. -/
abbrev toOldPresentation : Presentation (L := labels L) (time := t (L := L) (time := time)) ⥤
    Presentation (L := L) (time := time) :=
  toReindexed (L := L) (time := time) ⋙
    JTParametrizedTargetFamilies.reindexPresentation (L := L) (time := time) (π (L := L))

/-- The full native restriction evaluation compares naturally to the old
full evaluation, with its whole internal-necklace source functor explicit. -/
def comparison (F : Family Q L time) : evaluate (family F) ⟶
    toOldPresentation (L := L) (time := time) ⋙ evaluate F :=
  JTParametrizedTargetFamilyComparison.compare
      (L := labels L) (M := π (L := L) ⋙ L)
      (toOriginal L) (𝟙 (t (L := L) (time := time)))
      (family F) (F.precomp (π (L := L))) (compatible F) ≫
    Functor.whiskerLeft (toReindexed (L := L) (time := time))
      (JTParametrizedTargetFamilies.compareEvaluation_reindex F (π (L := L))) ≫
    (Functor.associator (toReindexed (L := L) (time := time))
      (JTParametrizedTargetFamilies.reindexPresentation
        (L := L) (time := time) (π (L := L))) (evaluate F)).inv

private theorem toReindexed_weak :
    WeakEquivalence (nerveMap (toReindexed (L := L) (time := time))) :=
  JTParametrizedTargetFamilyComparison.presentation_weak
    (L := labels L) (M := π (L := L) ⋙ L)
    (toOriginal L) (𝟙 (t (L := L) (time := time)))

private theorem reindex_weak : WeakEquivalence (nerveMap
    (JTParametrizedTargetFamilies.reindexPresentation
      (L := L) (time := time) (π (L := L)))) :=
  GrothendieckContractiblePreWeak.pre_weak
    (BoundaryNecklaceComma.fiberDiagram (cylinders (L := L) (time := time)))
    (π (L := L))
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at ((codes L).obj a) (time.obj a))
    (JTNativeRestrictionIndex.projection_weak (codes L))

/-- Neither complete presentation change loses the weak type of the original
index; all native restrictions together weakly cover the old full presentation. -/
theorem toOldPresentation_weak :
    WeakEquivalence (nerveMap (toOldPresentation (L := L) (time := time))) :=
  weak_nerve_comp (toReindexed (L := L) (time := time))
    (JTParametrizedTargetFamilies.reindexPresentation
      (L := L) (time := time) (π (L := L)))
    (toReindexed_weak (L := L) (time := time)) (reindex_weak (L := L) (time := time))

/-- Full evaluated comparisons compose even when their arrows also change the
original base object, retaining their exact internal-necklace associator. -/
theorem comparison_comp (F : Family Q L time) {a b c : Index L}
    (u : a ⟶ b) (v : b ⟶ c) :
    (JTNativePulledComparisonComposition.ComparisonData.ofNatTrans
      (JTTargetCommaPullback.diagram W x y Q)
      (cylinders (L := labels L) (time := t (L := L) (time := time)))
      (labels L) (liftNatural (family F)) u v).Property
        (JTTargetCommaExactEvaluation.fromPresentation W x y Q) :=
  JTNativePulledComparisonComposition.comparison_comp_ofNatTrans
    (JTTargetCommaPullback.diagram W x y Q)
    (cylinders (L := labels L) (time := t (L := L) (time := time)))
    (labels L) (liftNatural (family F)) u v
    (JTTargetCommaExactEvaluation.fromPresentation W x y Q)

end
end DaggerModels.PartII.JTNativeRestrictionEvaluation
