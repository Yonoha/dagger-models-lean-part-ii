import DaggerModelsPartII.JTActualJointChoicePrism
import DaggerModelsPartII.TimePrismChainProjection
import DaggerModelsPartII.JTPrismChainGraphCover
import DaggerModelsPartII.JTJointRelativeGraphFamily

/-! Pull the complete relative edge prisms to ordinary full-support chains. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChoiceChainGraph

noncomputable section

private abbrev std := SSet.stdSimplex.{0}

section GenericChart

variable {I : Type} [SmallCategory I] (K N : I ⥤ SimplexCategory)

private abbrev chainIndex := TimePrismChainDiagram.Index K N
private abbrev chainBase := TimePrismChainDiagram.base K N
private abbrev chainOrdinals := TimePrismChainDiagram.ordinals K N
private abbrev coeff := TimePrismChainDiagram.coeffProjection K N
private abbrev time := TimePrismChainDiagram.timeProjection K N

/-- The coefficient-time product, natural in arbitrary coefficient and time operators. -/
def prism : I ⥤ SSet.{0} :=
  Functor.diag I ⋙ (K ⋙ std).prod (N ⋙ std) ⋙
    MonoidalCategory.tensor SSet.{0}

/-- Include a chain simplex in the original coefficient-time product. -/
def chart : chainOrdinals K N ⋙ std ⟶ chainBase K N ⋙ prism K N where
  app p := lift (std.map ((coeff K N).app p)) (std.map ((time K N).app p))
  naturality {p q} f := by
    apply CartesianMonoidalCategory.hom_ext
    · change std.map ((chainOrdinals K N).map f) ≫
          lift (std.map ((coeff K N).app q)) (std.map ((time K N).app q)) ≫
            fst _ _ =
          lift (std.map ((coeff K N).app p)) (std.map ((time K N).app p)) ≫
            (std.map (K.map ((chainBase K N).map f)) ⊗ₘ
              std.map (N.map ((chainBase K N).map f))) ≫ fst _ _
      simp only [lift_fst_assoc, tensorHom_fst, ← std.map_comp]
      exact congrArg std.map ((coeff K N).naturality f)
    · change std.map ((chainOrdinals K N).map f) ≫
          lift (std.map ((coeff K N).app q)) (std.map ((time K N).app q)) ≫
            snd _ _ =
          lift (std.map ((coeff K N).app p)) (std.map ((time K N).app p)) ≫
            (std.map (K.map ((chainBase K N).map f)) ⊗ₘ
              std.map (N.map ((chainBase K N).map f))) ≫ snd _ _
      simp only [lift_snd_assoc, tensorHom_snd, ← std.map_comp]
      exact congrArg std.map ((time K N).naturality f)

end GenericChart

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

/-- The category of full ordered chains over all higher edge choices. -/
abbrev Index := TimePrismChainDiagram.Index
  (JTActualJointChoicePrism.coefficient F j) (JTActualJointChoicePrism.choiceTime F j)

/-- Forget a chain but retain its entire higher edge choice. -/
abbrev base : Index F j ⥤ JTActualJointChoiceCover.Cover F j :=
  TimePrismChainDiagram.base _ _

/-- The ordinal carried by a full coefficient-time chain. -/
abbrev ordinals : Index F j ⥤ SimplexCategory :=
  TimePrismChainDiagram.ordinals _ _

/-- The exact original coefficient projection of each full chain. -/
abbrev toOriginal : ordinals F j ⟶
    base F j ⋙ JTActualJointChoicePrism.coefficient F j :=
  TimePrismChainDiagram.coeffProjection _ _

/-- The exact higher choice time projection of each full chain. -/
abbrev toTime : ordinals F j ⟶
    base F j ⋙ JTActualJointChoicePrism.choiceTime F j :=
  TimePrismChainDiagram.timeProjection _ _

/-- Every original coefficient vertex occurs in each full chain. -/
theorem toOriginal_surjective (p : Index F j) :
    Function.Surjective ((toOriginal F j).app p).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective _ _ p

/-- All full coefficient-time chains form a nerve weak cover of higher choices. -/
theorem base_weak : WeakEquivalence (nerveMap (base F j)) :=
  TimePrismChainProjection.projection_weak _ _

/-- The literal full-chain chart into the coefficient-time prism. -/
abbrev chainChart : ordinals F j ⋙ std ⟶
    base F j ⋙ JTActualJointChoicePrism.prisms F j :=
  chart _ _

/-- The complete ending-edge map on every ordered chain, natural in chain arrows. -/
def chainEnding : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  chainChart F j ≫ Functor.whiskerLeft (base F j) (JTActualJointChoicePrism.ending F j)

/-- The complete starting-edge map on every ordered chain, natural in chain arrows. -/
def chainStarting : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋1⦌) :=
  chainChart F j ≫ Functor.whiskerLeft (base F j) (JTActualJointChoicePrism.starting F j)

/-- Retain the original parametrized family on each full-chain choice. -/
abbrev original := F.precomp
  (base F j ⋙ JTActualJointChoiceCover.projection F j ⋙
    JTExactlyMarkedSourceDiagram.base F j)

private abbrev toBase :=
  base F j ⋙ JTActualJointChoiceCover.projection F j ⋙
    JTExactlyMarkedSourceDiagram.base F j

/-- The unchanged original graph and its original parameter, reindexed on chains. -/
abbrev X := JTJointRelativeParameters.withTime Q.map J (toBase F j ⋙ time)
  (JTJointRelativeGraphFamily.native (original F j))
  (JTTargetIntervalOverMapping.whole Q.code)

private abbrev parameter₀ := JTJointRelativeGraphFamily.originalParameter (original F j)

/-- All graph points together with a coefficient lift to the chosen full chain. -/
abbrev graphCover : Index F j ⥤ SSet.{0} :=
  JTPrismChainGraphCover.cover (X F j) (parameter₀ F j) (toOriginal F j)

/-- Recover the unchanged original graph. -/
abbrev graphProjection : graphCover F j ⟶ X F j :=
  JTPrismChainGraphCover.projection (X F j) (parameter₀ F j) (toOriginal F j)

/-- The graph projection is a trivial fibration at each chain. -/
theorem graphProjection_trivialFibration (p : Index F j) :
    trivialFibrations SSet.{0} ((graphProjection F j).app p) :=
  JTPrismChainGraphCover.projection_trivialFibration (X F j) (parameter₀ F j)
    (toOriginal F j) (toOriginal_surjective F j) p

/-- The lifted graph parameter recovers the exact old coefficient parameter. -/
theorem graphParameter_projection :
    JTPrismChainGraphCover.parameter (X F j) (parameter₀ F j) (toOriginal F j) ≫
      Functor.whiskerRight (toOriginal F j) J =
    graphProjection F j ≫ parameter₀ F j :=
  JTPrismChainGraphCover.parameter_projection (X F j) (parameter₀ F j) (toOriginal F j)

/-- The original raw evaluation equation holds on the whole lifted graph. -/
theorem graph_rawOn :
    JTJointRelativeGraphFamily.RawOn (original F j) (graphProjection F j)
      (graphProjection F j ≫ parameter₀ F j) :=
  JTJointRelativeGraphFamily.original_rawOn (original F j) (graphProjection F j)

/-- The lifted parameter and the original parameter give the same raw evaluation. -/
theorem graph_rawOn_lifted :
    JTJointRelativeGraphFamily.RawOn (original F j) (graphProjection F j)
      (JTPrismChainGraphCover.parameter (X F j) (parameter₀ F j) (toOriginal F j) ≫
        Functor.whiskerRight (toOriginal F j) J) := by
  rw [graphParameter_projection]
  exact graph_rawOn F j



end

end DaggerModels.PartII.JTActualJointChoiceChainGraph
