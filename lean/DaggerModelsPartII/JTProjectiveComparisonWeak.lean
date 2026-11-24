import DaggerModelsPartII.JTWeightedComparisonWeak
import DaggerModelsPartII.JTProjectiveRealizationCofibrations
import DaggerModelsPartII.FunctorComparisonTransfinite
import DaggerModelsPartII.OrdinaryDwyerKanClosure
import DaggerModelsPartII.JTBarProjectiveCofibrancy
import CoproductCellSerialization
import Mathlib.CategoryTheory.SmallObject.Basic
import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
import Mathlib.CategoryTheory.Retract

/-!
# Actual JT comparison on projectively cofibrant inputs

The literal capital Lambda is ordinary DK after forgetting dagger on every
projectively cofibrant input. Single projective free boundary pushouts carry
comparison weakness because both free endpoint comparisons are already weak.
The original coproduct-cell serialization and source-controlled small object
factorization extend this to a chosen cellular target; a split retract returns
the result to the original input. The separately proved coherent-unitary
object witness then gives the literal dagger DK condition.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra DaggerModels Simplicial
open DaggerModels.OrdinaryDwyerKanCore DaggerOrdinaryRigidificationCof
open DaggerUnitaryInvariance

namespace DaggerModels.PartII.JTProjectiveComparisonWeak

open JTActualLambdaCellGluing JTProjectiveGeneratorRealization
open JTProjectiveRealizationCofibrations

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev I : MorphismProperty Source :=
  ProjectiveKanDiagram.boundaryGenerators ReverseSimplexᵒᵖ
private abbrev Co : MorphismProperty Source := I.rlp.llp
private abbrev F := sourceRealization
private abbrev G := targetRealization
private abbrev α := ordinaryComparison
private abbrev Q : MorphismProperty Source :=
  FunctorComparisonTransfinite.Q F G α Co

private local instance : HasColimits Source := inferInstance
private local instance : HasColimits SimplicialCat.{0, 0} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits
private local instance : PreservesColimitsOfSize.{0, 0}
    DaggerSimplicialCat.forget.{0, 0} :=
  DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
private local instance : PreservesColimitsOfSize.{0, 0} F := by
  letI : PreservesColimitsOfSize.{0, 0} JTFrameAdjunction.frameRealization :=
    JTFrameAdjunction.adjunction.leftAdjoint_preservesColimits
  infer_instance
private local instance : PreservesColimitsOfSize.{0, 0} G := by
  letI : PreservesColimitsOfSize.{0, 0}
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification) :=
    JTCoendMate.compositeAdjunction.leftAdjoint_preservesColimits
  infer_instance
private local instance : MorphismProperty.IsStableUnderTransfiniteComposition.{0} Co where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := by
    dsimp [Co]
    infer_instance

private theorem F_maps_Co {X Y : Source} (f : X ⟶ Y) (hf : Co f) :
    ordinaryCofibrations (F.map f) :=
  gamma_projective_cofibration f hf

private theorem G_maps_Co {X Y : Source} (f : X ⟶ Y) (hf : Co f) :
    ordinaryCofibrations (G.map f) :=
  xi_projective_cofibration f hf

/-- The original two realizations preserve the same projective initial
object, so the literal comparison at that source is an isomorphism. -/
private theorem initial_comparison_W : W (α.app (⊥_ Source)) := by
  have h0 : IsInitial (⊥_ Source) := initialIsInitial
  have hF : IsInitial (F.obj (⊥_ Source)) := h0.isInitialObj F _
  have hG : IsInitial (G.obj (⊥_ Source)) := h0.isInitialObj G _
  have heq : α.app (⊥_ Source) = (hF.uniqueUpToIso hG).hom := hF.hom_ext _ _
  rw [heq]
  exact W.of_isIso _

/-- An original free boundary cell, pushed out along an arbitrary attaching
map, propagates comparison weakness across its target arrow. -/
private theorem single_pushouts_le_Q : I.pushouts ≤ Q := by
  rintro X Y f ⟨A, B, p, a, g, hp, sq⟩
  have hpCo : Co p := I.le_llp_rlp p hp
  have hfCo : Co f := I.pushouts_le_llp_rlp f ⟨A, B, p, a, g, hp, sq⟩
  obtain ⟨⟨m, n⟩⟩ := hp
  refine ⟨hfCo, ?_⟩
  intro hX
  have hA : W (α.app
      ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ m).obj (SSet.boundary n))) := by
    change W (DaggerSimplicialCat.forget.map
      ((actualFreeComparison m.unop).app (SSet.boundary n)))
    exact JTWeightedComparisonWeak.actualFreeComparison_W m.unop (SSet.boundary n)
  have hB : W (α.app
      ((ProjectiveKanDiagram.free ReverseSimplexᵒᵖ m).obj Δ[n])) := by
    change W (DaggerSimplicialCat.forget.map
      ((actualFreeComparison m.unop).app Δ[n]))
    exact JTWeightedComparisonWeak.actualFreeComparison_W m.unop Δ[n]
  exact actualComparison_isPushout sq.flip
    (F_maps_Co _ hpCo) (G_maps_Co _ hpCo) hA hB hX

/-- Every original coproduct batch pushout belongs to Q, using the literal
one-cell serialization rather than a coproduct theorem for ordinary W. -/
private theorem batch_pushouts_le_Q : (coproducts.{0} I).pushouts ≤ Q := by
  letI : MorphismProperty.IsStableUnderTransfiniteComposition.{0} Q :=
    FunctorComparisonTransfinite.Q_transfinite F G α Co F_maps_Co G_maps_Co
  exact (DaggerCoproductCellSerialization.coproduct_pushouts_le I).trans
    ((MorphismProperty.transfiniteCompositions_monotone single_pushouts_le_Q).trans
      Q.transfiniteCompositions_le)

/-- Actual ordinary DK weakness on every projectively cofibrant input,
expressed by its original generator-defined initial cofibration. -/
theorem comparison_W_of_projective_cofibrant (X : Source)
    (hX : Co (initial.to X)) : W (α.app X) := by
  letI : MorphismProperty.IsStableUnderTransfiniteComposition.{0} Q :=
    FunctorComparisonTransfinite.Q_transfinite F G α Co F_maps_Co G_maps_Co
  letI : HasSmallObjectArgument.{0} I :=
    ProjectiveKanDiagram.boundaryGenerators_smallObjectArgument ReverseSimplexᵒᵖ
  obtain ⟨κ, hReg, hBot, hκ⟩ :=
    (HasSmallObjectArgument.exists_cardinal (I := I))
  letI : Fact κ.IsRegular := hReg
  letI : OrderBot κ.ord.ToType := hBot
  letI : IsCardinalForSmallObjectArgument.{0} I κ := hκ
  let f : (⊥_ Source) ⟶ X := initial.to X
  let j := SmallObject.ιObj I κ f
  let p := SmallObject.πObj I κ f
  have hjQ : Q j :=
    Q.transfiniteCompositionsOfShape_le κ.ord.ToType j
      (MorphismProperty.transfiniteCompositionsOfShape_monotone κ.ord.ToType
        batch_pushouts_le_Q j (SmallObject.transfiniteCompositionsOfShape_ιObj I κ f))
  have hCell : W (α.app (SmallObject.obj I κ f)) := hjQ.2 initial_comparison_W
  have sq : CommSq j f p (𝟙 X) := ⟨by simp [j, p, f]⟩
  have hLift : HasLiftingProperty f p := hX _ (SmallObject.rlp_πObj I κ f)
  letI : sq.HasLift := hLift.sq_hasLift sq
  let r : Retract X (SmallObject.obj I κ f) :=
    { i := sq.lift
      r := p
      retract := sq.fac_right }
  exact OrdinaryDwyerKanClosure.of_retract (NatTrans.retractArrowApp α r) hCell

/-- Model-category phrasing of the same statement, with no changed
projective cofibration class. -/
theorem comparison_W_of_isCofibrant (X : Source)
    (hX : (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsCofibrant X)) : W (α.app X) := by
  letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  have hCof : Cofibration (initial.to X) := (isCofibrant_iff X).mp hX
  rw [cofibration_iff, ProjectiveKanDiagram.model_cofibrations] at hCof
  exact comparison_W_of_projective_cofibrant X hCof

/-- The literal capital comparison is dagger DK on every original
projectively cofibrant reversal simplicial space. -/
theorem comparison_daggerDK_of_isCofibrant (X : Source)
    (hX : (letI := ProjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsCofibrant X)) :
    DaggerGlobalDK.daggerDK standardReplacement (JTCoendComparison.comparison.app X) := by
  refine ⟨?_, JTCoendEssentialSurjectivity.comparison_ess X⟩
  have hW := comparison_W_of_isCofibrant X hX
  change W (DaggerSimplicialCat.forget.map (JTCoendComparison.comparison.app X)) at hW
  intro a b
  exact hW.1 a b

/-- The original projective bar is a valid instance of the cofibrant-input
comparison theorem. This statement does not assert derived augmentation
weakness or the density conclusion. -/
theorem comparison_bar_daggerDK (X : DaggerSSet.{0}) :
    DaggerGlobalDK.daggerDK standardReplacement
      (JTCoendComparison.comparison.app (JTProjectiveBar.barOnDagger.obj X)) :=
  comparison_daggerDK_of_isCofibrant _
    (JTBarProjectiveCofibrancy.barOnDagger_isCofibrant X)

end

end DaggerModels.PartII.JTProjectiveComparisonWeak
