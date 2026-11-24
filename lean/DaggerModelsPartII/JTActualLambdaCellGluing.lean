import DaggerModelsPartII.OrdinaryDwyerKanPushoutComparison
import DaggerModelsPartII.OrdinaryFilteredDwyerKanComparison
import DaggerModelsPartII.JTWeightedFrameOrdinaryCofibrations
import DaggerModelsPartII.JTOrdinaryFrameWeakEquivalences

/-!
# Actual JT comparison and cofibration-cell gluing

The original ordinary DK pushout theorem applies to the literal capital
Lambda and the independently descended weighted comparison. The two actual
realizations preserve the supplied pushout, and their attachment legs are
proved ordinary cofibrations. All component-weakness premises remain explicit;
this is the successor step, not an assertion of arbitrary-weight weakness.
-/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels Simplicial
open DaggerModels.OrdinaryDwyerKanCore DaggerOrdinaryRigidificationCof

namespace DaggerModels.PartII.JTActualLambdaCellGluing

open JTProjectiveGeneratorRealization JTWeightedFrameOrdinaryCofibrations
open JTRelativeReedyFrame

noncomputable section

private local instance : HasColimits DaggerSimplicialCat.{0, 0} :=
  daggerSimplicialCatHasColimits
private local instance : PreservesColimitsOfSize.{0, 0}
    DaggerSimplicialCat.forget.{0, 0} :=
  DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize

/-- The actual source realization followed by the original dagger forgetting. -/
abbrev sourceRealization := JTFrameAdjunction.frameRealization ⋙ DaggerSimplicialCat.forget

/-- The actual JT realization followed by the original rigidification and forgetting. -/
abbrev targetRealization :=
  (DaggerJTRealization.daggerRealization ⋙
    OrdinaryRigidification.DaggerRigidification.daggerRigidification) ⋙
      DaggerSimplicialCat.forget

/-- The literal capital comparison after forgetting dagger. -/
def ordinaryComparison : sourceRealization ⟶ targetRealization :=
  Functor.whiskerRight JTCoendComparison.comparison DaggerSimplicialCat.forget

private local instance : PreservesColimitsOfSize.{0, 0} sourceRealization := by
  letI : PreservesColimitsOfSize.{0, 0} JTFrameAdjunction.frameRealization :=
    JTFrameAdjunction.adjunction.leftAdjoint_preservesColimits
  infer_instance

private local instance : PreservesColimitsOfSize.{0, 0} targetRealization := by
  letI : PreservesColimitsOfSize.{0, 0}
      (DaggerJTRealization.daggerRealization ⋙
        OrdinaryRigidification.DaggerRigidification.daggerRigidification) :=
    JTCoendMate.compositeAdjunction.leftAdjoint_preservesColimits
  infer_instance

/-- The actual capital comparison is ordinary DK at a supplied pushout apex
when it is so at the three span objects and both actual attachment legs are
ordinary cofibrations. -/
theorem actualComparison_isPushout
    {A B D P : SegalLocalizers.ReverseDaggerSpace.{0}}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P}
    (sq : IsPushout i k l r)
    (hiΓ : ordinaryCofibrations (sourceRealization.map i))
    (hiΞ : ordinaryCofibrations (targetRealization.map i))
    (hA : W (ordinaryComparison.app A))
    (hB : W (ordinaryComparison.app B))
    (hD : W (ordinaryComparison.app D)) :
    W (ordinaryComparison.app P) :=
  OrdinaryDwyerKanPushoutComparison.weak_of_pushoutComparison
    (sq.map sourceRealization) (sq.map targetRealization) hiΓ hiΞ
    (ordinaryComparison.app A) (ordinaryComparison.app B)
    (ordinaryComparison.app D) (ordinaryComparison.app P)
    (ordinaryComparison.naturality i) (ordinaryComparison.naturality k)
    (ordinaryComparison.naturality l) (ordinaryComparison.naturality r) hA hB hD

/-- The proved cofibration premises apply to every actual projective free
coefficient mono, retaining the literal comparison at all four objects. -/
theorem actualComparison_free_mono_isPushout
    (m : ReverseSimplex) {K L : SSet.{0}} (i : K ⟶ L) [Mono i]
    {D P : SegalLocalizers.ReverseDaggerSpace.{0}}
    {k : (outerFree m).obj K ⟶ D} {l : (outerFree m).obj L ⟶ P} {r : D ⟶ P}
    (sq : IsPushout ((outerFree m).map i) k l r)
    (hK : W (ordinaryComparison.app ((outerFree m).obj K)))
    (hL : W (ordinaryComparison.app ((outerFree m).obj L)))
    (hD : W (ordinaryComparison.app D)) : W (ordinaryComparison.app P) :=
  actualComparison_isPushout sq (gamma_free_mono_cofibration m i)
    (xi_free_mono_cofibration m i) hK hL hD

/-- The independently descended actual weighted comparison after forgetting dagger. -/
def ordinaryWeightedComparison (m : ReverseSimplex) :
    gammaWeighted m ⋙ DaggerSimplicialCat.forget ⟶
      xiWeighted m ⋙ DaggerSimplicialCat.forget :=
  Functor.whiskerRight (weightedComparison m) DaggerSimplicialCat.forget

/-- The same genuine successor gluing theorem for the actual weighted frames. -/
theorem weightedComparison_mono_isPushout
    (m : ReverseSimplex) {A B D P : SSet.{0}}
    {i : A ⟶ B} {k : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P} [Mono i]
    (sq : IsPushout i k l r)
    (hA : W ((ordinaryWeightedComparison m).app A))
    (hB : W ((ordinaryWeightedComparison m).app B))
    (hD : W ((ordinaryWeightedComparison m).app D)) :
    W ((ordinaryWeightedComparison m).app P) := by
  let G := gammaWeighted m ⋙ DaggerSimplicialCat.forget
  let X := xiWeighted m ⋙ DaggerSimplicialCat.forget
  letI : PreservesColimitsOfSize.{0, 0} (gammaWeighted m) :=
    (gammaWeightedAdjunction m).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} (xiWeighted m) :=
    (xiWeightedAdjunction m).leftAdjoint_preservesColimits
  have hΓ : ordinaryCofibrations (G.map i) := gamma_weighted_mono_cofibration m i
  have hΞ : ordinaryCofibrations (X.map i) := xi_weighted_mono_cofibration m i
  exact OrdinaryDwyerKanPushoutComparison.weak_of_pushoutComparison
    (sq.map G) (sq.map X) hΓ hΞ
    ((ordinaryWeightedComparison m).app A) ((ordinaryWeightedComparison m).app B)
    ((ordinaryWeightedComparison m).app D) ((ordinaryWeightedComparison m).app P)
    ((ordinaryWeightedComparison m).naturality i)
    ((ordinaryWeightedComparison m).naturality k)
    ((ordinaryWeightedComparison m).naturality l)
    ((ordinaryWeightedComparison m).naturality r) hA hB hD

/-- The weighted comparison on each original represented simplex is ordinary DK,
using its exact native Yoneda-unit calibration, not a conjugated definition. -/
theorem weightedComparison_represented_W (m : ReverseSimplex) (k : SimplexCategory) :
    W ((ordinaryWeightedComparison m).app (SSet.stdSimplex.obj k)) := by
  let uΓ := (uliftYoneda.{0}.leftKanExtensionUnit (GammaOuter.obj m)).app k
  have hvertical : W (DaggerSimplicialCat.forget.map ((verticalComparison m).app k)) := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, ⦋n⦌ = k :=
      ⟨k.len, SimplexCategory.ext _ _ rfl⟩
    change W (DaggerSimplicialCat.forget.map
      (JTCoendComparison.parameterComparison.app (m, ⦋n⦌)))
    rw [JTCoendComparison.parameterComparison_app]
    exact JTOrdinaryFrameWeakEquivalences.comparison_W m n
  have heq := congrArg DaggerSimplicialCat.forget.map (weightedComparison_fac m k)
  simp only [Functor.map_comp] at heq
  have hcomp : W (DaggerSimplicialCat.forget.map uΓ ≫
      (ordinaryWeightedComparison m).app (SSet.stdSimplex.obj k)) := by
    change W (DaggerSimplicialCat.forget.map
      ((uliftYoneda.{0}.leftKanExtensionUnit (GammaOuter.obj m)).app k) ≫
        DaggerSimplicialCat.forget.map
          ((weightedComparison m).app (uliftYoneda.{0}.obj k)))
    rw [heq]
    exact W.comp_mem _ _ hvertical (W.of_isIso _)
  exact W.of_precomp _ _ (W.of_isIso _) hcomp

/-- The initial weight supplies the empty base of cellular induction. Both
actual weighted realizations preserve the same initial weight. -/
theorem weightedComparison_initial_W (m : ReverseSimplex) (K : SSet.{0})
    (hK : IsInitial K) : W ((ordinaryWeightedComparison m).app K) := by
  let G := gammaWeighted m ⋙ DaggerSimplicialCat.forget
  let X := xiWeighted m ⋙ DaggerSimplicialCat.forget
  letI : PreservesColimitsOfSize.{0, 0} (gammaWeighted m) :=
    (gammaWeightedAdjunction m).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} (xiWeighted m) :=
    (xiWeightedAdjunction m).leftAdjoint_preservesColimits
  have hG : IsInitial (G.obj K) := hK.isInitialObj G K
  have hX : IsInitial (X.obj K) := hK.isInitialObj X K
  have h : (ordinaryWeightedComparison m).app K = (hG.uniqueUpToIso hX).hom :=
    hG.hom_ext _ _
  rw [h]
  exact W.of_isIso _

/-- The literal weighted comparison is weak at a supplied filtered colimit
of monic weight transitions if it is weak at all original stages. -/
theorem weightedComparison_filtered_W
    (m : ReverseSimplex) {J : Type} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ SSet.{0}) (c : Cocone D) (hc : IsColimit c)
    (hmono : ∀ {j k : J} (f : j ⟶ k), Mono (D.map f))
    (hstage : ∀ j : J, W ((ordinaryWeightedComparison m).app (D.obj j))) :
    W ((ordinaryWeightedComparison m).app c.pt) := by
  let G := gammaWeighted m ⋙ DaggerSimplicialCat.forget
  let X := xiWeighted m ⋙ DaggerSimplicialCat.forget
  letI : PreservesColimitsOfSize.{0, 0} (gammaWeighted m) :=
    (gammaWeightedAdjunction m).leftAdjoint_preservesColimits
  letI : PreservesColimitsOfSize.{0, 0} (xiWeighted m) :=
    (xiWeightedAdjunction m).leftAdjoint_preservesColimits
  apply OrdinaryFilteredDwyerKanComparison.filtered_W_of_colimits
    (Functor.whiskerLeft D (ordinaryWeightedComparison m))
    (isColimitOfPreserves G hc) (isColimitOfPreserves X hc)
    ((ordinaryWeightedComparison m).app c.pt)
    (fun j ↦ (ordinaryWeightedComparison m).naturality (c.ι.app j))
  · intro j k f a b
    have : Mono (D.map f) := hmono f
    exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
      _ (gamma_weighted_mono_cofibration m (D.map f)) a b
  · intro j k f a b
    have : Mono (D.map f) := hmono f
    exact OrdinaryCofibrationLocalComparison.ordinaryCofibrations_le_localHomMono
      _ (xi_weighted_mono_cofibration m (D.map f)) a b
  · exact hstage

end

end DaggerModels.PartII.JTActualLambdaCellGluing
