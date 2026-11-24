import DaggerModelsPartII.JTRelativeReedyFrameProperties
import OrdinaryRigidificationCof
import OriginalSimplicialTrivialFibrationTensor

/-!
# Forgetting actual dagger Bergner cofibrations

This module uses the original dagger generator class and the existing ordinary
Bergner cofibration candidate, which is LLP against object-surjective local
Kan trivial fibrations. It does not assume an ordinary Bergner model instance.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory Opposite Simplicial
  MorphismProperty
open scoped SSet.modelCategoryQuillen
open DaggerModels
open DaggerOriginalSimplicialTrivialFibrationTensor
open DaggerModels.PartII.JTRelativeReedyFrame

namespace DaggerModels.PartII.JTForgottenFrameCofibrancy

noncomputable section

private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits
private local instance : ModelCategory Coefficientᵒᵖ := inferInstance
private local instance : ModelCategory (SimplexCategoryᵒᵖ ⥤ Coefficientᵒᵖ) :=
  simplicialReedyModelCategory Coefficientᵒᵖ
private local instance : HasColimits SimplicialCat.{0, 0} := simplicialCatHasColimits
private local instance : HasLimits SimplicialCat.{0, 0}ᵒᵖ := inferInstance
private local instance : PreservesLimitsOfSize.{0, 0}
    (DaggerSimplicialCat.forget.{0, 0}.op) := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{0, 0} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  exact preservesLimitsOfSize_op _

private theorem cofree_hom_map {C D : SimplicialCat.{0, 0}} (p : C ⟶ D)
    (x y : C.Obj) :
    (DaggerSimplicialCat.Cofree.functor.map p).map x y =
      p.map x y ⊗ₘ p.map y x := by
  ext n z
  rfl

/-- The actual cofree dagger functor preserves the original ordinary
object-surjective local trivial-fibration class. -/
theorem cofree_preserves_ordinaryTrivialFibrations
    {C D : SimplicialCat.{0, 0}} (p : C ⟶ D)
    (hp : DaggerOrdinaryRigidificationCof.ordinaryTrivialFibrations p) :
    DaggerGeneratingCofibrations.generators.rlp
      (DaggerSimplicialCat.Cofree.functor.map p) := by
  apply (KanQuillenReuse.generators_rlp_iff_trivial
    (DaggerSimplicialCat.Cofree.functor.map p)).2
  refine ⟨hp.1, ?_⟩
  intro x y
  rw [cofree_hom_map p x y]
  have hxy : trivialFibrations SSet.{0} (p.map x y) := by
    exact (mem_trivialFibrations_iff _).2
      ⟨(hp.2 x y).1, (KanQuillenReuse.weakEquivalence_iff_geometric _).2
        (hp.2 x y).2⟩
  have hyx : trivialFibrations SSet.{0} (p.map y x) := by
    exact (mem_trivialFibrations_iff _).2
      ⟨(hp.2 y x).1, (KanQuillenReuse.weakEquivalence_iff_geometric _).2
        (hp.2 y x).2⟩
  exact (mem_trivialFibrations_iff _).1
    (tensorHom_trivialFibration (p.map x y) (p.map y x) hxy hyx)

/-- The actual forgetful functor preserves every original dagger Bergner
cofibration, as an ordinary Bergner cofibration in the original LLP class. -/
theorem forget_preserves_cofibrations
    {C D : DaggerSimplicialCat.{0, 0}} (i : C ⟶ D)
    (hi : cofibrations DaggerSimplicialCat.{0, 0} i) :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations
      (DaggerSimplicialCat.forget.map i) := by
  rw [DaggerActualRigidificationQuillen.target_cof] at hi
  intro X Y p hp
  exact (DaggerSimplicialCat.Cofree.adjunction.hasLiftingProperty_iff i p).2
    (hi (DaggerSimplicialCat.Cofree.functor.map p)
      (cofree_preserves_ordinaryTrivialFibrations p hp))

/-- Every actual Gamma matching map, reversed to a dagger simplicial-category
arrow and then forgotten, lies in the original ordinary Bergner cofibration
class. The native matching object here is the opposite of the dagger latching
object; the explicit comparison with the ordinary latching object is separate. -/
theorem forgotten_Gamma_matching_cofibration (m : ReverseSimplex) (n : ℕ) :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations
      (DaggerSimplicialCat.forget.map
        (((matchingComparison n).app (GammaOuter.obj m).op).unop)) := by
  have h : fibrations Coefficientᵒᵖ
      ((matchingComparison n).app (GammaOuter.obj m).op) :=
    (reedyFibrant_iff_matchingComparison ((GammaOuter.obj m).op)).1
      (GammaOuter_op_isFibrant m) n
  rw [fibrations_op] at h
  exact forget_preserves_cofibrations _ h

/-- The matching comparisons of the forgotten actual Gamma, when reversed to
ordinary simplicial-category arrows, lie in the original ordinary Bergner
cofibration class. They are the cosimplicial latching maps through opposites. -/
theorem forgotten_Gamma_ordinary_matching_cofibration (m : ReverseSimplex) (n : ℕ) :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations
      (((matchingComparison n).app
        ((GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).op)).unop) := by
  let P : MorphismProperty SimplicialCat.{0, 0}ᵒᵖ :=
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations.op
  have : P.RespectsIso := by
    dsimp [P, DaggerOrdinaryRigidificationCof.ordinaryCofibrations]
    infer_instance
  let G := DaggerSimplicialCat.forget.{0, 0}.op
  let W := (GammaOuter.obj m).op
  let e := ReedyCoefficientChange.matchingObjectIso G n W
  have h : P (G.map ((matchingComparison n).app W)) :=
    forgotten_Gamma_matching_cofibration m n
  have hc : P (G.map ((matchingComparison n).app W) ≫ e.hom) := by
    letI : IsIso e.hom := inferInstance
    exact RespectsIso.postcomp P e.hom _ h
  rw [ReedyCoefficientChange.matchingComparison_map] at hc
  change P ((matchingComparison n).app
    ((GammaOuter.obj m ⋙ DaggerSimplicialCat.forget).op)) at hc
  exact hc

end

end DaggerModels.PartII.JTForgottenFrameCofibrancy
