import DaggerModelsPartII.DerivedUnitQuillenCriterion
import DaggerModelsPartII.CosimplicialMappingInvariance
import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.OfFunctorialResolutions

/-! The chosen derived unit is inverted when the weak-preserving left
Quillen functor is fully faithful after localization. -/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace DaggerModels.PartII.QuillenDerivedUnitOfLocalizedFull

noncomputable section

variable {C D : Type*} [Category* C] [Category* D] [ModelCategory C] [ModelCategory D]
variable {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)

private theorem left_inverts
    (hL : ∀ {A B : C} (f : A ⟶ B), weakEquivalences C f →
      weakEquivalences D (L.map f)) :
    (weakEquivalences C).IsInvertedBy (L ⋙ (weakEquivalences D).Q) := by
  intro A B f hf
  exact Localization.inverts (weakEquivalences D).Q (weakEquivalences D) (L.map f) (hL f hf)

/-- The localization of the original weak-preserving left adjoint. -/
def localizedLeft
    (hL : ∀ {A B : C} (f : A ⟶ B), weakEquivalences C f →
      weakEquivalences D (L.map f)) :
    (weakEquivalences C).Localization ⥤ (weakEquivalences D).Localization :=
  Localization.lift _ (left_inverts hL) (weakEquivalences C).Q

private def fibrantIncl (D : Type*) [Category* D] [ModelCategory D] :
    LocalizerMorphism
      ((weakEquivalences D).inverseImage (FibrantObject.ι : FibrantObject D ⥤ D))
      (weakEquivalences D) where
  functor := FibrantObject.ι
  map := le_rfl

private theorem right_derives [adj.IsQuillenAdjunction] :
    (fibrantIncl D).Derives (G ⋙ (weakEquivalences C).Q) := by
  intro A B f hf
  letI := Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adj
  change IsIso ((weakEquivalences C).Q.map (G.map ((fibrantIncl D).functor.map f)))
  apply Localization.inverts (weakEquivalences C).Q (weakEquivalences C)
  apply map_weak_of_trivialFibration G _ _ hf
  intro X Y p hp
  exact (Functor.PreservesTrivialFibrations.trivialFibrations_le G p hp).2

/-- Full faithfulness after localization inverts the literal chosen derived unit.
The given functorial fibrant replacement supplies the right derivability structure. -/
theorem localization_inverts_chosenDerivedUnit [adj.IsQuillenAdjunction]
    (hL : ∀ {A B : C} (f : A ⟶ B), weakEquivalences C f →
      weakEquivalences D (L.map f))
    [hfull : (localizedLeft hL).Full] [hfaith : (localizedLeft hL).Faithful]
    (R : D ⥤ FibrantObject D) (r : 𝟭 D ⟶ R ⋙ FibrantObject.ι)
    (hr : ∀ Z, weakEquivalences D (r.app Z)) (A : C) :
    IsIso ((weakEquivalences C).Q.map (DerivedUnitQuillenCriterion.derivedUnit L G adj A)) := by
  let P := weakEquivalences C
  let W := weakEquivalences D
  letI : (fibrantIncl D).functor.Full := inferInstanceAs (FibrantObject.ι : FibrantObject D ⥤ D).Full
  letI : (fibrantIncl D).functor.Faithful :=
    inferInstanceAs (FibrantObject.ι : FibrantObject D ⥤ D).Faithful
  letI : (fibrantIncl D).IsRightDerivabilityStructure :=
    (fibrantIncl D).isRightDerivabilityStructure_of_functorial_resolutions (ρ := R) r hr rfl
  let left := localizedLeft hL
  let e : P.Q ⋙ left ≅ L ⋙ W.Q := Localization.fac _ (left_inverts hL) P.Q
  let T := G ⋙ P.Q
  have hT := right_derives adj
  letI := hT.hasPointwiseRightDerivedFunctor
  letI := T.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
  let right := T.totalRightDerived W.Q W
  let β := T.totalRightDerivedUnit W.Q W
  letI : right.IsRightDerivedFunctor β W := inferInstance
  letI : left.IsLeftDerivedFunctor e.hom P :=
    Functor.isLeftDerivedFunctor_of_inverts P _ e
  letI : (left ⋙ right).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight e.hom right) P :=
    Functor.isLeftDerivedFunctor_of_inverts P _
      ((Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e right)
  have hTr : (fibrantIncl D).Derives (T ⋙ left) := by
    intro X Y f hf
    have : IsIso (T.map ((fibrantIncl D).functor.map f)) := hT _ hf
    exact left.map_isIso _
  letI : (right ⋙ left).IsRightDerivedFunctor
      (Functor.whiskerRight β left ≫ (Functor.associator _ _ _).hom) W := by
    apply hTr.isRightDerivedFunctor_of_isIso
    intro Z
    have := hT.isIso β Z
    change IsIso (left.map (β.app _) ≫ 𝟙 _)
    infer_instance
  let dAdj := adj.derived P W e.hom β
  let d := DerivedUnitQuillenCriterion.replacementData L A
  have hZ : IsFibrant d.Z := (isFibrant_iff_of_isTerminal d.p terminalIsTerminal).mpr
    ((fibration_iff _).mpr d.hp)
  haveI : IsIso (β.app d.Z) := hT.isIso β (FibrantObject.mk d.Z)
  haveI : IsIso (W.Q.map d.i) := Localization.inverts _ _ _ d.hi.2
  haveI : left.Full := hfull
  haveI : left.Faithful := hfaith
  have hη : dAdj.unit.app (P.Q.obj A) ≫ right.map (e.hom.app A) =
      P.Q.map (adj.unit.app A) ≫ β.app (L.obj A) :=
    adj.derivedη_fac_app P e.hom β A
  have hnat := β.naturality d.i
  have ht : P.Q.map (DerivedUnitQuillenCriterion.derivedUnit L G adj A) ≫ β.app d.Z =
      (dAdj.unit.app (P.Q.obj A) ≫ right.map (e.hom.app A)) ≫ right.map (W.Q.map d.i) := by
    rw [hη, Category.assoc]
    change P.Q.map (adj.unit.app A ≫ G.map d.i) ≫ β.app d.Z =
      P.Q.map (adj.unit.app A) ≫ β.app (L.obj A) ≫ right.map (W.Q.map d.i)
    rw [P.Q.map_comp, Category.assoc]
    exact congrArg (fun k ↦ P.Q.map (adj.unit.app A) ≫ k) hnat
  have : IsIso (P.Q.map (DerivedUnitQuillenCriterion.derivedUnit L G adj A) ≫ β.app d.Z) := by
    rw [ht]
    infer_instance
  exact (isIso_comp_right_iff _ (β.app d.Z)).mp this

end

end DaggerModels.PartII.QuillenDerivedUnitOfLocalizedFull
