import DaggerModelsPartII.JTStrictificationMaps
import DaggerModelsPartII.JTObjectPreservingReplacement
import DaggerModelsPartII.JTProjectiveComparisonWeak
import DaggerModelsPartII.JTFreeInnerFactorization

/-!
# Actual coefficient replacements in the strictification construction

The projective source replacement, the free-inner replacement, and the
fixed-object Bergner replacement are the specified constructions. The
free-inner unit is an original trivial cofibration, so the literal rigidified
comparison into the chosen target is weak. Vertex preservation of that unit
and weakness of the resulting frame map are separate questions.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty DaggerModels
open OrdinaryRigidification.DaggerRigidification

namespace DaggerModels.PartII.JTStrictificationCoefficients

open SegalLocalizers JTStrictificationMaps JTObjectPreservingReplacement
open JTFrameAdjunction

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}

private local instance : ModelCategory DaggerSSet.{0} :=
  DaggerActualRigidificationQuillen.modelD.{0}
private local instance : ModelCategory DaggerSimplicialCat.{0, 0} :=
  DaggerActualRigidificationQuillen.modelG.{0}

/-- The actual object-preserving Bergner replacement of the frame realization
of the chosen projectively cofibrant source. -/
def frameCoefficient (W : Source) : DaggerSimplicialCat.{0, 0} :=
  Robj (frameRealization.obj (Qproj.obj W))

/-- The original frame unit associated to the literal fixed-object
replacement map. -/
def frameUnit (W : Source) :
    Qproj.obj W ⟶ frameNerve.obj (frameCoefficient W) :=
  adjunction.homEquiv (Qproj.obj W) (frameCoefficient W)
    (r (frameRealization.obj (Qproj.obj W)))

/-- The frame coefficient is fibrant in the original dagger Bergner model. -/
theorem frameCoefficient_fibrant (W : Source) :
    IsFibrant (frameCoefficient W) :=
  Robj_fibrant (frameRealization.obj (Qproj.obj W))

/-- The literal fixed-object Bergner target for a dagger simplicial set. -/
def rigidCoefficient (T : DaggerSSet.{0}) : DaggerSimplicialCat.{0, 0} :=
  Robj (daggerRigidification.obj T)

/-- The rigid coefficient is fibrant in the original dagger Bergner model. -/
theorem rigidCoefficient_fibrant (T : DaggerSSet.{0}) :
    IsFibrant (rigidCoefficient T) :=
  Robj_fibrant (daggerRigidification.obj T)

/-- The literal rigidified comparison into the chosen fixed-object target. -/
def strictA (W : Source) {T : DaggerSSet.{0}}
    (g : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ T) :
    daggerRigidification.obj
        (DaggerJTRealization.daggerRealization.obj (Qproj.obj W)) ⟶
      rigidCoefficient T :=
  JTStrictificationMaps.a W g (r (daggerRigidification.obj T))

/-- The transpose of the actual rigidified comparison. -/
def strictAFlat (W : Source) {T : DaggerSSet.{0}}
    (g : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ T) :
    Qproj.obj W ⟶ JTCoendMate.compositeNerve.obj (rigidCoefficient T) :=
  JTStrictificationMaps.aFlat W g (r (daggerRigidification.obj T))

/-- The literal frame unit–comparison map into the chosen rigid coefficient. -/
def strictPsi (W : Source) {T : DaggerSSet.{0}}
    (g : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ T) :
    Qproj.obj W ⟶ frameNerve.obj (rigidCoefficient T) :=
  JTStrictificationMaps.psi W g (r (daggerRigidification.obj T))

/-- The literal specialized mate equation. -/
theorem strictPsi_eq_strictAFlat_rightMate (W : Source)
    {T : DaggerSSet.{0}}
    (g : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ T) :
    strictPsi W g =
      strictAFlat W g ≫ JTCoendMate.rightMate.app (rigidCoefficient T) :=
  JTStrictificationMaps.psi_eq_aFlat_rightMate W g
    (r (daggerRigidification.obj T))

/-- If the supplied free-inner map is an original dagger Joyal trivial
cofibration, the actual capital comparison followed by its rigidification and
the fixed-object replacement is weak in the original dagger Bergner model. -/
theorem comparison_strictA_weak (W : Source) {T : DaggerSSet.{0}}
    (g : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ T)
    (hg : trivialCofibrations DaggerSSet.{0} g) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTCoendComparison.comparison.app (Qproj.obj W) ≫ strictA W g) := by
  let P := weakEquivalences DaggerSimplicialCat.{0, 0}
  have hLambda : P (JTCoendComparison.comparison.app (Qproj.obj W)) := by
    dsimp only [P]
    rw [DaggerActualRigidificationQuillen.target_weak]
    exact JTProjectiveComparisonWeak.comparison_daggerDK_of_isCofibrant
      (Qproj.obj W) (Qproj_cofibrant W)
  have hMapG : P (daggerRigidification.map g) := by
    have hPreserve : daggerRigidification.PreservesTrivialCofibrations :=
      DaggerActualRigidificationQuillen.preservesTrivialCofibrations
    exact (hPreserve.trivialCofibrations_le g hg).2
  have hR : P (r (daggerRigidification.obj T)) := by
    exact (weakEquivalence_iff _).mp
      (r_weak (daggerRigidification.obj T))
  change P (JTCoendComparison.comparison.app (Qproj.obj W) ≫
    (daggerRigidification.map g ≫ r (daggerRigidification.obj T)))
  exact P.comp_mem _ _ hLambda (P.comp_mem _ _ hMapG hR)

/-- The actual free-inner replacement target of the chosen projective input. -/
def chosenT (W : Source) : DaggerSSet.{0} :=
  JTFreeInnerFactorization.replacement.obj
    (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))

/-- The actual free-inner unit at the realized projective input. -/
def chosenG (W : Source) :
    DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶ chosenT W :=
  JTFreeInnerFactorization.unit.app
    (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))

/-- The chosen free-inner target has an underlying quasi-category. -/
theorem chosenT_quasicategory (W : Source) :
    (chosenT W).toSSet.Quasicategory :=
  JTFreeInnerFactorization.replacement_underlying_quasicategory
    (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))

/-- The chosen free-inner map is an original dagger Joyal trivial
cofibration. -/
theorem chosenG_trivialCofibration (W : Source) :
    trivialCofibrations DaggerSSet.{0} (chosenG W) :=
  JTFreeInnerFactorization.unit_trivialCofibration
    (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))

/-- The actual original rigidified map into the chosen Bergner-fibrant
fixed-object replacement. -/
def chosenA (W : Source) :
    daggerRigidification.obj
        (DaggerJTRealization.daggerRealization.obj (Qproj.obj W)) ⟶
      rigidCoefficient (chosenT W) :=
  strictA W (chosenG W)

/-- Its original composite-adjunction transpose. -/
def chosenAFlat (W : Source) :
    Qproj.obj W ⟶ JTCoendMate.compositeNerve.obj
      (rigidCoefficient (chosenT W)) :=
  strictAFlat W (chosenG W)

/-- Its literal frame-unit and capital-comparison composite. -/
def chosenPsi (W : Source) :
    Qproj.obj W ⟶ frameNerve.obj (rigidCoefficient (chosenT W)) :=
  strictPsi W (chosenG W)

/-- The chosen frame map has the exact original right-mate description. -/
theorem chosenPsi_eq_chosenAFlat_rightMate (W : Source) :
    chosenPsi W = chosenAFlat W ≫
      JTCoendMate.rightMate.app (rigidCoefficient (chosenT W)) :=
  strictPsi_eq_strictAFlat_rightMate W (chosenG W)

/-- The capital comparison followed by the actual chosen free-inner and
fixed-object replacements is weak in the original dagger Bergner model. -/
theorem comparison_chosenA_weak (W : Source) :
    weakEquivalences DaggerSimplicialCat.{0, 0}
      (JTCoendComparison.comparison.app (Qproj.obj W) ≫ chosenA W) :=
  comparison_strictA_weak W (chosenG W) (chosenG_trivialCofibration W)

end

end DaggerModels.PartII.JTStrictificationCoefficients
