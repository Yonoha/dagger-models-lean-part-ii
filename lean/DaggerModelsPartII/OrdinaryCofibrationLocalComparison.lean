import DaggerModelsPartII.OrdinaryTransfiniteLocalCobase
import DaggerModelsPartII.OrdinaryLocalCobaseRetract
import CoproductCellSerialization

/-!
# Local comparison along the original ordinary cofibrations

The universal ordinary local class contains the literal boundary and object
generators. Generic coproduct serialization and the proved transfinite
stability put their actual relative cell complexes in that class. The native
SOA/common-source retract argument then removes the relative-cell premise.
All supplied pushout maps and the original ordinary LLP class are retained.
No full ordinary model-category structure is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty DaggerModels

universe u

namespace DaggerModels.OrdinaryCofibrationLocalComparison

noncomputable section

open OrdinaryUniversalLocalCobase

/-- Pushouts of arbitrary coproducts of the original generating maps belong
to the same universal ordinary local class. -/
theorem batches_le_U :
    (MorphismProperty.coproducts.{u} OrdinaryBergnerGenerators.generators.{u}).pushouts ≤
      U := by
  letI : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  have hsingle : OrdinaryBergnerGenerators.generators.{u}.pushouts ≤ U :=
    (MorphismProperty.pushouts_le_iff).mpr generators_le_U
  exact (DaggerCoproductCellSerialization.coproduct_pushouts_le
    OrdinaryBergnerGenerators.generators).trans
      ((MorphismProperty.transfiniteCompositions_monotone hsingle).trans
        U.transfiniteCompositions_le)

/-- The literal relative cell class used by the original ordinary small
object argument lies in the universal local comparison class. -/
theorem relativeCells_le_U : OrdinaryLocalCobaseRetract.relativeCells.{u} ≤ U :=
  (MorphismProperty.transfiniteCompositions_monotone batches_le_U).trans
    U.transfiniteCompositions_le

/-- Every original ordinary LLP cofibration is monic on each actual source
Hom simplicial set, using its retained retract-cell description. -/
theorem ordinaryCofibrations_le_localHomMono :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations.{u} ≤ localHomMono := by
  have hcell : OrdinaryLocalCobaseRetract.relativeCells.{u} ≤ localHomMono :=
    relativeCells_le_U.trans U_le_localHomMono
  have hret : OrdinaryLocalCobaseRetract.relativeCells.{u}.retracts ≤ localHomMono :=
    MorphismProperty.retracts_le_iff.mpr hcell
  intro C B i hi
  apply hret i
  simpa only [OrdinaryLocalCobaseRetract.relativeCells,
    OrdinaryBergnerGenerators.ordinaryCofibrations_eq_retract_cells] using hi

/-- Cobase of a local geometric weak equivalence along any original ordinary
LLP cofibration is locally geometric on every actual source Hom. The relative
cell comparison premise has been discharged. -/
theorem local_geometric_of_isPushout
    {C D B P : SimplicialCat.{u, u}}
    (F : C ⟶ D) (i : C ⟶ B)
    (hi : DaggerOrdinaryRigidificationCof.ordinaryCofibrations i)
    (hF : LocalGeometric F) (j : D ⟶ P) (Fplus : B ⟶ P)
    (sq : IsPushout F i j Fplus) : LocalGeometric Fplus := by
  refine OrdinaryLocalCobaseRetract.cofibration_cobase_local_of_cells
    ?_ F i hi hF j Fplus sq
  intro C0 D0 B0 P0 F0 l hl hF0 j0 G0 sq0
  exact U_le_BaseLocal l (relativeCells_le_U l hl) F0 j0 G0 sq0 hF0

/-- The original ordinary cofibration class preserves the local geometric
comparison under every supplied cobase square. -/
theorem ordinaryCofibrations_le_BaseLocal :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations.{u} ≤ BaseLocal := by
  intro C B i hi D P F j Fplus sq hF
  exact local_geometric_of_isPushout F i hi hF j Fplus sq

/-- Every original ordinary cofibration has the full universal Hom-monic
and local-comparison property, with no new model structure or extra premise. -/
theorem ordinaryCofibrations_le_U :
    DaggerOrdinaryRigidificationCof.ordinaryCofibrations.{u} ≤ U := by
  letI :
      (DaggerOrdinaryRigidificationCof.ordinaryCofibrations.{u}).IsStableUnderCobaseChange := by
    dsimp [DaggerOrdinaryRigidificationCof.ordinaryCofibrations]
    infer_instance
  intro C B i hi
  apply (DaggerICellLocalComparison.universalCobase_iff _ i).mpr
  intro D P F G j sq
  have hj : DaggerOrdinaryRigidificationCof.ordinaryCofibrations j :=
    MorphismProperty.IsStableUnderCobaseChange.of_isPushout sq hi
  exact ⟨ordinaryCofibrations_le_localHomMono j hj,
    ordinaryCofibrations_le_BaseLocal j hj⟩

end

end DaggerModels.OrdinaryCofibrationLocalComparison
