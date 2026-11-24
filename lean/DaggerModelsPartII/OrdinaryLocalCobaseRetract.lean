import DaggerModelsPartII.OrdinaryBergnerGenerators
import OriginalOrdinaryHomRetractsReconciled
import PushoutRetract
import SSetGluingPushouts

/-!
# Ordinary local comparisons and the small-object retract step

The retained endpoint-aware Hom retract theorem transfers local geometric
weak equivalence to actual ordinary arrow retracts. A supplied cobase square
then inherits the local comparison from a common-source cell retraction.
The final theorem reduces ordinary LLP cofibrations to their actual relative
cell complexes, retaining the latter's local cobase comparison as an explicit
hypothesis. No full ordinary model structure is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryLocalCobaseRetract

noncomputable section

/-- The original geometric weak condition on every ordered source Hom. -/
abbrev LocalGeometric {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : Prop :=
  ∀ a b : C.Obj, DaggerSSetGluing.GW (F.map a b)

/-- Actual ordinary arrow retracts preserve the original local condition,
using the retained endpoint transports on each Hom arrow. -/
theorem local_of_retract {C D C' D' : SimplicialCat.{u, u}}
    {F : C ⟶ D} {G : C' ⟶ D'} (h : RetractArrow F G)
    (hG : LocalGeometric G) : LocalGeometric F := by
  intro a b
  have hg : weakEquivalences SSet.{u}
      (G.map (h.i.left.obj a) (h.i.left.obj b)) :=
    (weakEquivalence_iff _).mp
      ((DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (hG _ _))
  have hf := (weakEquivalences SSet.{u}).of_retract
    (OriginalOrdinaryHomRetracts.homRetract h a b) hg
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
    ((weakEquivalence_iff _).mpr hf)

/-- A common-source retract of attaching maps induces an actual arrow
retract of the two supplied cobase comparisons. -/
theorem local_of_cobase_retract
    {C D B P Z Q : SimplicialCat.{u, u}}
    {F : C ⟶ D} {i : C ⟶ B} {j : D ⟶ P} {Fplus : B ⟶ P}
    {l : C ⟶ Z} {jZ : D ⟶ Q} {G : Z ⟶ Q}
    (sq : IsPushout F i j Fplus) (sqL : IsPushout F l jZ G)
    (r : B ⟶ Z) (p : Z ⟶ B)
    (hir : i ≫ r = l) (hlp : l ≫ p = i) (hrp : r ≫ p = 𝟙 B)
    (hG : LocalGeometric G) : LocalGeometric Fplus :=
  local_of_retract
    (DaggerCofibrationPushoutRetract.cobaseRetract sq sqL r p hir hlp hrp) hG

/-- The literal relative cell class of the installed ordinary generators. -/
abbrev relativeCells : MorphismProperty SimplicialCat.{u, u} :=
  MorphismProperty.transfiniteCompositions.{u}
    (MorphismProperty.coproducts.{u} OrdinaryBergnerGenerators.generators.{u}).pushouts

/-- If actual relative ordinary cell complexes preserve the local comparison
under cobase, then the same holds for every original ordinary LLP cofibration.
The cell-comparison premise is not discharged by this theorem. -/
theorem cofibration_cobase_local_of_cells
    (hcell : ∀ {C D B P : SimplicialCat.{u, u}}
      (F : C ⟶ D) (l : C ⟶ B), relativeCells l → LocalGeometric F →
      ∀ (j : D ⟶ P) (G : B ⟶ P), IsPushout F l j G → LocalGeometric G)
    {C D B P : SimplicialCat.{u, u}}
    (F : C ⟶ D) (i : C ⟶ B)
    (hi : DaggerOrdinaryRigidificationCof.ordinaryCofibrations i)
    (hF : LocalGeometric F) (j : D ⟶ P) (Fplus : B ⟶ P)
    (sq : IsPushout F i j Fplus) : LocalGeometric Fplus := by
  let I := OrdinaryBergnerGenerators.generators.{u}
  letI : MorphismProperty.HasSmallObjectArgument.{u} I :=
    OrdinaryBergnerGenerators.generators_hasSmallObjectArgument
  obtain ⟨κ, hreg, hbot, hsoa⟩ :=
    MorphismProperty.HasSmallObjectArgument.exists_cardinal (I := I)
  letI := hreg
  letI := hbot
  letI := hsoa
  let l := SmallObject.ιObj I κ i
  let p := SmallObject.πObj I κ i
  have hlp : l ≫ p = i := SmallObject.ιObj_πObj I κ i
  have hl : relativeCells l :=
    (MorphismProperty.transfiniteCompositionsOfShape_le_transfiniteCompositions
      ((MorphismProperty.coproducts.{u} I).pushouts) κ.ord.ToType) l
        (SmallObject.transfiniteCompositionsOfShape_ιObj I κ i)
  have hp : I.rlp p := SmallObject.rlp_πObj I κ i
  have hi' : I.rlp.llp i := by
    change OrdinaryBergnerGenerators.generators.rlp.llp i
    rw [OrdinaryBergnerGenerators.generators_rlp_eq_ordinaryTrivialFibrations]
    exact hi
  letI : HasLiftingProperty i p := hi' p hp
  let liftSquare : CommSq l i p (𝟙 B) := CommSq.mk (by simpa using hlp)
  let r : B ⟶ SmallObject.obj I κ i := liftSquare.lift
  have hir : i ≫ r = l := liftSquare.fac_left
  have hrp : r ≫ p = 𝟙 B := liftSquare.fac_right
  letI : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
    SimplicialCat.SemanticColimit.simplicialCatHasColimits
  have sqL := IsPushout.of_hasPushout F l
  have hG : LocalGeometric (pushout.inr F l) :=
    hcell F l hl hF (pushout.inl F l) (pushout.inr F l) sqL
  exact local_of_cobase_retract sq sqL r p hir hlp hrp hG

end

end DaggerModels.OrdinaryLocalCobaseRetract
