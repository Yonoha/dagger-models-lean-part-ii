import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Equalizers

/-!
# Relative corners of an adjunction unit

For adjunctions `L ⊣ R ⊣ S`, the unit of `L ⋙ R ⊣ S ⋙ R`
has a right mate. The pushout corner of the unit and the pullback corner
of the mate satisfy the usual lifting equivalence.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace DaggerModels.PartII.AdjunctionUnitCorners

variable {C : Type u} {D : Type v} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} {S : C ⥤ D}
  (adjLR : L ⊣ R) (adjRS : R ⊣ S)

noncomputable section

private def compositeAdjunction : L ⋙ R ⊣ S ⋙ R := adjLR.comp adjRS

/-- The right mate of the unit of `L ⊣ R`, viewed as a transformation
from the right adjoint of `L ⋙ R` to the identity. -/
def unitRightMate : S ⋙ R ⟶ 𝟭 C :=
  conjugateEquiv (compositeAdjunction adjLR adjRS) Adjunction.id adjLR.unit

private def parameterLeft : WalkingParallelPair ⥤ C ⥤ C :=
  parallelPair adjLR.unit adjLR.unit

private def parameterRight : WalkingParallelPairᵒᵖ ⥤ C ⥤ C :=
  walkingParallelPairOpEquiv.inverse ⋙
    parallelPair (unitRightMate adjLR adjRS) (unitRightMate adjLR adjRS)

private def parameterAdjunctionAt (s : WalkingParallelPair) :
    (parameterLeft adjLR).obj s ⊣
      (parameterRight adjLR adjRS).obj (op s) :=
  match s with
  | .zero => Adjunction.id
  | .one => compositeAdjunction adjLR adjRS

private theorem mate_homEquiv_naturality (X Y : C) (q : (L ⋙ R).obj X ⟶ Y) :
    adjLR.unit.app X ≫ q =
      (compositeAdjunction adjLR adjRS).homEquiv X Y q ≫
        (unitRightMate adjLR adjRS).app Y := by
  rw [Adjunction.homEquiv_unit, Category.assoc]
  rw [(unitRightMate adjLR adjRS).naturality q]
  rw [← Category.assoc]
  have h := unit_conjugateEquiv
    (compositeAdjunction adjLR adjRS) Adjunction.id adjLR.unit X
  simpa [unitRightMate] using (congrArg (fun h => h ≫ q) h).symm

private def parameterAdjunction :
    parameterLeft adjLR ⊣₂ parameterRight adjLR adjRS :=
  ParametrizedAdjunction.mk' (parameterAdjunctionAt adjLR adjRS) (by
    intro s t g X Y q
    change WalkingParallelPairHom s t at g
    cases g with
    | left =>
      simp only [parameterAdjunctionAt, parameterLeft, parameterRight]
      change (Adjunction.id.homEquiv X Y) (adjLR.unit.app X ≫ q) = _
      rw [show (Adjunction.id.homEquiv X Y) (adjLR.unit.app X ≫ q) =
        adjLR.unit.app X ≫ q from by simp [Adjunction.homEquiv, Adjunction.id]]
      exact mate_homEquiv_naturality adjLR adjRS X Y q
    | right =>
      simp only [parameterAdjunctionAt, parameterLeft, parameterRight]
      change (Adjunction.id.homEquiv X Y) (adjLR.unit.app X ≫ q) = _
      rw [show (Adjunction.id.homEquiv X Y) (adjLR.unit.app X ≫ q) =
        adjLR.unit.app X ≫ q from by simp [Adjunction.homEquiv, Adjunction.id]]
      exact mate_homEquiv_naturality adjLR adjRS X Y q
    | id s =>
      cases s <;>
        change _ = _ ≫ 𝟙 _ <;>
        simp [parameterLeft, parameterRight, Category.comp_id])

variable {X Y A B : C} (f : X ⟶ Y) (p : A ⟶ B)

/-- The pushout corner of the unit along a map of the source category. -/
def unitPushoutCorner [HasPushouts C] :
    (parameterLeft adjLR).PushoutObjObj WalkingParallelPairHom.left f :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

/-- The pullback corner of the right mate along a map of the source category. -/
def matePullbackCorner [HasPullbacks C] :
    (parameterRight adjLR adjRS).PullbackObjObj WalkingParallelPairHom.left p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-- The chosen left corner is the pushout of the literal unit component
`X ⟶ R(L X)` along `f`. -/
theorem unitPushoutCorner_isPushout [HasPushouts C] :
    IsPushout (adjLR.unit.app X) f
      (unitPushoutCorner adjLR f).inl
      (unitPushoutCorner adjLR f).inr := by
  exact (unitPushoutCorner adjLR f).isPushout

/-- The chosen right corner is the pullback of `p` and the right mate
at `B`. -/
theorem matePullbackCorner_isPullback [HasPullbacks C] :
    IsPullback (matePullbackCorner adjLR adjRS p).fst
      (matePullbackCorner adjLR adjRS p).snd p
      ((unitRightMate adjLR adjRS).app B) := by
  exact (matePullbackCorner adjLR adjRS p).isPullback

/-- The left pushout corner restricts to `T.map f` on the `T X` face. -/
theorem unitPushoutCorner_inl_ι [HasPushouts C] :
    (unitPushoutCorner adjLR f).inl ≫ (unitPushoutCorner adjLR f).ι =
      (L ⋙ R).map f := by
  exact (unitPushoutCorner adjLR f).inl_ι

/-- The left pushout corner restricts to the unit at `Y` on the other face. -/
theorem unitPushoutCorner_inr_ι [HasPushouts C] :
    (unitPushoutCorner adjLR f).inr ≫ (unitPushoutCorner adjLR f).ι =
      adjLR.unit.app Y := by
  exact (unitPushoutCorner adjLR f).inr_ι

/-- The right pullback corner restricts to the mate at `A`. -/
theorem matePullbackCorner_π_fst [HasPullbacks C] :
    (matePullbackCorner adjLR adjRS p).π ≫
      (matePullbackCorner adjLR adjRS p).fst =
      (unitRightMate adjLR adjRS).app A := by
  exact (matePullbackCorner adjLR adjRS p).π_fst

/-- The right pullback corner restricts to `Q.map p` on the other face. -/
theorem matePullbackCorner_π_snd [HasPullbacks C] :
    (matePullbackCorner adjLR adjRS p).π ≫
      (matePullbackCorner adjLR adjRS p).snd =
      (S ⋙ R).map p := by
  exact (matePullbackCorner adjLR adjRS p).π_snd

/-- Relative-corner lifting for the unit and its right mate. -/
theorem unitPushoutCorner_hasLiftingProperty_iff
    [HasPushouts C] [HasPullbacks C] :
    HasLiftingProperty (unitPushoutCorner adjLR f).ι p ↔
      HasLiftingProperty f (matePullbackCorner adjLR adjRS p).π :=
  (parameterAdjunction adjLR adjRS).hasLiftingProperty_iff
    (unitPushoutCorner adjLR f) (matePullbackCorner adjLR adjRS p)

end

end DaggerModels.PartII.AdjunctionUnitCorners
