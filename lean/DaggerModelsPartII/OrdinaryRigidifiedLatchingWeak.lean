import OriginalLatchingFiniteUnionPushoutsReconciledRecovered
import OriginalLatchingGeometricReconciledRecovered
import LatchingIntersectionNaturality
import DaggerModelsPartII.OrdinaryDwyerKanPushoutComparison
import OrdinaryRigidificationCof

/-!
# Ordinary DK weakness of rigidified horizontal latching maps

The public target is the original latching map of an arbitrary simplicial
object of simplicial sets. The row hypothesis is applied at the exact lower
degree `n - I.card` through the retained intersection isomorphism. The
finite-union induction uses the recovered exact union pushouts and four
comparison equations. No additional union or latching weak-equivalence
hypothesis is part of the target statement.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty
open DaggerModels DaggerOrdinaryRigidificationCof
open DaggerModels.OrdinaryDwyerKanCore
open DaggerBisimplicialDiagonal

universe u

namespace DaggerModels.OrdinaryRigidifiedLatchingWeak

noncomputable section

private local instance : HasColimitsOfSize.{u, u} SimplicialCat.{u, u} :=
  SimplicialCat.SemanticColimit.simplicialCatHasColimits

private local instance : PreservesColimitsOfSize.{u, u} C.{u} :=
  OrdinaryRigidification.rigidificationCoherentNerveAdjunction.leftAdjoint_preservesColimits

/-- Every finite degeneracy intersection comparison is weak after the
literal original ordinary rigidification. -/
theorem intersection_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ m : ℕ, W (C.map (η.app (op ⦋m⦌))))
    (n : ℕ) (I : Finset (Fin n)) :
    W (C.map (intersectionMap η n I)) := by
  let e : Arrow.mk (C.map (η.app (op ⦋n - I.card⦌))) ≅
      Arrow.mk (C.map (intersectionMap η n I)) :=
    Arrow.isoMk (C.mapIso (intersectionIso B n I))
      (C.mapIso (intersectionIso B' n I)) (by
        change C.map (intersectionIso B n I).hom ≫
            C.map (intersectionMap η n I) =
          C.map (η.app (op ⦋n - I.card⦌)) ≫
            C.map (intersectionIso B' n I).hom
        rw [← C.map_comp, ← C.map_comp]
        exact congrArg C.map (intersectionIso_naturality η n I))
  exact (W.arrow_mk_iso_iff e).mp (hrow (n - I.card))

/-- Finite union comparison by the retained literal union-intersection
pushouts. The induction generalizes the fixed intersection index because
the upper-left corner uses `insert i J`. -/
private theorem finiteUnion_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ m : ℕ, W (C.map (η.app (op ⦋m⦌))))
    (n : ℕ) (J S : Finset (Fin n)) :
    W (C.map (unionInterMap η n J S)) := by
  induction S using Finset.induction_on generalizing J with
  | empty =>
      rw [← unionInterEmptyIso_hom η n J]
      exact W.of_isIso _
  | @insert i S hi ih =>
      have sq : IsPushout
          (C.map (unionInterTop B n J S i))
          (C.map (unionInterLeft B n J S i))
          (C.map (unionInterRight B n J S i))
          (C.map (unionInterBottom B n J S i)) :=
        (unionInter_isPushout B n J S i).map C
      have sq' : IsPushout
          (C.map (unionInterTop B' n J S i))
          (C.map (unionInterLeft B' n J S i))
          (C.map (unionInterRight B' n J S i))
          (C.map (unionInterBottom B' n J S i)) :=
        (unionInter_isPushout B' n J S i).map C
      have htopMono : Mono (unionInterTop B n J S i) := by
        dsimp [unionInterTop]
        infer_instance
      have htopMono' : Mono (unionInterTop B' n J S i) := by
        dsimp [unionInterTop]
        infer_instance
      letI : Mono (unionInterTop B n J S i) := htopMono
      letI : Mono (unionInterTop B' n J S i) := htopMono'
      have hcof : ordinaryCofibrations (C.map (unionInterTop B n J S i)) :=
        mono_rigidification_cofibration _
      have hcof' : ordinaryCofibrations (C.map (unionInterTop B' n J S i)) :=
        mono_rigidification_cofibration _
      have h₁ : C.map (unionInterTop B n J S i) ≫
          C.map (unionInterMap η n J S) =
          C.map (unionInterMap η n (insert i J) S) ≫
            C.map (unionInterTop B' n J S i) := by
        simpa only [← C.map_comp] using
          congrArg C.map (unionInterCube_top η n J S i)
      have h₂ : C.map (unionInterLeft B n J S i) ≫
          C.map (intersectionMap η n (insert i J)) =
          C.map (unionInterMap η n (insert i J) S) ≫
            C.map (unionInterLeft B' n J S i) := by
        simpa only [← C.map_comp] using
          congrArg C.map (unionInterCube_left η n J S i)
      have h₃ : C.map (unionInterRight B n J S i) ≫
          C.map (unionInterMap η n J (insert i S)) =
          C.map (unionInterMap η n J S) ≫
            C.map (unionInterRight B' n J S i) := by
        simpa only [← C.map_comp] using
          congrArg C.map (unionInterCube_right η n J S i)
      have h₄ : C.map (unionInterBottom B n J S i) ≫
          C.map (unionInterMap η n J (insert i S)) =
          C.map (intersectionMap η n (insert i J)) ≫
            C.map (unionInterBottom B' n J S i) := by
        simpa only [← C.map_comp] using
          congrArg C.map (unionInterCube_bottom η n J S i)
      exact OrdinaryDwyerKanPushoutComparison.weak_of_pushoutComparison
        sq sq' hcof hcof'
        (C.map (unionInterMap η n (insert i J) S))
        (C.map (unionInterMap η n J S))
        (C.map (intersectionMap η n (insert i J)))
        (C.map (unionInterMap η n J (insert i S)))
        h₁ h₂ h₃ h₄
        (ih (insert i J)) (ih J) (intersection_W η hrow n (insert i J))

/-- Original latching map, with no extra union-weakness premise. -/
theorem latching_W {B B' : SimplicialObject SSet.{u}}
    (η : B ⟶ B')
    (hrow : ∀ m : ℕ, W (C.map (η.app (op ⦋m⦌))))
    (n : ℕ) : W (C.map (latchingMap η n)) := by
  let e : Arrow.mk (C.map (unionInterMap η n ∅ Finset.univ)) ≅
      Arrow.mk (C.map (latchingMap η n)) :=
    Arrow.isoMk (C.mapIso (finiteUnionLatchingIso B n))
      (C.mapIso (finiteUnionLatchingIso B' n)) (by
        change C.map (finiteUnionLatchingIso B n).hom ≫
            C.map (latchingMap η n) =
          C.map (unionInterMap η n ∅ Finset.univ) ≫
            C.map (finiteUnionLatchingIso B' n).hom
        rw [← C.map_comp, ← C.map_comp]
        exact congrArg C.map (finiteUnionLatchingIso_naturality η n))
  exact (W.arrow_mk_iso_iff e).mp (finiteUnion_W η hrow n ∅ Finset.univ)

end

end DaggerModels.OrdinaryRigidifiedLatchingWeak
