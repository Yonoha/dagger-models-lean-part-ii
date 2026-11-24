import Mathlib.AlgebraicTopology.ModelCategory.Basic
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import DaggerModelsPartII.RelativeArrows

/-!
# The projective cofibration and trivial-fibration factorization on arrows

The projective cofibration of a square requires a cofibration on its left
component and on its actual pushout corner. Its right class consists of
trivial fibrations on both components. The factorization first factors the
left component, forms the induced pushout, and factors the corner map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MorphismProperty

universe v u

namespace DaggerModels.PartII.ProjectiveArrowFactorization

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasColimits C]

/-- The actual pushout corner of a commutative square of arrows. -/
def corner {A B : Arrow C} (f : A ⟶ B) :
    pushout A.hom f.left ⟶ B.right :=
  pushout.desc f.right B.hom (Arrow.w f).symm

omit [HasColimits C] in
/-- The retained relative-latching-arrow functor gives exactly this corner
for the walking-arrow structure transformation. -/
theorem corner_eq_relativeLatching {A B : Arrow C} (f : A ⟶ B) :
    corner f =
      (relativeLatchingArrow
        (Arrow.leftToRight : Arrow.leftFunc (C := C) ⟶ Arrow.rightFunc)
        (Arrow.mk f)).hom := rfl

/-- Projective cofibrations of arrows, with the corner condition retained. -/
def projectiveArrowCofibrations : MorphismProperty (Arrow C) :=
  fun _ _ f ↦ cofibrations C f.left ∧ cofibrations C (corner f)

/-- The pointwise trivial fibrations of arrows. -/
def pointwiseArrowTrivialFibrations : MorphismProperty (Arrow C) :=
  fun _ _ f ↦ trivialFibrations C f.left ∧ trivialFibrations C f.right

/-- The actual two-stage factorization data. -/
def factorization {A B : Arrow C} (f : A ⟶ B) :
    MapFactorizationData projectiveArrowCofibrations
      pointwiseArrowTrivialFibrations f := by
  let ds := factorizationData (cofibrations C) (trivialFibrations C) f.left
  let cornerToTarget : pushout A.hom ds.i ⟶ B.right :=
    pushout.desc f.right (ds.p ≫ B.hom) (by
      calc
        A.hom ≫ f.right = f.left ≫ B.hom := (Arrow.w f).symm
        _ = (ds.i ≫ ds.p) ≫ B.hom := by rw [ds.fac]
        _ = ds.i ≫ (ds.p ≫ B.hom) := Category.assoc _ _ _)
  let dt := factorizationData (cofibrations C) (trivialFibrations C) cornerToTarget
  let Z : Arrow C := Arrow.mk (pushout.inr A.hom ds.i ≫ dt.i)
  let i : A ⟶ Z := Arrow.homMk ds.i (pushout.inl A.hom ds.i ≫ dt.i) (by
    change ds.i ≫ (pushout.inr A.hom ds.i ≫ dt.i) =
      A.hom ≫ (pushout.inl A.hom ds.i ≫ dt.i)
    rw [← Category.assoc, ← Category.assoc, ← pushout.condition])
  let p : Z ⟶ B := Arrow.homMk ds.p dt.p (by
    calc
      ds.p ≫ B.hom = pushout.inr A.hom ds.i ≫ cornerToTarget := by
        simp only [cornerToTarget, pushout.inr_desc]
      _ = (pushout.inr A.hom ds.i ≫ dt.i) ≫ dt.p := by
        rw [Category.assoc, dt.fac])
  refine
    { Z := Z
      i := i
      p := p
      fac := ?_
      hi := ?_
      hp := ?_ }
  · apply Arrow.hom_ext
    · change ds.i ≫ ds.p = f.left
      exact ds.fac
    · change (pushout.inl A.hom ds.i ≫ dt.i) ≫ dt.p = f.right
      rw [Category.assoc, dt.fac]
      exact pushout.inl_desc _ _ _
  · constructor
    · exact ds.hi
    · change cofibrations C (corner i)
      have hcorner : corner i = dt.i := by
        apply pushout.hom_ext
        · simp only [corner, i, Arrow.homMk_left, Arrow.homMk_right, pushout.inl_desc]
        · simp only [corner, i, Z, Arrow.homMk_left, Arrow.mk_hom,
            pushout.inr_desc]
      rw [hcorner]
      exact dt.hi
  · exact ⟨ds.hp, dt.hp⟩

/-- Every arrow square has the actual projective-cofibration/pointwise-trivial-
fibration factorization. -/
instance : HasFactorization (projectiveArrowCofibrations (C := C))
    (pointwiseArrowTrivialFibrations (C := C)) where
  nonempty_mapFactorizationData f := ⟨factorization f⟩

omit [HasColimits C] in
/-- A projective arrow cofibration lifts against a pointwise trivial
fibration. The source lift is chosen first, then the corner lift. -/
theorem projective_lifts_pointwise
    {A B X Y : Arrow C} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : projectiveArrowCofibrations i)
    (hp : pointwiseArrowTrivialFibrations p) :
    HasLiftingProperty i p := by
  letI : HasLiftingProperty i.left p.left :=
    hasLiftingProperty_of_wfs i.left p.left hi.1 hp.1
  letI : HasLiftingProperty (corner i) p.right :=
    hasLiftingProperty_of_wfs (corner i) p.right hi.2 hp.2
  refine ⟨fun {u v} sq ↦ ?_⟩
  have sourceSq : CommSq u.left i.left p.left v.left :=
    ⟨Arrow.hom.congr_left sq.w⟩
  let ls : B.left ⟶ X.left := sourceSq.lift
  let t : pushout A.hom i.left ⟶ X.right :=
    pushout.desc u.right (ls ≫ X.hom) (by
      calc
        A.hom ≫ u.right = u.left ≫ X.hom := (Arrow.w u).symm
        _ = (i.left ≫ ls) ≫ X.hom := by rw [sourceSq.fac_left]
        _ = i.left ≫ (ls ≫ X.hom) := Category.assoc _ _ _)
  have targetSq : CommSq t (corner i) p.right v.right := by
    constructor
    apply pushout.hom_ext
    · calc
        pushout.inl A.hom i.left ≫ t ≫ p.right = u.right ≫ p.right := by
          simp only [← Category.assoc, t, pushout.inl_desc]
        _ = i.right ≫ v.right := Arrow.hom.congr_right sq.w
        _ = pushout.inl A.hom i.left ≫ corner i ≫ v.right := by
          simp only [← Category.assoc, corner, pushout.inl_desc]
    · calc
        pushout.inr A.hom i.left ≫ t ≫ p.right =
            ls ≫ X.hom ≫ p.right := by
          simp only [← Category.assoc, t, pushout.inr_desc]
        _ = ls ≫ p.left ≫ Y.hom := by rw [← Arrow.w p]
        _ = v.left ≫ Y.hom := by rw [← Category.assoc, sourceSq.fac_right]
        _ = B.hom ≫ v.right := Arrow.w v
        _ = pushout.inr A.hom i.left ≫ corner i ≫ v.right := by
          simp only [← Category.assoc, corner, pushout.inr_desc]
  let lt : B.right ⟶ X.right := targetSq.lift
  let l : B ⟶ X := Arrow.homMk ls lt (by
    calc
      ls ≫ X.hom = pushout.inr A.hom i.left ≫ t := by
        simp only [t, pushout.inr_desc]
      _ = pushout.inr A.hom i.left ≫ corner i ≫ lt := by
        rw [targetSq.fac_left]
      _ = B.hom ≫ lt := by simp only [← Category.assoc, corner, pushout.inr_desc])
  exact ⟨⟨{
    l := l
    fac_left := by
      apply Arrow.hom_ext
      · exact sourceSq.fac_left
      · calc
          i.right ≫ lt = pushout.inl A.hom i.left ≫ corner i ≫ lt := by
            simp only [← Category.assoc, corner, pushout.inl_desc]
          _ = pushout.inl A.hom i.left ≫ t := by
            rw [targetSq.fac_left]
          _ = u.right := by simp only [t, pushout.inl_desc]
    fac_right := by
      apply Arrow.hom_ext
      · exact sourceSq.fac_right
      · exact targetSq.fac_right
  }⟩⟩

/-- Projective arrow cofibrations are closed under arrow retracts. The
corner retract is functorial through the existing relative-latching-arrow
functor for `Arrow.leftToRight`. -/
instance : (projectiveArrowCofibrations (C := C)).IsStableUnderRetracts where
  of_retract {A B X Y i g} h hg := by
    constructor
    · exact MorphismProperty.of_retract (P := cofibrations C)
        (h.map Arrow.leftFunc) hg.1
    · have hc : RetractArrow (corner i) (corner g) := by
        change Retract (Arrow.mk (corner i)) (Arrow.mk (corner g))
        exact CategoryTheory.Retract.map h
          (relativeLatchingArrows (Arrow.leftToRight :
            Arrow.leftFunc (C := C) ⟶ Arrow.rightFunc))
      exact MorphismProperty.of_retract (P := cofibrations C) hc hg.2

/-- Pointwise trivial fibrations are closed under arrow retracts. -/
instance : (pointwiseArrowTrivialFibrations (C := C)).IsStableUnderRetracts where
  of_retract h hq :=
    ⟨MorphismProperty.of_retract (P := trivialFibrations C)
        (h.map Arrow.leftFunc) hq.1,
      MorphismProperty.of_retract (P := trivialFibrations C)
        (h.map Arrow.rightFunc) hq.2⟩

omit [HasColimits C] in
/-- The first projective weak factorization system on the walking arrow. -/
theorem projectiveArrowWfs :
    IsWeakFactorizationSystem (projectiveArrowCofibrations (C := C))
      (pointwiseArrowTrivialFibrations (C := C)) :=
  IsWeakFactorizationSystem.mk' _ _
    (fun i p hi hp ↦ projective_lifts_pointwise i p hi hp)

end

end DaggerModels.PartII.ProjectiveArrowFactorization
