import DaggerModelsPartII.ReedyDegreeFactorization
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# One degree of the Reedy lifting argument

Given a lift on the lower diagrams, a square between the relative latching
and matching maps in the coefficient category extends that lift to the
new degree data.
-/

set_option autoImplicit false

open CategoryTheory Limits

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ}
  {Xₗ Yₗ Uₗ Vₗ : BelowDegree n ⥤ C}
  {X : DegreeExtension Xₗ} {Y : DegreeExtension Yₗ}
  {U : DegreeExtension Uₗ} {V : DegreeExtension Vₗ}
  {i : Xₗ ⟶ Yₗ} {p : Uₗ ⟶ Vₗ}
  {a : Xₗ ⟶ Uₗ} {b : Yₗ ⟶ Vₗ}
  (I : DegreeExtension.Hom i X Y) (P : DegreeExtension.Hom p U V)
  (A : DegreeExtension.Hom a X U) (B : DegreeExtension.Hom b Y V)
  (l : Yₗ ⟶ Uₗ) (hl : i ≫ l = a) (hr : l ≫ p = b)

/-- The top arrow of the lifting problem in the coefficient category. -/
def degreeLiftingTop :
    pushout X.fromLatching ((lowerLatching n).map i) ⟶ U.obj :=
  pushout.desc A.app ((lowerLatching n).map l ≫ U.fromLatching) (by
    rw [← Category.assoc, ← (lowerLatching n).map_comp, hl, A.latching_naturality])

/-- The bottom arrow of the lifting problem in the coefficient category. -/
def degreeLiftingBottom :
    Y.obj ⟶ pullback ((lowerMatching n).map p) V.toMatching :=
  pullback.lift (Y.toMatching ≫ (lowerMatching n).map l) B.app (by
    rw [Category.assoc, ← (lowerMatching n).map_comp, hr, B.matching_naturality])

/-- Compatibility of the square on degree components gives the relative lifting square. -/
theorem degreeLiftingSquare (hs : A.app ≫ P.app = I.app ≫ B.app) :
    CommSq (degreeLiftingTop A l hl) I.relativeLatching P.relativeMatching
      (degreeLiftingBottom B l hr) := by
  constructor
  apply pullback.hom_ext
  · simp only [Category.assoc, DegreeExtension.Hom.relativeMatching, degreeLiftingBottom,
      pullback.lift_fst]
    apply pushout.hom_ext
    · simp only [degreeLiftingTop, DegreeExtension.Hom.relativeLatching, pushout.inl_desc_assoc]
      rw [A.matching_naturality, ← Category.assoc I.app, I.matching_naturality, Category.assoc,
        ← (lowerMatching n).map_comp, hl]
    · simp only [degreeLiftingTop, DegreeExtension.Hom.relativeLatching, Category.assoc,
        pushout.inr_desc_assoc, U.boundary]
      rw [← Category.assoc Y.fromLatching, Y.boundary]
      exact lowerBoundaryMap_naturality l
  · simp only [Category.assoc, DegreeExtension.Hom.relativeMatching, degreeLiftingBottom,
      pullback.lift_snd]
    apply pushout.hom_ext
    · simpa only [degreeLiftingTop, DegreeExtension.Hom.relativeLatching, Category.assoc,
        pushout.inl_desc_assoc] using hs
    · simp only [degreeLiftingTop, DegreeExtension.Hom.relativeLatching, Category.assoc,
        pushout.inr_desc_assoc]
      rw [← P.latching_naturality, ← Category.assoc, ← (lowerLatching n).map_comp, hr,
        B.latching_naturality]

include hl hr in
/-- A lift between the relative maps extends the given lower lift by one degree. -/
theorem exists_liftedDegree (hs : A.app ≫ P.app = I.app ≫ B.app)
    (hp : HasLiftingProperty I.relativeLatching P.relativeMatching) :
    ∃ L : DegreeExtension.Hom l Y U, I.app ≫ L.app = A.app ∧ L.app ≫ P.app = B.app := by
  letI := hp
  let s := degreeLiftingSquare I P A B l hl hr hs
  refine ⟨⟨s.lift, ?_, ?_⟩, ?_, ?_⟩
  · have h := congrArg (fun k ↦ pushout.inr X.fromLatching ((lowerLatching n).map i) ≫ k)
      s.fac_left
    simpa only [Category.assoc, DegreeExtension.Hom.relativeLatching, degreeLiftingTop,
      pushout.inr_desc_assoc, pushout.inr_desc] using h.symm
  · have h := congrArg
      (fun k ↦ k ≫ pullback.fst ((lowerMatching n).map p) V.toMatching) s.fac_right
    simpa only [Category.assoc, DegreeExtension.Hom.relativeMatching, degreeLiftingBottom,
      pullback.lift_fst] using h
  · have h := congrArg (fun k ↦ pushout.inl X.fromLatching ((lowerLatching n).map i) ≫ k)
      s.fac_left
    simpa only [Category.assoc, DegreeExtension.Hom.relativeLatching, degreeLiftingTop,
      pushout.inl_desc_assoc, pushout.inl_desc] using h
  · have h := congrArg
      (fun k ↦ k ≫ pullback.snd ((lowerMatching n).map p) V.toMatching) s.fac_right
    simpa only [Category.assoc, DegreeExtension.Hom.relativeMatching, degreeLiftingBottom,
      pullback.lift_snd] using h

end

end DaggerModels.PartII
