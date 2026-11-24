import DaggerModelsPartII.ReedyMaps
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Coefficient change for relative Reedy corner maps

The comparison is purely categorical: preservation of the matching limit and
pullback, or of the latching colimit and pushout, gives an isomorphism in the
arrow category. There is no model-category instance on either coefficient.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe v₁ u₁ v₂ u₂

namespace DaggerModels.PartII.ReedyCoefficientChange

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

noncomputable section

section Matching

variable [HasLimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} D]
variable (G : C ⥤ D) [PreservesLimitsOfSize.{0, 0} G]

/-- The canonical isomorphism comparing the two matching objects. -/
def matchingObjectIso (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    G.obj ((matchingFunctor n).obj W) ≅
      (matchingFunctor n).obj (W ⋙ G) :=
  preservesLimitIso G (matchingProjection n ⋙ W)

/-- The matching comparison commutes with coefficient change. -/
theorem matchingComparison_map (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    G.map ((matchingComparison n).app W) ≫
      (matchingObjectIso G n W).hom =
        (matchingComparison n).app (W ⋙ G) := by
  apply limit.hom_ext
  intro s
  change (_ ≫ (matchingObjectIso G n W).hom) ≫
      limit.π ((matchingProjection n ⋙ W) ⋙ G) s =
    limit.lift _ (matchingCone n (W ⋙ G)) ≫
      limit.π (matchingProjection n ⋙ (W ⋙ G)) s
  dsimp only [matchingObjectIso]
  rw [Category.assoc, preservesLimitIso_hom_π, ← G.map_comp, limit.lift_π]
  change G.map (limit.lift _ (matchingCone n W) ≫ limit.π _ s) =
    G.map (W.map s.obj.hom)
  rw [limit.lift_π]
  rfl

/-- Naturality of the matching-object comparison in the simplicial diagram. -/
theorem matchingObjectIso_naturality (n : ℕ)
    {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    G.map ((matchingFunctor n).map f) ≫
      (matchingObjectIso G n V).hom =
    (matchingObjectIso G n W).hom ≫
      (matchingFunctor n).map (Functor.whiskerRight f G) := by
  have h := (preservesLimitNatIso (J := MatchingIndex n) G).hom.naturality
    (Functor.whiskerLeft (matchingProjection n) f)
  exact h

/-- The target of the relative matching map commutes with coefficient change. -/
def matchingPullbackIso (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) :
    G.obj (pullback ((matchingFunctor n).map f)
      ((matchingComparison n).app V)) ≅
      pullback ((matchingFunctor n).map (Functor.whiskerRight f G))
        ((matchingComparison n).app (V ⋙ G)) := by
  let eW := matchingObjectIso G n W
  let eV := matchingObjectIso G n V
  have h₁ : G.map ((matchingFunctor n).map f) ≫ eV.hom =
      eW.hom ≫ (matchingFunctor n).map (Functor.whiskerRight f G) :=
    matchingObjectIso_naturality G n f
  have h₂ : G.map ((matchingComparison n).app V) ≫ eV.hom =
      (𝟙 _) ≫ (matchingComparison n).app (V ⋙ G) := by
    simpa only [Category.id_comp] using matchingComparison_map G n V
  exact PreservesPullback.iso G ((matchingFunctor n).map f)
      ((matchingComparison n).app V) ≪≫
    asIso (pullback.map _ _ _ _ eW.hom (𝟙 _) eV.hom h₁ h₂)

/-- The relative matching arrow itself commutes with coefficient change. -/
def relativeMatchingArrowIso (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) :
    Arrow.mk (G.map (relativeMatchingMap n f)) ≅
      Arrow.mk (relativeMatchingMap n (Functor.whiskerRight f G)) := by
  refine Arrow.isoMk (Iso.refl _ ) (matchingPullbackIso G n f) ?_
  apply pullback.hom_ext
  · simp [matchingPullbackIso, relativeMatchingMap, matchingObjectIso]
    exact (matchingComparison_map G n W).symm
  · simp [matchingPullbackIso, relativeMatchingMap]

end Matching

section Latching

variable [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
variable (G : C ⥤ D) [PreservesColimitsOfSize.{0, 0} G]

/-- The canonical isomorphism comparing the two latching objects. -/
def latchingObjectIso (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    G.obj ((latchingFunctor n).obj W) ≅
      (latchingFunctor n).obj (W ⋙ G) :=
  preservesColimitIso G (latchingProjection n ⋙ W)

/-- The latching comparison commutes with coefficient change. -/
theorem latchingComparison_map (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    (latchingObjectIso G n W).inv ≫
      G.map ((latchingComparison n).app W) =
        (latchingComparison n).app (W ⋙ G) := by
  apply colimit.hom_ext
  intro s
  dsimp only [latchingObjectIso]
  change colimit.ι ((latchingProjection n ⋙ W) ⋙ G) s ≫
      ((preservesColimitIso G (latchingProjection n ⋙ W)).inv ≫
        G.map ((latchingComparison n).app W)) =
    colimit.ι (latchingProjection n ⋙ (W ⋙ G)) s ≫
      (latchingComparison n).app (W ⋙ G)
  rw [← Category.assoc, ι_preservesColimitIso_inv]
  change G.map (colimit.ι _ s) ≫ G.map (colimit.desc _ (latchingCocone n W)) =
    colimit.ι _ s ≫ colimit.desc _ (latchingCocone n (W ⋙ G))
  rw [← G.map_comp, colimit.ι_desc, colimit.ι_desc]
  rfl

/-- Naturality of the latching-object comparison in the simplicial diagram. -/
theorem latchingObjectIso_naturality (n : ℕ)
    {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    G.map ((latchingFunctor n).map f) ≫
      (latchingObjectIso G n V).hom =
    (latchingObjectIso G n W).hom ≫
      (latchingFunctor n).map (Functor.whiskerRight f G) := by
  have h := (preservesColimitNatIso (J := LatchingIndex n) G).hom.naturality
    (Functor.whiskerLeft (latchingProjection n) f)
  exact h

/-- The source of the relative latching map commutes with coefficient change. -/
def latchingPushoutIso (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) :
    G.obj (pushout ((latchingComparison n).app W)
      ((latchingFunctor n).map f)) ≅
      pushout ((latchingComparison n).app (W ⋙ G))
        ((latchingFunctor n).map (Functor.whiskerRight f G)) := by
  let eW := latchingObjectIso G n W
  let eV := latchingObjectIso G n V
  have h₁ : G.map ((latchingComparison n).app W) ≫ (𝟙 _) =
      eW.hom ≫ (latchingComparison n).app (W ⋙ G) := by
    rw [Category.comp_id]
    calc
      G.map ((latchingComparison n).app W) =
          eW.hom ≫ (eW.inv ≫ G.map ((latchingComparison n).app W)) := by simp
      _ = eW.hom ≫ (latchingComparison n).app (W ⋙ G) := by
        rw [latchingComparison_map]
  have h₂ : G.map ((latchingFunctor n).map f) ≫ eV.hom =
      eW.hom ≫ (latchingFunctor n).map (Functor.whiskerRight f G) :=
    latchingObjectIso_naturality G n f
  exact (PreservesPushout.iso G ((latchingComparison n).app W)
      ((latchingFunctor n).map f)).symm ≪≫
    asIso (pushout.map _ _ _ _ (𝟙 _) eV.hom eW.hom h₁ h₂)

/-- The relative latching arrow itself commutes with coefficient change. -/
def relativeLatchingArrowIso (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C}
    (f : W ⟶ V) :
    Arrow.mk (G.map (relativeLatchingMap n f)) ≅
      Arrow.mk (relativeLatchingMap n (Functor.whiskerRight f G)) := by
  refine Arrow.isoMk (latchingPushoutIso G n f) (Iso.refl _) ?_
  let e := PreservesPushout.iso G ((latchingComparison n).app W)
    ((latchingFunctor n).map f)
  apply (cancel_epi e.hom).mp
  apply pushout.hom_ext
  · simp [latchingPushoutIso, relativeLatchingMap, latchingObjectIso, e]
  · simp [latchingPushoutIso, relativeLatchingMap, e]
    calc
      (latchingObjectIso G n V).hom ≫
          (latchingComparison n).app (V ⋙ G) =
        (latchingObjectIso G n V).hom ≫
          ((latchingObjectIso G n V).inv ≫
            G.map ((latchingComparison n).app V)) :=
        congrArg (fun x ↦ (latchingObjectIso G n V).hom ≫ x)
          (latchingComparison_map G n V).symm
      _ = G.map ((latchingComparison n).app V) := by simp

end Latching

section PropertyTransfer

variable (P : MorphismProperty D) [P.RespectsIso]

/-- Any isomorphism-invariant property of the mapped relative matching
arrow is equivalent to the property of the relative matching arrow after
coefficient change. -/
theorem relativeMatchingMap_property_iff
    [HasLimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} D]
    (G : C ⥤ D) [PreservesLimitsOfSize.{0, 0} G]
    (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    P (G.map (relativeMatchingMap n f)) ↔
      P (relativeMatchingMap n (Functor.whiskerRight f G)) :=
  P.arrow_mk_iso_iff (relativeMatchingArrowIso G n f)

/-- The dual property transfer for relative latching arrows. -/
theorem relativeLatchingMap_property_iff
    [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D]
    (G : C ⥤ D) [PreservesColimitsOfSize.{0, 0} G]
    (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    P (G.map (relativeLatchingMap n f)) ↔
      P (relativeLatchingMap n (Functor.whiskerRight f G)) :=
  P.arrow_mk_iso_iff (relativeLatchingArrowIso G n f)

end PropertyTransfer

end

end DaggerModels.PartII.ReedyCoefficientChange
