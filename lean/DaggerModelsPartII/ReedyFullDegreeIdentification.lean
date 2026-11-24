import DaggerModelsPartII.ReedyDegreeIdentification
import DaggerModelsPartII.ReedyExtensionBoundaryRecovery

/-! Identify the degree data of a full diagram from its two consecutive restrictions. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C] {n : ℕ} {Z : BelowDegree n ⥤ C}
  (E : DegreeExtension Z) (W : SimplexCategoryᵒᵖ ⥤ C)
  (hFull : lowerDiagram (n + 1) W = extendBelowDiagram E)
  (hLow : lowerDiagram n W = Z)

def fullDegreeObjEq : (DegreeExtension.ofDiagram n W).obj = E.obj :=
  (CategoryTheory.Functor.congr_obj hFull (degreeTop n)).trans (extendBelowDiagram_top E)

theorem fullDegreeLatching_component (s : LatchingIndex n) :
    W.map s.obj.hom ≫ eqToHom (fullDegreeObjEq E W hFull) =
      eqToHom (CategoryTheory.Functor.congr_obj hLow ((latchingBelow n).obj s)) ≫
        colimit.ι (latchingBelow n ⋙ Z) s ≫ E.fromLatching := by
  have h := CategoryTheory.Functor.congr_hom hFull (truncatedLatchingArrow s)
  change W.map s.obj.hom = _ at h
  rw [h, extendBelowDiagram_map_latching]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

theorem fullDegreeMatching_component (s : MatchingIndex n) :
    W.map s.obj.hom ≫
        eqToHom (CategoryTheory.Functor.congr_obj hLow ((matchingBelow n).obj s)) =
      eqToHom (fullDegreeObjEq E W hFull) ≫ E.toMatching ≫
        limit.π (matchingBelow n ⋙ Z) s := by
  have h := CategoryTheory.Functor.congr_hom hFull (truncatedMatchingArrow s)
  change W.map s.obj.hom = _ at h
  rw [h, extendBelowDiagram_map_matching]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- Recover the two degree legs in the full diagram. -/
def fullDegreeIdentification : DegreeIdentification (DegreeExtension.ofDiagram n W) E where
  lower := hLow
  obj := fullDegreeObjEq E W hFull
  latching := by
    rw [← eqToHom_map (lowerLatching n) hLow]
    apply colimit.hom_ext
    intro s
    change colimit.ι (latchingProjection n ⋙ W) s ≫
        colimit.desc _ (latchingCocone n W) ≫ eqToHom (fullDegreeObjEq E W hFull) =
      colimit.ι (latchingBelow n ⋙ lowerDiagram n W) s ≫
        colimMap (CategoryTheory.Functor.whiskerLeft (latchingBelow n) (eqToHom hLow)) ≫
        E.fromLatching
    simp only [colimit.ι_desc_assoc, ι_colimMap_assoc, CategoryTheory.Functor.whiskerLeft_app,
      eqToHom_app]
    exact fullDegreeLatching_component E W hFull hLow s
  matching := by
    rw [← eqToHom_map (lowerMatching n) hLow]
    apply limit.hom_ext
    intro s
    change (limit.lift _ (matchingCone n W) ≫
        limMap (CategoryTheory.Functor.whiskerLeft (matchingBelow n) (eqToHom hLow))) ≫
        limit.π (matchingBelow n ⋙ Z) s =
      (eqToHom (fullDegreeObjEq E W hFull) ≫ E.toMatching) ≫ limit.π _ s
    simp only [Category.assoc, limMap_π, limit.lift_π_assoc,
      CategoryTheory.Functor.whiskerLeft_app, eqToHom_app]
    exact fullDegreeMatching_component E W hFull hLow s

end

end DaggerModels.PartII
