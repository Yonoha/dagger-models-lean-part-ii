import DaggerModelsPartII.ReedyFactorization
import DaggerModelsPartII.ReedyFullDegreeIdentification

/-! The relative maps of the glued factors have the chosen coefficient properties. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]

abbrev reedyChosenDegree (n : ℕ) :=
  chooseReedyFactorizationDegree (prev := reedyFactorizationBelow f P Q n) P Q

def reedyChosenDegreeIdentification (n : ℕ) :
    DegreeIdentification (DegreeExtension.ofDiagram n (reedyFactorizationMid f P Q))
      (reedyChosenDegree f P Q n).mid :=
  fullDegreeIdentification (reedyChosenDegree f P Q n).mid (reedyFactorizationMid f P Q)
    (glueDiagramTower_restrict (reedyFactorizationTower f P Q) (n + 1))
    (glueDiagramTower_restrict (reedyFactorizationTower f P Q) n)

theorem reedyLeft_lower_comparison (n : ℕ) :
    CategoryTheory.Functor.whiskerLeft (belowDegree n).ι (reedyFactorizationLeft f P Q) ≫
      eqToHom (reedyChosenDegreeIdentification f P Q n).lower =
      (reedyFactorizationBelow f P Q n).left := by
  ext s
  change reedyFactorizationLeftApp f P Q s.obj ≫
    (eqToHom (reedyChosenDegreeIdentification f P Q n).lower).app s = _
  rw [eqToHom_app, reedyFactorizationLeftApp_eq_at f P Q s.obj s.property]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem reedyRight_lower_comparison (n : ℕ) :
    CategoryTheory.Functor.whiskerLeft (belowDegree n).ι (reedyFactorizationRight f P Q) =
      eqToHom (reedyChosenDegreeIdentification f P Q n).lower ≫
        (reedyFactorizationBelow f P Q n).right := by
  ext s
  change reedyFactorizationRightApp f P Q s.obj =
    (eqToHom (reedyChosenDegreeIdentification f P Q n).lower).app s ≫ _
  rw [eqToHom_app]
  exact reedyFactorizationRightApp_eq_at f P Q s.obj s.property

theorem reedyLeft_degree_comparison (n : ℕ) :
    (reedyFactorizationLeft f P Q).app (op ⦋n⦌) ≫
      eqToHom (reedyChosenDegreeIdentification f P Q n).obj =
      (reedyChosenDegree f P Q n).left.app := by
  let D := reedyChosenDegree f P Q n
  change D.next.left.app (degreeTop n) ≫ eqToHom
    (reedyChosenDegreeIdentification f P Q n).obj = D.left.app
  simp only [ReedyFactorizationDegree.next, NatTrans.comp_app, eqToHom_app,
    extendBelowTransformation_app_top, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

theorem reedyRight_degree_comparison (n : ℕ) :
    (reedyFactorizationRight f P Q).app (op ⦋n⦌) =
      eqToHom (reedyChosenDegreeIdentification f P Q n).obj ≫
        (reedyChosenDegree f P Q n).right.app := by
  let D := reedyChosenDegree f P Q n
  change D.next.right.app (degreeTop n) = eqToHom
    (reedyChosenDegreeIdentification f P Q n).obj ≫ D.right.app
  simp only [ReedyFactorizationDegree.next, NatTrans.comp_app, eqToHom_app,
    extendBelowTransformation_app_top, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- Each relative latching map of the left factor has the chosen left property. -/
theorem reedyFactorizationLeft_relative_mem (n : ℕ) :
    P (relativeLatchingMap n (reedyFactorizationLeft f P Q)) := by
  let D := reedyChosenDegree f P Q n
  let hX := DegreeIdentification.refl (DegreeExtension.ofDiagram n X)
  have h := relativeMaps_mem_iff_of_identification
    (DegreeExtension.Hom.ofDiagram (reedyFactorizationLeft f P Q) n) D.left
    hX (reedyChosenDegreeIdentification f P Q n)
    (by simpa only [eqToHom_refl, Category.id_comp] using reedyLeft_lower_comparison f P Q n)
    (by simpa only [eqToHom_refl, Category.id_comp] using reedyLeft_degree_comparison f P Q n)
    P Q
  exact h.1.mpr D.left_mem

/-- Each relative matching map of the right factor has the chosen right property. -/
theorem reedyFactorizationRight_relative_mem (n : ℕ) :
    Q (relativeMatchingMap n (reedyFactorizationRight f P Q)) := by
  let D := reedyChosenDegree f P Q n
  let hY := DegreeIdentification.refl (DegreeExtension.ofDiagram n Y)
  have h := relativeMaps_mem_iff_of_identification
    (DegreeExtension.Hom.ofDiagram (reedyFactorizationRight f P Q) n) D.right
    (reedyChosenDegreeIdentification f P Q n) hY
    (by simpa only [eqToHom_refl, Category.comp_id] using reedyRight_lower_comparison f P Q n)
    (by simpa only [eqToHom_refl, Category.comp_id] using reedyRight_degree_comparison f P Q n)
    P Q
  exact h.2.mpr D.right_mem

end

end DaggerModels.PartII
