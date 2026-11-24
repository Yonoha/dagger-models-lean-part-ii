import DaggerModelsPartII.ReedySeededMaps
import DaggerModelsPartII.ReedyFactorizationProperties

/-! Relative Reedy properties of the factors extending a prescribed first stage. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]
  (seed : ReedyFactorizationBelow f 1)

private abbrev seededChosenDegree (n : ℕ) :=
  chooseReedyFactorizationDegree
    (prev := seededReedyBelow f P Q seed (n + 1)) P Q

private def seededChosenDegreeIdentification (n : ℕ) :
    DegreeIdentification (DegreeExtension.ofDiagram (n + 1)
      (seededReedyMid f P Q seed)) (seededChosenDegree f P Q seed n).mid :=
  fullDegreeIdentification (seededChosenDegree f P Q seed n).mid
    (seededReedyMid f P Q seed)
    (glueDiagramTower_restrict (seededReedyTower f P Q seed) (n + 2))
    (glueDiagramTower_restrict (seededReedyTower f P Q seed) (n + 1))

private theorem seededLeft_lower_comparison (n : ℕ) :
    CategoryTheory.Functor.whiskerLeft (belowDegree (n + 1)).ι
        (seededReedyLeft f P Q seed) ≫
      eqToHom (seededChosenDegreeIdentification f P Q seed n).lower =
      (seededReedyBelow f P Q seed (n + 1)).left := by
  ext s
  change seededReedyLeftApp f P Q seed s.obj ≫
    (eqToHom (seededChosenDegreeIdentification f P Q seed n).lower).app s = _
  rw [eqToHom_app, seededReedyLeftApp_eq_at f P Q seed s.obj s.property]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

private theorem seededRight_lower_comparison (n : ℕ) :
    CategoryTheory.Functor.whiskerLeft (belowDegree (n + 1)).ι
      (seededReedyRight f P Q seed) =
      eqToHom (seededChosenDegreeIdentification f P Q seed n).lower ≫
        (seededReedyBelow f P Q seed (n + 1)).right := by
  ext s
  change seededReedyRightApp f P Q seed s.obj =
    (eqToHom (seededChosenDegreeIdentification f P Q seed n).lower).app s ≫ _
  rw [eqToHom_app]
  exact seededReedyRightApp_eq_at f P Q seed s.obj s.property

private theorem seededLeft_degree_comparison (n : ℕ) :
    (seededReedyLeft f P Q seed).app (op ⦋n + 1⦌) ≫
      eqToHom (seededChosenDegreeIdentification f P Q seed n).obj =
      (seededChosenDegree f P Q seed n).left.app := by
  let D := seededChosenDegree f P Q seed n
  change D.next.left.app (degreeTop (n + 1)) ≫ eqToHom
    (seededChosenDegreeIdentification f P Q seed n).obj = D.left.app
  simp only [ReedyFactorizationDegree.next, NatTrans.comp_app, eqToHom_app,
    extendBelowTransformation_app_top, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem seededRight_degree_comparison (n : ℕ) :
    (seededReedyRight f P Q seed).app (op ⦋n + 1⦌) =
      eqToHom (seededChosenDegreeIdentification f P Q seed n).obj ≫
        (seededChosenDegree f P Q seed n).right.app := by
  let D := seededChosenDegree f P Q seed n
  change D.next.right.app (degreeTop (n + 1)) = eqToHom
    (seededChosenDegreeIdentification f P Q seed n).obj ≫ D.right.app
  simp only [ReedyFactorizationDegree.next, NatTrans.comp_app, eqToHom_app,
    extendBelowTransformation_app_top, Category.assoc, eqToHom_trans,
    eqToHom_refl, Category.comp_id]

/-- Every positive-degree relative latching map of the seeded left factor
belongs to the selected coefficient class. -/
theorem seededReedyLeft_relative_mem_positive (n : ℕ) :
    P (relativeLatchingMap (n + 1) (seededReedyLeft f P Q seed)) := by
  let D := seededChosenDegree f P Q seed n
  let hX := DegreeIdentification.refl (DegreeExtension.ofDiagram (n + 1) X)
  have h := relativeMaps_mem_iff_of_identification
    (DegreeExtension.Hom.ofDiagram (seededReedyLeft f P Q seed) (n + 1)) D.left
    hX (seededChosenDegreeIdentification f P Q seed n)
    (by simpa only [eqToHom_refl, Category.id_comp] using
      seededLeft_lower_comparison f P Q seed n)
    (by simpa only [eqToHom_refl, Category.id_comp] using
      seededLeft_degree_comparison f P Q seed n)
    P Q
  exact h.1.mpr D.left_mem

/-- Every positive-degree relative matching map of the seeded right factor
belongs to the selected coefficient class. -/
theorem seededReedyRight_relative_mem_positive (n : ℕ) :
    Q (relativeMatchingMap (n + 1) (seededReedyRight f P Q seed)) := by
  let D := seededChosenDegree f P Q seed n
  let hY := DegreeIdentification.refl (DegreeExtension.ofDiagram (n + 1) Y)
  have h := relativeMaps_mem_iff_of_identification
    (DegreeExtension.Hom.ofDiagram (seededReedyRight f P Q seed) (n + 1)) D.right
    (seededChosenDegreeIdentification f P Q seed n) hY
    (by simpa only [eqToHom_refl, Category.comp_id] using
      seededRight_lower_comparison f P Q seed n)
    (by simpa only [eqToHom_refl, Category.comp_id] using
      seededRight_degree_comparison f P Q seed n)
    P Q
  exact h.2.mpr D.right_mem

/-- The seed supplies the relative latching property in degree zero. -/
theorem seededReedyLeft_relative_mem_zero [P.RespectsIso]
    (hseed : P (seed.left.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩)) :
    P (relativeLatchingMap 0 (seededReedyLeft f P Q seed)) := by
  let g := seededReedyLeft f P Q seed
  have h0 : P (g.app (op ⦋0⦌)) := by
    change P ((seededReedyLeft f P Q seed).app (op ⦋0⦌))
    rw [seededReedyLeft_app_zero]
    exact hseed
  have hcomp : P ((relativeLatchingZeroSourceIso g).inv ≫ relativeLatchingMap 0 g) := by
    rw [relativeLatchingMap_zero]
    exact h0
  exact ((P.cancel_left_of_respectsIso
    (relativeLatchingZeroSourceIso g).inv (relativeLatchingMap 0 g)).1 hcomp)

/-- The seed supplies the relative matching property in degree zero. -/
theorem seededReedyRight_relative_mem_zero [Q.RespectsIso]
    (hseed : Q (seed.right.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩)) :
    Q (relativeMatchingMap 0 (seededReedyRight f P Q seed)) := by
  let g := seededReedyRight f P Q seed
  have h0 : Q (g.app (op ⦋0⦌)) := by
    change Q ((seededReedyRight f P Q seed).app (op ⦋0⦌))
    rw [seededReedyRight_app_zero]
    exact hseed
  have hcomp : Q (relativeMatchingMap 0 g ≫ (relativeMatchingZeroTargetIso g).hom) := by
    rw [relativeMatchingMap_zero]
    exact h0
  exact ((Q.cancel_right_of_respectsIso
    (relativeMatchingMap 0 g) (relativeMatchingZeroTargetIso g).hom).1 hcomp)

/-- The chosen left class holds in every degree once it holds in the seed. -/
theorem seededReedyLeft_relative_mem [P.RespectsIso]
    (hseed : P (seed.left.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩))
    (n : ℕ) : P (relativeLatchingMap n (seededReedyLeft f P Q seed)) := by
  cases n with
  | zero => exact seededReedyLeft_relative_mem_zero f P Q seed hseed
  | succ n => exact seededReedyLeft_relative_mem_positive f P Q seed n

/-- The chosen right class holds in every degree once it holds in the seed. -/
theorem seededReedyRight_relative_mem [Q.RespectsIso]
    (hseed : Q (seed.right.app ⟨op ⦋0⦌, by change (0 : ℕ) < 1; decide⟩))
    (n : ℕ) : Q (relativeMatchingMap n (seededReedyRight f P Q seed)) := by
  cases n with
  | zero => exact seededReedyRight_relative_mem_zero f P Q seed hseed
  | succ n => exact seededReedyRight_relative_mem_positive f P Q seed n

end

end DaggerModels.PartII
