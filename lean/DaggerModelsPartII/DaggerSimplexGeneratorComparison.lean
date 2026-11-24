import DaggerModelsPartII.DaggerSimplexPartIComparison

/-!
# Named generators in the Part I free dagger simplex

The Part I adjunction unit names the positive adjacent arrows.  The canonical
comparison sends them to the corresponding one-letter paths.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexFreeProperty
open DaggerModels.PartII.ConstantDaggerSource
open DaggerModels.PartII.DaggerSimplexPartIComparison
open DaggerOriginalSimplicialDegreeCategory
open DaggerNativeDaggerDegreeCotensor

namespace DaggerModels.PartII.DaggerSimplexGeneratorComparison

noncomputable section

private def adj :=
  OrdinaryRigidification.daggerRigidificationLiftWitness.{0}.freeSCatAdjunction

private instance targetDagger (D : DaggerSimplicialCat.{0, 0}) :
    DaggerCategory (degreeObjects D.toSimplicialCat (op ⦋0⦌)) :=
  degreeDaggerCategory D (op ⦋0⦌)

/-- The forward comparison arrow is the inverse image of the identity under
the natural equivalence of represented Hom functors. -/
theorem comparisonIso_hom (n : ℕ) :
    (comparisonIso n).hom =
      (comparisonEquiv n (pathFree n)).symm (𝟙 (pathFree n)) := by
  rfl

/-- The degree-zero ordinary diagram named by the unit of the Part I
free dagger simplicial category adjunction. -/
def partIOrdinal (n : ℕ) :
    Fin (n + 1) ⥤ degreeObjects (partIFree n).toSimplicialCat (op ⦋0⦌) :=
  toOrdinarySimplicial (A := Fin (n + 1))
    (adj.unit.app (source n))

/-- The canonical ordinal diagram in the path presentation. -/
def pathOrdinal (n : ℕ) :
    Fin (n + 1) ⥤ degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌) :=
  (freeDaggerSimplexOrdinalEquiv n
    (degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌)))
    ((homEquiv (A := FreeDaggerSimplex n) (D := pathFree n)).symm
      (𝟙 (pathFree n)))

/-- The canonical comparison identifies the Part I unit diagram with the
ordinary finite-ordinal diagram inside the path category. -/
theorem partIOrdinal_comp_comparison (n : ℕ) :
    partIOrdinal n ⋙
      degreeFunctor (comparisonIso n).hom.toEnrichedFunctor (op ⦋0⦌) =
      pathOrdinal n := by
  let h := (comparisonIso n).hom
  have he : comparisonEquiv n (pathFree n) h = 𝟙 (pathFree n) := by
    rw [show h = (comparisonIso n).hom from rfl, comparisonIso_hom]
    exact (comparisonEquiv n (pathFree n)).apply_symm_apply _
  have hu : adj.homEquiv (source n) (pathFree n) h =
      adj.unit.app (source n) ≫ h.toEnrichedFunctor := by
    simpa using adj.homEquiv_naturality_right
      (𝟙 (partIFree n)) h
  have hord :
      (simplicialHomEquiv (A := Fin (n + 1))
        (E := (pathFree n).toSimplicialCat)).symm
        (adj.homEquiv (source n) (pathFree n) h) = pathOrdinal n := by
    let W := (freeDaggerSimplexOrdinalEquiv n
      (degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌))).symm
        ((simplicialHomEquiv (A := Fin (n + 1))
          (E := (pathFree n).toSimplicialCat)).symm
          (adj.homEquiv (source n) (pathFree n) h))
    have hh := congrArg
      (toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)) he
    change toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)
        ((homEquiv (A := FreeDaggerSimplex n) (D := pathFree n))
          ((freeDaggerSimplexOrdinalEquiv n
            (degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌))).symm
            ((simplicialHomEquiv (A := Fin (n + 1))
              (E := (pathFree n).toSimplicialCat)).symm
              (adj.homEquiv (source n) (pathFree n) h)))) =
      toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)
        (𝟙 (pathFree n)) at hh
    change toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)
      (@fromOrdinary (FreeDaggerSimplex n) _ _ (pathFree n) W.1 W.2) =
        toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)
          (𝟙 (pathFree n)) at hh
    rw [to_from] at hh
    have hp : W = (homEquiv (A := FreeDaggerSimplex n)
        (D := pathFree n)).symm (𝟙 (pathFree n)) := Subtype.ext hh
    apply (freeDaggerSimplexOrdinalEquiv n
      (degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌))).symm.injective
    simpa [W, pathOrdinal] using hp
  rw [hu] at hord
  change toOrdinarySimplicial (A := Fin (n + 1))
    (adj.unit.app (source n) ≫ h.toEnrichedFunctor) = pathOrdinal n at hord
  have hcomp : partIOrdinal n ⋙
      degreeFunctor h.toEnrichedFunctor (op ⦋0⦌) =
      toOrdinarySimplicial (A := Fin (n + 1))
        (adj.unit.app (source n) ≫ h.toEnrichedFunctor) := by
    apply CategoryTheory.Functor.ext
    case h_obj => intro x; rfl
    case h_map =>
      intro x y f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
  exact hcomp.trans hord

/-- The positive adjacent arrow in the finite ordinal. -/
def adjacentOrdinalHom (n a : ℕ) (ha : a + 1 ≤ n) :
    (⟨a, by omega⟩ : Fin (n + 1)) ⟶
      (⟨a + 1, by omega⟩ : Fin (n + 1)) :=
  CategoryTheory.homOfLE (by
    change a ≤ a + 1
    omega)

/-- The named positive generator in the actual Part I free object, obtained
from the unit of its free-forgetful adjunction. -/
def partIPositiveGenerator (n a : ℕ) (ha : a + 1 ≤ n) :
    (partIOrdinal n).obj ⟨a, by omega⟩ ⟶
      (partIOrdinal n).obj ⟨a + 1, by omega⟩ :=
  (partIOrdinal n).map (adjacentOrdinalHom n a ha)

theorem pathOrdinal_adjacent (n a : ℕ) (ha : a + 1 ≤ n) :
    (pathOrdinal n).map (adjacentOrdinalHom n a ha) =
      forwardEdge n a ha := by
  let F := (homEquiv (A := FreeDaggerSimplex n) (D := pathFree n)).symm
    (𝟙 (pathFree n))
  change wordValue n (degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌))
    (restrict n _ F)
    (forwardWord n a (a + 1) (by omega) ha (by omega)) = forwardEdge n a ha
  rw [wordValue_restrict]
  change (toOrdinary (A := FreeDaggerSimplex n) (D := pathFree n)
    (𝟙 (pathFree n))).map
      (forwardWord n a (a + 1) (by omega) ha (by omega)) = forwardEdge n a ha
  rw [forwardWord_step n a (a + 1) (by omega) ha (by omega)]
  rw [forwardWord_self]
  change (forwardEdge n a (by omega : a + 1 ≤ n) ≫ 𝟙 _) = forwardEdge n a ha
  simp

/-- The Part I unit's named positive generator becomes the one-letter
positive path under the canonical comparison isomorphism. -/
theorem comparisonIso_positive_generator (n a : ℕ) (ha : a + 1 ≤ n) :
    (partIOrdinal n ⋙
      degreeFunctor (comparisonIso n).hom.toEnrichedFunctor (op ⦋0⦌)).map
        (adjacentOrdinalHom n a ha) = forwardEdge n a ha := by
  have hmap := congr_arg_heq
    (fun F : Fin (n + 1) ⥤
        degreeObjects (pathFree n).toSimplicialCat (op ⦋0⦌) =>
      F.map (adjacentOrdinalHom n a ha))
    (partIOrdinal_comp_comparison n)
  exact eq_of_heq (hmap.trans (heq_of_eq (pathOrdinal_adjacent n a ha)))

/-- The same generator formula stated directly using the named Part I arrow. -/
theorem comparisonIso_map_partIPositiveGenerator (n a : ℕ)
    (ha : a + 1 ≤ n) :
    (degreeFunctor (comparisonIso n).hom.toEnrichedFunctor (op ⦋0⦌)).map
      (partIPositiveGenerator n a ha) = forwardEdge n a ha :=
  comparisonIso_positive_generator n a ha

end

end DaggerModels.PartII.DaggerSimplexGeneratorComparison
