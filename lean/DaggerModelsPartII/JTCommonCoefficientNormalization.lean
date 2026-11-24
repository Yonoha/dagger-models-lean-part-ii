import DaggerModelsPartII.JTCommonCoefficientCompatibleBoundary
import DaggerModelsPartII.SemiSimplexBoundaryLifting

/-!
# Forgetting a common-coefficient enlargement

The exact extension choices form a semisimplicial presheaf over the original
simplicial set of normalization choices. Forgetting the enlargement lifts
every compatible proper-face boundary.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTCommonCoefficientNormalization

open JTCommonCoefficientParameter
open JTCommonCoefficientLiftChoices (Extension underlying underlying_timeMap)
open JTFixedLiftSpaceTimeEquiv (timeEquiv timeMap timeMap_map)
open SemiSimplexBoundaryLifting

noncomputable section

private abbrev simplex := SSet.stdSimplex.{0}
private abbrev inc := SemiSimplexCategory.toSimplexCategory

variable {b : SimplexCategory} {k : ℕ} {c : ⦋k⦌ ⟶ b}
variable {A X Y : SSet.{0}} {i : A ⟶ simplex.obj ⦋k⦌}
variable {t : A ⟶ X} {p : X ⟶ Y} {g : simplex.obj b ⟶ Y}
variable (sq : CommSq t i p (simplex.map c ≫ g))

private def restrict {m n : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) (E : Extension sq ⦋n⦌) :
    Extension sq ⦋m⦌ :=
  JTCommonCoefficientLiftChoices.restrict sq sq (𝟙 ⦋k⦌) (Category.id_comp c)
    (by rw [simplex.map_id, Category.comp_id]) j hj E

private theorem restrict_map {m n : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) (E : Extension sq ⦋n⦌) :
    (restrict sq j hj E).map = simplex.map (timeOperator c n j hj) ≫ E.map := rfl

/-- The enlarged normalization choices at one coefficient, with their genuine
injective time restrictions. -/
def choices : SemiSimplexCategoryᵒᵖ ⥤ Type where
  obj n := Extension sq (inc.obj n.unop)
  map j := restrict sq (inc.map j.unop) (SemiSimplexCategory.homEquiv j.unop).injective
  map_id n := by
    funext E
    exact JTCommonCoefficientLiftChoices.restrict_id sq E
  map_comp j a := by
    funext E
    apply Extension.ext
    change (restrict sq (inc.map (a.unop ≫ j.unop)) _ E).map =
      (restrict sq (inc.map a.unop) _ (restrict sq (inc.map j.unop) _ E)).map
    rw [restrict_map, restrict_map, restrict_map]
    simp only [inc.map_comp]
    rw [timeOperator_comp c _ (inc.map a.unop) (inc.map j.unop)
      (SemiSimplexCategory.homEquiv a.unop).injective
      (SemiSimplexCategory.homEquiv j.unop).injective, simplex.map_comp, Category.assoc]

private theorem underlying_restrict {m n : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) (E : Extension sq ⦋n⦌) :
    underlying sq (restrict sq j hj E) =
      (SSet.ihomToPullbackFiber sq : SSet.{0}).map j.op (underlying sq E) := by
  apply (timeEquiv sq ⦋m⦌).injective
  apply Subtype.ext
  change timeMap sq ⦋m⦌ (underlying sq (restrict sq j hj E)) = timeMap sq ⦋m⦌ _
  rw [underlying_timeMap, restrict_map, timeMap_map, underlying_timeMap,
    ← Category.assoc, prism_timeOperator, Category.assoc]

/-- Forgetting the enlargement is natural in every original injective time operator. -/
def forget : choices sq ⟶ inc.op ⋙ (SSet.ihomToPullbackFiber sq : SSet.{0}) where
  app _ := underlying sq
  naturality _ _ j := by
    funext E
    exact underlying_restrict sq (inc.map j.unop) (SemiSimplexCategory.homEquiv j.unop).injective E

private def asFace {m n : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) : ⦋m⦌ₛ ⟶ ⦋n⦌ₛ :=
  letI : Mono j := SimplexCategory.mono_iff_injective.mpr hj
  SemiSimplexCategory.homOfMono' j

private theorem asFace_map {m n : ℕ} (j : ⦋m⦌ₛ ⟶ ⦋n⦌ₛ) :
    asFace (inc.map j) (SemiSimplexCategory.homEquiv j).injective = j := by
  apply inc.map_injective
  exact SemiSimplexCategory.toSimplexCategory_map_homOfMono (inc.map j)

private theorem asFace_comp {l m n : ℕ} (a : ⦋l⦌ ⟶ ⦋m⦌) (j : ⦋m⦌ ⟶ ⦋n⦌)
    (ha : Function.Injective a.toOrderHom) (hj : Function.Injective j.toOrderHom) :
    asFace (a ≫ j) (hj.comp ha) = asFace a ha ≫ asFace j hj := by
  apply inc.map_injective
  simp [asFace]

private theorem proper_iff {m n : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌)
    (hj : Function.Injective j.toOrderHom) :
    (¬ Function.Surjective j.toOrderHom) ↔ m < n := by
  constructor
  · intro h
    have he := Fintype.card_le_of_injective j.toOrderHom hj
    simp only [SimplexCategory.len_mk, Fintype.card_fin] at he
    have hmn : m ≤ n := Nat.le_of_succ_le_succ he
    by_contra hn
    have hm : m = n := Nat.le_antisymm hmn (Nat.le_of_not_gt hn)
    subst n
    exact h (Finite.surjective_of_injective hj)
  · intro h hs
    have he := Fintype.card_le_of_surjective j.toOrderHom hs
    simp only [SimplexCategory.len_mk, Fintype.card_fin] at he
    exact (Nat.not_le_of_gt h) (Nat.le_of_succ_le_succ he)

/-- The exact forgetful map lifts full compatible boundaries above any original
normalization simplex. -/
theorem hasBoundaryLifting [Fibration p] : HasBoundaryLifting (forget sq) := by
  rintro ⟨n⟩ v face hface
  let faceAt {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom) : Extension sq ⦋m⦌ :=
    face.face (asFace j hj) ((proper_iff j hj).1 hn)
  have hcomp {l m : ℕ} (a : ⦋l⦌ ⟶ ⦋m⦌) (j : ⦋m⦌ ⟶ ⦋n⦌)
      (ha : Function.Injective a.toOrderHom) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom) :
      (faceAt (a ≫ j) (hj.comp ha) (fun he ↦ hn (Function.Surjective.of_comp he))).map =
        simplex.map (timeOperator c m a ha) ≫ (faceAt j hj hn).map := by
    have he := face.naturality (asFace a ha) (asFace j hj) ((proper_iff j hj).1 hn)
    have hm := congrArg Extension.map he
    change (face.face _ _).map =
      (restrict sq (inc.map (asFace a ha)) _ (faceAt j hj hn)).map at hm
    rw [restrict_map] at hm
    simpa only [faceAt, asFace_comp, asFace, SemiSimplexCategory.toSimplexCategory_map_homOfMono]
      using hm
  have hv {m : ℕ} (j : ⦋m⦌ ⟶ ⦋n⦌) (hj : Function.Injective j.toOrderHom)
      (hn : ¬ Function.Surjective j.toOrderHom) :
      underlying sq (faceAt j hj hn) = (SSet.ihomToPullbackFiber sq : SSet.{0}).map j.op v := by
    have he := hface (asFace j hj) ((proper_iff j hj).1 hn)
    change underlying sq (faceAt j hj hn) =
      (SSet.ihomToPullbackFiber sq : SSet.{0}).map (inc.map (asFace j hj)).op v at he
    simpa only [asFace, SemiSimplexCategory.toSimplexCategory_map_homOfMono] using he
  obtain ⟨E, hE, hB⟩ := fill_compatible_boundary c sq v @faceAt @hcomp @hv
  refine ⟨E, hE, ?_⟩
  rintro ⟨m⟩ j hn
  apply Extension.ext
  have hj := (SemiSimplexCategory.homEquiv j).injective
  change (restrict sq (inc.map j) hj E).map = _
  rw [restrict_map]
  have he := hB (inc.map j) hj ((proper_iff (inc.map j) hj).2 hn)
  simpa only [faceAt, asFace_map] using he

end
end DaggerModels.PartII.JTCommonCoefficientNormalization
