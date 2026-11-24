import DaggerModelsPartII.JTMixedGraphHorizontalTraversal
import DaggerModelsPartII.JTPaddedTimeOperators

/-!
# The padded time simplex as one native bead

The two new exterior vertices are retained by every map of the original
simplex category.  The native one-bead model has the same simplicial set
as the padded standard simplex, naturally in the original time parameter.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTPaddedSingleNecklaceDiagram

noncomputable section

private abbrev pad := JTPaddedTimeOperators.pad
private abbrev timeMap {d e : SimplexCategory} (f : d ⟶ e) : pad d ⟶ pad e :=
  JTPaddedTimeOperators.map f
private abbrev std := SSet.stdSimplex.{0}

/-- A padded ordinal is represented by one native bead. -/
def code : SimplexCategory ⥤ NecklaceCode where
  obj d := single (pad d).len
  map {d e} f := JTMixedGraphHorizontalTraversal.singleOperator (timeMap f)
    (JTPaddedTimeOperators.map_first f) (JTPaddedTimeOperators.map_last f)
  map_id d := by
    apply Hom.ext
    change (singleIso (pad d).len).hom ≫ std.map (timeMap (𝟙 d)) ≫
      (singleIso (pad d).len).inv = 𝟙 _
    rw [show timeMap (𝟙 d) = 𝟙 (pad d) from JTPaddedTimeOperators.functor.map_id d]
    simp
  map_comp {d e f} u v := by
    apply Hom.ext
    change (singleIso (pad d).len).hom ≫ std.map (timeMap (u ≫ v)) ≫
      (singleIso (pad f).len).inv =
      ((singleIso (pad d).len).hom ≫ std.map (timeMap u) ≫
        (singleIso (pad e).len).inv) ≫
      ((singleIso (pad e).len).hom ≫ std.map (timeMap v) ≫
        (singleIso (pad f).len).inv)
    rw [show timeMap (u ≫ v) = timeMap u ≫ timeMap v from
      JTPaddedTimeOperators.functor.map_comp u v]
    simp only [std.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- The actual inner ordinal chart commutes with every padded native operator. -/
theorem singleIso_naturality {d e : SimplexCategory} (f : d ⟶ e) :
    ((code.map f).map : (code.obj d).toSSet ⟶ (code.obj e).toSSet) ≫
      (singleIso (pad e).len).hom =
      (singleIso (pad d).len).hom ≫ std.map (timeMap f) := by
  change ((singleIso (pad d).len).hom ≫ std.map (timeMap f) ≫
    (singleIso (pad e).len).inv) ≫ (singleIso (pad e).len).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Natural identification of the native bead with the padded standard simplex. -/
def simplicialIso : code ⋙ NecklaceCode.simplicialFunctor ≅
    JTPaddedTimeOperators.functor ⋙ std :=
  NatIso.ofComponents (fun d ↦ singleIso (pad d).len) (by
    intro d e f
    exact singleIso_naturality f)

end

end DaggerModels.PartII.JTPaddedSingleNecklaceDiagram
