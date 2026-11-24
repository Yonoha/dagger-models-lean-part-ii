import OrdinarySegalHorizontalCotensorPoint
import Mathlib.CategoryTheory.Functor.Currying

/-!
# The literal diagonal of the horizontal walking-groupoid cotensor

This constructs the diagram underlying Rezk's precompletion formula. The
parameter is the existing `GroupoidSimplex.parameter`, and the unit is the
constant horizontal map in every parameter and simplex degree. This module
asserts no Segal, completeness, fibrancy, or weak-equivalence property.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalPrecompletion

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (constantSection)

noncomputable section

/-- Contravariance in the exact horizontal simplicial-set parameter. -/
def parameterCotensor (W : Space) : SSet.{0}ᵒᵖ ⥤ Space where
  obj K := cotensor K.unop W
  map f := pre f.unop W
  map_id K := by
    change pre (𝟙 K.unop) W = 𝟙 (cotensor K.unop W)
    exact OrdinarySegalHorizontalCotensor.pre_id K.unop W
  map_comp f g := by
    simpa only [unop_comp] using
      OrdinarySegalHorizontalCotensor.pre_comp g.unop f.unop W

/-- The outer simplicial diagram takes the actual groupoid simplex `E(n)`
as its cotensor parameter, retaining the full inner simplicial space. -/
def resolution (W : Space) : SimplexCategoryᵒᵖ ⥤ Space :=
  GroupoidSimplex.parameter.op ⋙ parameterCotensor W

/-- A constant horizontal map remains constant after contravariant
precomposition by any map of the original parameter. -/
theorem constantSection_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    constantSection L W ≫ pre f W = constantSection K W := by
  rw [constantSection, constantSection, OrdinarySegalHorizontalCotensor.constantMap,
    OrdinarySegalHorizontalCotensor.constantMap, Category.assoc,
    ← OrdinarySegalHorizontalCotensor.pre_comp]
  have h : f ≫ SSet.stdSimplex.isTerminalObj₀.from L =
      SSet.stdSimplex.isTerminalObj₀.from K :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h]

/-- The original simplicial space maps into every outer resolution stage,
with naturality in all groupoid-simplex operators. -/
def resolutionUnit (W : Space) :
    (Functor.const SimplexCategoryᵒᵖ).obj W ⟶ resolution W where
  app n := constantSection (GroupoidSimplex.parameter.obj n.unop) W
  naturality := by
    intro n m θ
    change constantSection (GroupoidSimplex.parameter.obj n.unop) W ≫
        pre (GroupoidSimplex.parameter.map θ.unop) W =
      𝟙 W ≫ constantSection (GroupoidSimplex.parameter.obj m.unop) W
    rw [Category.id_comp]
    exact constantSection_pre (GroupoidSimplex.parameter.map θ.unop) W

/-- The literal two-index resolution before taking its diagonal. -/
def bisimplicialResolution (W : Space) :
    SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ SSet.{0} :=
  Functor.uncurry.obj (resolution W)

/-- Restrict both independent indices of the original resolution to the
same simplex degree. This is only the precompletion object. -/
def precompletion (W : Space) : Space :=
  Functor.diag SimplexCategoryᵒᵖ ⋙ bisimplicialResolution W

/-- The diagonal unit uses the literal constant section of `W` at `E(n)`.
Its naturality combines outer parameter naturality and inner simplex
naturality, rather than replacing either index. -/
def unit (W : Space) : W ⟶ precompletion W where
  app n := (constantSection (GroupoidSimplex.parameter.obj n.unop) W).app n
  naturality := by
    intro n m θ
    let K := GroupoidSimplex.parameter.obj m.unop
    let L := GroupoidSimplex.parameter.obj n.unop
    let f : K ⟶ L := GroupoidSimplex.parameter.map θ.unop
    let cK := constantSection K W
    let cL := constantSection L W
    change W.map θ ≫ cK.app m =
      (cL.app n ≫ (pre f W).app n) ≫ (cotensor K W).map θ
    have h : cL.app n ≫ (pre f W).app n = cK.app n := by
      change (cL ≫ pre f W).app n = cK.app n
      rw [constantSection_pre]
    rw [h]
    exact cK.naturality θ

/-- The unit's component retains the exact constant-section map at every
original simplex degree. -/
theorem unit_app (W : Space) (n : SimplexCategoryᵒᵖ) :
    (unit W).app n =
      (constantSection (GroupoidSimplex.parameter.obj n.unop) W).app n := rfl

#print axioms parameterCotensor
#print axioms resolution
#print axioms constantSection_pre
#print axioms resolutionUnit
#print axioms bisimplicialResolution
#print axioms precompletion
#print axioms unit
#print axioms unit_app

end

end DaggerModels.PartII.OrdinarySegalPrecompletion
