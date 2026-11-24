import DaggerModelsPartII.JTRowGraphFiber
import DaggerModelsPartII.JTCommonCoefficientPrism
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# One fixed common coefficient base for all supported graphs over a raw simplex
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerSSetGluing

namespace DaggerModels.PartII.JTRowGraphCommonCenter

open OrdinaryJTRealization JTRowGraphFiber JTRowGraphCategory

noncomputable section

variable {W : BiPresheaf} {d : SimplexCategory}
variable (q : SSet.stdSimplex.{0}.obj d ⟶ OrdinaryJTRealization.realization.obj W)

private abbrev B := (center q).obj.degree

/-- The reduction of a supported graph into the one canonical coefficient base. -/
def baseAt (G : Fiber q) : Over (B q) :=
  Over.mk (((reductionAt q).app G).hom.operator)

/-- Naturality of reduction gives the exact commuting coefficient triangle. -/
def baseMap {G H : Fiber q} (u : G ⟶ H) : baseAt q G ⟶ baseAt q H :=
  Over.homMk ((supportAt q).map u).hom.operator (by
    have h := congrArg (fun a : (supportAt q).obj G ⟶ center q ↦ a.hom.operator)
      ((reductionAt q).naturality u)
    exact h)

/-- Supported coefficient presentations all lie over the same canonical base. -/
def diagram : Fiber q ⥤ Over (B q) where
  obj := baseAt q
  map := baseMap q
  map_id G := by
    apply Over.OverMorphism.ext
    exact congrArg (fun a : (supportAt q).obj G ⟶ (supportAt q).obj G ↦ a.hom.operator)
      ((supportAt q).map_id G)
  map_comp u v := by
    apply Over.OverMorphism.ext
    exact congrArg
      (fun a : (supportAt q).obj _ ⟶ (supportAt q).obj _ ↦ a.hom.operator)
      ((supportAt q).map_comp u v)

/-- The supported graph coefficient is the exact pullback of the center
coefficient along its arrow in the fixed common-base diagram. -/
theorem supported_coefficient (G : Fiber q) :
    ((JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)).map
        (((diagram q).obj G).hom.op) (center q).obj.coefficient =
      ((supportAt q).obj G).obj.coefficient :=
  ((reductionAt q).app G).hom.coefficient

/-- The same common-base arrow preserves the complete original graph parameter. -/
theorem supported_parameter (G : Fiber q) :
    ((supportAt q).obj G).obj.parameter ≫
        GroupoidSimplex.parameter.map ((diagram q).obj G).hom =
      (center q).obj.parameter :=
  ((reductionAt q).app G).hom.parameter

/-- The actual common-base coefficient and face-operator parameter over all
supported graphs and all semisimplicial time degrees. -/
def semisimplexParameter : (Fiber q × SemiSimplexCategory) ⥤ SimplexCategory :=
  (diagram q).prod (𝟭 SemiSimplexCategory) ⋙
    JTCommonCoefficientParameter.parameter (B q)

end

end DaggerModels.PartII.JTRowGraphCommonCenter
