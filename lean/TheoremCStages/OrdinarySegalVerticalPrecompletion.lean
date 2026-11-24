import OrdinarySegalPrecompletion
import DaggerModelsPartII.JTParameterZero
import NativeBisimplicialDiagonal

/-!
# Vertical diagonal of the original groupoid-simplex cotensor resolution

At horizontal degree `n` and vertical simplex degree `q`, the parameter is
`E[q]`. This is the index order of Rezk's precompletion construction.
The older `OrdinarySegalPrecompletion.precompletion` instead uses `E[n]`.
No Segal, fibrancy, completeness, or weak-equivalence property is asserted.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletion

open OrdinaryCSSLocalization (Space)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open OrdinarySegalHorizontalCotensorPoint (constantSection pointIso)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

/-- The vertical diagonal keeps horizontal degree fixed while the outer
groupoid-simplex parameter and the inner simplex degree both vary with `q`. -/
def precompletion (W : Space) : Space :=
  (OrdinarySegalPrecompletion.resolution W).flip ⋙ diagonalFunctor

/-- The diagonal of the constant vertical resolution is the original space. -/
def constantDiagonalIso (W : Space) :
    (((Functor.const SimplexCategoryᵒᵖ).obj W).flip ⋙ diagonalFunctor) ≅ W :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro n m θ
    rfl)

/-- Flip the already checked resolution unit and take the native diagonal.
The source is identified with `W` by the constant-diagonal isomorphism. -/
def unit (W : Space) : W ⟶ precompletion W :=
  (constantDiagonalIso W).inv ≫
    Functor.whiskerRight
      ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ SSet.{0}).map
        (OrdinarySegalPrecompletion.resolutionUnit W)) diagonalFunctor

/-- The exact three-index value has horizontal degree `n`, outer parameter
`E[q]`, and inner simplex degree `q`. -/
theorem precompletion_obj_obj (W : Space) (n q : SimplexCategoryᵒᵖ) :
    ((precompletion W).obj n).obj q =
      ((cotensor (GroupoidSimplex.parameter.obj q.unop) W).obj n).obj q := rfl

/-- The unit at those same indices is the original constant section. -/
theorem unit_app_app (W : Space) (n q : SimplexCategoryᵒᵖ) :
    ((unit W).app n).app q =
      ((constantSection (GroupoidSimplex.parameter.obj q.unop) W).app n).app q := by
  rfl

/-- The exact vertex action keeps all three indices and the original point. -/
theorem unit_app_app_apply (W : Space) (n q : SimplexCategoryᵒᵖ)
    (x : (W.obj n).obj q) :
    ((unit W).app n).app q x =
      ((constantSection (GroupoidSimplex.parameter.obj q.unop) W).app n).app q x :=
  congrFun (unit_app_app W n q) x

/-- Horizontal naturality retains the original horizontal operator. -/
theorem unit_horizontal_naturality (W : Space) {n m : SimplexCategoryᵒᵖ}
    (θ : n ⟶ m) (q : SimplexCategoryᵒᵖ) :
    (W.map θ).app q ≫ ((unit W).app m).app q =
      ((unit W).app n).app q ≫ ((precompletion W).map θ).app q := by
  exact congrArg (fun f ↦ f.app q) ((unit W).naturality θ)

/-- Vertical naturality uses the same outer parameter operator and inner
simplicial operator, rather than holding either one fixed. -/
theorem unit_vertical_naturality (W : Space) (n : SimplexCategoryᵒᵖ)
    {q r : SimplexCategoryᵒᵖ} (θ : q ⟶ r) :
    (W.obj n).map θ ≫ ((unit W).app n).app r =
      ((unit W).app n).app q ≫ ((precompletion W).obj n).map θ :=
  ((unit W).app n).naturality θ

/-- The actual `E[0]` constant section is an isomorphism of whole spaces. -/
theorem constantSection_zero_isIso (W : Space) :
    IsIso (constantSection (GroupoidSimplex.parameter.obj ⦋0⦌) W) := by
  let q : GroupoidSimplex.parameter.obj ⦋0⦌ ⟶ (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.from (GroupoidSimplex.parameter.obj ⦋0⦌)
  have hq : q = JTParameterZero.parameterZeroIso.hom :=
    JTParameterZero.parameterZeroIso_hom.symm
  haveI : IsIso q := by
    rw [hq]
    infer_instance
  haveI : IsIso (pre q W) := by
    change IsIso ((OrdinarySegalPrecompletion.parameterCotensor W).map q.op)
    infer_instance
  change IsIso ((pointIso W).inv ≫ pre q W)
  infer_instance

/-- At vertical degree zero, the corrected unit is the `E[0]` constant
section evaluated vertically, hence an isomorphism of horizontal spaces. -/
theorem unit_verticalZero_isIso (W : Space) :
    IsIso (NatTrans.flipApp (unit W) (op ⦋0⦌)) := by
  have h : NatTrans.flipApp (unit W) (op ⦋0⦌) =
      NatTrans.flipApp
        (constantSection (GroupoidSimplex.parameter.obj ⦋0⦌) W) (op ⦋0⦌) := by
    apply NatTrans.ext
    funext n
    exact unit_app_app W n (op ⦋0⦌)
  rw [h]
  haveI := constantSection_zero_isIso W
  infer_instance

#print axioms precompletion
#print axioms unit
#print axioms unit_app_app
#print axioms unit_verticalZero_isIso

end

end DaggerModels.PartII.OrdinarySegalVerticalPrecompletion
