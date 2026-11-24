import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# Interpolation of finite families of groupoid-parameter maps
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTGraphParameterInterpolation

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTCodiscreteParameterPairing JTParameterContraction

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev iso (k : SimplexCategory) := parameterCodiscreteIso.app k

/-- A vertex-indexed family over an arbitrary simplicial time parameter. -/
def interpolateBy {X Y : SSet.{0}} {k : SimplexCategory}
    (s : Y.obj (op ⦋0⦌) → (X ⟶ J.obj k)) :
    X ⊗ Y ⟶ J.obj k :=
  mapOfVertices _ (fun z ↦ vertexLabels (s z.2 ≫ (iso k).hom) z.1) ≫
    (iso k).inv

theorem coord_interpolateBy {X Y : SSet.{0}} {k : SimplexCategory}
    (s : Y.obj (op ⦋0⦌) → (X ⟶ J.obj k))
    (q : SimplexCategoryᵒᵖ) (z : (X ⊗ Y).obj q)
    (v : Fin (q.unop.len + 1)) :
    coord k q ((interpolateBy s).app q z) v =
      coord k q ((s (Y.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z.2)).app q z.1) v := by
  let φ : (X ⊗ Y).obj (op ⦋0⦌) → Fin (k.len + 1) :=
    fun w ↦ vertexLabels (s w.2 ≫ (iso k).hom) w.1
  have H : interpolateBy s ≫ (iso k).hom = mapOfVertices _ φ := by
    unfold interpolateBy
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun w ↦ (w.obj v).as) (congrFun (NatTrans.congr_app H q) z)
  change coord k q ((interpolateBy s).app q z) v =
    vertexLabels
      (s (Y.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z.2) ≫
        (iso k).hom)
      (X.map ((⦋0⦌ : SimplexCategory).const q.unop v).op z.1) at hv
  rw [vertexLabels_natural] at hv
  exact hv

theorem slice_interpolateBy {X Y : SSet.{0}} {k : SimplexCategory}
    (s : Y.obj (op ⦋0⦌) → (X ⟶ J.obj k))
    (y : Y.obj (op ⦋0⦌)) :
    CartesianMonoidalCategory.lift (𝟙 X)
      (SSet.stdSimplex.isTerminalObj₀.from X ≫ SSet.yonedaEquiv.symm y) ≫
        interpolateBy s = s y := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  let t : (Δ[0] : SSet.{0}).obj q :=
    (SSet.stdSimplex.isTerminalObj₀.from X).app q z
  have hy : Y.map ((⦋0⦌ : SimplexCategory).const q.unop v).op
      ((SSet.yonedaEquiv.symm y).app q t) = y := by
    calc
      _ = (SSet.yonedaEquiv.symm y).app (op ⦋0⦌)
            ((Δ[0] : SSet.{0}).map
              ((⦋0⦌ : SimplexCategory).const q.unop v).op t) :=
        (congrFun ((SSet.yonedaEquiv.symm y).naturality
          ((⦋0⦌ : SimplexCategory).const q.unop v).op) t).symm
      _ = (SSet.yonedaEquiv.symm y).app (op ⦋0⦌)
            (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) := by
        have ht : (Δ[0] : SSet.{0}).map
            ((⦋0⦌ : SimplexCategory).const q.unop v).op t =
              SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})) :=
          Subsingleton.elim _ _
        rw [ht]
      _ = y := by
        rw [← SSet.yonedaEquiv_comp, Category.id_comp,
          Equiv.apply_symm_apply]
  change coord k q ((interpolateBy s).app q
    (z, (SSet.yonedaEquiv.symm y).app q t)) v =
      coord k q ((s y).app q z) v
  rw [coord_interpolateBy, hy]

/-- Interpolate a finite family of parameter maps by selecting its member
at each vertex of the parameter simplex. -/
def interpolate {X : SSet.{0}} {k n : SimplexCategory}
    (s : Fin (n.len + 1) → (X ⟶ J.obj k)) :
    X ⊗ J.obj n ⟶ J.obj k :=
  interpolateBy (fun y ↦ s (coord n (op ⦋0⦌) y 0))

theorem coord_interpolate {X : SSet.{0}} {k n : SimplexCategory}
    (s : Fin (n.len + 1) → (X ⟶ J.obj k))
    (q : SimplexCategoryᵒᵖ) (z : (X ⊗ J.obj n).obj q)
    (v : Fin (q.unop.len + 1)) :
    coord k q ((interpolate s).app q z) v =
      coord k q ((s (coord n q z.2 v)).app q z.1) v := by
  rw [interpolate, coord_interpolateBy]
  have h : coord n (op ⦋0⦌)
      ((J.obj n).map ((⦋0⦌ : SimplexCategory).const q.unop v).op z.2) 0 =
      coord n q z.2 v :=
    vertexLabels_natural (iso n).hom q z.2 v
  rw [h]

theorem slice_interpolate {X : SSet.{0}} {k n : SimplexCategory}
    (s : Fin (n.len + 1) → (X ⟶ J.obj k))
    (i : Fin (n.len + 1)) :
    CartesianMonoidalCategory.lift (𝟙 X)
      (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex n i) ≫
        interpolate s = s i := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z v
  change coord k q ((interpolate s).app q
    (z, (parameterVertex n i).app q
      (SSet.stdSimplex.isTerminalObj₀.from X |>.app q z))) v =
    coord k q ((s i).app q z) v
  rw [coord_interpolate, coord_vertex]

end

end DaggerModels.PartII.JTGraphParameterInterpolation
