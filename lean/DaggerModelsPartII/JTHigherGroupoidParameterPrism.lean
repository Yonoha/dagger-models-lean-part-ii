import DaggerModelsPartII.JTHigherInterleavedOperators
import DaggerModelsPartII.JTCylinderCEComparison
import DaggerModelsPartII.JTParameterContraction

/-!
# Higher prisms of the actual groupoid parameters
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTHigherGroupoidParameterPrism

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTHigherInterleavedParameter JTParameterContraction

noncomputable section

private abbrev J := parameter
private abbrev iso (k : SimplexCategory) := parameterCodiscreteIso.app k

private def coord (k : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (J.obj k).obj q) (i : Fin (q.unop.len + 1)) : Fin (k.len + 1) :=
  (((iso k).hom.app q z).obj i).as

private theorem parameter_hom_ext {X : SSet.{0}} {k : SimplexCategory}
    {f g : X ⟶ J.obj k}
    (h : ∀ q z i, coord k q (f.app q z) i = coord k q (g.app q z) i) : f = g := by
  apply (cancel_mono (iso k).hom).mp
  apply NatTrans.ext
  funext q z
  apply nerve.ext_of_isThin
  funext i
  exact Codiscrete.ext (h q z i)

private theorem coord_map {k l : SimplexCategory} (j : k ⟶ l)
    (q : SimplexCategoryᵒᵖ) (z : (J.obj k).obj q) (i : Fin (q.unop.len + 1)) :
    coord l q ((J.map j).app q z) i = j.toOrderHom (coord k q z i) := by
  have h : J.map j ≫ (iso l).hom = (iso k).hom ≫ codiscreteNerve.map (vertices.map j) :=
    parameterCodiscreteIso.hom.naturality j
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app h q) z)

private theorem coord_vertex (k : SimplexCategory) (a : Fin (k.len + 1))
    (q : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{0}).obj q) (i : Fin (q.unop.len + 1)) :
    coord k q ((parameterVertex k a).app q z) i = a := by
  have h : parameterVertex k a ≫ (iso k).hom =
      mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ a) := by
    change (mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ a) ≫ (iso k).inv) ≫
      (iso k).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app h q) z)

private def codiscretePrism (k n : SimplexCategory) :
    codiscreteNerve.obj (Fin (k.len + 1)) ⊗ codiscreteNerve.obj (Fin (n.len + 1)) ⟶
      codiscreteNerve.obj (Fin ((common k n).len + 1)) where
  app _ z := Codiscrete.functor
    (fun i ↦ vertexEquiv k n ((z.1.obj i).as, (z.2.obj i).as))
  naturality _ _ j := by
    funext z
    apply nerve.ext_of_isThin
    funext i
    rfl

/-- Pair actual groupoid parameters in every time degree. -/
def paired (k n : SimplexCategory) : J.obj k ⊗ J.obj n ⟶ J.obj (common k n) :=
  ((iso k).hom ⊗ₘ (iso n).hom) ≫ codiscretePrism k n ≫ (iso (common k n)).inv

private theorem coord_paired (k n : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (z : (J.obj k ⊗ J.obj n).obj q) (i : Fin (q.unop.len + 1)) :
    coord (common k n) q ((paired k n).app q z) i =
      vertexEquiv k n (coord k q z.1 i, coord n q z.2 i) := by
  have h : paired k n ≫ (iso (common k n)).hom =
      ((iso k).hom ⊗ₘ (iso n).hom) ≫ codiscretePrism k n := by
    unfold paired
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app h q) z)

/-- The fixed-time inclusion into the actual groupoid prism. -/
def timeSlice (X : SSet.{0}) (n : SimplexCategory) (t : Fin (n.len + 1)) : X ⟶ X ⊗ J.obj n :=
  lift (𝟙 X) (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex n t)

theorem timeSlice_natural {X Y : SSet.{0}} (f : X ⟶ Y)
    (n : SimplexCategory) (t : Fin (n.len + 1)) :
    timeSlice X n t ≫ (f ⊗ₘ 𝟙 (J.obj n)) = f ≫ timeSlice Y n t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc,
      Category.comp_id, Category.id_comp]
  · simp only [timeSlice, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
    have h : f ≫ SSet.stdSimplex.isTerminalObj₀.from Y =
        SSet.stdSimplex.isTerminalObj₀.from X := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc f, h]

theorem paired_slice (k n : SimplexCategory) (t : Fin (n.len + 1)) :
    timeSlice (J.obj k) n t ≫ paired k n = J.map (slice k n t) := by
  apply parameter_hom_ext
  intro q z i
  change coord (common k n) q ((paired k n).app q
    (z, (parameterVertex n t).app q (SSet.stdSimplex.isTerminalObj₀.from (J.obj k) |>.app q z))) i =
      coord (common k n) q ((J.map (slice k n t)).app q z) i
  rw [coord_paired, coord_vertex, coord_map]
  rfl

theorem paired_ret (k n : SimplexCategory) :
    paired k n ≫ J.map (ret k n) = fst (J.obj k) (J.obj n) := by
  apply parameter_hom_ext
  intro q z i
  change coord k q ((J.map (ret k n)).app q ((paired k n).app q z)) i = coord k q z.1 i
  rw [coord_map, coord_paired, ret_vertexEquiv]

theorem paired_vertex (k n : SimplexCategory) (a : Fin (k.len + 1)) :
    (parameterVertex k a ⊗ₘ 𝟙 (J.obj n)) ≫ paired k n =
      snd (Δ[0] : SSet.{0}) (J.obj n) ≫ J.map (vertical k n a) := by
  apply parameter_hom_ext
  intro q z i
  change coord (common k n) q
      ((paired k n).app q ((parameterVertex k a).app q z.1, z.2)) i =
    coord (common k n) q ((J.map (vertical k n a)).app q z.2) i
  rw [coord_paired, coord_vertex, coord_map]
  rfl

theorem paired_mapTime (k : SimplexCategory) {n m : SimplexCategory} (f : n ⟶ m) :
    paired k n ≫ J.map (mapTime k f) = (J.obj k ◁ J.map f) ≫ paired k m := by
  apply parameter_hom_ext
  intro q z i
  change coord (common k m) q ((J.map (mapTime k f)).app q ((paired k n).app q z)) i =
    coord (common k m) q ((paired k m).app q (z.1, (J.map f).app q z.2)) i
  rw [coord_map, coord_paired, coord_paired, coord_map, mapTime_vertexEquiv]

private theorem coord_simplexUnit (k : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (SSet.stdSimplex.{0}.obj k).obj q) (i : Fin (q.unop.len + 1)) :
    coord k q ((JTCylinderCEComparison.simplexUnit.app k).app q z) i =
      (SSet.stdSimplex.objEquiv z).toOrderHom i := rfl

/-- The ordinary coefficient prism and actual groupoid prism use the same
vertex pairs under the original free-groupoid unit. -/
theorem paired_simplexUnit (k n : SimplexCategory) :
    (JTCylinderCEComparison.simplexUnit.app k ⊗ₘ JTCylinderCEComparison.simplexUnit.app n) ≫
        paired k n =
      prism k n ≫ JTCylinderCEComparison.simplexUnit.app (common k n) := by
  apply parameter_hom_ext
  intro q z i
  induction k using SimplexCategory.rec with
  | _ k =>
    induction n using SimplexCategory.rec with
    | _ n =>
      induction q using Opposite.rec with | op q =>
        induction q using SimplexCategory.rec with | h d =>
          change coord _ _ ((paired ⦋k⦌ ⦋n⦌).app _
              ((JTCylinderCEComparison.simplexUnit.app ⦋k⦌).app _ z.1,
              (JTCylinderCEComparison.simplexUnit.app ⦋n⦌).app _ z.2)) i =
            coord _ _ ((JTCylinderCEComparison.simplexUnit.app (common ⦋k⦌ ⦋n⦌)).app _
              ((prism ⦋k⦌ ⦋n⦌).app _ z)) i
          rw [coord_paired, coord_simplexUnit, coord_simplexUnit, coord_simplexUnit]
          rfl

end

end DaggerModels.PartII.JTHigherGroupoidParameterPrism
