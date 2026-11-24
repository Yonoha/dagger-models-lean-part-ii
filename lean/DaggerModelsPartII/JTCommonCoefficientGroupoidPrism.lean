import DaggerModelsPartII.JTCommonCoefficientPrism
import DaggerModelsPartII.JTHigherGroupoidParameterPrism

/-!
# Pairing actual groupoid parameters over a common coefficient
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

namespace DaggerModels.PartII.JTCommonCoefficientParameter

open JTHigherInterleavedParameter (common)
open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective JTParameterContraction
open JTHigherGroupoidParameterPrism (timeSlice)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev iso (k : SimplexCategory) := parameterCodiscreteIso.app k

variable {k l b n m : SimplexCategory}

private def coord (k : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (J.obj k).obj q) (a : Fin (q.unop.len + 1)) : Fin (k.len + 1) :=
  (((iso k).hom.app q z).obj a).as

private theorem parameter_hom_ext {X : SSet.{0}} {k : SimplexCategory}
    {f g : X ⟶ J.obj k}
    (h : ∀ q z a, coord k q (f.app q z) a = coord k q (g.app q z) a) : f = g := by
  apply (cancel_mono (iso k).hom).mp
  apply NatTrans.ext
  funext q z
  apply nerve.ext_of_isThin
  funext a
  exact Codiscrete.ext (h q z a)

private theorem coord_map (f : k ⟶ l) (q : SimplexCategoryᵒᵖ)
    (z : (J.obj k).obj q) (a : Fin (q.unop.len + 1)) :
    coord l q ((J.map f).app q z) a = f.toOrderHom (coord k q z a) := by
  have h : J.map f ≫ (iso l).hom = (iso k).hom ≫ codiscreteNerve.map (vertices.map f) :=
    parameterCodiscreteIso.hom.naturality f
  exact congrArg (fun w ↦ (w.obj a).as) (congrFun (NatTrans.congr_app h q) z)

private theorem coord_vertex (k : SimplexCategory) (a : Fin (k.len + 1))
    (q : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{0}).obj q) (i : Fin (q.unop.len + 1)) :
    coord k q ((parameterVertex k a).app q z) i = a := by
  have h : parameterVertex k a ≫ (iso k).hom =
      mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ a) := by
    change (mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ a) ≫ (iso k).inv) ≫
      (iso k).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app h q) z)

/-- The codiscrete parameter map is determined by the same vertex
pairs as the ordinary prism. -/
def paired (c : k ⟶ b) (n : SimplexCategory) :
    J.obj k ⊗ J.obj n ⟶ J.obj (common k n) :=
  mapOfVertices _ (fun z ↦ vertexEquiv c n
    (vertexLabels (iso k).hom z.1, vertexLabels (iso n).hom z.2)) ≫
    (iso (common k n)).inv

private theorem coord_paired (c : k ⟶ b) (n : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (z : (J.obj k ⊗ J.obj n).obj q) (a : Fin (q.unop.len + 1)) :
    coord (common k n) q ((paired c n).app q z) a =
      vertexEquiv c n (coord k q z.1 a, coord n q z.2 a) := by
  let φ : (J.obj k ⊗ J.obj n).obj (op ⦋0⦌) → Fin ((common k n).len + 1) :=
    fun w ↦ vertexEquiv c n (vertexLabels (iso k).hom w.1, vertexLabels (iso n).hom w.2)
  have h : paired c n ≫ (iso (common k n)).hom = mapOfVertices _ φ := by
    unfold paired
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ht := congrArg (fun w ↦ (w.obj a).as) (congrFun (NatTrans.congr_app h q) z)
  change coord (common k n) q ((paired c n).app q z) a = vertexEquiv c n
    (vertexLabels (iso k).hom ((J.obj k).map ((⦋0⦌ : SimplexCategory).const q.unop a).op z.1),
      vertexLabels (iso n).hom ((J.obj n).map ((⦋0⦌ : SimplexCategory).const q.unop a).op z.2)) at ht
  rw [vertexLabels_natural, vertexLabels_natural] at ht
  exact ht

/-- The full pairing commutes with a coefficient operator over the
common base and with an injective time operator. -/
theorem paired_map {c : k ⟶ b} {d : l ⟶ b} (f : k ⟶ l) (hf : f ≫ d = c)
    (j : n ⟶ m) (hj : Function.Injective j.toOrderHom) :
    paired c n ≫ J.map (map f hf j hj) = (J.map f ⊗ₘ J.map j) ≫ paired d m := by
  apply parameter_hom_ext
  intro q z a
  change coord _ q ((J.map (map f hf j hj)).app q ((paired c n).app q z)) a =
    coord _ q ((paired d m).app q ((J.map f).app q z.1, (J.map j).app q z.2)) a
  rw [coord_map, coord_paired, coord_paired, coord_map, coord_map, map_vertexEquiv]

theorem paired_base (c : k ⟶ b) (n : SimplexCategory) :
    paired c n ≫ J.map (base c n) = fst (J.obj k) (J.obj n) ≫ J.map c := by
  apply parameter_hom_ext
  intro q z a
  change coord _ q ((J.map (base c n)).app q ((paired c n).app q z)) a =
    coord _ q ((J.map c).app q z.1) a
  rw [coord_map, coord_map, coord_paired, base_vertexEquiv]

theorem paired_slice (c : k ⟶ b) (n : SimplexCategory) (t : Fin (n.len + 1)) :
    timeSlice (J.obj k) n t ≫ paired c n = J.map (slice c n t) := by
  apply parameter_hom_ext
  intro q z a
  change coord _ q ((paired c n).app q (z, (parameterVertex n t).app q
      ((SSet.stdSimplex.isTerminalObj₀.from (J.obj k)).app q z))) a =
    coord _ q ((J.map (slice c n t)).app q z) a
  rw [coord_paired, coord_vertex, coord_map]
  rfl

theorem paired_vertex (c : k ⟶ b) (n : SimplexCategory) (x : Fin (k.len + 1)) :
    (parameterVertex k x ⊗ₘ 𝟙 (J.obj n)) ≫ paired c n =
      snd (Δ[0] : SSet.{0}) (J.obj n) ≫ J.map (vertical c n x) := by
  apply parameter_hom_ext
  intro q z a
  change coord _ q ((paired c n).app q ((parameterVertex k x).app q z.1, z.2)) a =
    coord _ q ((J.map (vertical c n x)).app q z.2) a
  rw [coord_paired, coord_vertex, coord_map]
  rfl

private theorem coord_simplexUnit (k : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (SSet.stdSimplex.{0}.obj k).obj q) (a : Fin (q.unop.len + 1)) :
    coord k q ((JTCylinderCEComparison.simplexUnit.app k).app q z) a =
      (SSet.stdSimplex.objEquiv z).toOrderHom a := rfl

theorem paired_simplexUnit (c : k ⟶ b) (n : SimplexCategory) :
    (JTCylinderCEComparison.simplexUnit.app k ⊗ₘ JTCylinderCEComparison.simplexUnit.app n) ≫
      paired c n = prism c n ≫ JTCylinderCEComparison.simplexUnit.app (common k n) := by
  apply parameter_hom_ext
  intro q z a
  cases k using SimplexCategory.rec with
  | _ k =>
    cases n using SimplexCategory.rec with
    | _ n =>
      cases q using Opposite.rec with | op q =>
        cases q using SimplexCategory.rec with | h d =>
          change coord _ _ ((paired c ⦋n⦌).app _
              ((JTCylinderCEComparison.simplexUnit.app ⦋k⦌).app _ z.1,
                (JTCylinderCEComparison.simplexUnit.app ⦋n⦌).app _ z.2)) a =
            coord _ _ ((JTCylinderCEComparison.simplexUnit.app (common ⦋k⦌ ⦋n⦌)).app _
              ((prism c ⦋n⦌).app _ z)) a
          rw [coord_paired, coord_simplexUnit, coord_simplexUnit, coord_simplexUnit, prism_apply]
          rfl

private theorem old_coord_paired (b n : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (z : (J.obj b ⊗ J.obj n).obj q) (a : Fin (q.unop.len + 1)) :
    coord (common b n) q ((JTHigherGroupoidParameterPrism.paired b n).app q z) a =
      JTHigherInterleavedParameter.vertexEquiv b n (coord b q z.1 a, coord n q z.2 a) := by
  let w : (codiscreteNerve.obj (Fin ((common b n).len + 1))).obj q :=
    Codiscrete.functor (fun i ↦ JTHigherInterleavedParameter.vertexEquiv b n
      (coord b q z.1 i, coord n q z.2 i))
  have h : (iso (common b n)).hom.app q ((iso (common b n)).inv.app q w) = w :=
    congrFun (NatTrans.congr_app (iso (common b n)).inv_hom_id q) w
  change (((iso (common b n)).hom.app q ((iso (common b n)).inv.app q w)).obj a).as = _
  rw [h]
  rfl

/-- An ordered comparison that retains the coordinate pairs compares
the entire actual groupoid prisms. -/
theorem paired_toInterleaved (c : k ⟶ b) (n : SimplexCategory)
    (h : common k n ⟶ common b n)
    (hh : ∀ x : Fin (k.len + 1) × Fin (n.len + 1),
      h.toOrderHom (vertexEquiv c n x) =
        JTHigherInterleavedParameter.vertexEquiv b n (c.toOrderHom x.1, x.2)) :
    paired c n ≫ J.map h =
      (J.map c ▷ J.obj n) ≫ JTHigherGroupoidParameterPrism.paired b n := by
  apply parameter_hom_ext
  intro q z a
  change coord _ q ((J.map h).app q ((paired c n).app q z)) a =
    coord _ q ((JTHigherGroupoidParameterPrism.paired b n).app q
      ((J.map c).app q z.1, z.2)) a
  rw [coord_map, coord_paired, old_coord_paired, coord_map, hh]

end

end DaggerModels.PartII.JTCommonCoefficientParameter
