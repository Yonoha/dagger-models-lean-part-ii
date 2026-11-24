import DaggerModelsPartII.JTHigherGroupoidParameterPrism

/-!
# Vertex formulas for literal codiscrete parameter maps
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTCodiscreteParameterPairing

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective JTParameterContraction

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev iso (k : SimplexCategory) := parameterCodiscreteIso.app k

def coord (a : SimplexCategory) (q : SimplexCategoryᵒᵖ)
    (z : (J.obj a).obj q) (v : Fin (q.unop.len + 1)) : Fin (a.len + 1) :=
  (((iso a).hom.app q z).obj v).as

theorem hom_ext {X : SSet.{0}} {a : SimplexCategory}
    {f g : X ⟶ J.obj a}
    (H : ∀ q z v, coord a q (f.app q z) v = coord a q (g.app q z) v) : f = g := by
  apply (cancel_mono (iso a).hom).mp
  apply NatTrans.ext
  funext q z
  apply nerve.ext_of_isThin
  funext v
  exact Codiscrete.ext (H q z v)

theorem coord_map {a a' : SimplexCategory} (f : a ⟶ a') (q : SimplexCategoryᵒᵖ)
    (z : (J.obj a).obj q) (v : Fin (q.unop.len + 1)) :
    coord a' q ((J.map f).app q z) v = f.toOrderHom (coord a q z v) :=
  congrArg (fun w ↦ (w.obj v).as)
    (congrFun (NatTrans.congr_app (parameterCodiscreteIso.hom.naturality f) q) z)

theorem coord_vertex (a : SimplexCategory) (v : Fin (a.len + 1))
    (q : SimplexCategoryᵒᵖ) (z : (Δ[0] : SSet.{0}).obj q) (i : Fin (q.unop.len + 1)) :
    coord a q ((parameterVertex a v).app q z) i = v := by
  have H : parameterVertex a v ≫ (iso a).hom =
      mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ v) := by
    change (mapOfVertices (Δ[0] : SSet.{0}) (fun _ ↦ v) ≫ (iso a).inv) ≫ (iso a).hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app H q) z)

def pairBy {a t z : SimplexCategory}
    (f : Fin (a.len + 1) × Fin (t.len + 1) → Fin (z.len + 1)) :
    J.obj a ⊗ J.obj t ⟶ J.obj z :=
  mapOfVertices _ (fun w ↦ f (vertexLabels (iso a).hom w.1, vertexLabels (iso t).hom w.2)) ≫
    (iso z).inv

theorem coord_pairBy {a t z : SimplexCategory}
    (f : Fin (a.len + 1) × Fin (t.len + 1) → Fin (z.len + 1))
    (q : SimplexCategoryᵒᵖ) (w : (J.obj a ⊗ J.obj t).obj q) (v : Fin (q.unop.len + 1)) :
    coord z q ((pairBy f).app q w) v = f (coord a q w.1 v, coord t q w.2 v) := by
  let φ : (J.obj a ⊗ J.obj t).obj (op ⦋0⦌) → Fin (z.len + 1) :=
    fun s ↦ f (vertexLabels (iso a).hom s.1, vertexLabels (iso t).hom s.2)
  have H : pairBy f ≫ (iso z).hom = mapOfVertices _ φ := by
    unfold pairBy
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hv := congrArg (fun s ↦ (s.obj v).as) (congrFun (NatTrans.congr_app H q) w)
  change coord z q ((pairBy f).app q w) v = f
    (vertexLabels (iso a).hom ((J.obj a).map ((⦋0⦌ : SimplexCategory).const q.unop v).op w.1),
      vertexLabels (iso t).hom ((J.obj t).map ((⦋0⦌ : SimplexCategory).const q.unop v).op w.2)) at hv
  rw [vertexLabels_natural, vertexLabels_natural] at hv
  exact hv

end

end DaggerModels.PartII.JTCodiscreteParameterPairing
