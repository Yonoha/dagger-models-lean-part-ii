import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.JTParameterContraction

/-!
# The actual groupoid parameter prism

The existing codiscrete comparison transports the interleaved vertex
assignment to the actual groupoid parameter. This gives a map on the
whole prism, with its two slices and duplicate-vertex edges.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTGroupoidParameterPrism

open GroupoidSimplex DaggerOriginalCodiscreteNerveInjective
open JTInterleavedParameter JTParameterContraction

noncomputable section

private abbrev J := parameter
private abbrev I := J.obj ⦋1⦌
private abbrev K := common
private abbrev iso (k : SimplexCategory) := parameterCodiscreteIso.app k

private def interleaved (k : SimplexCategory) (a : Fin (k.len + 1)) (t : Fin 2) :
    Fin ((K k).len + 1) :=
  ⟨2 * a.val + t.val, by
    have ha := a.isLt
    have ht := t.isLt
    change 2 * a.val + t.val < 2 * k.len + 1 + 1
    omega⟩

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

private def codiscretePrism (k : SimplexCategory) :
    codiscreteNerve.obj (Fin (k.len + 1)) ⊗ codiscreteNerve.obj (Fin 2) ⟶
      codiscreteNerve.obj (Fin ((K k).len + 1)) where
  app _ z := Codiscrete.functor
    (fun i ↦ interleaved k (z.1.obj i).as (z.2.obj i).as)
  naturality _ _ j := by
    funext z
    apply nerve.ext_of_isThin
    funext i
    rfl

/-- Pair a groupoid-parameter simplex with a groupoid time simplex. -/
def paired (k : SimplexCategory) : J.obj k ⊗ I ⟶ J.obj (K k) :=
  ((iso k).hom ⊗ₘ (iso ⦋1⦌).hom) ≫ codiscretePrism k ≫ (iso (K k)).inv

private theorem coord_paired (k : SimplexCategory)
    (q : SimplexCategoryᵒᵖ) (z : (J.obj k ⊗ I).obj q) (i : Fin (q.unop.len + 1)) :
    coord (K k) q ((paired k).app q z) i =
      interleaved k (coord k q z.1 i) (coord ⦋1⦌ q z.2 i) := by
  have h : paired k ≫ (iso (K k)).hom =
      ((iso k).hom ⊗ₘ (iso ⦋1⦌).hom) ≫ codiscretePrism k := by
    unfold paired
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun w ↦ (w.obj i).as) (congrFun (NatTrans.congr_app h q) z)

/-- The actual fixed-time inclusion into a groupoid prism. -/
def timeSlice (X : SSet.{0}) (t : Fin 2) : X ⟶ X ⊗ I :=
  lift (𝟙 X) (SSet.stdSimplex.isTerminalObj₀.from X ≫ parameterVertex ⦋1⦌ t)

theorem timeSlice_fst (X : SSet.{0}) (t : Fin 2) :
    timeSlice X t ≫ fst X I = 𝟙 X :=
  lift_fst _ _

theorem timeSlice_natural {X Y : SSet.{0}} (f : X ⟶ Y) (t : Fin 2) :
    timeSlice X t ≫ (f ⊗ₘ 𝟙 I) = f ≫ timeSlice Y t := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [timeSlice, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc,
      Category.comp_id, Category.id_comp]
  · simp only [timeSlice, Category.assoc, tensorHom_snd, lift_snd,
      Category.comp_id]
    have h : f ≫ SSet.stdSimplex.isTerminalObj₀.from Y =
        SSet.stdSimplex.isTerminalObj₀.from X := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc f, h]

/-- Time slices are the actual groupoid maps of the two ordinal inclusions. -/
theorem paired_slice (k : SimplexCategory) (t : Fin 2) :
    timeSlice (J.obj k) t ≫ paired k = J.map (slice k t) := by
  apply parameter_hom_ext
  intro q z i
  change coord (K k) q ((paired k).app q
    (z, (parameterVertex ⦋1⦌ t).app q (SSet.stdSimplex.isTerminalObj₀.from (J.obj k) |>.app q z))) i =
      coord (K k) q ((J.map (slice k t)).app q z) i
  rw [coord_paired, coord_vertex, coord_map]
  apply Fin.ext
  exact (slice_apply k t _).symm

/-- Forgetting time gives the original parameter on the whole prism. -/
theorem paired_ret (k : SimplexCategory) :
    paired k ≫ J.map (ret k) = fst (J.obj k) I := by
  apply parameter_hom_ext
  intro q z i
  change coord k q ((J.map (ret k)).app q ((paired k).app q z)) i = coord k q z.1 i
  rw [coord_map, coord_paired]
  apply Fin.ext
  rw [ret_apply]
  change (2 * (coord k q z.1 i).val + (coord ⦋1⦌ q z.2 i).val) / 2 =
    (coord k q z.1 i).val
  have ht : (coord ⦋1⦌ q z.2 i).val < 2 := (coord ⦋1⦌ q z.2 i).isLt
  omega

/-- Over a fixed original vertex, the whole time prism uses its
duplicate edge in the larger parameter. -/
theorem paired_vertex (k : SimplexCategory) (a : Fin (k.len + 1)) :
    (parameterVertex k a ⊗ₘ 𝟙 I) ≫ paired k =
      snd (Δ[0] : SSet.{0}) I ≫ J.map (edge k a) := by
  apply parameter_hom_ext
  intro q z i
  change coord (K k) q ((paired k).app q ((parameterVertex k a).app q z.1, z.2)) i =
    coord (K k) q ((J.map (edge k a)).app q z.2) i
  rw [coord_paired, coord_vertex, coord_map]
  apply Fin.ext
  exact (edge_apply k a _).symm

end

end DaggerModels.PartII.JTGroupoidParameterPrism
