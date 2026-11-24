import DaggerModelsPartII.JTPaddedTimeOperators
import DaggerModelsPartII.JTHomotopyTargetTimeResolution
import NativeWeaklyContractibleMaps

/-! A contractible time parameter with a specified edge between its added vertices.

The homotopy uses the original simplices of the input. Its ordinal operator
moves interior vertices to the first added vertex until the specified time
changes to one. Both added vertices and their whole edge stay fixed.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTFixedEdgePaddedTime

open JTPaddedTimeOperators

noncomputable section

private def slideOrder {n : SimplexCategory} (t : n ⟶ ⦋1⦌) :
    Fin (n.len + 1) →o Fin ((pad n).len + 1) where
  toFun i := if t.toOrderHom i = 0 then 0 else inside n i
  monotone' := by
    intro i j hij
    by_cases hi : t.toOrderHom i = 0
    · simp only [hi, if_true]
      exact Fin.zero_le _
    · have hj : t.toOrderHom j ≠ 0 := by
        intro h
        have e := t.toOrderHom.monotone hij
        rw [h] at e
        exact hi (le_antisymm e (Fin.zero_le _))
      simp only [hi, hj, if_false]
      exact (inside n).monotone hij

private def slide {n : SimplexCategory} (t : n ⟶ ⦋1⦌) : pad n ⟶ pad n :=
  extend (slideOrder t)

private theorem slide_inside {n : SimplexCategory} (t : n ⟶ ⦋1⦌) (i : Fin (n.len + 1)) :
    (slide t).toOrderHom (inside n i) = if t.toOrderHom i = 0 then 0 else inside n i :=
  extend_inside _ _

private theorem slide_edge {n : SimplexCategory} (t : n ⟶ ⦋1⦌) :
    edge n ≫ slide t = edge n := by
  apply SimplexCategory.Hom.ext_one_left
  · change (slide t).toOrderHom 0 = 0
    exact extend_first _
  · change (slide t).toOrderHom (Fin.last (pad n).len) = Fin.last (pad n).len
    exact extend_last _

private theorem slide_natural {m n : SimplexCategory} (f : m ⟶ n) (t : n ⟶ ⦋1⦌) :
    slide (f ≫ t) ≫ map f = map f ≫ slide t := by
  apply hom_ext (n := m)
  · change (map f).toOrderHom ((slide (f ≫ t)).toOrderHom 0) =
      (slide t).toOrderHom ((map f).toOrderHom 0)
    rw [show (slide (f ≫ t)).toOrderHom 0 = 0 from extend_first _, map_first]
    exact (extend_first _).symm
  · intro i
    change (map f).toOrderHom ((slide (f ≫ t)).toOrderHom (inside m i)) =
      (slide t).toOrderHom ((map f).toOrderHom (inside m i))
    rw [slide_inside, map_inside, slide_inside]
    change (map f).toOrderHom (if t.toOrderHom (f.toOrderHom i) = 0 then 0 else inside m i) = _
    split
    · rw [map_first]
    · rw [map_inside]
  · change (map f).toOrderHom ((slide (f ≫ t)).toOrderHom (Fin.last (pad m).len)) =
      (slide t).toOrderHom ((map f).toOrderHom (Fin.last (pad m).len))
    rw [show (slide (f ≫ t)).toOrderHom (Fin.last (pad m).len) =
      Fin.last (pad m).len from extend_last _, map_last]
    exact (extend_last _).symm

private theorem slide_zero (n : SimplexCategory) :
    slide (SimplexCategory.const n ⦋1⦌ 0) = collapse n ≫ edge n := by
  apply hom_ext (n := n)
  · change (slide (SimplexCategory.const n ⦋1⦌ 0)).toOrderHom 0 =
      (edge n).toOrderHom ((collapse n).toOrderHom 0)
    rw [show (collapse n).toOrderHom 0 = 0 from extend_first _]
    exact extend_first _
  · intro i
    change (slide (SimplexCategory.const n ⦋1⦌ 0)).toOrderHom (inside n i) =
      (edge n).toOrderHom ((collapse n).toOrderHom (inside n i))
    rw [slide_inside, SimplexCategory.const_apply]
    rw [show (collapse n).toOrderHom (inside n i) = 0 from extend_inside _ _]
    rfl
  · change (slide (SimplexCategory.const n ⦋1⦌ 0)).toOrderHom (Fin.last (pad n).len) =
      (edge n).toOrderHom ((collapse n).toOrderHom (Fin.last (pad n).len))
    rw [show (collapse n).toOrderHom (Fin.last (pad n).len) = Fin.last 1 from extend_last _]
    exact extend_last _

private theorem slide_one (n : SimplexCategory) :
    slide (SimplexCategory.const n ⦋1⦌ 1) = 𝟙 (pad n) := by
  apply hom_ext (n := n)
  · exact extend_first _
  · intro i
    rw [slide_inside, SimplexCategory.const_apply]
    rfl
  · exact extend_last _

variable (X : SSet.{0}) (e : X.obj (op ⦋1⦌))

private abbrev At (n : SimplexCategory) :=
  {a : X.obj (op (pad n)) // X.map (edge n).op a = e}

private theorem map_apply_comp {k l m : SimplexCategory} (f : k ⟶ l) (g : l ⟶ m)
    (a : X.obj (op m)) :
    X.map f.op (X.map g.op a) = X.map (f ≫ g).op a :=
  (FunctorToTypes.map_comp_apply X g.op f.op a).symm

private def restrict {m n : SimplexCategory} (f : pad m ⟶ pad n) (h : edge m ≫ f = edge n)
    (a : At X e n) : At X e m :=
  ⟨X.map f.op a.val, by
    rw [map_apply_comp, h]
    exact a.property⟩

/-- All padded time simplices carrying the same entire edge at their two added vertices. -/
def space : SSet.{0} where
  obj n := At X e n.unop
  map f := restrict X e (map f.unop) (edge_map f.unop)
  map_id n := by
    funext a
    apply Subtype.ext
    change X.map (map (𝟙 n.unop)).op a.val = a.val
    rw [show map (𝟙 n.unop) = 𝟙 (pad n.unop) from functor.map_id n.unop, op_id]
    exact FunctorToTypes.map_id_apply X a.val
  map_comp f g := by
    funext a
    apply Subtype.ext
    change X.map (map (g.unop ≫ f.unop)).op a.val =
      X.map (map g.unop).op (X.map (map f.unop).op a.val)
    rw [map_apply_comp]
    have h : map (g.unop ≫ f.unop) = map g.unop ≫ map f.unop :=
      functor.map_comp g.unop f.unop
    rw [h]

private def centerAt (n : SimplexCategory) : At X e n :=
  ⟨X.map (collapse n).op e, by rw [map_apply_comp, edge_collapse, op_id, FunctorToTypes.map_id_apply]⟩

/-- The padded zero-simplex with its only interior vertex at the first endpoint of the edge. -/
def center : (space X e).obj (op ⦋0⦌) :=
  centerAt X e ⦋0⦌

private theorem center_const (n : SimplexCategoryᵒᵖ) (a : (space X e).obj n) :
    (SSet.const (center X e) : space X e ⟶ space X e).app n a = centerAt X e n.unop := by
  apply Subtype.ext
  change X.map (map (SimplexCategory.const n.unop ⦋0⦌ 0)).op
      (X.map (collapse ⦋0⦌).op e) = X.map (collapse n.unop).op e
  rw [map_apply_comp, map_collapse]

private def homotopyMap : space X e ⊗ Δ[1] ⟶ space X e where
  app _ u := restrict X e (slide (SSet.stdSimplex.objEquiv u.2))
    (slide_edge (SSet.stdSimplex.objEquiv u.2)) u.1
  naturality {n m} f := by
    funext u
    apply Subtype.ext
    let t := SSet.stdSimplex.objEquiv u.2
    change X.map (slide (f.unop ≫ t)).op (X.map (map f.unop).op u.1.val) =
      X.map (map f.unop).op (X.map (slide t).op u.1.val)
    rw [map_apply_comp, map_apply_comp, slide_natural]

/-- A contraction through the original padded simplices, preserving the prescribed edge. -/
def contraction : SSet.Homotopy (SSet.const (center X e)) (𝟙 (space X e)) :=
  SSet.Homotopy.mk (homotopyMap X e)
    (by
      apply NatTrans.ext
      funext n a
      rw [center_const X e n a]
      apply Subtype.ext
      change X.map (slide (SimplexCategory.const n.unop ⦋1⦌ 0)).op a.val =
        X.map (collapse n.unop).op e
      rw [slide_zero, ← map_apply_comp, a.property])
    (by
      apply NatTrans.ext
      funext n a
      apply Subtype.ext
      change X.map (slide (SimplexCategory.const n.unop ⦋1⦌ 1)).op a.val = a.val
      rw [slide_one, op_id, FunctorToTypes.map_id_apply])

/-- The specified edge gives weak contractibility without a Kan hypothesis on the input. -/
theorem point_GW : GW (pointMap (space X e)) := by
  have h : WeakEquivalence (SSet.const (center X e) : space X e ⟶ space X e) :=
    (DaggerNativeRawHomotopyWeakInvariance.weakEquivalence_iff_homotopy
      (contraction X e)).mpr inferInstance
  have hc := DaggerNativeWeaklyContractibleMaps.collapse_weak_of_const (center X e) h
  have he : DaggerNativeWeaklyContractibleMaps.collapse (space X e) ≫
      (SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal).hom =
        pointMap (space X e) := pointIsTerminal.hom_ext _ _
  rw [← he, ← weakEquivalence_iff_GW]
  infer_instance

end

end DaggerModels.PartII.JTFixedEdgePaddedTime
