import ChosenNecklaceTargetJoints
import ChosenNecklaceWedgeFunctor
import ChosenNecklaceMapInclusion
import Mathlib.AlgebraicTopology.SimplicialSet.RegularEpi

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode

universe u

namespace DaggerModels.PartII.JTNativeFactorVertexFibers

noncomputable section

variable {S T Q : NecklaceCode}
variable (g : S ⟶ T) (r : S ⟶ Q)

private theorem cocone_eq_of_vertex_fibers
    (hv : ∀ x y : Fin (S.len + 1),
      orderMap g.map x = orderMap g.map y → orderMap r.map x = orderMap r.map y)
    {W : SSet.{u}} (a b : W ⟶ S.toSSet)
    (hg : a ≫ g.map = b ≫ g.map) : a ≫ r.map = b ≫ r.map := by
  apply (cancel_mono Q.inclusion).1
  apply NatTrans.ext
  funext q z
  obtain ⟨q⟩ := q
  induction q using SimplexCategory.rec with
  | _ d =>
    let q : SimplexCategoryᵒᵖ := op ⦋d⦌
    apply SSet.stdSimplex.ext
    intro i
    have hgi := congrArg
      (fun x : T.toSSet.obj q ↦ (T.inclusion.app q x) i)
      (congrFun (NatTrans.congr_app hg q) z)
    have hga := congrArg
      (fun x : (Δ[T.len] : SSet.{u}).obj q ↦ x i)
      (congrFun (NatTrans.congr_app (map_inclusion g.map) q) (a.app q z))
    have hgb := congrArg
      (fun x : (Δ[T.len] : SSet.{u}).obj q ↦ x i)
      (congrFun (NatTrans.congr_app (map_inclusion g.map) q) (b.app q z))
    have hgv : orderMap g.map ((S.inclusion.app q (a.app q z)) i) =
        orderMap g.map ((S.inclusion.app q (b.app q z)) i) := by
      calc
        _ = (T.inclusion.app q (g.map.app q (a.app q z))) i := hga.symm
        _ = (T.inclusion.app q (g.map.app q (b.app q z))) i := hgi
        _ = _ := hgb
    have hrv := hv _ _ hgv
    have hra := congrArg
      (fun x : (Δ[Q.len] : SSet.{u}).obj q ↦ x i)
      (congrFun (NatTrans.congr_app (map_inclusion r.map) q) (a.app q z))
    have hrb := congrArg
      (fun x : (Δ[Q.len] : SSet.{u}).obj q ↦ x i)
      (congrFun (NatTrans.congr_app (map_inclusion r.map) q) (b.app q z))
    calc
      _ = orderMap r.map ((S.inclusion.app q (a.app q z)) i) := hra
      _ = orderMap r.map ((S.inclusion.app q (b.app q z)) i) := hrv
      _ = _ := hrb.symm

theorem factor_iff_vertex_fibers [Epi g.map] :
    (∃ r' : T ⟶ Q, g ≫ r' = r) ↔
      (∀ x y : Fin (S.len + 1),
        orderMap g.map x = orderMap g.map y →
          orderMap r.map x = orderMap r.map y) := by
  constructor
  · rintro ⟨r', he⟩ x y hxy
    have hm : g.map ≫ r'.map = r.map := congrArg Hom.map he
    rw [← hm, orderMap_comp_apply, orderMap_comp_apply, hxy]
  · intro hv
    letI : IsRegularEpi g.map := IsRegularEpiCategory.regularEpiOfEpi g.map
    have he : IsRegularEpi.left g.map ≫ r.map =
        IsRegularEpi.right g.map ≫ r.map :=
      cocone_eq_of_vertex_fibers g r hv _ _ (IsRegularEpi.w g.map)
    let m : T.toSSet ⟶ Q.toSSet := IsRegularEpi.desc g.map r.map he
    have hm : g.map ≫ m = r.map := IsRegularEpi.fac g.map r.map he
    have hf : pointAt T (ULift.up 0) ≫ m = pointAt Q (ULift.up 0) := by
      rw [← pointAt_first_comp g, Category.assoc, hm, pointAt_first_comp r]
    have hl : pointAt T (ULift.up (Fin.last T.len)) ≫ m =
        pointAt Q (ULift.up (Fin.last Q.len)) := by
      rw [← pointAt_last_comp g, Category.assoc, hm, pointAt_last_comp r]
    let r' : T ⟶ Q := ⟨m, first_of_point m hf, last_of_point m hl⟩
    refine ⟨r', ?_⟩
    exact Hom.ext hm

end

end DaggerModels.PartII.JTNativeFactorVertexFibers
