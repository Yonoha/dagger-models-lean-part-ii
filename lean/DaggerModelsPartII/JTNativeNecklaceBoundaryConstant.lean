import ChosenNecklaceOrderMaps
import ChosenNecklaceWedgeMaps

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeNecklaceBoundaryConstant

noncomputable section

private theorem pointAt_injective {T : NecklaceCode}
    {v w : Vertices.{0} T} (h : pointAt T v = pointAt T w) : v = w := by
  have h' := congrArg (fun p : Δ[0] ⟶ T.toSSet ↦
    T.verticesEquiv (SSet.yonedaEquiv p)) h
  simpa only [pointAt_vertex, Equiv.apply_symm_apply] using h'

theorem constant_of_last_first {A T : NecklaceCode}
    (f : toSSet.{0} A ⟶ toSSet.{0} T)
    (h : pointAt A (ULift.up (Fin.last A.len)) ≫ f = pointAt T (ULift.up 0)) :
    f = SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ pointAt T (ULift.up 0) := by
  have hlast : orderMap f (Fin.last A.len) = 0 := by
    rw [pointAt_comp] at h
    exact congrArg ULift.down (pointAt_injective h)
  apply hom_ext_vertices
  funext v
  have hv : orderMap f v.down = 0 := by
    apply le_antisymm
    · simpa only [hlast] using (orderMap f).monotone (Fin.le_last v.down)
    · exact Fin.zero_le _
  have hp : pointAt A v ≫ f = pointAt T (ULift.up 0) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact hv
  have ht : pointAt A v ≫ SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
      𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hp' : pointAt A v ≫
      (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ pointAt T (ULift.up 0)) =
      pointAt T (ULift.up 0) := by
    rw [← Category.assoc, ht, Category.id_comp]
  rw [pointAt_comp] at hp hp'
  exact pointAt_injective (hp.trans hp'.symm)

theorem constant_of_first_last {A T : NecklaceCode}
    (f : toSSet.{0} A ⟶ toSSet.{0} T)
    (h : pointAt A (ULift.up 0) ≫ f =
      pointAt T (ULift.up (Fin.last T.len))) :
    f = SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
      pointAt T (ULift.up (Fin.last T.len)) := by
  have hfirst : orderMap f 0 = Fin.last T.len := by
    rw [pointAt_comp] at h
    exact congrArg ULift.down (pointAt_injective h)
  apply hom_ext_vertices
  funext v
  have hv : orderMap f v.down = Fin.last T.len := by
    apply le_antisymm
    · exact Fin.le_last _
    · simpa only [hfirst] using (orderMap f).monotone (Fin.zero_le _)
  have hp : pointAt A v ≫ f = pointAt T (ULift.up (Fin.last T.len)) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact hv
  have ht : pointAt A v ≫ SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
      𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hp' : pointAt A v ≫
      (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt T (ULift.up (Fin.last T.len))) =
      pointAt T (ULift.up (Fin.last T.len)) := by
    rw [← Category.assoc, ht, Category.id_comp]
  rw [pointAt_comp] at hp hp'
  exact pointAt_injective (hp.trans hp'.symm)

end

end DaggerModels.PartII.JTNativeNecklaceBoundaryConstant
