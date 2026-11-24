import ChosenNecklaceWedgeFunctor

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerChosenRigidificationNecklace.NecklaceCode

universe u

noncomputable section

variable (L T R : NecklaceCode)

/-- The canonical map from a necklace to the terminal simplex. -/
def outerTerminal (A : NecklaceCode) :
    toSSet.{u} A ⟶ (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.from _

private theorem point_terminal (A : NecklaceCode) (v : Vertices.{u} A) :
    pointAt A v ≫ outerTerminal A = 𝟙 (Δ[0] : SSet.{u}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem collapse_joint_left :
    pointAt L (ULift.up (Fin.last L.len)) ≫
      (outerTerminal L ≫ pointAt T (ULift.up 0)) =
      pointAt T (ULift.up 0) ≫ (𝟙 (toSSet.{u} T)) := by
  rw [← Category.assoc, point_terminal, Category.id_comp, Category.comp_id]

private theorem collapse_joint_right :
    pointAt T (ULift.up (Fin.last T.len)) ≫ (𝟙 (toSSet.{u} T)) =
      pointAt R (ULift.up 0) ≫
        (outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len))) := by
  rw [Category.comp_id, ← Category.assoc, point_terminal, Category.id_comp]

private def collapseMap :
    toSSet.{u} (wedge L (wedge T R)) ⟶ toSSet.{u} T :=
  tripleRightDesc L T R
    (outerTerminal L ≫ pointAt T (ULift.up 0))
    (𝟙 _)
    (outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)))
    (collapse_joint_left L T)
    (collapse_joint_right T R)

/-- Collapse both outer necklaces to the respective endpoints of the middle necklace. -/
def collapse : Hom.{u} (wedge L (wedge T R)) T where
  map := collapseMap L T R
  first := first_of_point _ (by
    rw [← pointAt_first_left L (wedge T R), Category.assoc]
    change pointAt L (ULift.up 0) ≫ tripleRightT L T R ≫ collapseMap L T R = _
    rw [collapseMap, tripleRightDesc_T, ← Category.assoc, point_terminal,
      Category.id_comp])
  last := last_of_point _ (by
    rw [← pointAt_last_right L (wedge T R), ← pointAt_last_right T R]
    change (pointAt R (ULift.up (Fin.last R.len)) ≫ wedgeιRight T R) ≫
      wedgeιRight L (wedge T R) ≫ collapseMap L T R = _
    rw [Category.assoc]
    change pointAt R (ULift.up (Fin.last R.len)) ≫ tripleRightV L T R ≫
      collapseMap L T R = _
    rw [collapseMap, tripleRightDesc_V, ← Category.assoc, point_terminal,
      Category.id_comp])

theorem collapse_left :
    tripleRightT L T R ≫ (collapse L T R).map =
      outerTerminal L ≫ pointAt T (ULift.up 0) :=
  tripleRightDesc_T _ _ _ _ _ _ (collapse_joint_left L T) (collapse_joint_right T R)

theorem collapse_middle :
    tripleRightU L T R ≫ (collapse L T R).map = 𝟙 _ :=
  tripleRightDesc_U _ _ _ _ _ _ (collapse_joint_left L T) (collapse_joint_right T R)

theorem collapse_right :
    tripleRightV L T R ≫ (collapse L T R).map =
      outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)) :=
  tripleRightDesc_V _ _ _ _ _ _ (collapse_joint_left L T) (collapse_joint_right T R)

instance collapse_map_epi : Epi (collapse L T R).map := by
  haveI : IsSplitEpi (collapse L T R).map :=
    IsSplitEpi.mk' { section_ := tripleRightU L T R, id := collapse_middle L T R }
  infer_instance

theorem factors_of_outer_constants {X : SSet.{u}}
    (f : toSSet.{u} (wedge L (wedge T R)) ⟶ X)
    (hL : tripleRightT L T R ≫ f =
      outerTerminal L ≫ pointAt T (ULift.up 0) ≫ (tripleRightU L T R ≫ f))
    (hR : tripleRightV L T R ≫ f =
      outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)) ≫
        (tripleRightU L T R ≫ f)) :
    f = (collapse L T R).map ≫ (tripleRightU L T R ≫ f) := by
  apply tripleRight_hom_ext
  · rw [hL]
    simp only [← Category.assoc, collapse_left]
  · rw [← Category.assoc, collapse_middle, Category.id_comp]
  · rw [hR]
    simp only [← Category.assoc, collapse_right]

/-- An underlying factorization through the outer collapse is a native endpoint-preserving map. -/
def nativeFactor (Q : NecklaceCode)
    (f : Hom.{u} (wedge L (wedge T R)) Q)
    (g : toSSet.{u} T ⟶ toSSet.{u} Q)
    (h : f.map = (collapse L T R).map ≫ g) : Hom.{u} T Q where
  map := g
  first := first_of_point g (by
    calc
      pointAt T (ULift.up 0) ≫ g =
          (pointAt (wedge L (wedge T R)) (ULift.up 0) ≫
            (collapse L T R).map) ≫ g := by rw [pointAt_first_comp]
      _ = pointAt (wedge L (wedge T R)) (ULift.up 0) ≫ f.map := by
        rw [Category.assoc, ← h]
      _ = pointAt Q (ULift.up 0) := pointAt_first_comp f)
  last := last_of_point g (by
    calc
      pointAt T (ULift.up (Fin.last T.len)) ≫ g =
          (pointAt (wedge L (wedge T R))
            (ULift.up (Fin.last (wedge L (wedge T R)).len)) ≫
              (collapse L T R).map) ≫ g := by rw [pointAt_last_comp]
      _ = pointAt (wedge L (wedge T R))
            (ULift.up (Fin.last (wedge L (wedge T R)).len)) ≫ f.map := by
        rw [Category.assoc, ← h]
      _ = pointAt Q (ULift.up (Fin.last Q.len)) := pointAt_last_comp f)

theorem collapse_nativeFactor (Q : NecklaceCode)
    (f : Hom.{u} (wedge L (wedge T R)) Q)
    (g : toSSet.{u} T ⟶ toSSet.{u} Q)
    (h : f.map = (collapse L T R).map ≫ g) :
    Hom.comp (collapse L T R) (nativeFactor L T R Q f g h) = f :=
  Hom.ext h.symm

/-- A native map with constant outer restrictions factors through the middle necklace. -/
def factorNative (Q : NecklaceCode)
    (f : Hom.{u} (wedge L (wedge T R)) Q)
    (hL : tripleRightT L T R ≫ f.map =
      outerTerminal L ≫ pointAt T (ULift.up 0) ≫ (tripleRightU L T R ≫ f.map))
    (hR : tripleRightV L T R ≫ f.map =
      outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)) ≫
        (tripleRightU L T R ≫ f.map)) : Hom.{u} T Q :=
  nativeFactor L T R Q f (tripleRightU L T R ≫ f.map)
    (factors_of_outer_constants L T R f.map hL hR)

theorem collapse_factorNative (Q : NecklaceCode)
    (f : Hom.{u} (wedge L (wedge T R)) Q)
    (hL : tripleRightT L T R ≫ f.map =
      outerTerminal L ≫ pointAt T (ULift.up 0) ≫ (tripleRightU L T R ≫ f.map))
    (hR : tripleRightV L T R ≫ f.map =
      outerTerminal R ≫ pointAt T (ULift.up (Fin.last T.len)) ≫
        (tripleRightU L T R ≫ f.map)) :
    Hom.comp (collapse L T R) (factorNative L T R Q f hL hR) = f :=
  collapse_nativeFactor L T R Q f (tripleRightU L T R ≫ f.map)
    (factors_of_outer_constants L T R f.map hL hR)

end

end DaggerChosenRigidificationNecklace.NecklaceCode
