import ChosenNecklaceIntervalTerminal
import ChosenNecklacesOverWedge
import ChosenNecklaceCutDegree
import ChosenNecklaceSingleBead

/-!
# Native assembly with the same outer correction edges

The original intervals are retained on both sides of an inserted cut. Two
one-simplex correction pieces at each outer cut map to that exact original
vertex. An arbitrary middle necklace maps to the inserted vertex. This is a
native construction over the original necklace; no raw-label equation or
normalized comparison is inferred from it.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCorrectedIntervalAssembly

noncomputable section

private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- A whole native piece constant at the specified actual vertex. -/
def constantOver (N : NecklaceCode) {X : SSet.{0}} (v : X.obj (op ⦋0⦌)) :
    NecklacesOver X v v where
  code := N
  map := term N.toSSet ≫ SSet.yonedaEquiv.symm v
  first := pointAt_vertex_apply v _
  last := pointAt_vertex_apply v _

variable (T : NecklaceCode) (a b c : Fin (T.len + 1)) (hab : a ≤ b) (hbc : b ≤ c)

private abbrev vertex (v : Fin (T.len + 1)) := T.verticesEquiv.symm (ULift.up v)
private abbrev E := single 1

/-- The corrected prefix ending at the original inserted vertex b. -/
def leftOver : NecklacesOver T.toSSet (vertex T 0) (vertex T b) :=
  NecklacesOver.wedge
    (NecklacesOver.wedge (intervalOver T 0 a (Fin.zero_le a))
      (constantOver E (vertex T a)))
    (NecklacesOver.wedge (constantOver E (vertex T a)) (intervalOver T a b hab))

/-- The corrected suffix beginning at that SAME original vertex b. -/
def rightOver : NecklacesOver T.toSSet (vertex T b) (vertex T (Fin.last T.len)) :=
  NecklacesOver.wedge (intervalOver T b c hbc)
    (NecklacesOver.wedge (constantOver E (vertex T c))
      (NecklacesOver.wedge (constantOver E (vertex T c))
        (intervalOver T c (Fin.last T.len) (Fin.le_last c))))

/-- Collapse both earlier corrections into the literal old prefix at b. -/
def leftToCut : (leftOver T a b hab).code ⟶ cutLeft T b :=
  (toInterval T 0 b (Fin.zero_le b) (leftOver T a b hab)).hom

/-- Its complete native map into the old source agrees, including zero intervals. -/
theorem leftToCut_fac :
    (leftToCut T a b hab).map ≫ cutLeftι T b = (leftOver T a b hab).map :=
  (toInterval T 0 b (Fin.zero_le b) (leftOver T a b hab)).w

/-- Collapse both later corrections into the literal old suffix at b. -/
def rightToCut : (rightOver T b c hbc).code ⟶ cutRight T b :=
  (toInterval T b (Fin.last T.len) (Fin.le_last b) (rightOver T b c hbc)).hom

/-- This suffix collapse keeps the entire map into the SAME original source. -/
theorem rightToCut_fac :
    (rightToCut T b c hbc).map ≫ cutRightι T b = (rightOver T b c hbc).map :=
  (toInterval T b (Fin.last T.len) (Fin.le_last b) (rightOver T b c hbc)).w

/-- The whole corrected native source with an arbitrary middle piece at b. -/
def wholeOver (M : NecklaceCode) :
    NecklacesOver T.toSSet (vertex T 0) (vertex T (Fin.last T.len)) :=
  NecklacesOver.wedge (leftOver T a b hab)
    (NecklacesOver.wedge (constantOver M (vertex T b)) (rightOver T b c hbc))

/-- Native assembly retains both actual global endpoints of T. -/
def assembly (M : NecklaceCode) : (wholeOver T a b c hab hbc M).code ⟶ T where
  map := (wholeOver T a b c hab hbc M).map
  first := (wholeOver T a b c hab hbc M).first
  last := (wholeOver T a b c hab hbc M).last

/-- Restriction of the whole assembly to the full corrected left piece. -/
theorem assembly_left (M : NecklaceCode) :
    wedgeιLeft (leftOver T a b hab).code
        (wedge M (rightOver T b c hbc).code) ≫
      (assembly T a b c hab hbc M).map = (leftOver T a b hab).map :=
by
  dsimp only [assembly, wholeOver, NecklacesOver.wedge, constantOver]
  exact wedgeDesc_left _ _ _ _ _

/-- The entire middle piece goes to the exact inserted original vertex. -/
theorem assembly_middle (M : NecklaceCode) :
    (wedgeιLeft M (rightOver T b c hbc).code ≫
      wedgeιRight (leftOver T a b hab).code (wedge M (rightOver T b c hbc).code)) ≫
        (assembly T a b c hab hbc M).map =
      term M.toSSet ≫ SSet.yonedaEquiv.symm (vertex T b) := by
  dsimp only [assembly, wholeOver, NecklacesOver.wedge, constantOver]
  rw [Category.assoc, wedgeDesc_right, wedgeDesc_left]

/-- Restriction to the full corrected right piece, without dropping either edge. -/
theorem assembly_right (M : NecklaceCode) :
    (wedgeιRight M (rightOver T b c hbc).code ≫
      wedgeιRight (leftOver T a b hab).code (wedge M (rightOver T b c hbc).code)) ≫
        (assembly T a b c hab hbc M).map = (rightOver T b c hbc).map := by
  dsimp only [assembly, wholeOver, NecklacesOver.wedge, constantOver]
  rw [Category.assoc, wedgeDesc_right, wedgeDesc_right]

/-- Postcomposing the full native assembly retains any supplied original target map. -/
theorem assembly_middle_postcomp (M : NecklaceCode) {X : SSet.{0}} (q : T.toSSet ⟶ X) :
    (wedgeιLeft M (rightOver T b c hbc).code ≫
      wedgeιRight (leftOver T a b hab).code (wedge M (rightOver T b c hbc).code)) ≫
        ((assembly T a b c hab hbc M).map ≫ q) =
      term M.toSSet ≫ SSet.yonedaEquiv.symm (vertex T b) ≫ q := by
  rw [← Category.assoc, assembly_middle, Category.assoc]

end
end DaggerModels.PartII.JTCorrectedIntervalAssembly
