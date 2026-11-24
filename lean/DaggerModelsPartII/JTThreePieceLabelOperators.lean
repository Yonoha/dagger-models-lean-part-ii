import DaggerModelsPartII.JTComposedPrismLabelOperators

/-! Whisker an unbased middle-label comparison with its actual surrounding labels. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTThreePieceLabelOperators

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_first
  glue_last glue_left glue_right wedgeMappingPullback)
open ReversalDiscreteFreeColimits (discreteFree)
open OrderedNecklaceVertexPoints (zeroPoint)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map f) W

/-- Three full coefficients share the original degree and fixed GLOBAL
endpoints; their two internal endpoint families are allowed to vary. -/
structure Data (W : Source) (P M R : NecklaceCode) (k : SimplexCategory) (x y : Vertex W) where
  left : std.obj k ⟶ labels W P
  middle : std.obj k ⟶ labels W M
  right : std.obj k ⟶ labels W R
  left_join : left ≫ lastRestriction W P = middle ≫ firstRestriction W M
  right_join : middle ≫ lastRestriction W M = right ≫ firstRestriction W R
  first : left ≫ firstRestriction W P = term (std.obj k) ≫ zeroPoint W x
  last : right ≫ lastRestriction W R = term (std.obj k) ≫ zeroPoint W y

variable {W : Source} {P M R P' M' R' : NecklaceCode}
variable {k l : SimplexCategory} {x y : Vertex W}

/-- The middle and right are glued without fixing their varying initial endpoint. -/
def inside (C : Data W P M R k x y) := glue W M R k C.middle C.right C.right_join

private theorem seam (C : Data W P M R k x y) :
    C.left ≫ lastRestriction W P = inside C ≫ firstRestriction W (wedge M R) := by
  rw [inside, glue_first]
  exact C.left_join

/-- The complete three-piece label has exactly the prescribed outer endpoints. -/
def coefficients (C : Data W P M R k x y) :
    JTComposedPrismLabels.Coefficients W P (wedge M R) k x y where
  left := C.left
  right := inside C
  seam := seam C
  first := C.first
  last := by rw [inside, glue_last]; exact C.last

/-- The actual full decorated index, after both surrounding pieces are attached. -/
abbrev index (C : Data W P M R k x y) := JTComposedPrismLabels.index (coefficients C)

private theorem pre_left {A B A' B' : NecklaceCode} (f : A ⟶ A') (g : B ⟶ B') :
    pre W (wedgeMap f g).map ≫ pre W (wedgeιLeft A B) =
      pre W (wedgeιLeft A' B') ≫ pre W f.map := by
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discreteFree.map_comp, ← discreteFree.map_comp, wedgeMap_left]

private theorem pre_right {A B A' B' : NecklaceCode} (f : A ⟶ A') (g : B ⟶ B') :
    pre W (wedgeMap f g).map ≫ pre W (wedgeιRight A B) =
      pre W (wedgeιRight A' B') ≫ pre W g.map := by
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discreteFree.map_comp, ← discreteFree.map_comp, wedgeMap_right]

/-- A mapping-space coefficient operator may be checked on both native pieces
without assuming fixed endpoints on either piece separately. -/
theorem wedge_coefficient_map {A B A' B' : NecklaceCode}
    (f : A ⟶ A') (g : B ⟶ B') (v : k ⟶ l)
    (a : std.obj k ⟶ labels W (wedge A B))
    (b : std.obj l ⟶ labels W (wedge A' B'))
    (hL : a ≫ pre W (wedgeιLeft A B) =
      std.map v ≫ b ≫ pre W (wedgeιLeft A' B') ≫ pre W f.map)
    (hR : a ≫ pre W (wedgeιRight A B) =
      std.map v ≫ b ≫ pre W (wedgeιRight A' B') ≫ pre W g.map) :
    a = std.map v ≫ b ≫ pre W (wedgeMap f g).map := by
  apply (wedgeMappingPullback W A B).hom_ext
  · rw [hL]
    simp only [Category.assoc, pre_left]
  · rw [hR]
    simp only [Category.assoc, pre_right]

variable (C : Data W P M R k x y) (D : Data W P' M' R' l x y)
variable (f : P ⟶ P') (g : M ⟶ M') (h : R ⟶ R') (v : k ⟶ l)
variable (hL : C.left = std.map v ≫ D.left ≫ pre W f.map)
variable (hM : C.middle = std.map v ≫ D.middle ≫ pre W g.map)
variable (hR : C.right = std.map v ≫ D.right ≫ pre W h.map)

include hM hR in
/-- The arbitrary middle comparison is glued to the entire right coefficient. -/
theorem inside_map : inside C = std.map v ≫ inside D ≫ pre W (wedgeMap g h).map := by
  apply wedge_coefficient_map g h v
  · rw [inside, glue_left, hM]
    simp only [← Category.assoc, inside, glue_left]
  · rw [inside, glue_right, hR]
    simp only [← Category.assoc, inside, glue_right]

/-- A comparison of all three full coefficients gives an actual decorated
arrow after whiskering, even if the middle's endpoint row varies. -/
def indexMap : index C ⟶ index D :=
  JTComposedPrismLabelOperators.indexMap (coefficients C) (coefficients D)
    f (wedgeMap g h) v hL (inside_map C D g h v hM hR)

/-- The surrounding pieces, middle operator and coefficient operator are retained literally. -/
theorem indexMap_projection :
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)).map
      (indexMap C D f g h v hL hM hR) = (wedgeMap f (wedgeMap g h), v) := rfl

end
end DaggerModels.PartII.JTThreePieceLabelOperators
