import DaggerModelsPartII.JTThreePieceLabelOperators

/-! Restrict or descend only the varying middle label before forming decorated arrows. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskeredMiddleRestriction

open JTThreePieceLabelOperators (Data index indexMap)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open ReversalDiscreteFreeColimits (discreteFree)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map i) W

variable {W : Source} {P M N R : NecklaceCode} {k : SimplexCategory} {x y : Vertex W}

/-- Genuine native operators retain both entire endpoint coefficient families. -/
theorem pre_first (f : M ⟶ N) : pre W f.map ≫ firstRestriction W M =
    firstRestriction W N := by
  unfold pre firstRestriction
  rw [← diagramMappingPrecomp_comp, ← discreteFree.map_comp, pointAt_first_comp f]

theorem pre_last (f : M ⟶ N) : pre W f.map ≫ lastRestriction W M =
    lastRestriction W N := by
  unfold pre lastRestriction
  rw [← diagramMappingPrecomp_comp, ← discreteFree.map_comp, pointAt_last_comp f]

private theorem pre_id (T : NecklaceCode) :
    pre W ((𝟙 T : T ⟶ T).map) = 𝟙 (labels W T) := by
  change diagramMappingPrecomp (discreteFree.map (𝟙 T.toSSet)) W = 𝟙 _
  rw [discreteFree.map_id]
  exact diagramMappingPrecomp_id _ W

/-- Pull the middle coefficient back along an actual native map. The two
surrounding coefficients and the global endpoint proofs stay literal. -/
def pullMiddle (D : Data W P N R k x y) (f : M ⟶ N) : Data W P M R k x y where
  left := D.left
  middle := D.middle ≫ pre W f.map
  right := D.right
  left_join := by rw [Category.assoc, pre_first]; exact D.left_join
  right_join := by rw [Category.assoc, pre_last]; exact D.right_join
  first := D.first
  last := D.last

/-- Pullback of the unbased middle gives an actual arrow of the full decorated labels. -/
def pullMiddleMap (D : Data W P N R k x y) (f : M ⟶ N) :
    index (pullMiddle D f) ⟶ index D := by
  apply indexMap (pullMiddle D f) D (𝟙 P) f (𝟙 R) (𝟙 k)
  · change D.left = std.map (𝟙 k) ≫ D.left ≫ pre W ((𝟙 P : P ⟶ P).map)
    rw [std.map_id, Category.id_comp, pre_id, Category.comp_id]
  · change D.middle ≫ pre W f.map = std.map (𝟙 k) ≫ D.middle ≫ pre W f.map
    rw [std.map_id, Category.id_comp]
  · change D.right = std.map (𝟙 k) ≫ D.right ≫ pre W ((𝟙 R : R ⟶ R).map)
    rw [std.map_id, Category.id_comp, pre_id, Category.comp_id]

/-- A middle coefficient that descends along a native map inherits the
matching seams from the original whole label, without fixing its endpoints separately. -/
def descendMiddle (C : Data W P M R k x y) (f : M ⟶ N)
    (m : std.obj k ⟶ labels W N) (hm : C.middle = m ≫ pre W f.map) :
    Data W P N R k x y where
  left := C.left
  middle := m
  right := C.right
  left_join := by
    have h := C.left_join
    rw [hm, Category.assoc, pre_first] at h
    exact h
  right_join := by
    have h := C.right_join
    rw [hm, Category.assoc, pre_last] at h
    exact h
  first := C.first
  last := C.last

/-- The descended middle gives the original full decorated arrow. -/
def descendMiddleMap (C : Data W P M R k x y) (f : M ⟶ N)
    (m : std.obj k ⟶ labels W N) (hm : C.middle = m ≫ pre W f.map) :
    index C ⟶ index (descendMiddle C f m hm) := by
  apply indexMap C (descendMiddle C f m hm) (𝟙 P) f (𝟙 R) (𝟙 k)
  · change C.left = std.map (𝟙 k) ≫ C.left ≫ pre W ((𝟙 P : P ⟶ P).map)
    rw [std.map_id, Category.id_comp, pre_id, Category.comp_id]
  · change C.middle = std.map (𝟙 k) ≫ m ≫ pre W f.map
    rw [std.map_id, Category.id_comp]
    exact hm
  · change C.right = std.map (𝟙 k) ≫ C.right ≫ pre W ((𝟙 R : R ⟶ R).map)
    rw [std.map_id, Category.id_comp, pre_id, Category.comp_id]

end
end DaggerModels.PartII.JTWhiskeredMiddleRestriction
