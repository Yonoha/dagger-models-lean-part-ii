import DaggerModelsPartII.JTComposedPrismLabels

/-! Coefficient operators on the two-piece labels with a varying common endpoint. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTComposedPrismLabelOperators

open ReversalDiscreteFreeColimits OrderedNecklaceVertexPoints
open JTComposedPrismLabels (Coefficients coefficient orderedPoint)
open TripleBeadEndpointLabel (wedgeMappingPullback glue_left glue_right)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev F := discreteFree.{0}

private abbrev pre (W : Source) {X Y : SSet.{0}} (i : X ⟶ Y) :=
  diagramMappingPrecomp (F.map i) W

variable {W : Source} {x y : Vertex W} {T U T' U' : NecklaceCode}
variable {k k' : SimplexCategory}
variable (L : Coefficients W T U k x y) (R : Coefficients W T' U' k' x y)
variable (f : T ⟶ T') (g : U ⟶ U') (r : k ⟶ k')

set_option maxHeartbeats 700000 in
/-- A pair of exact operators on the two pieces induces the original
coefficient equation on their native wedge. -/
theorem coefficient_map
    (hl : L.left = std.map r ≫ R.left ≫ pre W f.map)
    (hr : L.right = std.map r ≫ R.right ≫ pre W g.map) :
    coefficient L = std.map r ≫ coefficient R ≫ pre W (wedgeMap f g).map := by
  apply (wedgeMappingPullback W T U).hom_ext
  · rw [coefficient, glue_left, hl]
    have hp : pre W (wedgeMap f g).map ≫ pre W (wedgeιLeft T U) =
        pre W (wedgeιLeft T' U') ≫ pre W f.map := by
      rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp, ← F.map_comp,
        ← F.map_comp, wedgeMap_left]
    simp only [Category.assoc]
    change _ = std.map r ≫ coefficient R ≫
      (pre W (wedgeMap f g).map ≫ pre W (wedgeιLeft T U))
    rw [hp, ← Category.assoc (coefficient R), coefficient, glue_left]
  · rw [coefficient, glue_right, hr]
    have hp : pre W (wedgeMap f g).map ≫ pre W (wedgeιRight T U) =
        pre W (wedgeιRight T' U') ≫ pre W g.map := by
      rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp, ← F.map_comp,
        ← F.map_comp, wedgeMap_right]
    simp only [Category.assoc]
    change _ = std.map r ≫ coefficient R ≫
      (pre W (wedgeMap f g).map ≫ pre W (wedgeιRight T U))
    rw [hp, ← Category.assoc (coefficient R), coefficient, glue_right]

set_option maxHeartbeats 800000 in
/-- The exact coefficient operators define an arrow of the actual decorated labels. -/
def indexMap (hl : L.left = std.map r ≫ R.left ≫ pre W f.map)
    (hr : L.right = std.map r ≫ R.right ≫ pre W g.map) :
    JTComposedPrismLabels.index L ⟶ JTComposedPrismLabels.index R :=
  JTOrderedLabelWedge.indexHomOfCoefficient (wedgeMap f g) r (orderedPoint L) (orderedPoint R) (by
    unfold JTOrderedLabelBinaryGlue.coefficient
    rw [JTComposedPrismLabels.orderedPoint_coefficient,
      JTComposedPrismLabels.orderedPoint_coefficient]
    simpa only [Equiv.symm_apply_apply] using coefficient_map L R f g r hl hr)

end
end DaggerModels.PartII.JTComposedPrismLabelOperators
