import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTCylinderCEComparison
import DaggerModelsPartII.JTCylinderBlockQuotient
import DaggerModelsPartII.NecklaceCylinderHomSpan
import ChosenNecklaceUnitCodeMaps

/-!
# A three-bead traversal of the actual two-bead reduced cylinder

The first code map collapses the middle bead and retains both horizontal
beads. The second collapses the outer beads and retains the middle bead.
Their product, followed by the original reduced-cylinder leg, is a literal
map of simplicial sets; no raw target or weak-equivalence assertion enters.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.TwoBeadCylinderTraversal

noncomputable section

/-- The two original consecutive single-edge beads. -/
def twoBead : NecklaceCode := wedge (single 1) (single 1)

/-- Horizontal bead at time zero, vertical seam bead, horizontal bead at
time one. This is definitionally the old two-block quotient's native code. -/
def threeBead : NecklaceCode :=
  wedge (single 1) (wedge (single 1) (single 1))

theorem threeBead_eq_blockCode : threeBead = JTCylinderBlockQuotient.code 1 1 := rfl

/-- The native one-bead collapse to the zero necklace. -/
def edgeToPoint : NecklaceCode.Hom.{0} (single 1) point where
  map := SSet.stdSimplex.isTerminalObj₀.from _
  first := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    exact Fin.ext (by omega)
  last := by
    apply SSet.stdSimplex.obj₀Equiv.injective
    exact Fin.ext (by omega)

/-- Keep the first and last horizontal beads and collapse only the seam. -/
def collapseMiddle : NecklaceCode.Hom.{0} threeBead twoBead :=
  let first : NecklaceCode.Hom.{0} threeBead
      (wedge (single 1) (wedge point (single 1))) :=
    wedgeMap (Hom.id (single 1)) (wedgeMap edgeToPoint (Hom.id (single 1)))
  let second : NecklaceCode.Hom.{0}
      (wedge (single 1) (wedge point (single 1))) twoBead :=
    wedgeMap (Hom.id (single 1)) (wedgeLeftUnitCode (single 1))
  Hom.comp first second

/-- Collapse both outer horizontal beads and retain exactly the middle
single-edge bead as the parameter interval. -/
def collapseOuter : NecklaceCode.Hom.{0} threeBead (single 1) :=
  let first : NecklaceCode.Hom.{0} threeBead
      (wedge point (wedge (single 1) point)) :=
    wedgeMap edgeToPoint (wedgeMap (Hom.id (single 1)) edgeToPoint)
  let second : NecklaceCode.Hom.{0}
      (wedge point (wedge (single 1) point)) (wedge point (single 1)) :=
    wedgeMap (Hom.id point) (wedgeRightUnitCode (single 1))
  Hom.comp (Hom.comp first second) (wedgeLeftUnitCode (single 1))

private abbrev A : NecklaceCode := single 1
private abbrev L : A.toSSet ⟶ threeBead.toSSet := tripleRightT A A A
private abbrev M : A.toSSet ⟶ threeBead.toSSet := tripleRightU A A A
private abbrev RR : A.toSSet ⟶ threeBead.toSSet := tripleRightV A A A

private theorem leftUnit_right :
    wedgeιRight point A ≫ (wedgeLeftUnitCode A).map =
      𝟙 A.toSSet := by
  change (wedgeLeftUnit A).inv ≫ (wedgeLeftUnit A).hom = 𝟙 _
  exact (wedgeLeftUnit A).inv_hom_id

private theorem rightUnit_left :
    wedgeιLeft A point ≫ (wedgeRightUnitCode A).map =
      𝟙 A.toSSet := by
  change (wedgeRightUnit A).inv ≫ (wedgeRightUnit A).hom = 𝟙 _
  exact (wedgeRightUnit A).inv_hom_id

private theorem leftUnit_left :
    wedgeιLeft point A ≫ (wedgeLeftUnitCode A).map =
      pointAt A (ULift.up 0) :=
  wedgeLeftUnit_point A

private theorem rightUnit_right :
    wedgeιRight A point ≫ (wedgeRightUnitCode A).map =
      pointAt A (ULift.up (Fin.last A.len)) :=
  wedgeRightUnit_point A

private theorem idMap (T : NecklaceCode) : (Hom.id.{0} T).map = 𝟙 T.toSSet := rfl

/-- The initial horizontal bead is the actual first bead of the two-bead
necklace after collapsing the middle bead. -/
theorem collapseMiddle_left :
    L ≫ collapseMiddle.map = wedgeιLeft A A := by
  change (wedgeιLeft A (wedge A A) ≫
      (wedgeMap (Hom.id A) (wedgeMap edgeToPoint (Hom.id A))).map) ≫
      (wedgeMap (Hom.id A) (wedgeLeftUnitCode A)).map = _
  rw [wedgeMap_left]
  rw [idMap A, Category.id_comp]
  rw [wedgeMap_left]
  rw [idMap A, Category.id_comp]

/-- The terminal horizontal bead is the actual second bead. -/
theorem collapseMiddle_right :
    RR ≫ collapseMiddle.map = wedgeιRight A A := by
  change ((wedgeιRight A A ≫ wedgeιRight A (wedge A A)) ≫
      (wedgeMap (Hom.id A) (wedgeMap edgeToPoint (Hom.id A))).map) ≫
      (wedgeMap (Hom.id A) (wedgeLeftUnitCode A)).map = _
  rw [Category.assoc (wedgeιRight A A) (wedgeιRight A (wedge A A))
    (wedgeMap (Hom.id A) (wedgeMap edgeToPoint (Hom.id A))).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιRight A A)
    (wedgeMap edgeToPoint (Hom.id A)).map
    (wedgeιRight A (wedge point A)), wedgeMap_right]
  rw [idMap A, Category.id_comp]
  rw [Category.assoc (wedgeιRight point A) (wedgeιRight A (wedge point A))
    (wedgeMap (Hom.id A) (wedgeLeftUnitCode A)).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιRight point A) (wedgeLeftUnitCode A).map
    (wedgeιRight A A), leftUnit_right, Category.id_comp]

private theorem jointPoint :
    pointAt A (ULift.up 0) ≫ wedgeιRight A A =
      pointAt twoBead (ULift.up (1 : Fin (twoBead.len + 1))) := by
  rw [pointAt_comp, wedgeιRight_vertices]
  rfl

/-- The seam has constant first coordinate at the actual joint of the
two-bead necklace. -/
theorem collapseMiddle_middle :
    M ≫ collapseMiddle.map =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt twoBead (ULift.up (1 : Fin (twoBead.len + 1))) := by
  change ((wedgeιLeft A A ≫ wedgeιRight A (wedge A A)) ≫
      (wedgeMap (Hom.id A) (wedgeMap edgeToPoint (Hom.id A))).map) ≫
      (wedgeMap (Hom.id A) (wedgeLeftUnitCode A)).map = _
  rw [Category.assoc (wedgeιLeft A A) (wedgeιRight A (wedge A A))
    (wedgeMap (Hom.id A) (wedgeMap edgeToPoint (Hom.id A))).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιLeft A A)
    (wedgeMap edgeToPoint (Hom.id A)).map
    (wedgeιRight A (wedge point A)), wedgeMap_left]
  rw [Category.assoc (edgeToPoint.map ≫ wedgeιLeft point A)
    (wedgeιRight A (wedge point A))
    (wedgeMap (Hom.id A) (wedgeLeftUnitCode A)).map, wedgeMap_right]
  rw [← Category.assoc (edgeToPoint.map ≫ wedgeιLeft point A)
    (wedgeLeftUnitCode A).map (wedgeιRight A A)]
  rw [Category.assoc edgeToPoint.map (wedgeιLeft point A)
    (wedgeLeftUnitCode A).map, leftUnit_left]
  change (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
      pointAt A (ULift.up 0)) ≫ wedgeιRight A A = _
  rw [Category.assoc, jointPoint]

/-- The middle vertical bead retains the complete original parameter edge. -/
theorem collapseOuter_middle :
    M ≫ collapseOuter.map = 𝟙 A.toSSet := by
  change (((wedgeιLeft A A ≫ wedgeιRight A (wedge A A)) ≫
      (wedgeMap edgeToPoint (wedgeMap (Hom.id A) edgeToPoint)).map) ≫
      (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map) ≫
      (wedgeLeftUnitCode A).map = _
  rw [Category.assoc (wedgeιLeft A A) (wedgeιRight A (wedge A A))
    (wedgeMap edgeToPoint (wedgeMap (Hom.id A) edgeToPoint)).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιLeft A A)
    (wedgeMap (Hom.id A) edgeToPoint).map
    (wedgeιRight point (wedge A point)), wedgeMap_left]
  rw [idMap A, Category.id_comp]
  rw [Category.assoc (wedgeιLeft A point) (wedgeιRight point (wedge A point))
    (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιLeft A point) (wedgeRightUnitCode A).map
    (wedgeιRight point A), rightUnit_left, Category.id_comp,
    leftUnit_right]

/-- The first horizontal bead sits at parameter vertex zero. -/
theorem collapseOuter_left :
    L ≫ collapseOuter.map =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt A (ULift.up 0) := by
  change ((wedgeιLeft A (wedge A A) ≫
      (wedgeMap edgeToPoint (wedgeMap (Hom.id A) edgeToPoint)).map) ≫
      (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map) ≫
      (wedgeLeftUnitCode A).map = _
  rw [wedgeMap_left]
  rw [Category.assoc edgeToPoint.map (wedgeιLeft point (wedge A point))
    (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map, wedgeMap_left]
  rw [idMap point, Category.id_comp]
  rw [Category.assoc edgeToPoint.map (wedgeιLeft point A)
    (wedgeLeftUnitCode A).map, leftUnit_left]
  all_goals rfl

/-- The last horizontal bead sits at parameter vertex one. -/
theorem collapseOuter_right :
    RR ≫ collapseOuter.map =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt A (ULift.up (Fin.last A.len)) := by
  change (((wedgeιRight A A ≫ wedgeιRight A (wedge A A)) ≫
      (wedgeMap edgeToPoint (wedgeMap (Hom.id A) edgeToPoint)).map) ≫
      (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map) ≫
      (wedgeLeftUnitCode A).map = _
  rw [Category.assoc (wedgeιRight A A) (wedgeιRight A (wedge A A))
    (wedgeMap edgeToPoint (wedgeMap (Hom.id A) edgeToPoint)).map,
    wedgeMap_right]
  rw [← Category.assoc (wedgeιRight A A)
    (wedgeMap (Hom.id A) edgeToPoint).map
    (wedgeιRight point (wedge A point)), wedgeMap_right]
  rw [Category.assoc (edgeToPoint.map ≫ wedgeιRight A point)
    (wedgeιRight point (wedge A point))
    (wedgeMap (Hom.id point) (wedgeRightUnitCode A)).map, wedgeMap_right]
  rw [← Category.assoc (edgeToPoint.map ≫ wedgeιRight A point)
    (wedgeRightUnitCode A).map (wedgeιRight point A)]
  rw [Category.assoc edgeToPoint.map (wedgeιRight A point)
    (wedgeRightUnitCode A).map, rightUnit_right]
  rw [Category.assoc edgeToPoint.map
    (pointAt A (ULift.up (Fin.last A.len))) (wedgeιRight point A)]
  rw [Category.assoc edgeToPoint.map
    (pointAt A (ULift.up (Fin.last A.len)) ≫ wedgeιRight point A)
    (wedgeLeftUnitCode A).map]
  rw [Category.assoc (pointAt A (ULift.up (Fin.last A.len)))
    (wedgeιRight point A) (wedgeLeftUnitCode A).map,
    leftUnit_right, Category.comp_id]
  all_goals rfl

/-- The two complete native code maps give the actual tensor traversal.
The parameter edge is the free-groupoid unit on the original standard
one-simplex, with its entire simplicial structure retained. -/
def productTraversal : threeBead.toSSet ⟶
    twoBead.toSSet ⊗ GroupoidSimplex.parameter.obj ⦋1⦌ :=
  CartesianMonoidalCategory.lift collapseMiddle.map
    (collapseOuter.map ≫ (singleIso 1).hom ≫
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌)

/-- The literal three-bead map into the original reduced cylinder. -/
def cylinderTraversal : threeBead.toSSet ⟶
    (JTNecklaceEndpointCylinder.value twoBead).obj ⦋1⦌ :=
  productTraversal ≫ (JTNecklaceEndpointCylinder.cylinder twoBead).app ⦋1⦌

private theorem firstInclusion :
    SSet.boundary₁.ι₀ ≫ JTNecklaceEndpointCylinder.endpointInclusion twoBead =
      pointAt twoBead (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc twoBead.first twoBead.last =
    SSet.yonedaEquiv.symm twoBead.first
  exact SSet.boundary₁.ι₀_desc _ _

private theorem lastInclusion :
    SSet.boundary₁.ι₁ ≫ JTNecklaceEndpointCylinder.endpointInclusion twoBead =
      pointAt twoBead (ULift.up (Fin.last twoBead.len)) := by
  change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc twoBead.first twoBead.last =
    SSet.yonedaEquiv.symm twoBead.last
  exact SSet.boundary₁.ι₁_desc _ _

/-- The entire first endpoint map lands on the fixed ordered boundary of
the reduced pushout, independent of the source parameter vertex. -/
theorem cylinderTraversal_first_point :
    pointAt threeBead (ULift.up 0) ≫ cylinderTraversal =
      SSet.boundary₁.ι₀ ≫
        (JTNecklaceEndpointCylinder.boundary twoBead).app ⦋1⦌ := by
  let q : (Δ[0] : SSet.{0}) ⟶ GroupoidSimplex.parameter.obj ⦋1⦌ :=
    pointAt threeBead (ULift.up 0) ≫ collapseOuter.map ≫
      (singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌
  have hp : pointAt threeBead (ULift.up 0) ≫ productTraversal =
      CartesianMonoidalCategory.lift SSet.boundary₁.ι₀ q ≫
        (JTNecklaceEndpointCylinder.endpointInclusion twoBead ⊗ₘ
          𝟙 (GroupoidSimplex.parameter.obj ⦋1⦌)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [productTraversal, q, Category.assoc,
        CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst, Category.comp_id] using
          (pointAt_first_comp collapseMiddle).trans firstInclusion.symm
    · simp only [productTraversal, q, Category.assoc,
        CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
  calc
    _ = (pointAt threeBead (ULift.up 0) ≫ productTraversal) ≫
        (JTNecklaceEndpointCylinder.cylinder twoBead).app ⦋1⦌ :=
          (Category.assoc _ _ _).symm
    _ = (CartesianMonoidalCategory.lift SSet.boundary₁.ι₀ q ≫
          (JTNecklaceEndpointCylinder.endpointInclusion twoBead ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj ⦋1⦌))) ≫
          (JTNecklaceEndpointCylinder.cylinder twoBead).app ⦋1⦌ := by rw [hp]
    _ = CartesianMonoidalCategory.lift SSet.boundary₁.ι₀ q ≫
          CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary
            (GroupoidSimplex.parameter.obj ⦋1⦌) ≫
          (JTNecklaceEndpointCylinder.boundary twoBead).app ⦋1⦌ := by
            rw [Category.assoc, (JTNecklaceEndpointCylinder.isPushout twoBead ⦋1⦌).w]
    _ = _ := by
      rw [← Category.assoc, CartesianMonoidalCategory.lift_fst]

/-- The entire last endpoint map is the other fixed ordered boundary leg. -/
theorem cylinderTraversal_last_point :
    pointAt threeBead (ULift.up (Fin.last threeBead.len)) ≫ cylinderTraversal =
      SSet.boundary₁.ι₁ ≫
        (JTNecklaceEndpointCylinder.boundary twoBead).app ⦋1⦌ := by
  let q : (Δ[0] : SSet.{0}) ⟶ GroupoidSimplex.parameter.obj ⦋1⦌ :=
    pointAt threeBead (ULift.up (Fin.last threeBead.len)) ≫ collapseOuter.map ≫
      (singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌
  have hp : pointAt threeBead (ULift.up (Fin.last threeBead.len)) ≫
      productTraversal =
      CartesianMonoidalCategory.lift SSet.boundary₁.ι₁ q ≫
        (JTNecklaceEndpointCylinder.endpointInclusion twoBead ⊗ₘ
          𝟙 (GroupoidSimplex.parameter.obj ⦋1⦌)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [productTraversal, q, Category.assoc,
        CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst, Category.comp_id] using
          (pointAt_last_comp collapseMiddle).trans lastInclusion.symm
    · simp only [productTraversal, q, Category.assoc,
        CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
  calc
    _ = (pointAt threeBead (ULift.up (Fin.last threeBead.len)) ≫
          productTraversal) ≫
        (JTNecklaceEndpointCylinder.cylinder twoBead).app ⦋1⦌ :=
          (Category.assoc _ _ _).symm
    _ = (CartesianMonoidalCategory.lift SSet.boundary₁.ι₁ q ≫
          (JTNecklaceEndpointCylinder.endpointInclusion twoBead ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj ⦋1⦌))) ≫
          (JTNecklaceEndpointCylinder.cylinder twoBead).app ⦋1⦌ := by rw [hp]
    _ = CartesianMonoidalCategory.lift SSet.boundary₁.ι₁ q ≫
          CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary
            (GroupoidSimplex.parameter.obj ⦋1⦌) ≫
          (JTNecklaceEndpointCylinder.boundary twoBead).app ⦋1⦌ := by
            rw [Category.assoc, (JTNecklaceEndpointCylinder.isPushout twoBead ⦋1⦌).w]
    _ = _ := by
      rw [← Category.assoc, CartesianMonoidalCategory.lift_fst]

/-- The actual first native vertex is the cylinder's original first point. -/
theorem cylinderTraversal_first :
    cylinderTraversal.app (op ⦋0⦌) threeBead.first =
      NecklaceCylinderHomSpan.firstVertex twoBead ⦋1⦌ := by
  have h := congrArg SSet.yonedaEquiv cylinderTraversal_first_point
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    NecklaceCylinderHomSpan.firstVertex] using h

/-- The actual last native vertex is the cylinder's original last point. -/
theorem cylinderTraversal_last :
    cylinderTraversal.app (op ⦋0⦌) threeBead.last =
      NecklaceCylinderHomSpan.lastVertex twoBead ⦋1⦌ := by
  have h := congrArg SSet.yonedaEquiv cylinderTraversal_last_point
  simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
    NecklaceCylinderHomSpan.lastVertex] using h

/-- The requested actual native necklace over the two-bead cylinder,
with both original ordered boundary vertices fixed. -/
def necklaceOverCylinder :
    DaggerChosenRigidificationNecklace.NecklacesOver
      ((JTNecklaceEndpointCylinder.value twoBead).obj ⦋1⦌)
      (NecklaceCylinderHomSpan.firstVertex twoBead ⦋1⦌)
      (NecklaceCylinderHomSpan.lastVertex twoBead ⦋1⦌) where
  code := threeBead
  map := cylinderTraversal
  first := cylinderTraversal_first
  last := cylinderTraversal_last

end

end DaggerModels.PartII.TwoBeadCylinderTraversal
