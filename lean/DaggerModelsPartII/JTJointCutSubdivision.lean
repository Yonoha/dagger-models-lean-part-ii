import ChosenNecklaceIntervalTerminal
import ChosenNecklacesOverWedge
import DaggerModelsPartII.JTNativeTargetKanWeak
import DaggerModelsPartII.JTJointClippedCylinder

/-!
# Compare two cuts through the common three-interval subdivision

The maps preserve the two original ordered endpoints and the entire map into
the original necklace, including when either cut lies inside a bead.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

open CategoryTheory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerSSetGluing
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointCutSubdivision

open JTNecklaceEndpointCylinder (nativeMap)
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural)

noncomputable section

variable (T : NecklaceCode) (a b c : Fin (T.len + 1)) (hab : a ≤ b) (hbc : b ≤ c)

/-- Concatenate adjacent original intervals over their literal union. -/
def concat :
    NecklacesOver.wedge (intervalOver.{0} T a b hab) (intervalOver.{0} T b c hbc) ⟶
      intervalOver.{0} T a c (hab.trans hbc) :=
  toInterval T a c (hab.trans hbc) _

/-- On the first piece the concatenation is the original interval inclusion. -/
@[reassoc]
theorem concat_first :
    wedgeιLeft (intervalCode T a b hab) (intervalCode T b c hbc) ≫
      (concat T a b c hab hbc).hom.map ≫ intervalι T a c (hab.trans hbc) =
        intervalι T a b hab := by
  change _ ≫ (concat T a b c hab hbc).hom.map ≫
    (intervalOver.{0} T a c (hab.trans hbc)).map = _
  rw [(concat T a b c hab hbc).w]
  exact NecklacesOver.wedge_left (intervalOver.{0} T a b hab) (intervalOver.{0} T b c hbc)

/-- On the second piece the concatenation is the original interval inclusion. -/
@[reassoc]
theorem concat_last :
    wedgeιRight (intervalCode T a b hab) (intervalCode T b c hbc) ≫
      (concat T a b c hab hbc).hom.map ≫ intervalι T a c (hab.trans hbc) =
        intervalι T b c hbc := by
  change _ ≫ (concat T a b c hab hbc).hom.map ≫
    (intervalOver.{0} T a c (hab.trans hbc)).map = _
  rw [(concat T a b c hab hbc).w]
  exact NecklacesOver.wedge_right (intervalOver.{0} T a b hab) (intervalOver.{0} T b c hbc)

variable (v w : Fin (T.len + 1)) (h : v ≤ w)

private abbrev initial := intervalOver.{0} T 0 v (Fin.zero_le v)
private abbrev gap := intervalOver.{0} T v w h
private abbrev suffix := intervalOver.{0} T w (Fin.last T.len) (Fin.le_last w)

/-- The two-piece subdivision at the specified cut, over the original necklace. -/
abbrev cut (v : Fin (T.len + 1)) :=
  NecklacesOver.wedge (intervalOver.{0} T 0 v (Fin.zero_le v))
    (intervalOver.{0} T v (Fin.last T.len) (Fin.le_last v))

/-- The subdivision retaining all three original intervals. -/
abbrev common :=
  NecklacesOver.wedge (NecklacesOver.wedge (initial T v) (gap T v w h)) (suffix T w)

/-- Keep the earlier cut by joining the gap to the suffix. -/
def toEarlier : common T v w h ⟶ cut T v :=
  NecklacesOver.wedgeAssocOver (initial T v) (gap T v w h) (suffix T w) ≫
    NecklacesOver.wedgeHom (𝟙 (initial T v)) (concat T v w (Fin.last T.len) h (Fin.le_last w))

/-- Keep the later cut by joining the gap to the initial. -/
def toLater : common T v w h ⟶ cut T w :=
  NecklacesOver.wedgeHom (concat T 0 v w (Fin.zero_le v) h) (𝟙 (suffix T w))

/-- Both maps to the original necklace agree, retaining both ordered endpoints. -/
theorem over_original :
    (toEarlier T v w h).hom.map ≫ (cut T v).map =
      (toLater T v w h).hom.map ≫ (cut T w).map :=
  (toEarlier T v w h).w.trans (toLater T v w h).w.symm

private theorem map_weak {X Y : NecklaceCode} (f : toSSet.{0} X ⟶ toSSet.{0} Y) :
    WeakEquivalence f := by
  letI : WeakEquivalence (pointMap X.toSSet) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW X)
  letI : WeakEquivalence (pointMap Y.toSSet) :=
    (weakEquivalence_iff_GW _).mpr (JTNativeTargetKanWeak.point_GW Y)
  exact weakEquivalence_of_postcomp_of_fac
    (pointIsTerminal.hom_ext (f ≫ pointMap Y.toSSet) (pointMap X.toSSet))

/-- The map to the earlier cut remains weak on the whole reduced cylinder. -/
theorem toEarlier_cylinder_weak (k : SimplexCategory) :
    WeakEquivalence (nativeMap (toEarlier T v w h).hom k) :=
  JTJointClippedCylinder.nativeMap_weak _ (map_weak _) _

/-- The map to the later cut remains weak on the whole reduced cylinder. -/
theorem toLater_cylinder_weak (k : SimplexCategory) :
    WeakEquivalence (nativeMap (toLater T v w h).hom k) :=
  JTJointClippedCylinder.nativeMap_weak _ (map_weak _) _

/-- The entire reduced cylinders compare over the original native target. -/
theorem cylinders_over_original (k : SimplexCategory) :
    nativeMap (toEarlier T v w h).hom k ≫ augmentation (cut T v).code k ≫ (cut T v).map =
      nativeMap (toLater T v w h).hom k ≫ augmentation (cut T w).code k ≫ (cut T w).map := by
  simp only [← Category.assoc (nativeMap _ _), augmentation_native_natural,
    Category.assoc, over_original]

end
end DaggerModels.PartII.JTJointCutSubdivision
