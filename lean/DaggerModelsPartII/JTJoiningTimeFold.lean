import DaggerModelsPartII.JTJoiningTimeBifunctor
import DaggerModelsPartII.JTBinaryPrismSideTransport

/-! Folding enlarged phase and time diagrams on the original reduced cylinders. -/

set_option autoImplicit false

open CategoryTheory Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJoiningTimeFold

open JTJoiningTimeBifunctor (joiningTime joiningTime_map)
open JTHigherGraphTimeFamily (fold fold_mapTime fold_mapCopies)
open JTHigherInterleavedParameter (mapTime)
open JTFiniteCoefficientBridgeTime (mapCopies)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev inc := SemiSimplexCategory.toSimplexCategory

/-- The whole phase-time joining map preserves the original time after folding. -/
theorem fold_joiningTime_map
    {p q : SemiSimplexCategory × SimplexCategory} (f : p ⟶ q) :
    J.map (joiningTime.map f) ≫ fold (inc.obj q.1) q.2 =
      fold (inc.obj p.1) p.2 ≫ J.map f.2 := by
  rw [joiningTime_map, J.map_comp, Category.assoc]
  change J.map (mapTime (inc.obj p.1) f.2) ≫
      J.map (mapCopies (inc.map f.1) _ q.2) ≫ fold ⦋q.1.len⦌ q.2 = _
  rw [fold_mapCopies]
  exact fold_mapTime (inc.obj p.1) f.2

/-- The pure-time parameter on a native code and a phase-time joining ordinal. -/
def foldParameter (S : NecklaceCode)
    (p : SemiSimplexCategory × SimplexCategory) :
    S.toSSet ⊗ J.obj (joiningTime.obj p) ⟶ J.obj p.2 :=
  snd S.toSSet (J.obj (joiningTime.obj p)) ≫ fold (inc.obj p.1) p.2

/-- Native code and phase-time transport commute on the entire parameter. -/
theorem foldParameter_square {S T : NecklaceCode} (h : S ⟶ T)
    {p q : SemiSimplexCategory × SimplexCategory} (f : p ⟶ q) :
    (h.map ⊗ₘ J.map (joiningTime.map f)) ≫ foldParameter T q =
      foldParameter S p ≫ J.map f.2 := by
  unfold foldParameter
  rw [← Category.assoc, tensorHom_snd, Category.assoc, fold_joiningTime_map]
  rw [Category.assoc]

/-- The actual reduced-cylinder comparison for the pure-time parameter. -/
theorem reducedCylinder_square {S T : NecklaceCode} (h : S ⟶ T)
    {p q : SemiSimplexCategory × SimplexCategory} (f : p ⟶ q) :
    JTInterpolatedReducedCylinder.cylinderMap S (foldParameter S p) ≫
        (JTNecklaceEndpointCylinder.nativeMap h p.2 ≫
          (JTNecklaceEndpointCylinder.value T).map f.2) =
      (JTNecklaceEndpointCylinder.nativeMap h (joiningTime.obj p) ≫
        (JTNecklaceEndpointCylinder.value T).map (joiningTime.map f)) ≫
          JTInterpolatedReducedCylinder.cylinderMap T (foldParameter T q) := by
  exact JTBinaryPrismSideTransport.mixedCylinderSquare h f.2
    (joiningTime.map f) (foldParameter S p) (foldParameter T q)
    (foldParameter_square h f)

end

end DaggerModels.PartII.JTJoiningTimeFold
