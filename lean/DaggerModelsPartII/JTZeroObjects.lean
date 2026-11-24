import DaggerModelsPartII.RigidifiedJTFrames
import DaggerModels.DaggerAdjunction
import DaggerModels.FreeDagger
import Mathlib.CategoryTheory.HomCongr

/-!
# Objects classified by the actual zero rigidified JT frame

The zero reversal simplex is the free dagger zero simplex. Its rigidification
classifies an actual target object through the original adjunctions and the
degree-zero coherent-nerve vertex equivalence.
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels
open DaggerModels.OrdinaryRigidification

namespace DaggerModels.PartII.JTZeroObjects

noncomputable section

def zeroIndex : ReverseSimplex := ReverseSimplex.inclusion.obj ⦋0⦌

def zeroInputIso :
    RigidifiedJTFrames.A.obj zeroIndex ≅
      DaggerRigidification.daggerRigidification.obj
        (freeDagger.obj (Δ[0] : SSet.{0})) :=
  DaggerRigidification.daggerRigidification.mapIso
    (DaggerJTFrameUnderlying.reversalSimplexFreeIso.app ⦋0⦌)

/-- A map from the exact zero frame selects one object of the target. -/
def zeroHomEquiv (C : DaggerSimplicialCat.{0, 0}) :
    (RigidifiedJTFrames.A.obj zeroIndex ⟶ C) ≃ C.Obj :=
  (zeroInputIso.homCongr (Iso.refl C)).trans
    ((DaggerAdjunction.homEquiv
      (freeDagger.obj (Δ[0] : SSet.{0})) C).trans
    ((freeDaggerAdjunction.homEquiv (Δ[0] : SSet.{0})
      (DaggerNerve.daggerCoherentNerve.obj C)).trans
    ((SSet.yonedaEquiv (X := (DaggerNerve.daggerCoherentNerve.obj C).toSSet)
      (n := ⦋0⦌)).trans
      (NerveVertices.vertexEquiv C.toSimplicialCat))))

/-- The actual map representing a selected object. -/
def objectMap (C : DaggerSimplicialCat.{0, 0}) (x : C.Obj) :
    RigidifiedJTFrames.A.obj zeroIndex ⟶ C :=
  (zeroHomEquiv C).symm x

@[simp] theorem zeroHomEquiv_objectMap (C : DaggerSimplicialCat.{0, 0})
    (x : C.Obj) : zeroHomEquiv C (objectMap C x) = x :=
  Equiv.apply_symm_apply _ _

/-- The selected object of the zero frame is the identity's vertex. -/
def zeroObject : (RigidifiedJTFrames.A.obj zeroIndex).Obj :=
  zeroHomEquiv (RigidifiedJTFrames.A.obj zeroIndex) (𝟙 _)

/-- Object classification is natural for actual dagger simplicial functors. -/
theorem zeroHomEquiv_naturality {C D : DaggerSimplicialCat.{0, 0}}
    (F : C ⟶ D) (g : RigidifiedJTFrames.A.obj zeroIndex ⟶ C) :
    zeroHomEquiv D (g ≫ F) = F.obj (zeroHomEquiv C g) := by
  rfl

/-- Evaluation is literally the image of the distinguished source object. -/
theorem zeroHomEquiv_eq_obj (C : DaggerSimplicialCat.{0, 0})
    (g : RigidifiedJTFrames.A.obj zeroIndex ⟶ C) :
    zeroHomEquiv C g = g.obj zeroObject := by
  simpa only [Category.id_comp, zeroObject] using
    (zeroHomEquiv_naturality g (𝟙 (RigidifiedJTFrames.A.obj zeroIndex)))

/-- The map representing an object is natural in its target. -/
theorem objectMap_naturality {C D : DaggerSimplicialCat.{0, 0}}
    (F : C ⟶ D) (x : C.Obj) :
    objectMap C x ≫ F = objectMap D (F.obj x) := by
  apply (zeroHomEquiv D).injective
  rw [zeroHomEquiv_naturality, zeroHomEquiv_objectMap,
    zeroHomEquiv_objectMap]

/-- The inverse representing map sends the distinguished zero-frame object
to the specified target object. -/
@[simp] theorem objectMap_object (C : DaggerSimplicialCat.{0, 0})
    (x : C.Obj) : (objectMap C x).obj zeroObject = x := by
  have h := zeroHomEquiv_naturality (objectMap C x)
    (𝟙 (RigidifiedJTFrames.A.obj zeroIndex))
  simpa only [Category.id_comp, zeroObject, zeroHomEquiv_objectMap] using h.symm

end

end DaggerModels.PartII.JTZeroObjects
