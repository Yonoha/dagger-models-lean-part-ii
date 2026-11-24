import DaggerModelsPartII.JTProjectiveRealizationMappingWeak
import DaggerModelsPartII.JTFreeInnerUnderlying

/-!
# The canonical raw free-inner comparison

This auxiliary comparison retains the original chosen free-inner target and
the actual projective replacement map. No dagger-Joyal fibrancy of either
free-inner target is asserted.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OrdinaryRigidification
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRawFreeInnerComparison

open JTStrictificationMaps JTStrictificationCoefficients

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The same functorial free-inner replacement, now applied to the raw realization. -/
def rawTarget (W : Source) : DaggerSSet.{0} :=
  JTFreeInnerFactorization.replacement.obj
    (DaggerJTRealization.daggerRealization.obj W)

/-- Its actual unit at the raw realization. -/
def rawG (W : Source) :
    DaggerJTRealization.daggerRealization.obj W ⟶ rawTarget W :=
  JTFreeInnerFactorization.unit.app
    (DaggerJTRealization.daggerRealization.obj W)

/-- Functoriality gives the canonical map from the original chosen target. -/
def ell (W : Source) : chosenT W ⟶ rawTarget W :=
  JTFreeInnerFactorization.replacement.map
    (DaggerJTRealization.daggerRealization.map (p.app W))

/-- The unit naturality square holds strictly in the original dagger category. -/
theorem chosenG_ell (W : Source) :
    chosenG W ≫ ell W =
      DaggerJTRealization.daggerRealization.map (p.app W) ≫ rawG W := by
  exact (JTFreeInnerFactorization.unit.naturality
    (DaggerJTRealization.daggerRealization.map (p.app W))).symm

/-- The same strict square after forgetting the dagger. -/
theorem underlying_square (W : Source) :
    (chosenG W).hom ≫ (ell W).hom =
      (DaggerJTRealization.daggerRealization.map (p.app W)).hom ≫
        (rawG W).hom := by
  exact congrArg
    (fun f : DaggerJTRealization.daggerRealization.obj (Qproj.obj W) ⟶
        rawTarget W ↦ f.hom) (chosenG_ell W)

/-- The forgotten projective map is definitionally the retained ordinary map. -/
theorem underlying_projective_map (W : Source) :
    (DaggerJTRealization.daggerRealization.map (p.app W)).hom =
      JTProjectiveRealizationMappingWeak.realizedP W := rfl

/-- The original chosen unit remains bijective on actual degree-zero vertices. -/
theorem chosenG_vertex_bijective (W : Source) :
    Function.Bijective ((chosenG W).hom.app (op ⦋0⦌)) :=
  JTFreeInnerUnderlying.unit_vertex_bijective
    (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))

/-- The same unit is bijective on original rigidification objects. -/
theorem chosenG_rigidification_object_bijective (W : Source) :
    Function.Bijective
      (rigidification.map (chosenG W).hom).obj :=
  DaggerActualInnerAnodyneRigidification.object_bijective
    (chosenG W).hom
      (JTFreeInnerUnderlying.unit_underlying_innerAnodyne
        (DaggerJTRealization.daggerRealization.obj (Qproj.obj W)))

/-- Every original rigidified Hom of the canonical comparison is Kan weak.
The original projective comparison and both free-inner units are the three
input maps in the strict naturality square. -/
theorem ell_rigidified_hom_weak (W : Source)
    (a b : (rigidification.obj (chosenT W).toSSet).Obj) :
    WeakEquivalence ((rigidification.map (ell W).hom).map a b) := by
  let f := (chosenG W).hom
  let e := (ell W).hom
  let h := JTProjectiveRealizationMappingWeak.realizedP W
  let k := (rawG W).hom
  let F := rigidification.map f
  let E := rigidification.map e
  let H := rigidification.map h
  let K := rigidification.map k
  have hbij : Function.Bijective F.obj := by
    exact chosenG_rigidification_object_bijective W
  obtain ⟨a₀, rfl⟩ := hbij.2 a
  obtain ⟨b₀, rfl⟩ := hbij.2 b
  have hf : WeakEquivalence (F.map a₀ b₀) :=
    DaggerActualInnerAnodyneRigidification.hom_weak f
      (JTFreeInnerUnderlying.unit_underlying_innerAnodyne
        (DaggerJTRealization.daggerRealization.obj (Qproj.obj W))) a₀ b₀
  have hh : WeakEquivalence (H.map a₀ b₀) :=
    JTProjectiveRealizationMappingWeak.rigidified_realizedP_hom_weak W a₀ b₀
  have hk : WeakEquivalence (K.map (H.obj a₀) (H.obj b₀)) :=
    DaggerActualInnerAnodyneRigidification.hom_weak k
      (JTFreeInnerUnderlying.unit_underlying_innerAnodyne
        (DaggerJTRealization.daggerRealization.obj W)) (H.obj a₀) (H.obj b₀)
  have hs : f ≫ e = h ≫ k := by
    change (chosenG W).hom ≫ (ell W).hom =
      JTProjectiveRealizationMappingWeak.realizedP W ≫ (rawG W).hom
    rw [← underlying_projective_map W]
    exact underlying_square W
  have hmap : F ≫ E = H ≫ K := by
    dsimp only [F, E, H, K]
    rw [← rigidification.map_comp, ← rigidification.map_comp, hs]
  have hright : WeakEquivalence ((H ≫ K).map a₀ b₀) := by
    change WeakEquivalence (H.map a₀ b₀ ≫ K.map (H.obj a₀) (H.obj b₀))
    letI : WeakEquivalence (H.map a₀ b₀) := hh
    letI : WeakEquivalence (K.map (H.obj a₀) (H.obj b₀)) := hk
    infer_instance
  have hleft : WeakEquivalence ((F ≫ E).map a₀ b₀) := by
    rw [hmap]
    exact hright
  have hleft' : WeakEquivalence
      (F.map a₀ b₀ ≫ E.map (F.obj a₀) (F.obj b₀)) := hleft
  letI : WeakEquivalence (F.map a₀ b₀) := hf
  letI : WeakEquivalence
      (F.map a₀ b₀ ≫ E.map (F.obj a₀) (F.obj b₀)) := hleft'
  exact weakEquivalence_of_precomp (F.map a₀ b₀)
    (E.map (F.obj a₀) (F.obj b₀))

end

end DaggerModels.PartII.JTRawFreeInnerComparison
