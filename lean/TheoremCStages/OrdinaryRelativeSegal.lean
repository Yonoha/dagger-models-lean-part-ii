import OrdinaryZeroCoskeletonMapping
import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import NativeSSetFibrationsOverBaseWeakPullbacks

/-!
# Ordinary Segal condition after fixing the original zero row

The checked relative Segal argument is transported to the ordinary
index category using the exact ordinary spine and evaluation adjunction.
The target is injectively fibrant; no ordinary completeness is required.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryRelativeSegal

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryZeroCoskeleton OrdinaryZeroCoskeletonMapping

noncomputable section

private abbrev S := Space
private abbrev J := SimplexCategoryᵒᵖ
private abbrev zero : J := op ⦋0⦌

private def restriction {A B : S} (i : A ⟶ B) :
    diagramMappingTarget B ⟶ diagramMappingTarget A where
  app Z := diagramMappingPrecomp i Z
  naturality _ _ _ := by
    apply NatTrans.ext
    funext q z
    rfl

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

/-- The target over the source zero row inherits the original Segal condition. -/
theorem targetOverZero_segal {W Z : S} (f : W ⟶ Z) [IsFibrant Z]
    (hZ : OrdinaryCSSConditions.segalCondition Z) :
    OrdinaryCSSConditions.segalCondition (targetOverZero f) := by
  intro n hn
  let F := diagramMappingTarget (discrete.obj (Δ[n] : SSet.{0}))
  let G := diagramMappingTarget (discrete.obj (DaggerNativeStandardSpineInner.spine n : SSet.{0}))
  let r : F ⟶ G := restriction (OrdinaryCSSLocalization.spineMap n)
  let V := coskeleton.obj (Z.obj zero)
  let K := coskeleton.obj (W.obj zero)
  let v : Z ⟶ V := vertices Z
  let k : K ⟶ V := coskeleton.map (f.app zero)
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramTensorMappingAdjunction (discrete.obj (Δ[n] : SSet.{0}))).rightAdjoint_preservesLimits
  let aG := diagramTensorMappingAdjunction
    (discrete.obj (DaggerNativeStandardSpineInner.spine n : SSet.{0}))
  letI : PreservesLimitsOfSize.{0, 0} G := aG.rightAdjoint_preservesLimits
  letI := spineMap_zero_isIso n
  letI : IsIso (r.app K) := precomp_isIso (OrdinaryCSSLocalization.spineMap n) (W.obj zero)
  letI : IsIso (r.app V) := precomp_isIso (OrdinaryCSSLocalization.spineMap n) (Z.obj zero)
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  letI : F.PreservesFibrations :=
    InjectiveKanDiagram.diagramMappingTarget_preservesFibrations J (discrete.obj (Δ[n] : SSet.{0}))
  letI : G.PreservesFibrations :=
    InjectiveKanDiagram.diagramMappingTarget_preservesFibrations J
      (discrete.obj (DaggerNativeStandardSpineInner.spine n : SSet.{0}))
  letI : Fibration v := vertices_fibration Z
  letI : Fibration (F.map v) := inferInstance
  letI : Fibration (G.map v) := inferInstance
  let p := F.map v ≫ r.app V
  let q := G.map v
  let b := G.map k
  letI : Fibration p := inferInstance
  letI : WeakEquivalence (r.app Z) := (weakEquivalence_iff _).mpr (hZ n hn)
  let hp : r.app Z ≫ q = p := (r.naturality v).symm
  let m := DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver p q (r.app Z) hp b
  letI : WeakEquivalence m :=
    DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_weakEquivalence p q _ hp b
  let h := IsPullback.of_hasPullback v k
  have hBase : IsPullback (F.map k) (r.app K) (r.app V) b :=
    IsPullback.of_vert_isIso ⟨(r.naturality k).symm⟩
  let eF := ((h.map F).paste_vert hBase).isoPullback
  let eG := (h.map G).isoPullback
  have hm : eF.hom ≫ m = r.app (pullback v k) ≫ eG.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, m, DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst]
      rw [← Category.assoc eF.hom, IsPullback.isoPullback_hom_fst,
        IsPullback.isoPullback_hom_fst, r.naturality]
    · simp only [Category.assoc, m, DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver,
        pullback.lift_snd]
      rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd, r.naturality]
  exact (weakEquivalence_iff _).mp (weakEquivalence_of_postcomp_of_fac hm.symm)


#print axioms targetOverZero_segal

end

end DaggerModels.PartII.OrdinaryRelativeSegal
