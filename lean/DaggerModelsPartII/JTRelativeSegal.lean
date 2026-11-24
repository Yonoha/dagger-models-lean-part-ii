import DaggerModelsPartII.JTZeroCoskeletonMapping
import DaggerModels.FreeDaggerPushout

/-! Base change of the literal Segal condition along the original zero row. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRelativeSegal

open SegalLocalizers JTZeroCoskeleton JTZeroCoskeletonMapping

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev zero : J := op ⟨0⟩

private theorem freeUnit_zero_isIso (A : SSet.{0}) :
    IsIso ((freeDaggerAdjunction.unit.app A).app (op ⦋0⦌)) := by
  rw [← FreeDaggerPushout.inl_isoFreeDagger_hom A]
  let t := DaggerSSet.forget.map (FreeDaggerPushout.isoFreeDagger.hom.app A)
  let E := SSet.evaluation.{0}.obj (op ⦋0⦌)
  letI : IsIso (E.map t) := Functor.map_isIso _ _
  change IsIso ((FreeDaggerPushout.inl A).app (op ⦋0⦌) ≫ E.map t)
  infer_instance

/-- The literal spine contains every vertex, including after free dagger completion. -/
theorem segalMap_zero_isIso (n : ℕ) : IsIso ((segalMap.{0} n).app zero) := by
  let A := ordinarySpine.{0} n
  let B := (Δ[n] : SSet.{0})
  let i : A ⟶ B := (DaggerNativeStandardSpineInner.spine n).ι
  letI := segalMap_mono.{0} n
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  apply (isIso_iff_bijective _).mpr
  refine ⟨(mono_iff_injective _).mp inferInstance, ?_⟩
  letI := freeUnit_zero_isIso B
  intro z
  change (freeDagger.obj B).toSSet.obj (op ⦋0⦌) at z
  obtain ⟨x, rfl⟩ :=
    ((isIso_iff_bijective ((freeDaggerAdjunction.unit.app B).app (op ⦋0⦌))).mp
      inferInstance).2 z
  have hx : x ∈ (DaggerNativeStandardSpineInner.spine n).obj (op ⦋0⦌) := by
    rw [DaggerNativeStandardSpineInner.mem_spine_iff]
    have hindex : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hindex]
    omega
  let a : A.obj (op ⦋0⦌) := ⟨x, hx⟩
  refine ⟨(freeDaggerAdjunction.unit.app A).app (op ⦋0⦌) a, ?_⟩
  exact (congrFun (NatTrans.congr_app (freeDaggerAdjunction.unit.naturality i) (op ⦋0⦌)) a).symm

private def restriction {A B : S} (i : A ⟶ B) :
    diagramMappingTarget B ⟶ diagramMappingTarget A where
  app Z := diagramMappingPrecomp i Z
  naturality _ _ _ := by
    apply NatTrans.ext
    funext q z
    rfl

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

set_option maxHeartbeats 2000000 in
/-- The target over the source zero row inherits the original Segal condition. -/
theorem targetOverZero_segal {W Z : S} (f : W ⟶ Z) [IsFibrant Z]
    (hZ : segalCondition Z) : segalCondition (targetOverZero f) := by
  intro n hn
  let F := diagramMappingTarget (daggerSimplex.{0} n)
  let G := diagramMappingTarget (daggerSpine.{0} n)
  let r : F ⟶ G := restriction (segalMap n)
  let V := coskeleton.obj (Z.obj zero)
  let K := coskeleton.obj (W.obj zero)
  let v : Z ⟶ V := vertices Z
  let k : K ⟶ V := coskeleton.map (f.app zero)
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramTensorMappingAdjunction (daggerSimplex n)).rightAdjoint_preservesLimits
  letI : PreservesLimitsOfSize.{0, 0} G :=
    (diagramTensorMappingAdjunction (daggerSpine n)).rightAdjoint_preservesLimits
  letI := segalMap_zero_isIso n
  letI : IsIso (r.app K) := precomp_isIso (segalMap n) (W.obj zero)
  letI : IsIso (r.app V) := precomp_isIso (segalMap n) (Z.obj zero)
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  letI : F.PreservesFibrations :=
    InjectiveKanDiagram.diagramMappingTarget_preservesFibrations J (daggerSimplex n)
  letI : G.PreservesFibrations :=
    InjectiveKanDiagram.diagramMappingTarget_preservesFibrations J (daggerSpine n)
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

end

end DaggerModels.PartII.JTRelativeSegal
