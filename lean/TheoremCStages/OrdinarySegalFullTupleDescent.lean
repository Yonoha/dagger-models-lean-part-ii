import OrdinarySegalSurjectiveObjectDescent
import OrdinaryRelativeSegal
import OrdinaryAllVertexSquareComparison
import OriginalSimplicialPiZeroWeakEquivalence

/-!
# Segal descent from the complete ordered vertex tuples

The zero-coskeleton pullback of an ordinary map is assumed Segal. If its
source covers every connected component of every ordered vertex-tuple
mapping space of the target, then the target itself is Segal. The proof
reflects the actual spine test through the exact base-change square.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalFullTupleDescent

open OrdinaryCSSLocalization (Space discrete)
open OrdinaryZeroCoskeleton OrdinaryZeroCoskeletonMapping
open OrdinaryAllVertexSquareComparison (coskeletonMappingIso coskeletonMappingIso_natural)
open OrdinarySegalVertexTupleFibres (vertices)

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev zero : J := op ⦋0⦌

private def restriction {A B : Space} (i : A ⟶ B) :
    diagramMappingTarget B ⟶ diagramMappingTarget A where
  app Z := diagramMappingPrecomp i Z
  naturality _ _ _ := by
    apply NatTrans.ext
    funext q z
    rfl

private local instance : ModelCategory Space :=
  InjectiveKanDiagram.modelCategory J

/-- The simplex mapping-space map of the zero coskeleton is surjective on
components if the original complete vertex-tuple map is so. -/
private theorem simplex_components_surjective {W Z : Space} (f : W ⟶ Z)
    (hTupleSurj : ∀ n : ℕ, Function.Surjective
      (SSet.mapπ₀ (diagramMappingPostcomp (discrete.obj (vertices n)) f)))
    (n : ℕ) : Function.Surjective (SSet.mapπ₀
      (diagramMappingPostcomp (discrete.obj (Δ[n] : SSet.{0}))
        (coskeleton.map (f.app zero)))) := by
  let K := coskeleton.obj (W.obj zero)
  let V := coskeleton.obj (Z.obj zero)
  let k : K ⟶ V := coskeleton.map (f.app zero)
  let t := diagramMappingPostcomp (discrete.obj (vertices n)) f
  let iW := OrdinarySegalWalkingEvaluation.simplexMappingIso K n ≪≫
    coskeletonMappingIso W n
  let iZ := OrdinarySegalWalkingEvaluation.simplexMappingIso V n ≪≫
    coskeletonMappingIso Z n
  have hs : diagramMappingPostcomp (discrete.obj (Δ[n] : SSet.{0})) k ≫
      iZ.hom = iW.hom ≫ t := by
    dsimp only [iW, iZ, Iso.trans_hom]
    rw [← Category.assoc,
      OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post k n,
      Category.assoc, coskeletonMappingIso_natural f n, ← Category.assoc]
  haveI : WeakEquivalence iW.hom := inferInstance
  haveI : WeakEquivalence iZ.hom := inferInstance
  have hW := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
    iW.hom).surjective
  have hZ := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
    iZ.hom).injective
  intro y
  obtain ⟨z, hz⟩ := hTupleSurj n (SSet.mapπ₀ iZ.hom y)
  obtain ⟨x, hx⟩ := hW z
  refine ⟨x, hZ ?_⟩
  have hπ := congrFun (congrArg SSet.mapπ₀ hs) x
  simp only [SSet.mapπ₀_comp_apply] at hπ
  exact hπ.trans (by rw [hx, hz])

/-- Segalness descends from the actual zero-row pullback along a map
covering every component of every ordered finite vertex tuple. -/
theorem segal_of_relative_and_tuple_surjective {W Z : Space} (f : W ⟶ Z)
    [IsFibrant Z]
    (hRelative : OrdinaryCSSConditions.segalCondition (targetOverZero f))
    (hTupleSurj : ∀ n : ℕ, Function.Surjective
      (SSet.mapπ₀ (diagramMappingPostcomp (discrete.obj (vertices n)) f))) :
    OrdinaryCSSConditions.segalCondition Z := by
  intro n hn
  let F := diagramMappingTarget (discrete.obj (Δ[n] : SSet.{0}))
  let G := diagramMappingTarget
    (discrete.obj (DaggerNativeStandardSpineInner.spine n : SSet.{0}))
  let r : F ⟶ G := restriction (OrdinaryCSSLocalization.spineMap n)
  let V := coskeleton.obj (Z.obj zero)
  let K := coskeleton.obj (W.obj zero)
  let v : Z ⟶ V := vertices Z
  let k : K ⟶ V := coskeleton.map (f.app zero)
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramTensorMappingAdjunction
      (discrete.obj (Δ[n] : SSet.{0}))).rightAdjoint_preservesLimits
  let aG := diagramTensorMappingAdjunction
    (discrete.obj (DaggerNativeStandardSpineInner.spine n : SSet.{0}))
  letI : PreservesLimitsOfSize.{0, 0} G := aG.rightAdjoint_preservesLimits
  letI := spineMap_zero_isIso n
  letI : IsIso (r.app K) := precomp_isIso (OrdinaryCSSLocalization.spineMap n)
    (W.obj zero)
  letI : IsIso (r.app V) := precomp_isIso (OrdinaryCSSLocalization.spineMap n)
    (Z.obj zero)
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  letI : F.PreservesFibrations :=
    InjectiveKanDiagram.diagramMappingTarget_preservesFibrations J
      (discrete.obj (Δ[n] : SSet.{0}))
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
  letI : Fibration q := inferInstance
  have hp : r.app Z ≫ q = p := (r.naturality v).symm
  let m := DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver
    p q (r.app Z) hp b
  have hFk : Function.Surjective (SSet.mapπ₀ (F.map k)) := by
    change Function.Surjective (SSet.mapπ₀
      (diagramMappingPostcomp (discrete.obj (Δ[n] : SSet.{0})) k))
    exact simplex_components_surjective f hTupleSurj n
  haveI : WeakEquivalence (r.app V) := inferInstance
  have hrV := (DaggerOriginalSimplicialPiZeroWeakEquivalence.bijective_mapPiZero
    (r.app V)).surjective
  have hb : Function.Surjective (SSet.mapπ₀ b) := by
    intro y
    obtain ⟨x, hx⟩ := hrV y
    obtain ⟨xK, hxK⟩ := hFk x
    refine ⟨SSet.mapπ₀ (r.app K) xK, ?_⟩
    have hc := congrFun (congrArg SSet.mapπ₀ (r.naturality k)) xK
    simp only [SSet.mapπ₀_comp_apply] at hc
    exact hc.symm.trans (by rw [hxK, hx])
  let h := IsPullback.of_hasPullback v k
  have hBase : IsPullback (F.map k) (r.app K) (r.app V) b :=
    IsPullback.of_vert_isIso ⟨(r.naturality k).symm⟩
  let eF := ((h.map F).paste_vert hBase).isoPullback
  let eG := (h.map G).isoPullback
  have hm : eF.hom ≫ m = r.app (pullback v k) ≫ eG.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, m,
        DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_fst]
      rw [← Category.assoc eF.hom, IsPullback.isoPullback_hom_fst,
        IsPullback.isoPullback_hom_fst, r.naturality]
    · simp only [Category.assoc, m,
        DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver, pullback.lift_snd]
      rw [IsPullback.isoPullback_hom_snd, IsPullback.isoPullback_hom_snd, r.naturality]
  letI : WeakEquivalence (r.app (pullback v k)) :=
    (weakEquivalence_iff _).mpr (hRelative n hn)
  have hmx : WeakEquivalence (eF.hom ≫ m) := by
    rw [hm]
    infer_instance
  have hmweak : WeakEquivalence m :=
    (weakEquivalence_precomp_iff eF.hom m).mp hmx
  have hZ : WeakEquivalence (r.app Z) :=
    OrdinarySegalSurjectiveObjectDescent.weak_of_component_surjective_baseChange
      p q (r.app Z) hp b hb hmweak
  exact (weakEquivalence_iff _).mp hZ

#print axioms segal_of_relative_and_tuple_surjective

end

end DaggerModels.PartII.OrdinarySegalFullTupleDescent
