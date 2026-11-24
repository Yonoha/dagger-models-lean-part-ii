import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.OuterFaceSpineGeometry
import DaggerModelsPartII.FibrationPullbackWeakComparison

/-! A map of injectively fibrant Segal diagrams is rowwise weak if it is weak
on the original zero and first rows. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSegalRowWeakRecognition

open SegalLocalizers ReversalDiscreteFreeColimits SpineOuterFacePushout OuterFaceSpineGeometry

noncomputable section

private abbrev J := ReverseSimplexᵒᵖ
private abbrev S := ReverseDaggerSpace.{0}

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

private theorem mapping_natural {A B W Z : S} (i : A ⟶ B) (f : W ⟶ Z) :
    diagramMappingPrecomp i W ≫ diagramMappingPostcomp A f =
      diagramMappingPostcomp B f ≫ diagramMappingPrecomp i Z := by
  apply NatTrans.ext
  funext q η
  rfl

private theorem mapping_weak_of_iso {A B W Z : S} (i : A ⟶ B) [IsIso i] (f : W ⟶ Z)
    [WeakEquivalence (diagramMappingPostcomp A f)] :
    WeakEquivalence (diagramMappingPostcomp B f) := by
  letI : IsIso (diagramMappingPrecomp i W) :=
    Functor.map_isIso (diagramMappingSource W) i.op
  letI : IsIso (diagramMappingPrecomp i Z) :=
    Functor.map_isIso (diagramMappingSource Z) i.op
  exact weakEquivalence_of_postcomp_of_fac (mapping_natural i f).symm

private theorem mapping_weak_of_pushout {A B D P W Z : S}
    {i : A ⟶ B} {j : A ⟶ D} {l : B ⟶ P} {r : D ⟶ P} (h : IsPushout i j l r)
    [Mono j] (f : W ⟶ Z) [IsFibrant W] [IsFibrant Z]
    [WeakEquivalence (diagramMappingPostcomp A f)]
    [WeakEquivalence (diagramMappingPostcomp B f)]
    [WeakEquivalence (diagramMappingPostcomp D f)] :
    WeakEquivalence (diagramMappingPostcomp P f) := by
  letI : PreservesLimitsOfShape WalkingCospan (diagramMappingSource W) :=
    diagramMappingSource_preservesLimitsOfShape WalkingCospan W
  letI : PreservesLimitsOfShape WalkingCospan (diagramMappingSource Z) :=
    diagramMappingSource_preservesLimitsOfShape WalkingCospan Z
  let hW := h.op.map (diagramMappingSource W)
  let hZ := h.op.map (diagramMappingSource Z)
  let p' := diagramMappingPrecomp j W
  let q' := diagramMappingPrecomp i W
  let p := diagramMappingPrecomp j Z
  let q := diagramMappingPrecomp i Z
  let a := diagramMappingPostcomp D f
  let b := diagramMappingPostcomp B f
  let c := diagramMappingPostcomp A f
  have ha : p' ≫ c = a ≫ p := mapping_natural j f
  have hb : q' ≫ c = b ≫ q := mapping_natural i f
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  letI : Fibration p' := InjectiveKanDiagram.diagramMappingPrecomp_isFibration J j W
  letI : Fibration p := InjectiveKanDiagram.diagramMappingPrecomp_isFibration J j Z
  let m := pullback.map p' q' p q a b c ha hb
  letI : WeakEquivalence m :=
    FibrationPullbackWeakComparison.weak_of_pullback_map p' q' p q a b c ha.symm hb.symm
  let eW := hW.isoPullback
  let eZ := hZ.isoPullback
  have he : eW.hom ≫ m = diagramMappingPostcomp P f ≫ eZ.hom := by
    apply pullback.hom_ext
    · simp only [m, Category.assoc, pullback.map, pullback.lift_fst]
      have h₁ : eW.hom ≫ pullback.fst p' q' = diagramMappingPrecomp r W :=
        hW.isoPullback_hom_fst
      have h₂ : eZ.hom ≫ pullback.fst p q = diagramMappingPrecomp r Z :=
        hZ.isoPullback_hom_fst
      rw [← Category.assoc eW.hom, h₁, h₂]
      exact mapping_natural r f
    · simp only [m, Category.assoc, pullback.map, pullback.lift_snd]
      have h₁ : eW.hom ≫ pullback.snd p' q' = diagramMappingPrecomp l W :=
        hW.isoPullback_hom_snd
      have h₂ : eZ.hom ≫ pullback.snd p q = diagramMappingPrecomp l Z :=
        hZ.isoPullback_hom_snd
      rw [← Category.assoc eW.hom, h₁, h₂]
      exact mapping_natural l f
  exact weakEquivalence_of_postcomp_of_fac he.symm

private theorem freeMappingIso_natural {W Z : S} (f : W ⟶ Z) (n : ℕ) :
    diagramMappingPostcomp (daggerSimplex n) f ≫
        (OrderedSimplexEndpointFiber.freeMappingIso Z n).hom =
      (OrderedSimplexEndpointFiber.freeMappingIso W n).hom ≫ f.app (op ⟨n⟩) := by
  apply NatTrans.ext
  funext q η
  rfl

private theorem simplexMapping_weak_iff {W Z : S} (f : W ⟶ Z) (n : ℕ) :
    WeakEquivalence (diagramMappingPostcomp (daggerSimplex n) f) ↔
      WeakEquivalence (f.app (op ⟨n⟩)) := by
  let eW := OrderedSimplexEndpointFiber.freeMappingIso W n
  let eZ := OrderedSimplexEndpointFiber.freeMappingIso Z n
  let m := diagramMappingPostcomp (daggerSimplex n) f
  have h : m ≫ eZ.hom = eW.hom ≫ f.app (op ⟨n⟩) := freeMappingIso_natural f n
  calc
    WeakEquivalence m ↔ WeakEquivalence (m ≫ eZ.hom) :=
      (weakEquivalence_postcomp_iff m eZ.hom).symm
    _ ↔ WeakEquivalence (eW.hom ≫ f.app (op ⟨n⟩)) := by rw [h]
    _ ↔ _ := weakEquivalence_precomp_iff eW.hom _

private theorem spineIso_of_le_one (n : ℕ) (hn : n ≤ 1) :
    IsIso (segalMap.{0} n) := by
  have h : DaggerNativeStandardSpineInner.spine.{0} n = ⊤ := by
    apply top_unique
    intro q c hc
    induction q using Opposite.rec with | op q =>
      induction q using SimplexCategory.rec with | h d =>
        rw [DaggerNativeStandardSpineInner.mem_spine_iff]
        have hr := (SSet.stdSimplex.asOrderHom c (Fin.last d)).isLt
        omega
  letI : IsIso (DaggerNativeStandardSpineInner.spine.{0} n).ι := by
    rw [h]
    change IsIso (SSet.Subcomplex.topIso (Δ[n] : SSet.{0})).hom
    infer_instance
  change IsIso (discreteFree.map (DaggerNativeStandardSpineInner.spine n).ι)
  infer_instance

private theorem spineMapping_weak {W Z : S} (f : W ⟶ Z) [IsFibrant W] [IsFibrant Z]
    [WeakEquivalence (f.app (op ⟨0⟩))] [WeakEquivalence (f.app (op ⟨1⟩))]
    (n : ℕ) : WeakEquivalence (diagramMappingPostcomp (daggerSpine n) f) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 1
    · letI := spineIso_of_le_one n hn
      haveI : WeakEquivalence (diagramMappingPostcomp (daggerSimplex n) f) := by
        apply (simplexMapping_weak_iff f n).mpr
        have he : n = 0 ∨ n = 1 := by omega
        rcases he with rfl | rfl <;> infer_instance
      exact mapping_weak_of_iso (inv (segalMap n)) f
    · let t := n - 2
      have ht : t + 2 = n := by omega
      have hmid := ih t (by omega)
      have hedge := ih (t + 1) (by omega)
      haveI := firstSpinePartMap_isIso.{0} t
      haveI := lastSpinePartMap_isIso.{0} t
      haveI := middleSpinePartMap_isIso.{0} t
      let i := discreteFree.map (middleSpinePartMap.{0} t)
      let j := discreteFree.map (firstSpinePartMap.{0} t)
      let k := discreteFree.map (lastSpinePartMap.{0} t)
      have hM := @mapping_weak_of_iso _ _ W Z i inferInstance f hmid
      have hF := @mapping_weak_of_iso _ _ W Z j inferInstance f hedge
      have hL := @mapping_weak_of_iso _ _ W Z k inferInstance f hedge
      let i' := SSet.Subcomplex.homOfLE
        (inf_le_right : middleSpinePart.{0} t ≤ lastSpinePart t)
      letI : Mono (discreteFree.map i') := ReversalDiscreteFreeColimits.map_mono i'
      let sq := map_isPushout (spinePartsPushout.{0} t)
      rw [← ht]
      exact @mapping_weak_of_pushout _ _ _ _ W Z _ _ _ _ sq inferInstance f
        inferInstance inferInstance hM hF hL

/-- On injectively fibrant Segal diagrams, the original zero and first rows
detect injective weakness. -/
theorem weak_of_zero_one {W Z : S} (f : W ⟶ Z) [IsFibrant W] [IsFibrant Z]
    (hW : segalCondition W) (hZ : segalCondition Z)
    [WeakEquivalence (f.app (op ⟨0⟩))] [WeakEquivalence (f.app (op ⟨1⟩))] :
    WeakEquivalence f := by
  apply (weakEquivalence_iff f).mpr
  rw [InjectiveKanDiagram.model_weakEquivalences]
  intro j
  obtain ⟨⟨n⟩⟩ := j
  apply (weakEquivalence_iff _).mp
  by_cases hn : n ≤ 1
  · have he : n = 0 ∨ n = 1 := by omega
    rcases he with rfl | rfl <;> infer_instance
  · apply (simplexMapping_weak_iff f n).mp
    haveI := spineMapping_weak f n
    haveI : WeakEquivalence (diagramMappingPrecomp (segalMap n) W) :=
      (weakEquivalence_iff _).mpr (hW n (by omega))
    haveI : WeakEquivalence (diagramMappingPrecomp (segalMap n) Z) :=
      (weakEquivalence_iff _).mpr (hZ n (by omega))
    exact weakEquivalence_of_postcomp_of_fac (mapping_natural (segalMap n) f).symm

end

end DaggerModels.PartII.JTSegalRowWeakRecognition
