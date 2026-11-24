import DaggerModelsPartII.JTZeroCoskeleton
import DaggerModelsPartII.JTUnitaryEndpointsFibration
import DaggerModelsPartII.CosimplicialMappingInvariance

/-! Restriction to the original walking boundary is invertible on the
zero coskeleton, in every inner simplicial degree. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTZeroCoskeletonMapping

open SegalLocalizers JTZeroCoskeleton

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}
private abbrev J := ReverseSimplexᵒᵖ
private abbrev zero : J := op ⟨0⟩
private abbrev adj := evaluationAdjunctionLeft SSet.{0} zero

/-- Every whole simplicial mapping degree out of a map which is invertible
at zero is invertible under restriction into the actual zero coskeleton. -/
theorem precomp_isIso {A B : S} (i : A ⟶ B) [IsIso (i.app zero)] (K : SSet.{0}) :
    IsIso (diagramMappingPrecomp i (coskeleton.obj K)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  let T := tensorRight (SSet.stdSimplex.obj q.unop)
  let j := Functor.whiskerRight i T
  haveI : IsIso (j.app zero) := inferInstanceAs (IsIso (T.map (i.app zero)))
  let eA := adj.homEquiv ((diagramTensor A).obj (SSet.stdSimplex.obj q.unop)) K
  let eB := adj.homEquiv ((diagramTensor B).obj (SSet.stdSimplex.obj q.unop)) K
  let e := eB.symm.trans (((asIso (j.app zero)).symm.homCongr (Iso.refl K)).trans eA)
  have h (g : (diagramMappingSpace B (coskeleton.obj K)).obj q) :
      (diagramMappingPrecomp i (coskeleton.obj K)).app q g = e g := by
    apply eA.symm.injective
    change eA.symm (j ≫ g) = eA.symm (eA ((j.app zero ≫ eB.symm g) ≫ 𝟙 K))
    rw [Equiv.symm_apply_apply, Category.comp_id]
    exact adj.homEquiv_naturality_left_symm j g
  apply (isIso_iff_bijective _).mpr
  constructor
  · intro x y hxy
    apply e.injective
    exact (h x).symm.trans (hxy.trans (h y))
  · intro y
    obtain ⟨x, hx⟩ := e.surjective y
    exact ⟨x, (h x).trans hx⟩

/-- The actual ordered walking-unitary boundary induces an isomorphism
on mapping spaces into the zero coskeleton. -/
theorem walkingBoundary_precomp_isIso (K : SSet.{0}) :
    IsIso (diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion (coskeleton.obj K)) := by
  letI := JTUnitaryEndpointsFibration.inclusion_zero_isIso
  exact precomp_isIso _ K

private abbrev E := walkingUnitarySpace.{0}
private abbrev B := OrderedNecklaceLabelDiagram.boundary
private abbrev F := diagramMappingTarget E
private abbrev G := diagramMappingTarget B

/-- Restriction to the two specified walking-unitary endpoints. -/
def restrict : F ⟶ G where
  app Z := diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion Z
  naturality X Y f := by
    apply NatTrans.ext
    funext q z
    rfl

set_option maxHeartbeats 1000000 in
/-- Pulling back to the original zero row preserves the actual ordered
walking-unitary fibers by a Cartesian square of whole mapping spaces. -/
theorem walkingBoundary_pullback {W Z : S} (f : W ⟶ Z) :
    IsPullback
      (diagramMappingPostcomp E (pullback.fst (vertices Z) (coskeleton.map (f.app zero))))
      (diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion (targetOverZero f))
      (diagramMappingPrecomp JTUnitaryEndpointsFibration.inclusion Z)
      (diagramMappingPostcomp B (pullback.fst (vertices Z) (coskeleton.map (f.app zero)))) := by
  let k := coskeleton.map (f.app zero)
  let h := IsPullback.of_hasPullback (vertices Z) k
  letI : PreservesLimitsOfSize.{0, 0} F :=
    (diagramTensorMappingAdjunction E).rightAdjoint_preservesLimits
  letI : PreservesLimitsOfSize.{0, 0} G :=
    (diagramTensorMappingAdjunction B).rightAdjoint_preservesLimits
  letI : IsIso (restrict.app (coskeleton.obj (W.obj zero))) :=
    walkingBoundary_precomp_isIso (W.obj zero)
  letI : IsIso (restrict.app (coskeleton.obj (Z.obj zero))) :=
    walkingBoundary_precomp_isIso (Z.obj zero)
  have hB : IsPullback (F.map k) (restrict.app (coskeleton.obj (W.obj zero)))
      (restrict.app (coskeleton.obj (Z.obj zero))) (G.map k) :=
    IsPullback.of_vert_isIso ⟨(restrict.naturality k).symm⟩
  have ho := (h.map F).paste_vert hB
  rw [restrict.naturality, restrict.naturality] at ho
  exact ho.of_bot (restrict.naturality (pullback.fst (vertices Z) k)).symm (h.map G)

open DaggerNativeSSetFibrationSquareFibreWeak

/-- The strict walking-unitary fiber map over the original boundary point. -/
def walkingFiberMap {W Z : S} (f : W ⟶ Z)
    (b : (Δ[0] : SSet.{0}) ⟶ G.obj W) :
    pullback (restrict.app W) b ⟶ pullback (restrict.app Z) (b ≫ G.map f) :=
  fibreMap (restrict.app W) (restrict.app Z) (F.map f) (G.map f)
    (restrict.naturality f).symm b (b ≫ G.map f) rfl

private theorem pointCast_fst {X Y K : SSet.{0}} (p : X ⟶ Y)
    {b c : K ⟶ Y} (h : b = c) :
    eqToHom (congrArg (fun u : K ⟶ Y ↦ pullback p u) h) ≫ pullback.fst p c = pullback.fst p b := by
  cases h
  exact Category.id_comp _

private theorem pointCast_snd {X Y K : SSet.{0}} (p : X ⟶ Y)
    {b c : K ⟶ Y} (h : b = c) :
    eqToHom (congrArg (fun u : K ⟶ Y ↦ pullback p u) h) ≫ pullback.snd p c = pullback.snd p b := by
  cases h
  exact Category.id_comp _

private theorem walkingFiberMap_comp {W P Z : S} (g : W ⟶ P) (f : P ⟶ Z)
    (b : (Δ[0] : SSet.{0}) ⟶ G.obj W) :
    walkingFiberMap g b ≫ walkingFiberMap f (b ≫ G.map g) =
      walkingFiberMap (g ≫ f) b ≫
        eqToHom (congrArg (fun u : (Δ[0] : SSet.{0}) ⟶ G.obj Z ↦ pullback (restrict.app Z) u)
          (show b ≫ G.map (g ≫ f) = (b ≫ G.map g) ≫ G.map f by
            rw [G.map_comp, Category.assoc])) := by
  let h : b ≫ G.map (g ≫ f) = (b ≫ G.map g) ≫ G.map f := by
    rw [G.map_comp, Category.assoc]
  apply pullback.hom_ext
  · rw [Category.assoc (walkingFiberMap g b), Category.assoc (walkingFiberMap (g ≫ f) b)]
    have hc := pointCast_fst (restrict.app Z) h
    conv_rhs => rw [hc]
    simp only [walkingFiberMap, fibreMap_fst, F.map_comp, ← Category.assoc]
  · rw [Category.assoc (walkingFiberMap g b), Category.assoc (walkingFiberMap (g ≫ f) b)]
    have hc := pointCast_snd (restrict.app Z) h
    conv_rhs => rw [hc]
    simp only [walkingFiberMap, fibreMap_snd]

private theorem walkingFiberMap_weak_comp {W P Z : S} (g : W ⟶ P) (f : P ⟶ Z)
    (b : (Δ[0] : SSet.{0}) ⟶ G.obj W)
    [WeakEquivalence (walkingFiberMap g b)]
    [WeakEquivalence (walkingFiberMap f (b ≫ G.map g))] :
    WeakEquivalence (walkingFiberMap (g ≫ f) b) := by
  have hw := walkingFiberMap_comp g f b
  exact weakEquivalence_of_postcomp_of_fac hw.symm

local instance : ModelCategory S := InjectiveKanDiagram.modelCategory J

private theorem mapping_weak (A : S) {W Z : S} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] :
    WeakEquivalence ((diagramMappingTarget A).map f) := by
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  let adj := diagramTensorMappingAdjunction A
  letI : adj.IsQuillenAdjunction := InjectiveKanDiagram.diagramTensorMapping_isQuillen J A
  letI : (diagramMappingTarget A).PreservesTrivialFibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialFibrations adj
  apply (weakEquivalence_iff _).mpr
  apply map_weak_of_trivialFibration (diagramMappingTarget A) _ f (mem_weakEquivalences _)
  intro X Y q hq
  haveI : Fibration q := (mem_trivialFibrations_iff q).mp hq |>.1
  haveI : WeakEquivalence q := (mem_trivialFibrations_iff q).mp hq |>.2
  exact mem_weakEquivalences _

private theorem restrict_fibration (W : S) [IsFibrant W] : Fibration (restrict.app W) := by
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos J) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos J⟩
  letI := JTUnitaryEndpointsFibration.inclusion_mono
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration J _ W

private theorem walkingFiberMap_weak_of_weak {W Z : S} [IsFibrant W] [IsFibrant Z]
    (f : W ⟶ Z) [WeakEquivalence f] (b : (Δ[0] : SSet.{0}) ⟶ G.obj W) :
    WeakEquivalence (walkingFiberMap f b) := by
  letI := mapping_weak E f
  letI := mapping_weak B f
  letI := restrict_fibration W
  letI := restrict_fibration Z
  exact fibreMap_weakEquivalence (restrict.app W) (restrict.app Z) (F.map f) (G.map f)
    (restrict.naturality f).symm b (b ≫ G.map f) rfl

private theorem walkingFiberMap_isIso_projection {W Z : S} (f : W ⟶ Z)
    (b : (Δ[0] : SSet.{0}) ⟶ G.obj (targetOverZero f)) :
    IsIso (walkingFiberMap (pullback.fst (vertices Z) (coskeleton.map (f.app zero))) b) := by
  let t := pullback.fst (vertices Z) (coskeleton.map (f.app zero))
  have h : IsPullback (F.map t) (restrict.app (targetOverZero f)) (restrict.app Z) (G.map t) :=
    walkingBoundary_pullback f
  let sq := (IsPullback.of_hasPullback (restrict.app (targetOverZero f)) b).paste_horiz h
  have he : sq.isoPullback.hom = walkingFiberMap t b := by
    apply pullback.hom_ext
    · exact (sq.isoPullback_hom_fst).trans (fibreMap_fst _ _ _ _ _ _ _ _).symm
    · exact (sq.isoPullback_hom_snd).trans (fibreMap_snd _ _ _ _ _ _ _ _).symm
  rw [← he]
  infer_instance

/-- If the actual comparison over the source zero row is rowwise weak, the
original map induces a weak map on each strict walking-unitary fiber. -/
theorem walkingFiberMap_weak_of_relative {W Z : S} (f : W ⟶ Z)
    [IsFibrant W] [IsFibrant Z] [IsFibrant (W.obj zero)]
    [WeakEquivalence (relativeComparison f)]
    (b : (Δ[0] : SSet.{0}) ⟶ G.obj W) :
    WeakEquivalence (walkingFiberMap f b) := by
  let a := relativeComparison f
  let t := pullback.fst (vertices Z) (coskeleton.map (f.app zero))
  letI := targetOverZero_fibrant f
  letI : WeakEquivalence (walkingFiberMap a b) := walkingFiberMap_weak_of_weak a b
  letI : IsIso (walkingFiberMap t (b ≫ G.map a)) := walkingFiberMap_isIso_projection f _
  have h : a ≫ t = f := pullback.lift_fst _ _ _
  have hweak := walkingFiberMap_weak_comp a t b
  have hc {f g : W ⟶ Z} (h : f = g) :
      WeakEquivalence (walkingFiberMap f b) ↔ WeakEquivalence (walkingFiberMap g b) := by
    subst g
    rfl
  exact (hc h).mp hweak

end

end DaggerModels.PartII.JTZeroCoskeletonMapping
