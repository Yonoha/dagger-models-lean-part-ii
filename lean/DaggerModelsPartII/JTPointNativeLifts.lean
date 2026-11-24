import DaggerModelsPartII.JTInterpolatedReducedCylinder
import DaggerModelsPartII.JTGraphPointLabel
import DaggerModelsPartII.JTNativeLiftRawComparison
import DaggerModelsPartII.JTRawVertexRecovery

/-! The category of all decorated lifts of a point native source. -/

set_option autoImplicit false
set_option maxHeartbeats 160000
open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTPointNativeLifts

open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
noncomputable section

private abbrev T := NecklaceCode.point
private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary

private def pointTerminal : IsTerminal (T.toSSet : SSet.{0}) :=
  IsTerminal.ofIso SSet.stdSimplex.isTerminalObj₀
    ((eqToIso (congrArg NecklaceCode.toSSet (NecklaceCode.code_eq_point_of_zero (NecklaceCode.single 0) rfl))).symm ≪≫
      NecklaceCode.singleIso 0).symm

private def endpointSection : (T.toSSet : SSet.{0}) ⟶ B :=
  SSet.stdSimplex.isTerminalObj₀.from T.toSSet ≫ SSet.boundary₁.ι₀

private theorem endpointSection_comp :
    endpointSection ≫ endpointInclusion T = 𝟙 T.toSSet :=
  pointTerminal.hom_ext _ _

private def sectionAt (k : SimplexCategory) : T.toSSet ⟶ (value T).obj k :=
  (JTInterpolatedReducedCylinder.slice T k 0).right

/-- The endpoint-reduced cylinder of a point is the point in every parameter degree. -/
private def isoPoint (k : SimplexCategory) : (value T).obj k ≅ T.toSSet where
  hom := augmentation T k
  inv := sectionAt k
  inv_hom_id := JTInterpolatedReducedCylinder.slice_augmentation T k 0
  hom_inv_id := by
    apply (isPushout T k).hom_ext
    · rw [← Category.assoc, augmentation_cylinder, Category.comp_id]
      let s := endpointSection ⊗ₘ 𝟙 (J.obj k)
      have hs : s ≫ (endpointInclusion T ⊗ₘ 𝟙 (J.obj k)) = 𝟙 _ := by
        change (endpointSection ⊗ₘ 𝟙 _) ≫ (endpointInclusion T ⊗ₘ 𝟙 _) = _
        rw [tensorHom_comp_tensorHom, endpointSection_comp, Category.id_comp, tensorHom_id, id_whiskerRight]
      have hc : (cylinder T).app k = s ≫ fst B (J.obj k) ≫ (boundary T).app k := by
        rw [← (isPushout T k).w, ← Category.assoc, hs, Category.id_comp]
      have hh : s ≫ fst B (J.obj k) = fst T.toSSet (J.obj k) ≫ endpointSection :=
        tensorHom_fst _ _
      rw [hc, ← Category.assoc, hh, Category.assoc]
      have hw : endpointInclusion T ≫ sectionAt k = (boundary T).app k :=
        Under.w (JTInterpolatedReducedCylinder.slice T k 0)
      have ht : endpointSection ≫ (boundary T).app k = sectionAt k := by
        rw [← hw, ← Category.assoc, endpointSection_comp, Category.id_comp]
      rw [ht]
    · rw [← Category.assoc, augmentation_boundary, Category.comp_id]
      exact Under.w (JTInterpolatedReducedCylinder.slice T k 0)

private theorem augmentation_endpoints (S : NecklaceCode) (k : SimplexCategory)
    (f : BoundaryNecklaceComma.necklaceUnder.obj T ⟶ (under S).obj k) :
    NecklaceCode.first.{0} S = NecklaceCode.last.{0} S := by
  let g := f.right ≫ augmentation S k
  have hg : endpointInclusion T ≫ g = endpointInclusion S := by
    rw [← Category.assoc]
    have hf : endpointInclusion T ≫ f.right = (boundary S).app k := Under.w f
    rw [hf, augmentation_boundary]
  have h := congrArg (JTEndpointObjects.boundaryHomEquiv S.toSSet) hg
  rw [endpointInclusion, JTGeneralOrderedFiberWeak.orderedBoundary_natural] at h
  change (JTEndpointObjects.boundaryHomEquiv S.toSSet)
    ((JTEndpointObjects.boundaryHomEquiv S.toSSet).symm
      (g.app (op ⦋0⦌) T.first, g.app (op ⦋0⦌) T.last)) =
    (JTEndpointObjects.boundaryHomEquiv S.toSSet)
      ((JTEndpointObjects.boundaryHomEquiv S.toSSet).symm (S.first, S.last)) at h
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact (congrArg Prod.fst h).symm.trans (congrArg Prod.snd h)

/-- A lift from a point into a reduced cylinder forces its decorated code to be a point. -/
private theorem code_eq_point (S : NecklaceCode) (k : SimplexCategory)
    (f : BoundaryNecklaceComma.necklaceUnder.obj T ⟶ (under S).obj k) :
    S = T :=
  NecklaceCode.code_eq_point_of_zero S
    (JTGraphPointLabel.length_eq_zero_of_endpoints_eq S (augmentation_endpoints S k f))

open ReversalDiscreteFreeColimits OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTProjectiveOrderedFiberComparison (row)
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open BoundaryNecklaceComma (necklaceUnder)
open JTNativeLiftRawComparison (composedTarget rawLifts rawLiftsIso)
open JTTargetCommaNativeFibers (lifts)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev F := discreteFree.{0}
private abbrev t := SSet.stdSimplex.isTerminalObj₀.from (T.toSSet : SSet.{0})

variable (W : Source) (x : Vertex W)

private def coefficient : (Δ[0] : SSet.{0}) ⟶ (necklaceLabels W).obj (op T) :=
  zeroPoint W x ≫ diagramMappingPrecomp (F.map t) W

private theorem coefficient_boundary :
    coefficient W x ≫ (necklaceBoundaryRestriction W).app (op T) = boundaryPoint W x x := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst]
    rw [boundaryPoint_first, coefficient, ← Category.assoc]
    change (zeroPoint W x ≫ diagramMappingPrecomp (F.map t) W) ≫
      diagramMappingPrecomp (boundaryNecklace T) W ≫
        diagramMappingPrecomp (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    rw [Category.assoc, ← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
    rw [boundaryNecklace, coprod.inl_desc, ← F.map_comp]
    have ht : SSet.yonedaEquiv.symm T.first ≫ t = 𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht, F.map_id, diagramMappingPrecomp_id, Category.comp_id]
  · simp only [Category.assoc, boundaryMappingIso_snd]
    rw [boundaryPoint_last, coefficient, ← Category.assoc]
    change (zeroPoint W x ≫ diagramMappingPrecomp (F.map t) W) ≫
      diagramMappingPrecomp (boundaryNecklace T) W ≫
        diagramMappingPrecomp (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    rw [Category.assoc, ← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
    rw [boundaryNecklace, coprod.inr_desc, ← F.map_comp]
    have ht : SSet.yonedaEquiv.symm T.last ≫ t = 𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [ht, F.map_id, diagramMappingPrecomp_id, Category.comp_id]

private def canonicalLabel :
    ((orderedNecklaceLabels W (boundaryPoint W x x)).obj (op T)).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (pullback.lift (coefficient W x) (𝟙 _)
    ((coefficient_boundary W x).trans (Category.id_comp _).symm))

private def canonicalIndex : DecoratedNecklaceHomDiagram.Index W x x :=
  OrderedLabelElements.mk W (boundaryPoint W x x) T ⦋0⦌ (canonicalLabel W x)

variable {W x}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W x))
variable (P : Over Q.code)
variable (hP : P.left = T)

private abbrev raw := rawLifts Q P

include hP in
/-- For a point source, an endpoint-preserving map to the raw target
is determined by its first endpoint. -/
private theorem point_hom_ext {A : Under B} {f g : necklaceUnder.obj P.left ⟶ A} :
    f = g := by
  have ht : IsTerminal (P.left.toSSet : SSet.{0}) := hP ▸ pointTerminal
  let e := ht.uniqueUpToIso SSet.stdSimplex.isTerminalObj₀
  apply Under.UnderMorphism.ext
  apply (cancel_epi e.inv).mp
  let u := SSet.boundary₁.ι₀ ≫ (necklaceUnder.obj P.left).hom
  have hu : u = e.inv := ht.hom_ext _ _
  rw [← hu]
  change u ≫ f.right = u ≫ g.right
  dsimp only [u]
  rw [Category.assoc, Category.assoc, Under.w f, Under.w g]

private def canonicalTraversal :
    necklaceUnder.obj P.left ⟶ (underDiagram W x x).obj (canonicalIndex W x) := by
  let s : P.left.toSSet ⟶ T.toSSet := pointTerminal.from _
  refine Under.homMk (s ≫ (isoPoint ⦋0⦌).inv) ?_
  change endpointInclusion P.left ≫ s ≫ (isoPoint ⦋0⦌).inv = (boundary T).app ⦋0⦌
  have hs : endpointInclusion P.left ≫ s = endpointInclusion T := pointTerminal.hom_ext _ _
  rw [← Category.assoc, hs]
  exact Under.w (JTInterpolatedReducedCylinder.slice T ⦋0⦌ 0)

private def canonicalLift : (raw Q P).obj (canonicalIndex W x) :=
  Over.homMk (canonicalTraversal Q P) (point_hom_ext Q P hP)

private def canonicalObject : (raw Q P).Elements :=
  (raw Q P).elementsMk (canonicalIndex W x) (canonicalLift Q P hP)

include hP in
private theorem index_code (i : DecoratedNecklaceHomDiagram.Index W x x)
    (z : (raw Q P).obj i) : OrderedLabelElements.necklace W (boundaryPoint W x x) i = T := by
  have f := z.left
  change necklaceUnder.obj P.left ⟶
    (under (OrderedLabelElements.necklace W (boundaryPoint W x x) i)).obj
      (OrderedLabelElements.degree W (boundaryPoint W x x) i) at f
  exact code_eq_point _ _ (eqToHom (congrArg necklaceUnder.obj hP.symm) ≫ f)

private def toCanonicalIndex (i : DecoratedNecklaceHomDiagram.Index W x x)
    (h : OrderedLabelElements.necklace W (boundaryPoint W x x) i = T) :
    i ⟶ canonicalIndex W x := by
  let b := boundaryPoint W x x
  let L := OrderedLabelElements.labelPresheaf W b
  let k := OrderedLabelElements.degree W b i
  let n := OrderedLabelElements.necklace W b i
  let f : (n, k) ⟶ (T, ⦋0⦌) := (eqToHom h, SimplexCategory.isTerminalZero.from k)
  refine (CategoryOfElements.homMk (L.elementsMk (op (T, ⦋0⦌)) (canonicalLabel W x))
    i.unop f.op ?_).op
  have hn : n.len = 0 := congrArg NecklaceCode.len h
  change ((orderedNecklaceLabels W b).obj (op n)).map (SimplexCategory.isTerminalZero.from k).op
    (((orderedNecklaceLabels W b).map (eqToHom h).op).app (op ⦋0⦌) (canonicalLabel W x)) = _
  exact (JTGraphPointLabel.label_subsingleton W n hn b k).elim _ _

/-- Every complete decorated lift of a point maps uniquely to the degree-zero lift. -/
private def canonicalTerminal : IsTerminal (canonicalObject Q P hP) := by
  let toIndex (a : (raw Q P).Elements) :=
    toCanonicalIndex a.1 (index_code Q P hP a.1 a.2)
  apply IsTerminal.ofUniqueHom (fun a ↦
    CategoryOfElements.homMk a (canonicalObject Q P hP) (toIndex a) (by
      apply Over.OverMorphism.ext
      exact point_hom_ext Q P hP))
  intro a g
  apply CategoryOfElements.ext
  haveI : (OrderedLabelElements.projection W (boundaryPoint W x x)).Faithful := by
    change ((CategoryOfElements.π
      (OrderedLabelElements.labelPresheaf W (boundaryPoint W x x))).leftOp).Faithful
    infer_instance
  change g.val = toIndex a
  apply (OrderedLabelElements.projection W (boundaryPoint W x x)).map_injective
  apply Prod.ext
  · apply NecklaceCode.Hom.ext
    exact pointTerminal.hom_ext _ _
  · exact SimplexCategory.isTerminalZero.hom_ext _ _

section Native

variable {y : Vertex W}
variable (Q' : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (P' : Over.{0, 0} Q'.code)

private theorem endpoints_eq (h : P'.left = T) : x = y := by
  apply JTRawVertexRecovery.rawZeroGeneratorVertex_injective W
  let V := composedTarget Q' P'
  have he : V.code.first = V.code.last := by
    change P'.left.first = P'.left.last
    rw [h]
    rfl
  exact V.first.symm.trans ((congrArg (V.map.app (op ⦋0⦌)) he).trans V.last)

/-- The category of exact lifts of any point native source has weakly contractible nerve. -/
theorem point_GW (h : P'.left = T) : GW (pointMap (nerve (lifts Q' P').Elements)) := by
  obtain rfl := endpoints_eq Q' P' h
  let X := (lifts Q' P').Elements
  let Y := (rawLifts Q' P').Elements
  let v := canonicalObject Q' P' h
  let e := Cat.equivOfIso (Functor.elementsFunctor.mapIso (rawLiftsIso Q' P'))
  let k : Over v ≌ Y := Over.equivalenceOfIsTerminal (canonicalTerminal Q' P' h)
  let p := pointMap (nerve Y)
  haveI : WeakEquivalence (nerveMap k.functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have hp : nerveMap k.functor ≫ p = pointMap (nerve (Over v)) := pointIsTerminal.hom_ext _ _
  haveI : WeakEquivalence (nerveMap k.functor ≫ p) :=
    (weakEquivalence_iff_GW _).mpr (hp.symm ▸ DaggerNativeOverNerveWeakContractibility.point_GW v)
  haveI : WeakEquivalence p := weakEquivalence_of_precomp (nerveMap k.functor) p
  let f : nerve X ⟶ nerve Y := nerveMap e.functor
  haveI : WeakEquivalence f :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e.functor
  have ht : f ≫ p = pointMap (nerve X) := pointIsTerminal.hom_ext _ _
  exact (weakEquivalence_iff_GW _).mp (ht ▸ (weakEquivalence_precomp_iff f p).mpr inferInstance)

/-- The original Theorem C follows from contracting the exact identity lifts
of the positive-length native necklaces. -/
theorem theoremC_of_positive_length_identity_lifts
    (h : ∀ (W : Source),
      (letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
       Localization.localObject SegalLocalizers.localizingFamily W) →
      ∀ (x y : Vertex W) (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)),
        0 < Q.code.len →
        GW (pointMap (nerve (lifts Q (Over.mk (𝟙 Q.code))).Elements))) :
    TheoremCStatement.statement := by
  apply JTNativeLiftRawComparison.theoremC_of_identity_lifts
  intro W hW x y Q
  by_cases hlen : 0 < Q.code.len
  · exact h W hW x y Q hlen
  · exact point_GW Q (Over.mk (𝟙 Q.code))
      (NecklaceCode.code_eq_point_of_zero Q.code (Nat.eq_zero_of_not_pos hlen))

end Native

end
end DaggerModels.PartII.JTPointNativeLifts

