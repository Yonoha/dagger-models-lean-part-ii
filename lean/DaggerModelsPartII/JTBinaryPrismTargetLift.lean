import DaggerModelsPartII.JTBinaryPrismParameter
import DaggerModelsPartII.JTBinaryPrismRealization
import DaggerModelsPartII.JTDecoratedIntervalEndpoint
import DaggerModelsPartII.NecklaceCylinderAugmentation
import DaggerModelsPartII.JTBinaryPrismOverlap
import DaggerModelsPartII.JTHigherMixedGraphTargetLift

/-!
# Binary prism comparisons over the native wedge
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismTargetLift

open JTProjectiveOrderedFiberComparison JTOrderedLabelBinaryGlue OrderedNecklaceVertexPoints
open OrderedNecklaceLabelDiagram JTRealizedLabelEndpoints
open JTNecklaceEndpointCylinder NecklaceCylinderAugmentation
open JTBinaryPrismRealization JTParameterBlocks
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev A := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode} {k l n : SimplexCategory}
variable (a : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k))
variable (b : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op l))
variable (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)

/-- The whole joined parameter in the common ordinal, including the entire
connector over time. -/
def parameter : (code T U).toSSet ⊗ J.obj n ⟶ J.obj (common k l) :=
  JTBinaryPrismParameter.parameter T U (common k l) (J.obj n)
    (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l))

/-- The original ordered label of the joined binary comparison. -/
def index : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code T U) (common k l)
    (orderedTriplePoint (blockInputs a b))

/-- The whole comparison into the original decorated cylinder, before
collapsing the two outside boundary components of the source. -/
def productMap : (code T U).toSSet ⊗ J.obj n ⟶ (value (code T U)).obj (common k l) :=
  lift (fst (code T U).toSSet (J.obj n)) (parameter s t) ≫ (cylinder (code T U)).app (common k l)

set_option maxHeartbeats 800000 in
private theorem productMap_boundary :
    (endpointInclusion (code T U) ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t =
      fst JTXiEndpointCollapse.boundary (J.obj n) ≫ (boundary (code T U)).app (common k l) := by
  let e := endpointInclusion (code T U)
  let g := lift (fst JTXiEndpointCollapse.boundary (J.obj n))
    ((e ⊗ₘ 𝟙 (J.obj n)) ≫ parameter s t)
  have h : (e ⊗ₘ 𝟙 (J.obj n)) ≫ lift (fst (code T U).toSSet (J.obj n)) (parameter s t) =
      g ≫ (e ⊗ₘ 𝟙 (J.obj (common k l))) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [g, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc]
    · simp only [g, Category.assoc, tensorHom_snd, lift_snd, Category.comp_id]
  unfold productMap
  rw [← Category.assoc, h, Category.assoc, (isPushout (code T U) (common k l)).w,
    ← Category.assoc]
  dsimp only [g]
  rw [lift_fst]

/-- The two original outer ends are collapsed in the entire source
cylinder. The connector retains the complete comparison. -/
def cylinderMap : (value (code T U)).obj n ⟶ (value (code T U)).obj (common k l) :=
  (isPushout (code T U) n).desc (productMap s t) ((boundary (code T U)).app (common k l))
    (productMap_boundary s t)

theorem cylinderMap_cylinder :
    (cylinder (code T U)).app n ≫ cylinderMap s t = productMap s t :=
  (isPushout (code T U) n).inl_desc _ _ _

theorem cylinderMap_boundary :
    (boundary (code T U)).app n ≫ cylinderMap s t = (boundary (code T U)).app (common k l) :=
  (isPushout (code T U) n).inr_desc _ _ _

/-- Restriction along a time operator keeps the whole joined parameter. -/
theorem parameter_mapTime {m : SimplexCategory} (j : m ⟶ n) :
    (𝟙 (code T U).toSSet ⊗ₘ J.map j) ≫ parameter s t =
      parameter ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ s) ((𝟙 U.toSSet ⊗ₘ J.map j) ≫ t) := by
  unfold parameter
  simpa only [Category.assoc] using
    JTBinaryPrismParameter.parameter_mapTime T U (common k l) (J.obj n)
      (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l)) (J.map j)

/-- The full product comparison restricts to the joined restrictions. -/
theorem productMap_mapTime {m : SimplexCategory} (j : m ⟶ n) :
    (𝟙 (code T U).toSSet ⊗ₘ J.map j) ≫ productMap s t =
      productMap ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ s) ((𝟙 U.toSSet ⊗ₘ J.map j) ≫ t) := by
  have h : (𝟙 (code T U).toSSet ⊗ₘ J.map j) ≫
      lift (fst (code T U).toSSet (J.obj n)) (parameter s t) =
      lift (fst (code T U).toSSet (J.obj m))
        (parameter ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ s) ((𝟙 U.toSSet ⊗ₘ J.map j) ≫ t)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · rw [Category.assoc, lift_snd, parameter_mapTime]
      exact (lift_snd _ _).symm
  unfold productMap
  rw [← Category.assoc, h]

/-- Restriction of the actual reduced comparison preserves the complete
cylinder map and the two ordered ends. -/
theorem cylinderMap_mapTime {m : SimplexCategory} (j : m ⟶ n) :
    (value (code T U)).map j ≫ cylinderMap s t =
      cylinderMap ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ s) ((𝟙 U.toSSet ⊗ₘ J.map j) ≫ t) := by
  have hC : (𝟙 (code T U).toSSet ⊗ₘ J.map j) ≫ (cylinder (code T U)).app n =
      (cylinder (code T U)).app m ≫ (value (code T U)).map j :=
    (cylinder (code T U)).naturality j
  have hB : (boundary (code T U)).app m ≫ (value (code T U)).map j =
      (boundary (code T U)).app n := by
    rw [← (boundary (code T U)).naturality j]
    exact Category.id_comp _
  apply (isPushout (code T U) m).hom_ext
  · rw [← Category.assoc, ← hC, Category.assoc, cylinderMap_cylinder,
      cylinderMap_cylinder, productMap_mapTime]
  · rw [← Category.assoc, hB, cylinderMap_boundary, cylinderMap_boundary]

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable (c : T ⟶ P.code) (e : U ⟶ Q.code)

private abbrev hsType := realizeProduct W k s (orderedLabel W x z T k a) =
  fst T.toSSet (J.obj n) ≫ c.map ≫ P.map

private abbrev htType := realizeProduct W l t (orderedLabel W z y U l b) =
  fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map

/-- The full raw equality before imposing the two outside boundary identifications. -/
theorem productMap_raw (hs : hsType a s c) (ht : htType b t e) :
    productMap s t ≫ ((underCocone W x y).app (index a b)).right =
      fst (code T U).toSSet (J.obj n) ≫ (collapse c e).map ≫ (NecklacesOver.wedge P Q).map := by
  change (lift _ (parameter s t) ≫ (cylinder (code T U)).app (common k l)) ≫
    descend W x y (code T U) (common k l) (orderedTriplePoint (blockInputs a b)) = _
  rw [Category.assoc, descend_cylinder]
  exact raw_over_wedge a b (parameter s t) c e s t
    (JTBinaryPrismParameter.parameter_left _ _ _ _ _ _)
    (JTBinaryPrismParameter.parameter_right _ _ _ _ _ _) hs ht

/-- The full raw equality on the actual reduced cylinder. -/
theorem cylinderMap_raw (hs : hsType a s c) (ht : htType b t e) :
    cylinderMap s t ≫ ((underCocone W x y).app (index a b)).right =
      augmentation (code T U) n ≫ (collapse c e).map ≫ (NecklacesOver.wedge P Q).map := by
  apply (isPushout (code T U) n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, ← Category.assoc ((cylinder _).app n),
      augmentation_cylinder]
    exact productMap_raw a b s t c e hs ht
  · change (boundary (code T U)).app n ≫ cylinderMap s t ≫
        descend W x y (code T U) (common k l) (orderedTriplePoint (blockInputs a b)) = _
    rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((boundary _).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion _), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, (NecklacesOver.wedge P Q).first,
      (NecklacesOver.wedge P Q).last]
    rfl

private def decoratedMap :
    (under (code T U)).obj n ⟶ (underDiagram W x y).obj (index a b) :=
  Under.homMk (cylinderMap s t) (cylinderMap_boundary s t)

private def nativeMap :
    (under (code T U)).obj n ⟶ necklaceUnder.obj (NecklacesOver.wedge P Q).code :=
  Under.homMk (augmentation (code T U) n ≫ (collapse c e).map) (by
    change (boundary (code T U)).app n ≫ augmentation (code T U) n ≫ (collapse c e).map =
      endpointInclusion (NecklacesOver.wedge P Q).code
    rw [← Category.assoc, augmentation_boundary, endpointInclusion_natural])

/-- The binary prism lifts into the actual decorated pullback over the
native wedge. Its native projection is the original augmentation and
collapse, while its decorated projection is the whole cylinder map. -/
def targetLift (hs : hsType a s c) (ht : htType b t e) :
    (under (code T U)).obj n ⟶
      (JTTargetCommaPullback.diagram W x y (NecklacesOver.wedge P Q)).obj (index a b) :=
  pullback.lift (decoratedMap a b s t) (nativeMap c e (n := n)) (by
    apply Under.UnderMorphism.ext
    exact cylinderMap_raw a b s t c e hs ht)

theorem targetLift_decorated (hs : hsType a s c) (ht : htType b t e) :
    (targetLift a b s t c e hs ht ≫
      JTTargetCommaPullback.fst W x y (NecklacesOver.wedge P Q) (index a b)).right =
      cylinderMap s t := by
  have h : targetLift a b s t c e hs ht ≫
      JTTargetCommaPullback.fst W x y (NecklacesOver.wedge P Q) (index a b) =
        decoratedMap a b s t := pullback.lift_fst _ _ _
  exact congrArg (fun u ↦ u.right) h

theorem targetLift_native (hs : hsType a s c) (ht : htType b t e) :
    (targetLift a b s t c e hs ht ≫
      JTTargetCommaPullback.snd W x y (NecklacesOver.wedge P Q) (index a b)).right =
      augmentation (code T U) n ≫ (collapse c e).map := by
  have h : targetLift a b s t c e hs ht ≫
      JTTargetCommaPullback.snd W x y (NecklacesOver.wedge P Q) (index a b) =
        nativeMap c e (n := n) := pullback.lift_snd _ _ _
  exact congrArg (fun u ↦ u.right) h

open JTDecoratedIntervalMapping JTBinaryPrismOverlap
open JTTargetIntervalGluing

private abbrev nativeSource : Over (NecklacesOver.wedge P Q).code :=
  Over.mk (collapse c e)

private abbrev cut := JTBinaryPrismOverlap.joint P.code Q.code

/-- The exact comparison is a point of the existing space of full lifts
over the entire native target. -/
def wholePoint (hs : hsType a s c) (ht : htType b t e) :
    (whole W x y (NecklacesOver.wedge P Q) J (nativeSource c e) (index a b)).obj (op n) :=
  Over.homMk (productMap s t) (productMap_raw a b s t c e hs ht)

/-- At the native cut, the two restricted comparisons agree on the full
source overlap inside the very same decorated cylinder. -/
theorem cut_agreement (hs : hsType a s c) (ht : htType b t e) :
    let S := nativeSource c e
    let i := index a b
    let j := cut (P := P) (Q := Q)
    let m := wholePoint a b s t c e hs ht
    (leftToOverlap W x y (NecklacesOver.wedge P Q) J S j i).app (op n)
        ((toLeft W x y (NecklacesOver.wedge P Q) J S j i).app (op n) m) =
      (rightToOverlap W x y (NecklacesOver.wedge P Q) J S j i).app (op n)
        ((toRight W x y (NecklacesOver.wedge P Q) J S j i).app (op n) m) :=
  congrFun (NatTrans.congr_app
    (JTDecoratedIntervalMapping.isPullback W x y (NecklacesOver.wedge P Q) J
      (nativeSource c e) (cut (P := P) (Q := Q)) (index a b)).w (op n))
    (wholePoint a b s t c e hs ht)


set_option maxHeartbeats 600000 in
/-- Two actual decorated comparisons over the same binary collapse agree
on the complete overlap when their side parameters agree on both plateaus. -/
theorem cut_eq_of_side_plateaus
    {s' : T.toSSet ⊗ J.obj n ⟶ J.obj k}
    {t' : U.toSSet ⊗ J.obj n ⟶ J.obj l}
    (hs : hsType a s c) (ht : htType b t e)
    (hs' : hsType a s' c) (ht' : htType b t' e)
    (hL : (middleInclusion c ⟨Fin.last P.code.len, P.code.last_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ s =
      (middleInclusion c ⟨Fin.last P.code.len, P.code.last_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ s')
    (hR : (middleInclusion e ⟨0, Q.code.first_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ t =
      (middleInclusion e ⟨0, Q.code.first_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ t') :
    let S := nativeSource c e
    let i := index a b
    let j := cut (P := P) (Q := Q)
    let restrict := (toLeft W x y (NecklacesOver.wedge P Q) J S j i) ≫
      (leftToOverlap W x y (NecklacesOver.wedge P Q) J S j i)
    restrict.app (op n) (wholePoint a b s t c e hs ht) =
      restrict.app (op n) (wholePoint a b s' t' c e hs' ht') := by
  dsimp only
  apply Over.OverMorphism.ext
  let j := cut (P := P) (Q := Q)
  let i := middleInclusion (collapse c e) j
  have hL' :
      (middleInclusion c ⟨Fin.last P.code.len, P.code.last_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫
          (s ≫ J.map (leftIn k l)) =
      (middleInclusion c ⟨Fin.last P.code.len, P.code.last_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫
          (s' ≫ J.map (leftIn k l)) := by
    rw [← Category.assoc, ← Category.assoc, hL]
  have hR' :
      (middleInclusion e ⟨0, Q.code.first_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ (t ≫ J.map (rightIn k l)) =
      (middleInclusion e ⟨0, Q.code.first_mem⟩ ⊗ₘ 𝟙 (J.obj n)) ≫ (t' ≫ J.map (rightIn k l)) := by
    rw [← Category.assoc, ← Category.assoc, hR]
  have hp : (i ⊗ₘ 𝟙 (J.obj n)) ≫ parameter s t =
      (i ⊗ₘ 𝟙 (J.obj n)) ≫ parameter s' t' :=
    overlapParameter_eq_of_plateaus c e (common k l) (J.obj n) _ _ hL' hR'
  change
    (middleLeft (collapse c e) j ⊗ₘ 𝟙 (J.obj n)) ≫
        (leftInclusion (collapse c e) j ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t =
      (middleLeft (collapse c e) j ⊗ₘ 𝟙 (J.obj n)) ≫
        (leftInclusion (collapse c e) j ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s' t'
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, middleLeft_fac]
  change (i ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t =
    (i ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s' t'
  unfold productMap
  simp only [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst]
  · simpa only [Category.assoc, lift_snd] using hp

/-- The full overlap comparison restricts on its embedded connector to
the prescribed binary prism on the whole connector, in every time degree. -/
theorem cut_on_connector (hs : hsType a s c) (ht : htType b t e) :
    let S := nativeSource c e
    let i := index a b
    let j := cut (P := P) (Q := Q)
    let m := wholePoint a b s t c e hs ht
    (connectorFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
        ((leftToOverlap W x y (NecklacesOver.wedge P Q) J S j i).app (op n)
          ((toLeft W x y (NecklacesOver.wedge P Q) J S j i).app (op n) m)).left =
      (tripleRightU T A U ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t := by
  change (connectorFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
    (middleLeft (collapse c e) (cut (P := P) (Q := Q)) ⊗ₘ 𝟙 (J.obj n)) ≫
    (leftInclusion (collapse c e) (cut (P := P) (Q := Q)) ⊗ₘ 𝟙 (J.obj n)) ≫
      productMap s t = _
  simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  rw [Category.assoc (connectorFactor c e), middleLeft_fac, connectorFactor_fac]

/-- The left comparison on the entire preimage interval retains the
given left comparison on its original side. -/
theorem cut_on_left (hs : hsType a s c) (ht : htType b t e) :
    (leftFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
        ((toLeft W x y (NecklacesOver.wedge P Q) J (nativeSource c e) (cut (P := P) (Q := Q))
          (index a b)).app (op n) (wholePoint a b s t c e hs ht)).left =
      lift (fst T.toSSet (J.obj n) ≫ tripleRightT T A U)
        (s ≫ J.map (leftIn k l)) ≫ (cylinder (code T U)).app (common k l) := by
  change (leftFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
    (leftInclusion (collapse c e) (cut (P := P) (Q := Q)) ⊗ₘ 𝟙 (J.obj n)) ≫
      productMap s t = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, leftFactor_fac]
  unfold productMap
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, tensorHom_fst]
  · rw [Category.assoc, lift_snd]
    calc
      (tripleRightT T A U ⊗ₘ 𝟙 (J.obj n)) ≫ parameter s t =
          s ≫ J.map (leftIn k l) := JTBinaryPrismParameter.parameter_left _ _ _ _ _ _
      _ = _ := (lift_snd _ _).symm

/-- The right comparison on the entire preimage interval retains the
given right comparison on its original side. -/
theorem cut_on_right (hs : hsType a s c) (ht : htType b t e) :
    (rightFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
        ((toRight W x y (NecklacesOver.wedge P Q) J (nativeSource c e) (cut (P := P) (Q := Q))
          (index a b)).app (op n) (wholePoint a b s t c e hs ht)).left =
      lift (fst U.toSSet (J.obj n) ≫ tripleRightV T A U)
        (t ≫ J.map (rightIn k l)) ≫ (cylinder (code T U)).app (common k l) := by
  change (rightFactor c e ⊗ₘ 𝟙 (J.obj n)) ≫
    (rightInclusion (collapse c e) (cut (P := P) (Q := Q)) ⊗ₘ 𝟙 (J.obj n)) ≫
      productMap s t = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, rightFactor_fac]
  unfold productMap
  rw [← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, tensorHom_fst]
  · rw [Category.assoc, lift_snd]
    calc
      (tripleRightV T A U ⊗ₘ 𝟙 (J.obj n)) ≫ parameter s t =
          t ≫ J.map (rightIn k l) := JTBinaryPrismParameter.parameter_right _ _ _ _ _ _
      _ = _ := (lift_snd _ _).symm

private theorem productMap_endpoint
    (i : Δ[0] ⟶ JTXiEndpointCollapse.boundary) :
    ((i ≫ endpointInclusion (code T U)) ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t =
      fst (Δ[0] : SSet.{0}) (J.obj n) ≫ i ≫ (boundary (code T U)).app (common k l) := by
  have h :
      (i ⊗ₘ 𝟙 (J.obj n)) ≫ (endpointInclusion (code T U) ⊗ₘ 𝟙 (J.obj n)) =
        (i ≫ endpointInclusion (code T U)) ⊗ₘ 𝟙 (J.obj n) := by
    rw [tensorHom_comp_tensorHom, Category.id_comp]
  rw [← h, Category.assoc, productMap_boundary, ← Category.assoc, tensorHom_fst, Category.assoc]

private theorem boundary_first (C : NecklaceCode) :
    SSet.boundary₁.ι₀ ≫ endpointInclusion C = pointAt C (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc C.first C.last = _
  rw [SSet.boundary₁.ι₀_desc]
  rfl

private theorem boundary_last (C : NecklaceCode) :
    SSet.boundary₁.ι₁ ≫ endpointInclusion C = pointAt C (ULift.up (Fin.last C.len)) := by
  change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc C.first C.last = _
  rw [SSet.boundary₁.ι₁_desc]
  rfl

/-- The sides of the binary comparison lie in the existing endpoint-fixed
pullback. The two full interval restrictions determine a unique whole
comparison over the original raw map. -/
theorem cut_glues (hs : hsType a s c) (ht : htType b t e) :
    let V := NecklacesOver.wedge P Q
    let S := nativeSource c e
    let i := index a b
    let j := cut (P := P) (Q := Q)
    let m := wholePoint a b s t c e hs ht
    ∃! v : (whole W x y V J S i).obj (op n),
      (toLeft W x y V J S j i).app (op n) v =
        (toLeft W x y V J S j i).app (op n) m ∧
      (toRight W x y V J S j i).app (op n) v =
        (toRight W x y V J S j i).app (op n) m ∧
      (pointAt S.left (ULift.up 0) ⊗ₘ 𝟙 (J.obj n)) ≫ v.left =
        fst (Δ[0] : SSet.{0}) (J.obj n) ≫ cylinderFirst W x y i ∧
      (pointAt S.left (ULift.up (Fin.last S.left.len)) ⊗ₘ 𝟙 (J.obj n)) ≫ v.left =
        fst (Δ[0] : SSet.{0}) (J.obj n) ≫ cylinderLast W x y i := by
  dsimp only
  let V := NecklacesOver.wedge P Q
  let S := nativeSource c e
  let i := index a b
  let j := cut (P := P) (Q := Q)
  let m := wholePoint a b s t c e hs ht
  apply existsUnique_glue W x y V J S j i n
    ((toLeft W x y V J S j i).app (op n) m)
    ((toRight W x y V J S j i).app (op n) m) (cut_agreement a b s t c e hs ht)
  · rw [first_restrict]
    change (pointAt (code T U) (ULift.up 0) ⊗ₘ 𝟙 (J.obj n)) ≫ productMap s t =
      fst (Δ[0] : SSet.{0}) (J.obj n) ≫ SSet.boundary₁.ι₀ ≫ (boundary (code T U)).app (common k l)
    rw [← boundary_first]
    exact productMap_endpoint s t SSet.boundary₁.ι₀
  · rw [last_restrict]
    change (pointAt (code T U) (ULift.up (Fin.last (code T U).len)) ⊗ₘ 𝟙 (J.obj n)) ≫
      productMap s t = fst (Δ[0] : SSet.{0}) (J.obj n) ≫
        SSet.boundary₁.ι₁ ≫ (boundary (code T U)).app (common k l)
    rw [← boundary_last]
    exact productMap_endpoint s t SSet.boundary₁.ι₁

section MixedGraphSides

open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement
open JTHigherInterleavedParameter (ret slice vertical)
open JTHigherGroupoidParameterPrism (paired)

private abbrev simplex (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m

/-- The side parameter of the checked higher mixed graph prism. -/
def mixedSideParameter {d : ℕ} {k : SimplexCategory} (s : simplex ⦋d⦌ ⟶ J.obj k)
    (n : SimplexCategory) :
    (MixedGraphCylinderTraversal.code d).toSSet ⊗ J.obj n ⟶
      J.obj (JTHigherInterleavedParameter.common k n) :=
  (nativeGraphParameter s ⊗ₘ 𝟙 (J.obj n)) ≫ paired k n

/-- A higher mixed graph comparison is an admissible entire side of
the binary construction, with its original target and collapse. -/
theorem mixedSide_raw {d : ℕ} {k n : SimplexCategory} {W : Source} {x y : Vertex W}
    (f : simplex k ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
    {q : (single d).toSSet ⟶ Raw W}
    (hq : nativeRawGraph W d k f s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (E : EdgeFamilies W ⦋d⦌ (JTHigherInterleavedParameter.common k n)
      (SSet.stdSimplex.map (ret k n) ≫ f) (s ≫ J.map (slice k n 0)) x y)
    (hL : SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (vertical k n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    realizeProduct W (JTHigherInterleavedParameter.common k n) (mixedSideParameter s n)
        (orderedLabel W x y (MixedGraphCylinderTraversal.code d)
          (JTHigherInterleavedParameter.common k n) (JTMixedGraphOrderedLabel.orderedPoint E)) =
      fst (MixedGraphCylinderTraversal.code d).toSSet (J.obj n) ≫
        (MixedGraphCylinderTraversal.collapseOuter d).map ≫ q := by
  have h := congrArg (fun u ↦ (cylinder (MixedGraphCylinderTraversal.code d)).app n ≫ u)
    (JTHigherMixedGraphTargetLift.whole_raw f s hq qx qy E hL hR)
  dsimp only at h
  rw [JTHigherMixedGraphPrismRealization.productRaw_cylinder,
    ← Category.assoc ((cylinder (MixedGraphCylinderTraversal.code d)).app n),
    augmentation_cylinder] at h
  exact h

end MixedGraphSides

end

end DaggerModels.PartII.JTBinaryPrismTargetLift
