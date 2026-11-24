import DaggerModelsPartII.JTRealizedLabelEndpoints
import DaggerModelsPartII.ReducedCylinder
import DaggerModelsPartII.JTGeneralOrderedFiberWeak

/-!
# The actual realized label descends through the necklace endpoint cylinder

The existing general reduced-cylinder functor is applied to the actual
ordered endpoints of every native necklace. Full parameter constancy at
both original raw vertices gives an actual descended map under that SAME
boundary. No universal rigidified-Hom simplex or weak equivalence follows
from this pushout construction alone.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTNecklaceEndpointCylinder

open JTRealizedLabelEndpoints JTNecklaceLabelRealization
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev J := GroupoidSimplex.parameter
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

/-- The original two native endpoints, as one ordered boundary map. -/
def endpointInclusion (T : NCode) : B ⟶ T.toSSet :=
  JTConeMappingPresentation.orderedBoundary T.toSSet T.first T.last

private theorem endpointInclusion_first (T : NCode) :
    SSet.boundary₁.ι₀ ≫ endpointInclusion T = SSet.yonedaEquiv.symm T.first :=
  SSet.boundary₁.ι₀_desc _ _

private theorem endpointInclusion_last (T : NCode) :
    SSet.boundary₁.ι₁ ≫ endpointInclusion T = SSet.yonedaEquiv.symm T.last :=
  SSet.boundary₁.ι₁_desc _ _

/-- All native necklace maps preserve this SAME ordered boundary. -/
theorem endpointInclusion_natural {T U : NCode} (f : T ⟶ U) :
    endpointInclusion T ≫ f.map = endpointInclusion U := by
  dsimp only [endpointInclusion]
  rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, f.first, f.last]

/-- The accepted reduced cylinder, evaluated on the original groupoid parameter. -/
def value (T : NCode) : SimplexCategory ⥤ SSet.{0} :=
  J ⋙ ReducedCylinder.value (endpointInclusion T)

/-- The uncollapsed necklace-cylinder leg of the SAME pushout. -/
def cylinder (T : NCode) : JTXiEndpointCollapse.parameterProduct T.toSSet ⟶ value T where
  app k := (ReducedCylinder.cylinder (endpointInclusion T)).app (J.obj k)
  naturality {_ _} g :=
    (ReducedCylinder.cylinder (endpointInclusion T)).naturality (J.map g)

/-- The SAME fixed ordered boundary in every parameter degree. -/
def boundary (T : NCode) : (Functor.const SimplexCategory).obj B ⟶ value T where
  app k := (ReducedCylinder.boundary (endpointInclusion T)).app (J.obj k)
  naturality {_ _} g :=
    (ReducedCylinder.boundary (endpointInclusion T)).naturality (J.map g)

/-- The actual cosimplicial necklace cylinder as an object under its boundary. -/
def under (T : NCode) : SimplexCategory ⥤ Under B :=
  Under.lift (value T) (boundary T)

/-- The existing pointwise pushout controls both actual legs. -/
def isPushout (T : NCode) (k : SimplexCategory) :
    IsPushout (endpointInclusion T ⊗ₘ 𝟙 (J.obj k))
      (CartesianMonoidalCategory.fst B (J.obj k))
      ((cylinder T).app k) ((boundary T).app k) :=
  ReducedCylinder.value_isPushout (endpointInclusion T)

/-- The common raw target boundary, with the original zero-generator vertices. -/
def rawBoundary (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) : B ⟶ R W :=
  JTConeMappingPresentation.orderedBoundary (R W)
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
    (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)

private theorem rawBoundary_first (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.boundary₁.ι₀ ≫ rawBoundary W x y = SSet.yonedaEquiv.symm
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) :=
  SSet.boundary₁.ι₀_desc _ _

private theorem rawBoundary_last (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    SSet.boundary₁.ι₁ ≫ rawBoundary W x y = SSet.yonedaEquiv.symm
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y) :=
  SSet.boundary₁.ι₁_desc _ _

/-- The actual ordered label's complete boundary-cylinder equation. -/
theorem realizedLabel_boundary (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (endpointInclusion T ⊗ₘ 𝟙 (J.obj k)) ≫
        realizedNecklaceLabel T W k (orderedLabel W x y T k z) =
      CartesianMonoidalCategory.fst B (J.obj k) ≫ rawBoundary W x y := by
  apply SSet.boundary₁.hom_ext_rightTensor
  · calc
      _ = firstTensor T k ≫
          realizedNecklaceLabel T W k (orderedLabel W x y T k z) := by
        change (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 (J.obj k)) ≫ _ = _
        rw [← Category.assoc, tensorHom_comp_tensorHom]
        rw [Category.id_comp, endpointInclusion_first]
        rfl
      _ = constantRawEndpoint W x k := realizedNecklaceLabel_first W x y T k z
      _ = _ := by
        change _ = (SSet.boundary₁.ι₀ ⊗ₘ 𝟙 (J.obj k)) ≫ _
        rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
        rw [rawBoundary_first]
        rfl
  · calc
      _ = lastTensor T k ≫
          realizedNecklaceLabel T W k (orderedLabel W x y T k z) := by
        change (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 (J.obj k)) ≫ _ = _
        rw [← Category.assoc, tensorHom_comp_tensorHom]
        rw [Category.id_comp, endpointInclusion_last]
        rfl
      _ = constantRawEndpoint W y k := realizedNecklaceLabel_last W x y T k z
      _ = _ := by
        change _ = (SSet.boundary₁.ι₁ ⊗ₘ 𝟙 (J.obj k)) ≫ _
        rw [← Category.assoc, CartesianMonoidalCategory.tensorHom_fst, Category.assoc]
        rw [rawBoundary_last]
        rfl

/-- The actual realized ordered label descends through the existing pushout. -/
def descend (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (value T).obj k ⟶ R W :=
  (isPushout T k).desc
    (realizedNecklaceLabel T W k (orderedLabel W x y T k z))
    (rawBoundary W x y) (realizedLabel_boundary W x y T k z)

/-- Restriction to the cylinder is the SAME original realized label. -/
theorem descend_cylinder (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (cylinder T).app k ≫ descend W x y T k z =
      realizedNecklaceLabel T W k (orderedLabel W x y T k z) :=
  (isPushout T k).inl_desc _ _ _

/-- Restriction to the fixed boundary is the SAME pair of raw vertices. -/
theorem descend_boundary (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (boundary T).app k ≫ descend W x y T k z = rawBoundary W x y :=
  (isPushout T k).inr_desc _ _ _

/-- The descended map is an actual morphism under the SAME ordered boundary. -/
def descendUnder (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    (under T).obj k ⟶ Under.mk (rawBoundary W x y) :=
  Under.homMk (descend W x y T k z) (descend_boundary W x y T k z)

private theorem orderedLabel_map_parameter (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    {k l : SimplexCategory} (g : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    orderedLabel W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map g.op z) =
      (diagramTensor (ReversalDiscreteFreeColimits.discreteFree.obj T.toSSet)).map
        (SSet.stdSimplex.map g) ≫ orderedLabel W x y T l z :=
  congrFun ((pullback.fst
    ((OrderedNecklaceLabelDiagram.necklaceBoundaryRestriction W).app (op T))
      (boundaryPoint W x y)).naturality g.op) z

/-- Descent commutes with EVERY original simplex operator on the parameter. -/
theorem descend_parameter_natural (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NCode)
    {k l : SimplexCategory} (g : k ⟶ l)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    (value T).map g ≫ descend W x y T l z =
      descend W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map g.op z) := by
  apply (isPushout T k).hom_ext
  · rw [← Category.assoc, ← (cylinder T).naturality g, Category.assoc,
      descend_cylinder, descend_cylinder]
    change (𝟙 T.toSSet ⊗ₘ J.map g) ≫
        realizedLabel T.toSSet W l (orderedLabel W x y T l z) = _
    rw [orderedLabel_map_parameter]
    exact realizedLabel_natural_k T.toSSet W g _
  · rw [← Category.assoc, ← (boundary T).naturality g]
    change (𝟙 B ≫ (boundary T).app l) ≫ descend W x y T l z = _
    rw [Category.id_comp, descend_boundary, descend_boundary]

/-- A native necklace map induces the actual map between the two pushouts. -/
def nativeMap {T U : NCode} (f : T ⟶ U) (k : SimplexCategory) :
    (value T).obj k ⟶ (value U).obj k :=
  (isPushout T k).desc
    ((f.map ⊗ₘ 𝟙 (J.obj k)) ≫ (cylinder U).app k) ((boundary U).app k) (by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
        endpointInclusion_natural]
      exact (isPushout U k).w)

/-- The map retains the SAME uncollapsed cylinder leg. -/
theorem nativeMap_cylinder {T U : NCode} (f : T ⟶ U) (k : SimplexCategory) :
    (cylinder T).app k ≫ nativeMap f k =
      (f.map ⊗ₘ 𝟙 (J.obj k)) ≫ (cylinder U).app k :=
  (isPushout T k).inl_desc _ _ _

/-- The native map fixes the common ordered boundary. -/
theorem nativeMap_boundary {T U : NCode} (f : T ⟶ U) (k : SimplexCategory) :
    (boundary T).app k ≫ nativeMap f k = (boundary U).app k :=
  (isPushout T k).inr_desc _ _ _

/-- Every native cylinder map is natural for ALL parameter operators. -/
theorem nativeMap_parameter_natural {T U : NCode} (f : T ⟶ U)
    {k l : SimplexCategory} (g : k ⟶ l) :
    (value T).map g ≫ nativeMap f l = nativeMap f k ≫ (value U).map g := by
  apply (isPushout T k).hom_ext
  · have hi : (𝟙 T.toSSet ⊗ₘ J.map g) ≫ (f.map ⊗ₘ 𝟙 (J.obj l)) =
        (f.map ⊗ₘ 𝟙 (J.obj k)) ≫ (𝟙 U.toSSet ⊗ₘ J.map g) := by
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    calc
      _ = (𝟙 T.toSSet ⊗ₘ J.map g) ≫
          ((f.map ⊗ₘ 𝟙 (J.obj l)) ≫ (cylinder U).app l) := by
        rw [← Category.assoc, ← (cylinder T).naturality g,
          Category.assoc, nativeMap_cylinder]
        rfl
      _ = (f.map ⊗ₘ 𝟙 (J.obj k)) ≫
          ((𝟙 U.toSSet ⊗ₘ J.map g) ≫ (cylinder U).app l) := by
        rw [← Category.assoc, hi, Category.assoc]
      _ = (f.map ⊗ₘ 𝟙 (J.obj k)) ≫
          ((cylinder U).app k ≫ (value U).map g) := by
        have hn := (cylinder U).naturality g
        change (𝟙 U.toSSet ⊗ₘ J.map g) ≫ (cylinder U).app l =
          (cylinder U).app k ≫ (value U).map g at hn
        exact congrArg (fun h ↦ (f.map ⊗ₘ 𝟙 (J.obj k)) ≫ h) hn
      _ = _ := by
        simpa only [Category.assoc] using
          congrArg (fun h ↦ h ≫ (value U).map g) (nativeMap_cylinder f k).symm
  · rw [← Category.assoc, ← (boundary T).naturality g,
      ← Category.assoc, nativeMap_boundary, ← (boundary U).naturality g]
    change (𝟙 B ≫ (boundary T).app l) ≫ nativeMap f l =
      𝟙 B ≫ (boundary U).app l
    rw [Category.id_comp, Category.id_comp, nativeMap_boundary]

/-- The native cylinder map of the identity is the identity. -/
theorem nativeMap_id (T : NCode) (k : SimplexCategory) :
    nativeMap (𝟙 T) k = 𝟙 ((value T).obj k) := by
  apply (isPushout T k).hom_ext
  · rw [nativeMap_cylinder, Category.comp_id]
    change (𝟙 T.toSSet ⊗ₘ 𝟙 (J.obj k)) ≫ (cylinder T).app k = _
    simp
  · rw [nativeMap_boundary, Category.comp_id]

/-- Native composition is literal composition of the SAME pushout maps. -/
theorem nativeMap_comp {T U V : NCode} (f : T ⟶ U) (g : U ⟶ V)
    (k : SimplexCategory) :
    nativeMap (f ≫ g) k = nativeMap f k ≫ nativeMap g k := by
  apply (isPushout T k).hom_ext
  · rw [nativeMap_cylinder, ← Category.assoc, nativeMap_cylinder,
      Category.assoc, nativeMap_cylinder, ← Category.assoc, tensorHom_comp_tensorHom,
      Category.id_comp]
    rfl
  · rw [nativeMap_boundary, ← Category.assoc, nativeMap_boundary, nativeMap_boundary]

private theorem orderedLabel_map_native (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) {T U : NCode} (f : T ⟶ U)
    (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op U)).obj (op k)) :
    orderedLabel W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app (op k) z) =
      Functor.whiskerRight (ReversalDiscreteFreeColimits.discreteFree.map f.map)
        (tensorRight (SSet.stdSimplex.obj k)) ≫ orderedLabel W x y U k z := by
  have h :
      (orderedNecklaceLabels W (boundaryPoint W x y)).map f.op ≫
        pullback.fst
          ((OrderedNecklaceLabelDiagram.necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y) =
      pullback.fst
          ((OrderedNecklaceLabelDiagram.necklaceBoundaryRestriction W).app (op U))
          (boundaryPoint W x y) ≫
        (OrderedNecklaceLabelDiagram.necklaceLabels W).map f.op := by
    simp only [OrderedNecklaceLabelDiagram.orderedNecklaceLabels,
      OrderedNecklaceLabelDiagram.orderedLabelDiagram, pullback.map, pullback.lift_fst]
  exact congrFun (NatTrans.congr_app h (op k)) z

/-- Descent respects every native endpoint-preserving map, including collapses. -/
theorem descend_native_natural (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) {T U : NCode} (f : T ⟶ U)
    (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op U)).obj (op k)) :
    nativeMap f k ≫ descend W x y U k z =
      descend W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app (op k) z) := by
  apply (isPushout T k).hom_ext
  · rw [← Category.assoc, nativeMap_cylinder, Category.assoc,
      descend_cylinder, descend_cylinder]
    rw [orderedLabel_map_native]
    exact realizedLabel_natural_X f.map W k _
  · rw [← Category.assoc, nativeMap_boundary, descend_boundary, descend_boundary]

end

end DaggerModels.PartII.JTNecklaceEndpointCylinder
