import DaggerModelsPartII.JTRawOrdinaryAdjoint
import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTCylinderCEComparison

/-!
# The raw ordinary unit on the original one-edge CE interval

This scratch module calibrates the literal raw transpose at the original
projective-image endpoints. The native-necklace single-edge descent and its
comparison to the literal CE pushout require a separate boundary-preserving
bridge; no weakness assertion is made here.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRawUnitCylinderCalibration

open JTRawFreeInnerComparison JTRawOrdinaryAdjoint
open JTStrictificationMaps JTStrictificationCoefficients
open JTProjectiveOrderedFiberComparison (row endpointArrow point)
open JTGtildeOrderedFiberAction (sourceRow targetVertices)
open JTRightAdjointOrderedFiber OrdinaryJTRealization JTReversalInput
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalFlagFlankification
open JTNecklaceEndpointCylinder
open JTRealizedLabelEndpoints

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The actual native single-edge boundary is carried to the literal CE
boundary by the canonical one-bead simplex isomorphism. -/
theorem singleBoundary_to_interval :
    endpointInclusion (single 1) ≫ (singleIso 1).hom =
      JTCylinderFrame.j := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc
      (single 1).first (single 1).last) ≫ (singleIso 1).hom = _
    rw [SSet.boundary₁.ι₀_desc]
    change SSet.yonedaEquiv.symm (single 1).first ≫
      (singleIso 1).hom = SSet.boundary₁.ι₀ ≫ JTCylinderFrame.j
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, singleIso_first]
    change _ = SSet.yonedaEquiv
      (SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι)
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    rfl
  · rw [← Category.assoc]
    change (SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc
      (single 1).first (single 1).last) ≫ (singleIso 1).hom = _
    rw [SSet.boundary₁.ι₁_desc]
    change SSet.yonedaEquiv.symm (single 1).last ≫
      (singleIso 1).hom = SSet.boundary₁.ι₁ ≫ JTCylinderFrame.j
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, singleIso_last]
    change _ = SSet.yonedaEquiv
      (SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι)
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    rfl

/-- The native single-edge endpoint cylinder maps to the ACTUAL CE
pushout, using both coprojections and the ordered boundary square. -/
def singleCylinderToCE (k : SimplexCategory) :
    (value (single 1)).obj k ⟶ JTXiEndpointCollapse.CE.obj k :=
  (isPushout (single 1) k).desc
    (((singleIso 1).hom ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
      JTXiEndpointCollapse.CE_interval.app k)
    (JTXiEndpointCollapse.CE_boundary.app k) (by
      have hCE : IsPushout
          (JTXiEndpointCollapse.cylinderInclusion.app k)
          (JTXiEndpointCollapse.cylinderProjection.app k)
          (JTXiEndpointCollapse.CE_interval.app k)
          (JTXiEndpointCollapse.CE_boundary.app k) :=
        (IsPushout.of_hasPushout
          JTXiEndpointCollapse.cylinderInclusion
          JTXiEndpointCollapse.cylinderProjection).map
          ((evaluation SimplexCategory SSet.{0}).obj k)
      calc
        (endpointInclusion (single 1) ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj k)) ≫
            ((singleIso 1).hom ⊗ₘ
              𝟙 (GroupoidSimplex.parameter.obj k)) ≫
              JTXiEndpointCollapse.CE_interval.app k =
          (JTCylinderFrame.j ⊗ₘ
            𝟙 (GroupoidSimplex.parameter.obj k)) ≫
              JTXiEndpointCollapse.CE_interval.app k := by
            rw [← Category.assoc, tensorHom_comp_tensorHom,
              Category.id_comp, singleBoundary_to_interval]
        _ = CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary
              (GroupoidSimplex.parameter.obj k) ≫
              JTXiEndpointCollapse.CE_boundary.app k := hCE.w)

theorem singleCylinderToCE_cylinder (k : SimplexCategory) :
    (cylinder (single 1)).app k ≫ singleCylinderToCE k =
      ((singleIso 1).hom ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        JTXiEndpointCollapse.CE_interval.app k :=
  (isPushout (single 1) k).inl_desc _ _ _

theorem singleCylinderToCE_boundary (k : SimplexCategory) :
    (boundary (single 1)).app k ≫ singleCylinderToCE k =
      JTXiEndpointCollapse.CE_boundary.app k :=
  (isPushout (single 1) k).inr_desc _ _ _

/-- The ACTUAL descended native single-edge label evaluates on every
box generator by the original raw two-index coend generator. This uses
the native ordered label, before any ambient-simplex substitution. -/
theorem singleDescend_generator (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (k m l : SimplexCategory)
    (z : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W
      (OrderedNecklaceVertexPoints.boundaryPoint W x y)).obj
        (op (single 1))).obj (op k))
    (a : (single 1).toSSet.obj (op m))
    (β : (SSet.stdSimplex.obj k).obj (op l)) :
    (SSet.yonedaEquiv.symm a ⊗ₘ
        GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv β)) ≫
      (cylinder (single 1)).app k ≫ descend W x y (single 1) k z =
        JTRealizationGenerators.generator (ordinaryInput.obj W) (m, l)
          (((orderedLabel W x y (single 1) k z).app
            (op (ReverseSimplex.inclusion.obj m))).app (op l)
              (((freeDaggerAdjunction.unit.app (single 1).toSSet).app
                (op m) a), β)) := by
  rw [descend_cylinder]
  exact JTNecklaceLabelRealization.realizedLabel_generator_formula
    (single 1).toSSet W k m l
    (orderedLabel W x y (single 1) k z) a β

/-- The raw transpose evaluates the actual raw free-inner unit after the
original two-index realization generator. -/
theorem gRawTilde_generator (W : Source)
    (q : OrdinaryJTRealization.Index)
    (w : (ordinaryInput.obj W).obj (op q)) :
    (gRawTilde W).app (op q) w =
      ULift.up
        (JTRealizationGenerators.generator (ordinaryInput.obj W) q w ≫
          (rawG W).hom) := by
  simpa only [gRawTilde, JTRealizationGenerators.generator,
    realizationNerveAdjunction, realization, realizationUnit] using
      (Presheaf.uliftYonedaAdjunction_homEquiv_app
        (L := realization) (α := realizationUnit)
        (f := (rawG W).hom) (z := w))

/-- The actual strict ordered-fiber action of the raw transpose at the
two original `p`-image vertices, before any fibration replacement. -/
def rawStrictFiberMapAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    pullback (endpointArrow W)
        (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
          (JTProjectiveOrderedFiberComparison.targetVertices W x y).2) ⟶
      ordinaryOrderedFiber (rawTarget W)
        ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1)
        ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2) :=
  DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
    (endpointArrow W) (ordinaryEndpointArrow (rawTarget W).toSSet)
    (gRawRow W ⦋1⦌) (gRawBase W) (gRawArrow_square W)
    (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
    (ordinaryEndpointPoint (rawTarget W)
      ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1)
      ((ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2))
    (rawPoint_square_at_p W x y)

/-- The unchanged original raw one-row coefficient carried by a simplex
of the actual pointed endpoint fiber. -/
def rawOneCoefficientAtP (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W)
      (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).obj (op k)) :
    (ordinaryInput.obj W).obj (op (⦋1⦌, k)) :=
  ((pullback.fst (endpointArrow W)
    (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).app (op k)) z

/-- In every inner degree, the actual CE interval leg of the raw strict
fiber action is the SAME original coend generator followed by `rawG`. -/
theorem rawStrictFiberCE_interval (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌))
    (k : SimplexCategory)
    (z : (pullback (endpointArrow W)
      (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
        (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)).obj (op k)) :
    let u := (ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1
    let v := (ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2
    let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
      (op k)) ((rawStrictFiberMapAtP W x y).app (op k) z)
    JTXiEndpointCollapse.CE_interval.app k ≫ f.right =
      JTRealizationGenerators.generator (ordinaryInput.obj W) (⦋1⦌, k)
        (rawOneCoefficientAtP W x y k z) ≫ (rawG W).hom := by
  dsimp only
  let u := (ell W).hom.app (op ⦋0⦌) (targetVertices W x y).1
  let v := (ell W).hom.app (op ⦋0⦌) (targetVertices W x y).2
  let z' := (rawStrictFiberMapAtP W x y).app (op k) z
  let f := ((JTCEOrdinaryFiber.originalFiberCEIso (rawTarget W) u v).hom.app
    (op k)) z'
  have hce := JTCEOrdinaryFiber.ceSpanIso_hom_val (rawTarget W) u v k f
  have hcollapse :
      ((JTCEOrdinaryFiber.ceSpanIso (rawTarget W) u v).hom.app (op k) f).val =
      ((ordinaryOrderedFiberIso (rawTarget W) u v).hom.app (op k) z').val := by
    let e := JTCEOrdinaryFiber.ceSpanIso (rawTarget W) u v
    let d := ordinaryOrderedFiberIso (rawTarget W) u v
    change (e.hom.app (op k) (e.inv.app (op k) (d.hom.app (op k) z'))).val =
      (d.hom.app (op k) z').val
    have hc := congrFun (Iso.inv_hom_id_app e (op k))
      (d.hom.app (op k) z')
    exact congrArg Subtype.val hc
  have hrow := ordinaryOrderedFiberIso_hom_val (rawTarget W) u v k z'
  have hfst := DaggerNativeSSetFibrationSquareFibreWeak.fibreMap_fst
    (endpointArrow W) (ordinaryEndpointArrow (rawTarget W).toSSet)
    (gRawRow W ⦋1⦌) (gRawBase W) (gRawArrow_square W)
    (point W (JTProjectiveOrderedFiberComparison.targetVertices W x y).1
      (JTProjectiveOrderedFiberComparison.targetVertices W x y).2)
    (ordinaryEndpointPoint (rawTarget W) u v)
    (rawPoint_square_at_p W x y)
  have hvalue := congrFun (NatTrans.congr_app hfst (op k)) z
  have hgen := gRawTilde_generator W (⦋1⦌, k) (rawOneCoefficientAtP W x y k z)
  calc
    JTXiEndpointCollapse.CE_interval.app k ≫ f.right =
        ((JTCEOrdinaryFiber.ceSpanIso (rawTarget W) u v).hom.app (op k) f).val :=
          hce.symm
    _ = ((ordinaryOrderedFiberIso (rawTarget W) u v).hom.app (op k) z').val :=
      hcollapse
    _ = ((pullback.fst (ordinaryEndpointArrow (rawTarget W).toSSet)
          (ordinaryEndpointPoint (rawTarget W) u v)).app (op k) z').down := hrow
    _ = ((gRawRow W ⦋1⦌).app (op k) (rawOneCoefficientAtP W x y k z)).down := by
      exact congrArg ULift.down hvalue
    _ = JTRealizationGenerators.generator (ordinaryInput.obj W) (⦋1⦌, k)
          (rawOneCoefficientAtP W x y k z) ≫ (rawG W).hom := by
      exact congrArg ULift.down hgen

end

end DaggerModels.PartII.JTRawUnitCylinderCalibration
