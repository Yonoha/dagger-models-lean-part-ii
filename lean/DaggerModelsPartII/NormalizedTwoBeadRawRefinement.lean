import DaggerModelsPartII.NormalizedTwoBeadLabelRestrictions
import DaggerModelsPartII.JTZeroRowParameterEdge
import DaggerModelsPartII.JTIdentityRowRealization
import DaggerModelsPartII.NormalizedTwoBeadPresentation

/-!
# Refining the specified zero-row path by the normalized three-bead traversal

The input is an explicit path on the original groupoid parameter. The middle
bead calculation is an equality of the complete original realization maps.
The two outer beads use their separate degree-zero identity calibration.
No arbitrary raw edge, target finality, or chosen-fiber weakness is claimed.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.NormalizedTwoBeadRawRefinement

open JTProjectiveOrderedFiberComparison JTEndpointNormalizationLifts
open TwoBeadCylinderTraversal JTNecklaceLabelRealization
open DaggerModels.PartII.ReversalDiscreteFreeColimits

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev A := (single 1).toSSet
private abbrev F := discreteFree.{0}
private abbrev J := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev J₀ := GroupoidSimplex.parameter.obj ⦋0⦌
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)

variable {W : Source} {z : J ⟶ row W ⦋0⦌}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (d : Families W ⦋1⦌ 0 1 z x y)

private abbrev targetMap : threeBead.toSSet ⟶ R W :=
  cylinderTraversal ≫ JTNecklaceEndpointCylinder.descend W x y twoBead
    ⦋1⦌ (NormalizedTwoBeadPresentation.orderedLabel d)

private abbrev rawMap (_d : Families W ⦋1⦌ 0 1 z x y) :
    threeBead.toSSet ⟶ R W :=
  collapseOuter.map ≫ JTZeroRowParameterEdge.nativeRawEdge W z

/-- The actual descended map retains the complete realized label on the
uncollapsed cylinder leg. -/
private theorem targetMap_eq_realized :
    targetMap d = productTraversal ≫
      realizedLabel twoBead.toSSet W ⦋1⦌
        (NormalizedTwoBeadLabelRestrictions.η d) := by
  dsimp only [targetMap, cylinderTraversal]
  rw [Category.assoc, JTNecklaceEndpointCylinder.descend_cylinder]
  rfl

/-- Restriction of the full native label to the joint is the same original
zero-row coefficient used by the raw parameter edge. -/
private theorem joint_coefficient :
    Functor.whiskerRight
        (ReversalDiscreteFreeColimits.discreteFree.map
          (pointAt twoBead (ULift.up (1 : Fin (twoBead.len + 1)))))
        (tensorRight (Δ[1] : SSet.{0})) ≫
      NormalizedTwoBeadLabelRestrictions.η d =
        JTZeroRowParameterEdge.zeroRowLabel W z := by
  have h := congrArg SSet.yonedaEquiv
    (NormalizedTwoBeadLabelRestrictions.joint_family d)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] at h
  change _ = JTZeroRowParameterEdge.zeroRowLabel W z at h
  exact h

/-- The first horizontal bead's specified time face is the ACTUAL identity
edge label at the original left zero-row vertex. -/
private theorem left_identity_face :
    (diagramTensor (F.obj A)).map
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)) ≫
      (Functor.whiskerRight (F.map (wedgeιLeft (single 1) (single 1)))
        (tensorRight (Δ[1] : SSet.{0})) ≫
          NormalizedTwoBeadLabelRestrictions.η d) =
        JTIdentityRowRealization.identityEdgeLabel W x := by
  rw [NormalizedTwoBeadLabelRestrictions.left_coefficient]
  change (TwoBeadEndpointLabel.edgeLabels W).map
      (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op
        (SSet.yonedaEquiv
          (leftSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  simpa only [JTIdentityRowRealization.identityEdgeLabel,
    Equiv.symm_apply_apply, Category.assoc] using
    congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
      (leftSimplex_degenerate d)

/-- The last horizontal bead's specified time face is the ACTUAL identity
edge label at the original right zero-row vertex. -/
private theorem right_identity_face :
    (diagramTensor (F.obj A)).map
        (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) ≫
      (Functor.whiskerRight (F.map (wedgeιRight (single 1) (single 1)))
        (tensorRight (Δ[1] : SSet.{0})) ≫
          NormalizedTwoBeadLabelRestrictions.η d) =
        JTIdentityRowRealization.identityEdgeLabel W y := by
  rw [NormalizedTwoBeadLabelRestrictions.right_coefficient]
  change (TwoBeadEndpointLabel.edgeLabels W).map
      (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op
        (SSet.yonedaEquiv
          (rightSimplexFamily d ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) = _
  apply SSet.yonedaEquiv.symm.injective
  rw [← SSet.stdSimplex.map_comp_yonedaEquiv_symm]
  simpa only [JTIdentityRowRealization.identityEdgeLabel,
    Equiv.symm_apply_apply, Category.assoc] using
    congrArg (fun q ↦ q ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)
      (rightSimplex_degenerate d)

/-- On the middle bead the first coordinate is the joint vertex and the
second coordinate is the complete original parameter one-simplex. -/
private theorem productTraversal_middle :
    tripleRightU (single 1) (single 1) (single 1) ≫ productTraversal =
      CartesianMonoidalCategory.lift
        (SSet.stdSimplex.isTerminalObj₀.from A)
        ((singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌) ≫
          (pointAt twoBead (ULift.up (1 : Fin (twoBead.len + 1))) ⊗ₘ
            𝟙 J) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.tensorHom_fst]
    exact collapseMiddle_middle
  · simp only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_snd,
      CartesianMonoidalCategory.tensorHom_snd, Category.comp_id,
      CartesianMonoidalCategory.lift_snd]
    rw [← Category.assoc (tripleRightU (single 1) (single 1) (single 1))
      collapseOuter.map, collapseOuter_middle, Category.id_comp]

/-- The uncollapsed middle bead maps to exactly the specified native raw
zero-row edge; no endpoint-normalizing lift choice remains in this formula. -/
theorem middle_refines_raw :
    tripleRightU (single 1) (single 1) (single 1) ≫ targetMap d =
      tripleRightU (single 1) (single 1) (single 1) ≫ rawMap d := by
  rw [targetMap_eq_realized, ← Category.assoc, productTraversal_middle]
  rw [Category.assoc, realizedLabel_natural_X
    (pointAt twoBead (ULift.up (1 : Fin (twoBead.len + 1)))) W ⦋1⦌
    (NormalizedTwoBeadLabelRestrictions.η d)]
  rw [joint_coefficient]
  have hp : CartesianMonoidalCategory.lift
      (SSet.stdSimplex.isTerminalObj₀.from A)
      ((singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌) =
      ((singleIso 1).hom ≫ JTCylinderCEComparison.simplexUnit.app ⦋1⦌) ≫
        CartesianMonoidalCategory.lift
          (SSet.stdSimplex.isTerminalObj₀.from J) (𝟙 J) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
      exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd,
        Category.comp_id]
  rw [hp]
  change _ = tripleRightU (single 1) (single 1) (single 1) ≫
    collapseOuter.map ≫ JTZeroRowParameterEdge.nativeRawEdge W z
  rw [← Category.assoc (tripleRightU (single 1) (single 1) (single 1))
    collapseOuter.map, collapseOuter_middle, Category.id_comp]
  exact Category.assoc _ _ _

private def δ (i : Fin 2) : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌ :=
  SimplexCategory.const ⦋0⦌ ⦋1⦌ i

private def outerStart : A ⟶ A ⊗ J₀ :=
  CartesianMonoidalCategory.lift (𝟙 A)
    (SSet.stdSimplex.isTerminalObj₀.from A ≫
      JTCylinderCEComparison.simplexUnit.app ⦋0⦌)

/-- The native single-edge endpoint is the same ordinary coface used by
the original free-groupoid simplex unit. -/
private theorem native_vertex (i : Fin 2) :
    pointAt (single 1) (ULift.up i) ≫ (singleIso 1).hom =
      SSet.stdSimplex.map (δ i) := by
  fin_cases i
  · change SSet.yonedaEquiv.symm (single 1).first ≫ (singleIso 1).hom = _
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      DaggerOriginalFlagFlankification.singleIso_first]
    rfl
  · change SSet.yonedaEquiv.symm (single 1).last ≫ (singleIso 1).hom = _
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      DaggerOriginalFlagFlankification.singleIso_last]
    rfl

/-- Full product-coordinate formula for either outer native bead. -/
private theorem outer_product (i : Fin 2)
    (bead : A ⟶ threeBead.toSSet) (f : A ⟶ twoBead.toSSet)
    (hf : bead ≫ collapseMiddle.map = f)
    (ht : bead ≫ collapseOuter.map =
      SSet.stdSimplex.isTerminalObj₀.from A ≫ pointAt (single 1) (ULift.up i)) :
    bead ≫ productTraversal = outerStart ≫
      (f ⊗ₘ GroupoidSimplex.parameter.map (δ i)) := by
  have hv : pointAt (single 1) (ULift.up i) ≫ (singleIso 1).hom ≫
      JTCylinderCEComparison.simplexUnit.app ⦋1⦌ =
        JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
          GroupoidSimplex.parameter.map (δ i) := by
    rw [← Category.assoc, native_vertex]
    exact JTCylinderCEComparison.simplexUnit.naturality (δ i)
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productTraversal, outerStart, Category.assoc,
      CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.tensorHom_fst]
    exact hf
  · simp only [productTraversal, outerStart, Category.assoc,
      CartesianMonoidalCategory.lift_snd,
      CartesianMonoidalCategory.tensorHom_snd]
    rw [← Category.assoc bead collapseOuter.map, ht]
    simp only [Category.assoc, CartesianMonoidalCategory.lift_snd_assoc, hv]

/-- Generic outer-bead calculation. Its four hypotheses are the exact
geometry, time-face, and raw-vertex equations checked for each side below. -/
private theorem outer_refines_raw (i : Fin 2)
    (v : (row W ⦋0⦌).obj (op ⦋0⦌))
    (bead : A ⟶ threeBead.toSSet) (f : A ⟶ twoBead.toSSet)
    (hf : bead ≫ collapseMiddle.map = f)
    (ht : bead ≫ collapseOuter.map =
      SSet.stdSimplex.isTerminalObj₀.from A ≫ pointAt (single 1) (ULift.up i))
    (hface : (diagramTensor (F.obj A)).map (SSet.stdSimplex.map (δ i)) ≫
      (Functor.whiskerRight (F.map f) (tensorRight (Δ[1] : SSet.{0})) ≫
        NormalizedTwoBeadLabelRestrictions.η d) =
          JTIdentityRowRealization.identityEdgeLabel W v)
    (hv : JTParameterContraction.parameterVertex ⦋1⦌ i ≫ z =
      vertexPoint W v) :
    bead ≫ targetMap d = bead ≫ rawMap d := by
  let q : (Δ[0] : SSet.{0}) ⟶ R W :=
    SSet.yonedaEquiv.symm
      (JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W v)
  have hreal : outerStart ≫
      (f ⊗ₘ GroupoidSimplex.parameter.map (δ i)) ≫
        realizedLabel twoBead.toSSet W ⦋1⦌
          (NormalizedTwoBeadLabelRestrictions.η d) =
      outerStart ≫ realizedLabel A W ⦋0⦌
        (JTIdentityRowRealization.identityEdgeLabel W v) := by
    calc
      _ = outerStart ≫ (𝟙 A ⊗ₘ GroupoidSimplex.parameter.map (δ i)) ≫
            (f ⊗ₘ 𝟙 J) ≫ realizedLabel twoBead.toSSet W ⦋1⦌
              (NormalizedTwoBeadLabelRestrictions.η d) := by
                rw [← Category.assoc (𝟙 A ⊗ₘ GroupoidSimplex.parameter.map (δ i))
                  (f ⊗ₘ 𝟙 J), tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      _ = outerStart ≫ (𝟙 A ⊗ₘ GroupoidSimplex.parameter.map (δ i)) ≫
            realizedLabel A W ⦋1⦌
              (Functor.whiskerRight (F.map f)
                (tensorRight (Δ[1] : SSet.{0})) ≫
                  NormalizedTwoBeadLabelRestrictions.η d) := by
                    rw [realizedLabel_natural_X]
      _ = outerStart ≫ realizedLabel A W ⦋0⦌
            ((diagramTensor (F.obj A)).map (SSet.stdSimplex.map (δ i)) ≫
              (Functor.whiskerRight (F.map f)
                (tensorRight (Δ[1] : SSet.{0})) ≫
                  NormalizedTwoBeadLabelRestrictions.η d)) := by
                    rw [realizedLabel_natural_k]
      _ = _ := by rw [hface]
  have hconst : outerStart ≫ realizedLabel A W ⦋0⦌
      (JTIdentityRowRealization.identityEdgeLabel W v) =
        SSet.stdSimplex.isTerminalObj₀.from A ≫ q := by
    rw [JTIdentityRowRealization.realizedIdentityEdgeLabel]
    have h : outerStart ≫
        SSet.stdSimplex.isTerminalObj₀.from (A ⊗ J₀) =
          SSet.stdSimplex.isTerminalObj₀.from A :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, h]
  have hraw : bead ≫ rawMap d =
      SSet.stdSimplex.isTerminalObj₀.from A ≫ q := by
    have he : SSet.stdSimplex.map (δ i) ≫ JTZeroRowParameterEdge.rawEdge W z = q :=
      JTZeroRowParameterEdge.rawEdge_endpoint W z i v hv
    calc
      _ = (bead ≫ collapseOuter.map) ≫ (singleIso 1).hom ≫
            JTZeroRowParameterEdge.rawEdge W z := by rfl
      _ = (SSet.stdSimplex.isTerminalObj₀.from A ≫
            pointAt (single 1) (ULift.up i)) ≫ (singleIso 1).hom ≫
              JTZeroRowParameterEdge.rawEdge W z := by rw [ht]
      _ = SSet.stdSimplex.isTerminalObj₀.from A ≫
            (SSet.stdSimplex.map (δ i) ≫
              JTZeroRowParameterEdge.rawEdge W z) := by
                rw [Category.assoc, ← Category.assoc (pointAt (single 1) (ULift.up i)),
                  native_vertex]
      _ = _ := by rw [he]
  calc
    _ = outerStart ≫ (f ⊗ₘ GroupoidSimplex.parameter.map (δ i)) ≫
          realizedLabel twoBead.toSSet W ⦋1⦌
            (NormalizedTwoBeadLabelRestrictions.η d) := by
              rw [targetMap_eq_realized, ← Category.assoc,
                outer_product i bead f hf ht, Category.assoc]
    _ = SSet.stdSimplex.isTerminalObj₀.from A ≫ q := hreal.trans hconst
    _ = _ := hraw.symm

/-- The left fixed-square data itself remembers the original initial
vertex equation of the specified path. -/
theorem left_path_vertex (d : Families W ⦋1⦌ 0 1 z x y) :
    JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ z = vertexPoint W x := by
  have h : d.leftFamily ≫ endpoint W 1 = z := by
    have hh := congrArg (fun q ↦ q ≫ prod.snd) d.left_boundary
    simpa only [Category.assoc, endpointArrow, prod.lift_snd] using hh
  calc
    _ = JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫
          (d.leftFamily ≫ endpoint W 1) := by rw [h]
    _ = (JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫
          d.leftFamily) ≫ endpoint W 1 := (Category.assoc _ _ _).symm
    _ = (vertexPoint W x ≫ identityFamily W) ≫ endpoint W 1 := by
          rw [d.left_degenerate]
    _ = _ := by rw [Category.assoc, identityFamily_endpoint, Category.comp_id]

/-- The right fixed-square data remembers the original terminal vertex. -/
theorem right_path_vertex (d : Families W ⦋1⦌ 0 1 z x y) :
    JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ z = vertexPoint W y := by
  have h : d.rightFamily ≫ endpoint W 0 = z := by
    have hh := congrArg (fun q ↦ q ≫ prod.fst) d.right_boundary
    simpa only [Category.assoc, endpointArrow, prod.lift_fst] using hh
  calc
    _ = JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫
          (d.rightFamily ≫ endpoint W 0) := by rw [h]
    _ = (JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫
          d.rightFamily) ≫ endpoint W 0 := (Category.assoc _ _ _).symm
    _ = (vertexPoint W y ≫ identityFamily W) ≫ endpoint W 0 := by
          rw [d.right_degenerate]
    _ = _ := by rw [Category.assoc, identityFamily_endpoint, Category.comp_id]

/-- The first horizontal bead refines the original raw vertex at time zero. -/
theorem left_refines_raw :
    tripleRightT (single 1) (single 1) (single 1) ≫ targetMap d =
      tripleRightT (single 1) (single 1) (single 1) ≫ rawMap d :=
  outer_refines_raw d 0 x
    (tripleRightT (single 1) (single 1) (single 1))
    (wedgeιLeft (single 1) (single 1))
    collapseMiddle_left collapseOuter_left (left_identity_face d)
      (left_path_vertex d)

/-- The final horizontal bead refines the original raw vertex at time one. -/
theorem right_refines_raw :
    tripleRightV (single 1) (single 1) (single 1) ≫ targetMap d =
      tripleRightV (single 1) (single 1) (single 1) ≫ rawMap d :=
  outer_refines_raw d 1 y
    (tripleRightV (single 1) (single 1) (single 1))
    (wedgeιRight (single 1) (single 1))
    collapseMiddle_right collapseOuter_right (right_identity_face d)
      (right_path_vertex d)

/-- Equality of the complete target map on all three original native beads. -/
theorem targetMap_eq_rawMap : targetMap d = rawMap d :=
  tripleRight_hom_ext (left_refines_raw d) (middle_refines_raw d)
    (right_refines_raw d)

/-- The actual native collapse is an original morphism over the SAME raw
realization, with the complete three-bead map as its commuting equation. -/
def nativeRefinement :
    (DecoratedCylinderNecklacePresentation.toTarget W x y).obj
        (NormalizedTwoBeadPresentation.presentationObject d) ⟶
      JTZeroRowParameterEdge.rawNecklaceOver W x y z
        (left_path_vertex d) (right_path_vertex d) where
  hom := collapseOuter
  w := by
    change collapseOuter.map ≫ JTZeroRowParameterEdge.nativeRawEdge W z =
      targetMap d
    exact (targetMap_eq_rawMap d).symm

/-- A concrete object of the actual target comma for the SPECIFIED
zero-row groupoid path. This is not a contraction of the comma category. -/
def rawTargetCommaObject :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y)
      (JTZeroRowParameterEdge.rawNecklaceOver W x y z
        (left_path_vertex d) (right_path_vertex d)) :=
  CostructuredArrow.mk (nativeRefinement d)

/-- The actual target comma at the specified raw zero-row edge has an object
under the original injective Kan fibrancy and the two prescribed endpoints. -/
def chosenRawTargetCommaObject (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (z : J ⟶ row W ⦋0⦌) (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫ z = vertexPoint W x)
    (hy : JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫ z = vertexPoint W y) :
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y)
      (JTZeroRowParameterEdge.rawNecklaceOver W x y z hx hy) :=
  rawTargetCommaObject (normalizedFamilies W hW ⦋1⦌ 0 1 z x y hx hy)

end

end DaggerModels.PartII.NormalizedTwoBeadRawRefinement
