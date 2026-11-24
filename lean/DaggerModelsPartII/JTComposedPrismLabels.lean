import DaggerModelsPartII.JTSharedCoefficientEvaluation
import DaggerModelsPartII.JTOrderedLabelWedge
import DaggerModelsPartII.JTJointTraceObstruction

/-!
# Full timed prisms of two native labels with an arbitrary common endpoint family

Both labels use the same coefficient simplex. At the internal joint they may
agree in a varying row-zero simplex. The two outer endpoints are fixed.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTComposedPrismLabels

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints ReversalDiscreteFreeColimits
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue
  glue_first glue_last glue_left glue_right)
open JTProjectiveOrderedFiberComparison (row)
open JTRealizedLabelEndpoints (orderedLabel)
open JTBinaryPrismRealization (realizeProduct)
open JTNecklaceLabelRealization (realizedLabel_natural_X realizedLabel_natural_k)
open JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder augmentation_boundary)
open JTInterpolatedReducedCylinder (cylinderMap cylinderMap_cylinder cylinderMap_boundary)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev J := GroupoidSimplex.parameter
private abbrev D := discreteFree.{0}

private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (D.map f) W

/-- A timed graph of an unordered label, expressed by its coefficient in the mapping space. -/
abbrev rawProduct (W : Source) {X I : SSet.{0}} {k : SimplexCategory}
    (p : X ⊗ I ⟶ J.obj k) (c : std.obj k ⟶ diagramMappingSpace (D.obj X) W) :=
  realizeProduct W k p (SSet.yonedaEquiv c)

/-- Restrict the whole raw product along any horizontal simplicial map. -/
theorem rawProduct_horizontal (W : Source) {X Y I : SSet.{0}} {k : SimplexCategory}
    (i : X ⟶ Y) (p : Y ⊗ I ⟶ J.obj k)
    (c : std.obj k ⟶ diagramMappingSpace (D.obj Y) W) :
    (i ⊗ₘ 𝟙 I) ≫ rawProduct W p c =
      rawProduct W ((i ⊗ₘ 𝟙 I) ≫ p) (c ≫ pre W i) := by
  have h : (i ⊗ₘ 𝟙 I) ≫ lift (fst Y I) p =
      lift (fst X I) ((i ⊗ₘ 𝟙 I) ≫ p) ≫ (i ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]
  unfold rawProduct realizeProduct
  rw [← Category.assoc, h, Category.assoc, realizedLabel_natural_X, SSet.yonedaEquiv_comp]
  rfl

/-- Restrict the full coefficient and retain the same raw value of the timed graph. -/
theorem rawProduct_coefficient (W : Source) {X I : SSet.{0}} {k l : SimplexCategory}
    (i : k ⟶ l) (p : X ⊗ I ⟶ J.obj k)
    (c : std.obj l ⟶ diagramMappingSpace (D.obj X) W) :
    rawProduct W (p ≫ J.map i) c = rawProduct W p (std.map i ≫ c) := by
  have h : lift (fst X I) (p ≫ J.map i) = lift (fst X I) p ≫ (𝟙 X ⊗ₘ J.map i) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc]
  unfold rawProduct realizeProduct
  rw [h, Category.assoc, realizedLabel_natural_k, SSet.yonedaEquiv_map_comp]
  rfl

/-- A coefficient pulled back from a point has the same value on every time prism. -/
theorem rawProduct_constant (W : Source) (z : Vertex W) (T : NecklaceCode)
    {k : SimplexCategory} {I : SSet.{0}} (p : T.toSSet ⊗ I ⟶ J.obj k) :
    rawProduct W p (JTConstantOrderedLabel.constantCoefficient W z T k) =
      fst T.toSSet I ≫ term T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  let c := JTConstantOrderedLabel.constantCoefficient W z T k
  have hc : orderedLabel W z z T k (JTConstantOrderedLabel.constantLabel W z T k) =
      SSet.yonedaEquiv c := by
    have h := congrArg SSet.yonedaEquiv
      (JTConstantOrderedLabel.coefficient_constantLabel W z T k)
    rw [JTOrderedLabelBinaryGlue.coefficient, Equiv.apply_symm_apply] at h
    exact h
  have h := JTJointTraceObstruction.constant_realizeProduct W z T k (snd T.toSSet (J.obj k))
  rw [hc, realizeProduct, lift_fst_snd, Category.id_comp] at h
  change lift (fst T.toSSet I) p ≫ JTNecklaceLabelRealization.realizedLabel T.toSSet W k
    (SSet.yonedaEquiv c) = _
  calc
    _ = lift (fst T.toSSet I) p ≫
        (fst T.toSSet (J.obj k) ≫ term T.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z)) :=
      congrArg (fun f : T.toSSet ⊗ J.obj k ⟶ Raw W ↦ lift (fst T.toSSet I) p ≫ f) h
    _ = _ := by rw [lift_fst_assoc]

/-- Unordered coefficients on the two pieces agree at the entire shared endpoint family. -/
structure Coefficients (W : Source) (T U : NecklaceCode) (k : SimplexCategory)
    (x y : Vertex W) where
  left : std.obj k ⟶ labels W T
  right : std.obj k ⟶ labels W U
  seam : left ≫ lastRestriction W T = right ≫ firstRestriction W U
  first : left ≫ firstRestriction W T = term (std.obj k) ≫ zeroPoint W x
  last : right ≫ lastRestriction W U = term (std.obj k) ≫ zeroPoint W y

variable {W : Source} {T U : NecklaceCode} {k n : SimplexCategory} {x y : Vertex W}
variable (C : Coefficients W T U k x y)

/-- Glue the two coefficients in the actual native wedge. -/
def coefficient : std.obj k ⟶ labels W (wedge T U) :=
  glue W T U k C.left C.right C.seam

private theorem boundary_first (W : Source) (T : NecklaceCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inl : D.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      firstRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inl W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inl_desc, firstRestriction]
  rfl

private theorem boundary_last (W : Source) (T : NecklaceCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inr : D.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      lastRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inr W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inr_desc, lastRestriction]
  rfl

private theorem outer :
    coefficient C ≫ (necklaceBoundaryRestriction W).app (op (wedge T U)) =
      term (std.obj k) ≫ boundaryPoint W x y := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst]
    rw [boundary_first, coefficient, glue_first, C.first, boundaryPoint_first]
  · simp only [Category.assoc, boundaryMappingIso_snd]
    rw [boundary_last, coefficient, glue_last, C.last, boundaryPoint_last]

/-- The wedge label with the two given outer vertices, in the original ordered pullback. -/
def orderedPoint :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (wedge T U))).obj (op k) :=
  SSet.yonedaEquiv (pullback.lift (coefficient C) (term (std.obj k)) (outer C))

theorem orderedPoint_coefficient :
    orderedLabel W x y (wedge T U) k (orderedPoint C) = SSet.yonedaEquiv (coefficient C) := by
  dsimp only [orderedPoint, orderedLabel]
  erw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
  rfl

/-- The actual decorated index that will be used to evaluate the two pieces. -/
def index : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (wedge T U) k (orderedPoint C)

variable {I : SSet.{0}}

private abbrev tend (T : NecklaceCode) := pointAt T (ULift.up (Fin.last T.len))
private abbrev tstart (T : NecklaceCode) := pointAt T (ULift.up 0)

private abbrev prismPushout (T U : NecklaceCode) (I : SSet.{0}) :=
  (wedgeIsPushout T U).map (tensorRight I)

/-- Paste two whole groupoid parameters which agree along the entire common boundary time. -/
def parameter (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (tend T ⊗ₘ 𝟙 I) ≫ p = (tstart U ⊗ₘ 𝟙 I) ≫ q) :
    (wedge T U).toSSet ⊗ I ⟶ J.obj k :=
  (prismPushout T U I).desc p q h

theorem parameter_left (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (tend T ⊗ₘ 𝟙 I) ≫ p = (tstart U ⊗ₘ 𝟙 I) ≫ q) :
    (wedgeιLeft T U ⊗ₘ 𝟙 I) ≫ parameter p q h = p :=
  (prismPushout T U I).inl_desc p q h

theorem parameter_right (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (tend T ⊗ₘ 𝟙 I) ≫ p = (tstart U ⊗ₘ 𝟙 I) ≫ q) :
    (wedgeιRight T U ⊗ₘ 𝟙 I) ≫ parameter p q h = q :=
  (prismPushout T U I).inr_desc p q h

set_option maxHeartbeats 900000 in
/-- Raw realization commutes with pasting of matching coefficients and parameters.
The endpoint conditions at the two ends are independent of this calculation. -/
theorem rawProduct_glue_eq (c : std.obj k ⟶ labels W T) (d : std.obj k ⟶ labels W U)
    (hc : c ≫ lastRestriction W T = d ≫ firstRestriction W U)
    (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (tend T ⊗ₘ 𝟙 I) ≫ p = (tstart U ⊗ₘ 𝟙 I) ≫ q)
    (g : (wedge T U).toSSet ⟶ Raw W)
    (hl : rawProduct W p c = fst T.toSSet I ≫ wedgeιLeft T U ≫ g)
    (hr : rawProduct W q d = fst U.toSSet I ≫ wedgeιRight T U ≫ g) :
    rawProduct W (parameter p q h) (glue W T U k c d hc) =
      fst (wedge T U).toSSet I ≫ g := by
  apply (prismPushout T U I).hom_ext
  · change (wedgeιLeft T U ⊗ₘ 𝟙 I) ≫ _ = (wedgeιLeft T U ⊗ₘ 𝟙 I) ≫ _
    rw [rawProduct_horizontal, parameter_left, glue_left, hl]
    simp only [tensorHom_fst_assoc]
  · change (wedgeιRight T U ⊗ₘ 𝟙 I) ≫ _ = (wedgeιRight T U ⊗ₘ 𝟙 I) ≫ _
    rw [rawProduct_horizontal, parameter_right, glue_right, hr]
    simp only [tensorHom_fst_assoc]

set_option maxHeartbeats 900000 in
/-- The whole pasted graph has the exact raw value if the two prism restrictions do. -/
theorem rawProduct_eq (p : T.toSSet ⊗ I ⟶ J.obj k) (q : U.toSSet ⊗ I ⟶ J.obj k)
    (h : (tend T ⊗ₘ 𝟙 I) ≫ p = (tstart U ⊗ₘ 𝟙 I) ≫ q)
    (g : (wedge T U).toSSet ⟶ Raw W)
    (hl : rawProduct W p C.left = fst T.toSSet I ≫ wedgeιLeft T U ≫ g)
    (hr : rawProduct W q C.right = fst U.toSSet I ≫ wedgeιRight T U ≫ g) :
    rawProduct W (parameter p q h) (coefficient C) = fst (wedge T U).toSSet I ≫ g :=
  rawProduct_glue_eq C.left C.right C.seam p q h g hl hr

set_option maxHeartbeats 900000 in
/-- A raw equality of the whole product descends to the original two-ended cylinder. -/
theorem reduced_raw {V : NecklaceCode} (a :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op V)).obj (op k))
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) (f : V ⟶ Q.code)
    (p : V.toSSet ⊗ J.obj n ⟶ J.obj k)
    (h : realizeProduct W k p (orderedLabel W x y V k a) =
      fst V.toSSet (J.obj n) ≫ f.map ≫ Q.map) :
    cylinderMap V p ≫ descend W x y V k a = augmentation V n ≫ f.map ≫ Q.map := by
  apply (isPushout V n).hom_ext
  · rw [← Category.assoc, cylinderMap_cylinder, Category.assoc, descend_cylinder,
      ← Category.assoc ((cylinder V).app n), augmentation_cylinder]
    exact h
  · rw [← Category.assoc, cylinderMap_boundary, descend_boundary,
      ← Category.assoc ((JTNecklaceEndpointCylinder.boundary V).app n), augmentation_boundary,
      ← Category.assoc (endpointInclusion _), endpointInclusion_natural]
    dsimp only [endpointInclusion, rawBoundary]
    rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural, Q.first, Q.last]

end
end DaggerModels.PartII.JTComposedPrismLabels
