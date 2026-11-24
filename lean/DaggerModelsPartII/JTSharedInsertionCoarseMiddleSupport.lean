import DaggerModelsPartII.JTSharedInsertionCoarseLabels
import DaggerModelsPartII.JTSharedInsertionCoarseGraph
import DaggerModelsPartII.JTIncidentChartSupport
import DaggerModelsPartII.JTSharedInsertionIncidentEdges
import DaggerModelsPartII.JTOrdinalInverseFaceDiagram

/-!
# The full timed support of the actual corrected coarse middle

Reuse the full actual chart face and its inclusion in both endpoint incident
supports. Take its canonical complete ordinal inverse image under the SAME
shared coefficient projection. Every original operator and the entire old
time are retained, including zero-width charts. No support or constancy
hypothesis is supplied by the caller.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTSharedInsertionCoarseMiddleSupport

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The original shared tuple and common coefficient/choice-clock chain. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The actual coarse adjacent chart underlying that shared chain. -/
abbrev charts : Index F j ⥤ JTJointSubdivisionBeadCharts.Index F j :=
  JTSharedInsertionChoices.base F j ⋙ JTSharedInsertionChoices.projection F j ⋙
    JTJointSubdivisionInsertion.toCharts F j

/-- The first endpoint is a natural actual chart vertex, also in width zero. -/
def firstVertex : Index F j ⥤ JTJointSubdivisionVertexSupport.VertexIndex F j where
  obj p := ⟨(charts F j).obj p,
    (0 : Fin (((JTJointSubdivisionBeadNormalization.degrees F j).obj
      ((charts F j).obj p)).len + 1))⟩
  map f := ⟨(charts F j).map f,
    JTJointSubdivisionBeadNormalization.first_map F j ((charts F j).map f)⟩
  map_id p := by
    apply CategoryOfElements.ext
    exact (charts F j).map_id p
  map_comp f g := by
    apply CategoryOfElements.ext
    exact (charts F j).map_comp f g

/-- The last endpoint is natural under all original chart operators. -/
def lastVertex : Index F j ⥤ JTJointSubdivisionVertexSupport.VertexIndex F j where
  obj p := ⟨(charts F j).obj p,
    Fin.last ((JTJointSubdivisionBeadNormalization.degrees F j).obj
      ((charts F j).obj p)).len⟩
  map f := ⟨(charts F j).map f,
    JTJointSubdivisionBeadNormalization.last_map F j ((charts F j).map f)⟩
  map_id p := by
    apply CategoryOfElements.ext
    exact (charts F j).map_id p
  map_comp f g := by
    apply CategoryOfElements.ext
    exact (charts F j).map_comp f g

/-- Both endpoint-vertex functors retain the same whole coarse chart. -/
def endpointVertices (which : Fin 2) :
    Index F j ⥤ JTJointSubdivisionVertexSupport.VertexIndex F j :=
  ![firstVertex F j, lastVertex F j] which

/-- The original coefficient ordinal at the unchanged original source. -/
abbrev oldDegrees := JTSharedInsertionCoarseGraph.oldDegrees F j

/-- The whole native-chart support includes every original time coordinate. -/
abbrev oldSupports : Index F j ⥤ SimplexCategory :=
  firstVertex F j ⋙ JTIncidentChartSupport.chartSupports F j

/-- Its literal monic face inclusion in the original coefficient simplex. -/
def oldInclusion : oldSupports F j ⟶ oldDegrees F j :=
  Functor.whiskerLeft (firstVertex F j) (JTIncidentChartSupport.chartInclusion F j)

/-- The old inclusion is exactly the existing full timed chart inclusion. -/
theorem oldInclusion_app (p : Index F j) : (oldInclusion F j).app p =
    JTJointSubdivisionVertexSupport.beadInclusion F j ((charts F j).obj p) := rfl

/-- Whole timed support inclusions are monomorphisms. -/
theorem oldInclusion_mono (p : Index F j) : Mono ((oldInclusion F j).app p) :=
  JTRowGraphParameterSupport.inclusion_mono _

/-- The SAME shared chain degree, with all its original operators. -/
abbrev degrees := JTSharedInsertionChoices.ordinals F j

/-- The actual given surjective projection to the original coefficient. -/
abbrev coefficientProjection := JTSharedInsertionChoices.toOriginal F j

/-- The canonical FULL inverse-image ordinal of the whole chart face. -/
abbrev supports : Index F j ⥤ SimplexCategory :=
  JTOrdinalInverseFaceDiagram.supportDiagram
    (oldSupports F j) (oldDegrees F j) (degrees F j)
    (oldInclusion F j) (coefficientProjection F j)
    (oldInclusion_mono F j) (JTSharedInsertionChoices.toOriginal_surjective F j)

/-- Include that exact inverse image in the same common coefficient chain. -/
abbrev inclusion : supports F j ⟶ degrees F j :=
  JTOrdinalInverseFaceDiagram.inclNat
    (oldSupports F j) (oldDegrees F j) (degrees F j)
    (oldInclusion F j) (coefficientProjection F j)
    (oldInclusion_mono F j) (JTSharedInsertionChoices.toOriginal_surjective F j)

/-- The exact inverse-image inclusion is monic at every shared chain. -/
theorem inclusion_mono (p : Index F j) : Mono ((inclusion F j).app p) :=
  JTOrdinalInverseFaceDiagram.incl_mono
    (oldSupports F j) (oldDegrees F j) (degrees F j)
    (oldInclusion F j) (coefficientProjection F j)
    (oldInclusion_mono F j) (JTSharedInsertionChoices.toOriginal_surjective F j) p

/-- The old-face coordinate of every vertex of the full inverse-image support. -/
abbrev toOldSupport : supports F j ⟶ oldSupports F j :=
  JTOrdinalInverseFaceDiagram.toFaceNat
    (oldSupports F j) (oldDegrees F j) (degrees F j)
    (oldInclusion F j) (coefficientProjection F j)
    (oldInclusion_mono F j) (JTSharedInsertionChoices.toOriginal_surjective F j)

/-- The natural support square keeps the exact old coefficient projection. -/
theorem natural_square : toOldSupport F j ≫ oldInclusion F j =
    inclusion F j ≫ coefficientProjection F j :=
  JTOrdinalInverseFaceDiagram.natural_square
    (oldSupports F j) (oldDegrees F j) (degrees F j)
    (oldInclusion F j) (coefficientProjection F j)
    (oldInclusion_mono F j) (JTSharedInsertionChoices.toOriginal_surjective F j)

/-- The actual corrected coarse middle, retaining both shared endpoint edges. -/
abbrev middleLabels := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairGapChainLabels.labels F j

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev E := NecklaceCode.single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (ReversalDiscreteFreeColimits.discreteFree.map g) W

private theorem first_cut (p : Index F j) :
    JTJointSubdivisionVertexSupport.cut F j ((charts F j).obj p) 0 =
      ((charts F j).obj p).2.firstCut := by
  change NecklaceCode.orderMap
    ((JTJointSubdivisionBeadCharts.simplexIso F j ((charts F j).obj p)).inv.map ≫
      NecklaceCode.intervalι _ _ _ _) 0 = _
  rw [NecklaceCode.orderMap_comp_apply, NecklaceCode.orderMap_first]
  change (NecklaceCode.mapVertices (NecklaceCode.intervalι _ _ _ _) (ULift.up 0)).down = _
  rw [NecklaceCode.intervalι_vertices, NecklaceCode.intervalEmbedding_first]
  rfl

private theorem last_cut (p : Index F j) :
    JTJointSubdivisionVertexSupport.cut F j ((charts F j).obj p)
      (Fin.last ((JTJointSubdivisionBeadNormalization.degrees F j).obj
        ((charts F j).obj p)).len) = ((charts F j).obj p).2.lastCut := by
  change NecklaceCode.orderMap
    ((JTJointSubdivisionBeadCharts.simplexIso F j ((charts F j).obj p)).inv.map ≫
      NecklaceCode.intervalι _ _ _ _) (Fin.last _) = _
  rw [NecklaceCode.orderMap_comp_apply, NecklaceCode.orderMap_last]
  change (NecklaceCode.mapVertices (NecklaceCode.intervalι _ _ _ _)
    (ULift.up (Fin.last _))).down = _
  rw [NecklaceCode.intervalι_vertices]
  exact NecklaceCode.intervalEmbedding_last _ _ _ _

private theorem first_marked (p : Index F j) :
    (JTJointSubdivisionVertexSupport.toMarked F j).obj ((firstVertex F j).obj p) =
      (JTSharedInsertionChainSupport.marks F j 0).obj p := by
  refine Functor.Elements.ext (F := JTExactlyMarkedSourceDiagram.vertices F j) _ _ rfl ?_
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
  exact Subtype.ext (first_cut F j p)

private theorem last_marked (p : Index F j) :
    (JTJointSubdivisionVertexSupport.toMarked F j).obj ((lastVertex F j).obj p) =
      (JTSharedInsertionChainSupport.marks F j 2).obj p := by
  refine Functor.Elements.ext (F := JTExactlyMarkedSourceDiagram.vertices F j) _ _ rfl ?_
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply]
  exact Subtype.ext (last_cut F j p)

private theorem support_eq_of_cut (a : A)
    (v w : (JTExactlyMarkedSourceDiagram.vertices F j).obj a) (h : v = w) :
    JTIncidentBeadSupportData.support F j ⟨a, v⟩ =
      JTIncidentBeadSupportData.support F j ⟨a, w⟩ := by
  subst w
  rfl

private theorem first_face (p : Index F j) :
    SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
      JTIncidentBeadSupportData.support F j
        ((JTSharedInsertionChainSupport.marks F j 0).obj p) := by
  have h := JTIncidentChartSupport.face_le_support F j ((firstVertex F j).obj p)
  change SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
    JTIncidentBeadSupportData.support F j
      ((JTJointSubdivisionVertexSupport.toMarked F j).obj ((firstVertex F j).obj p)) at h
  have he : ((JTJointSubdivisionVertexSupport.toMarked F j).obj
      ((firstVertex F j).obj p)).2 =
      ((JTSharedInsertionChainSupport.marks F j 0).obj p).2 :=
    Subtype.ext (first_cut F j p)
  have hs := support_eq_of_cut F j ((JTSharedInsertionCoarseGraph.original F j).obj p)
    _ _ he
  change SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
    JTIncidentBeadSupportData.support F j
      ⟨(JTSharedInsertionCoarseGraph.original F j).obj p,
        ((JTSharedInsertionChainSupport.marks F j 0).obj p).2⟩
  rw [← hs]
  exact h

private theorem last_face (p : Index F j) :
    SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
      JTIncidentBeadSupportData.support F j
        ((JTSharedInsertionChainSupport.marks F j 2).obj p) := by
  have h := JTIncidentChartSupport.face_le_support F j ((lastVertex F j).obj p)
  change SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
    JTIncidentBeadSupportData.support F j
      ((JTJointSubdivisionVertexSupport.toMarked F j).obj ((lastVertex F j).obj p)) at h
  have he : ((JTJointSubdivisionVertexSupport.toMarked F j).obj
      ((lastVertex F j).obj p)).2 =
      ((JTSharedInsertionChainSupport.marks F j 2).obj p).2 :=
    Subtype.ext (last_cut F j p)
  have hs := support_eq_of_cut F j ((JTSharedInsertionCoarseGraph.original F j).obj p)
    _ _ he
  change SSet.Subcomplex.range (std.map ((oldInclusion F j).app p)) ≤
    JTIncidentBeadSupportData.support F j
      ⟨(JTSharedInsertionCoarseGraph.original F j).obj p,
        ((JTSharedInsertionChainSupport.marks F j 2).obj p).2⟩
  rw [← hs]
  exact h

private theorem inverse_face_le {s d k l : SimplexCategory}
    (u : s ⟶ d) (alpha : d ⟶ k) (v : l ⟶ k) (w : s ⟶ l)
    (hs : u ≫ alpha = w ≫ v) (U : (std.obj k).Subcomplex)
    (hU : SSet.Subcomplex.range (std.map v) ≤ U) :
    SSet.Subcomplex.range (std.map u) ≤ U.preimage (std.map alpha) := by
  intro n x hx
  rcases hx with ⟨y, rfl⟩
  change (std.map alpha).app n ((std.map u).app n y) ∈ U.obj n
  have he := congrFun (NatTrans.congr_app (congrArg std.map hs) n) y
  simp only [std.map_comp] at he
  change (std.map alpha).app n ((std.map u).app n y) =
    (std.map v).app n ((std.map w).app n y) at he
  rw [he]
  exact hU n ⟨(std.map w).app n y, rfl⟩

private theorem support_square (p : Index F j) :
    (inclusion F j).app p ≫ (coefficientProjection F j).app p =
      (toOldSupport F j).app p ≫ (oldInclusion F j).app p :=
  (NatTrans.congr_app (natural_square F j) p).symm

private def toFirstSupport (p : Index F j) :
    std.obj ((supports F j).obj p) ⟶ (JTSharedInsertionChainSupport.diagram F j 0).obj p :=
  (JTSharedInsertionChainSupport.support F j 0 p).lift
    (std.map ((inclusion F j).app p))
    (inverse_face_le _ _ _ _ (support_square F j p) _ (first_face F j p))

private def toLastSupport (p : Index F j) :
    std.obj ((supports F j).obj p) ⟶ (JTSharedInsertionChainSupport.diagram F j 2).obj p :=
  (JTSharedInsertionChainSupport.support F j 2 p).lift
    (std.map ((inclusion F j).app p))
    (inverse_face_le _ _ _ _ (support_square F j p) _ (last_face F j p))

private theorem constant_of_factor {C U X Y : SSet.{0}}
    (a : C ⟶ U) (b : U ⟶ X) (f : X ⟶ Y) (v : (Δ[0] : SSet.{0}) ⟶ Y)
    (h : b ≫ f = term U ≫ v) : (a ≫ b) ≫ f = term C ≫ v := by
  rw [Category.assoc, h, ← Category.assoc]
  congr 1

private theorem starting_onFace (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        (JTSharedInsertionIncidentEdges.starting F j 0).app p =
      term (std.obj ((supports F j).obj p)) ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W (z j) ≫
          JTEndpointNormalizationLifts.identityFamily W :=
  constant_of_factor (toFirstSupport F j p)
    ((JTSharedInsertionChainSupport.inclusion F j 0).app p)
    ((JTSharedInsertionIncidentEdges.starting F j 0).app p) _
    (JTSharedInsertionIncidentEdges.starting_on_support F j 0 p)

private theorem ending_onFace (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        (JTSharedInsertionIncidentEdges.ending F j 2).app p =
      term (std.obj ((supports F j).obj p)) ≫
        JTProjectiveOrderedFiberComparison.vertexPoint W (z j) ≫
          JTEndpointNormalizationLifts.identityFamily W :=
  constant_of_factor (toLastSupport F j p)
    ((JTSharedInsertionChainSupport.inclusion F j 2).app p)
    ((JTSharedInsertionIncidentEdges.ending F j 2).app p) _
    (JTSharedInsertionIncidentEdges.ending_on_support F j 2 p)

private theorem pre_comp (W : Source) {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pre W (f ≫ g) = pre W g ≫ pre W f := by
  rw [pre, ReversalDiscreteFreeColimits.discreteFree.map_comp, diagramMappingPrecomp_comp]

private theorem pre_id (W : Source) (X : SSet.{0}) : pre W (𝟙 X) = 𝟙 _ := by
  rw [pre, ReversalDiscreteFreeColimits.discreteFree.map_id, diagramMappingPrecomp_id]

private theorem constant_of_iso {T U : NecklaceCode} {k l : SimplexCategory}
    (e : T.toSSet ≅ U.toSSet) (u : l ⟶ k) (v : Vertex W)
    (c : std.obj k ⟶ TripleBeadEndpointLabel.labels W T)
    (h : (std.map u ≫ c) ≫ pre W e.inv =
      JTConstantOrderedLabel.constantCoefficient W v U l) :
    std.map u ≫ c = JTConstantOrderedLabel.constantCoefficient W v T l := by
  have he : pre W e.inv ≫ pre W e.hom = 𝟙 _ := by
    rw [← pre_comp, e.hom_inv_id, pre_id]
  calc
    std.map u ≫ c = ((std.map u ≫ c) ≫ pre W e.inv) ≫ pre W e.hom := by
      rw [Category.assoc, he]
      exact (Category.comp_id _).symm
    _ = JTConstantOrderedLabel.constantCoefficient W v U l ≫ pre W e.hom :=
      congrArg (fun q ↦ q ≫ pre W e.hom) h
    _ = _ := (JTSupportedNormalizedLabel.constant_restrict v e.hom).symm

private theorem chart_bead_coefficient (q : JTJointSubdivisionBeadCharts.Index F j) :
    JTJointPairGapDiagram.coefficient F j ((JTJointSubdivisionBeadCharts.toPairs F j).obj q) ≫
        pre W (JTJointSubdivisionBeadCharts.simplexIso F j q).inv.map =
      SSet.yonedaEquiv.symm (JTParametrizedBeadGraph.beadLabel
        (a := (JTJointSubdivisionBeadCharts.base F j).obj q)
        ((JTJointSubdivisionBeadNormalization.degrees F j).obj q).len
        (JTJointSubdivisionBeadNormalization.inclusion F j q)) := by
  change (JTActualJointCutPrism.originalCoefficient (L := L)
      ((JTJointSubdivisionBeadCharts.base F j).obj q) ≫ pre W _) ≫ pre W _ = _
  rw [Category.assoc, ← pre_comp]
  change SSet.yonedaEquiv.symm _ ≫
    pre W (JTJointSubdivisionBeadNormalization.inclusion F j q) = _
  rw [SSet.yonedaEquiv_symm_comp]
  rfl

private theorem chart_coefficient_onSupport (q : JTJointSubdivisionBeadCharts.Index F j) :
    std.map (JTJointSubdivisionVertexSupport.beadInclusion F j q) ≫
        JTJointPairGapDiagram.coefficient F j
          ((JTJointSubdivisionBeadCharts.toPairs F j).obj q) =
      JTConstantOrderedLabel.constantCoefficient W (z j)
        ((JTJointSubdivisionBeadCharts.native F j).obj q)
        (JTJointSubdivisionVertexSupport.beadSupport F j q) := by
  apply constant_of_iso
    (NecklaceCode.simplicialFunctor.mapIso (JTJointSubdivisionBeadCharts.simplexIso F j q))
  change std.map (JTJointSubdivisionVertexSupport.beadInclusion F j q) ≫
    (JTJointPairGapDiagram.coefficient F j
      ((JTJointSubdivisionBeadCharts.toPairs F j).obj q) ≫
        pre W (JTJointSubdivisionBeadCharts.simplexIso F j q).inv.map) = _
  rw [chart_bead_coefficient F j q]
  have h := JTJointBeadSupportedNormalization.coefficient_onSupport F
    ((JTJointSubdivisionBeadCharts.base F j).obj q)
    ((JTJointSubdivisionBeadNormalization.degrees F j).obj q).len j
    (JTJointSubdivisionBeadNormalization.toJointInterval F j q)
  change std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F _ _
      (JTJointSubdivisionBeadNormalization.toJointInterval F j q ≫
        JTTargetIntervalGluing.middleInclusion _ j)) ≫
      SSet.yonedaEquiv.symm (JTParametrizedBeadGraph.beadLabel (a := _ ) _
        (JTJointSubdivisionBeadNormalization.toJointInterval F j q ≫
          JTTargetIntervalGluing.middleInclusion _ j)) =
    JTConstantOrderedLabel.constantCoefficient W (z j)
      (NecklaceCode.single ((JTJointSubdivisionBeadNormalization.degrees F j).obj q).len)
      (JTParametrizedBeadGraph.fullBeadSupport F _ _
        (JTJointSubdivisionBeadNormalization.toJointInterval F j q ≫
          JTTargetIntervalGluing.middleInclusion _ j)) at h
  rw [JTJointSubdivisionBeadNormalization.toJointInterval_fac] at h
  exact h

private abbrev pair := JTSharedInsertionCoarseChoice.toPairChain F j

private theorem gap_onFace (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        JTJointPairGapChainLabels.gapCoefficient F j ((pair F j).obj p) =
      JTConstantOrderedLabel.constantCoefficient W (z j)
        ((JTJointSubdivisionBeadCharts.native F j).obj ((charts F j).obj p))
        ((supports F j).obj p) := by
  change std.map ((inclusion F j).app p) ≫
    (std.map ((coefficientProjection F j).app p) ≫
      JTJointPairGapDiagram.coefficient F j
        ((JTJointSubdivisionBeadCharts.toPairs F j).obj ((charts F j).obj p))) = _
  rw [← Category.assoc, ← std.map_comp, support_square, std.map_comp, Category.assoc,
    oldInclusion_app, chart_coefficient_onSupport F j ((charts F j).obj p)]
  exact (JTConstantOrderedLabel.constantCoefficient_ordinal W (z j) _
    ((toOldSupport F j).app p)).symm

private theorem front_onFace (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        (JTJointPairGapChainLabels.coefficients F j ((pair F j).obj p)).left =
      JTConstantOrderedLabel.constantCoefficient W (z j) E ((supports F j).obj p) := by
  change std.map ((inclusion F j).app p) ≫
    ((JTActualJointChoiceChainGraph.chainStarting F j).app
      ((JTJointPairChainDiagram.earlier F j).obj ((pair F j).obj p)) ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) = _
  rw [JTSharedInsertionCoarseChoice.earlier_starting]
  exact JTWhiskerEdgeCoefficient.onFace W ((inclusion F j).app p) (z j)
    ((JTSharedInsertionIncidentEdges.starting F j 0).app p) (starting_onFace F j p)

private theorem back_onFace (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        ((JTActualJointChainSideLabels.leftCoefficients F j
          ((JTJointPairChainDiagram.later F j).obj ((pair F j).obj p))).right) =
      JTConstantOrderedLabel.constantCoefficient W (z j) E ((supports F j).obj p) := by
  change std.map ((inclusion F j).app p) ≫
    ((JTActualJointChoiceChainGraph.chainEnding F j).app
      ((JTJointPairChainDiagram.later F j).obj ((pair F j).obj p)) ≫
        TwoBeadEndpointLabel.edgeLabelFromRow W) = _
  rw [JTSharedInsertionCoarseChoice.later_ending]
  exact JTWhiskerEdgeCoefficient.onFace W ((inclusion F j).app p) (z j)
    ((JTSharedInsertionIncidentEdges.ending F j 2).app p) (ending_onFace F j p)

/-- The WHOLE actual corrected coarse middle is constant on its full timed support. -/
theorem coefficient_onSupport (p : Index F j) :
    std.map ((inclusion F j).app p) ≫
        JTSupportedOrderedCoefficientChoices.old W (z j) (middleLabels F j) p =
      JTSupportedOrderedCoefficientChoices.supportedConstant W (z j)
        (middleLabels F j) (supports F j) p := by
  change std.map ((inclusion F j).app p) ≫ SSet.yonedaEquiv.symm
    (JTRealizedLabelEndpoints.orderedLabel W (z j) (z j) _ _
      (JTComposedPrismLabels.orderedPoint
        (JTJointPairGapChainLabels.coefficients F j ((pair F j).obj p)))) = _
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  apply JTSupportedNormalizedLabel.glue_onFace
  · exact front_onFace F j p
  · apply JTSupportedNormalizedLabel.glue_onFace
    · exact gap_onFace F j p
    · exact back_onFace F j p

end

end DaggerModels.PartII.JTSharedInsertionCoarseMiddleSupport
