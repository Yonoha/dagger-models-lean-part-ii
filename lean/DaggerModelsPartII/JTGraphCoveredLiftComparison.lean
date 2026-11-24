import DaggerModelsPartII.JTGraphCoveredEvaluationSquares
import DaggerModelsPartII.JTGraphCoveredLiftInterface

/-!
# Full fixed-Q evaluation comparisons from actual covered graph maps

The inputs are the two actual ordered-raw equations, full reduced-source
transport, native/coefficient squares and SAME-Q target equation. The conclusion
is a natural transformation on ALL internal necklaces after the exact source
change and reindexing. Existing pullback lifts and presentation transport are
reused; no whole-product Family, section or point-target replacement is made.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredLiftComparison

open JTParametrizedTargetFamilies (codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The exact ordered-raw equation of the existing full graph evaluator. -/
def RawEquation {C : Type} [SmallCategory C] {W : Source} {x y : Vertex W}
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
    (L : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
    (c : codes L ⟶ (Functor.const C).obj Q.code)
    {Y : C ⥤ SSet.{0}}
    (π : Y ⟶ JTJointRelativeParameters.withTime Q.map J t (Over.lift (codes L) c)
      (JTTargetIntervalOverMapping.whole Q.code))
    (θ : Y ⟶ JTParametrizedTargetFamilyComparison.degrees L ⋙ J) : Prop :=
  ∀ p, lift (π.app p ≫ fst _ _) (θ.app p) ≫
    JTNecklaceLabelRealization.realizedLabel ((codes L).obj p).toSSet W
      ((JTParametrizedTargetFamilyComparison.degrees L).obj p)
      (JTRealizedLabelEndpoints.orderedLabel W x y ((codes L).obj p)
        ((JTParametrizedTargetFamilyComparison.degrees L).obj p)
        (OrderedLabelElements.label W (OrderedNecklaceVertexPoints.boundaryPoint W x y)
          (L.obj p))) =
    (π.app p ≫ fst _ _) ≫ (c.app p).map ≫ Q.map

variable {I K : Type} [SmallCategory I] [SmallCategory K]
variable {W : Source} {x y : Vertex W}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (G : I ⥤ K)
variable (N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (M : K ⥤ DecoratedNecklaceHomDiagram.Index W x y)
variable (nt : I ⥤ SimplexCategory) (mt : K ⥤ SimplexCategory)
variable (nc : codes N ⟶ (Functor.const I).obj Q.code)
variable (mc : codes M ⟶ (Functor.const K).obj Q.code)

private abbrev product {C : Type} [SmallCategory C]
    (L : C ⥤ DecoratedNecklaceHomDiagram.Index W x y) (t : C ⥤ SimplexCategory)
    (c : codes L ⟶ (Functor.const C).obj Q.code) :=
  JTJointRelativeParameters.withTime Q.map J t (Over.lift (codes L) c)
    (JTTargetIntervalOverMapping.whole Q.code)

variable {NY : I ⥤ SSet.{0}} {MY : K ⥤ SSet.{0}}
variable (np : NY ⟶ product Q N nt nc) (mp : MY ⟶ product Q M mt mc)
variable (nq : NY ⟶ JTParametrizedTargetFamilyComparison.degrees N ⋙ J)
variable (mq : MY ⟶ JTParametrizedTargetFamilyComparison.degrees M ⋙ J)
variable (r : N ⟶ G ⋙ M) (η : NY ⟶ G ⋙ MY)

private abbrev newD := JTGraphCoveredLabelEvaluation.reduced Q N nt nc np
private abbrev oldD := JTGraphCoveredLabelEvaluation.reduced Q M mt mc mp
private abbrev ni := JTGraphCoveredCylinderEquations.inc Q N nt nc np
private abbrev mi := JTGraphCoveredCylinderEquations.inc Q M mt mc mp

variable (s : newD Q N nt nc np ⟶ G ⋙ oldD Q M mt mc mp)
variable (hi : ∀ a, (ni Q N nt nc np).app a ≫ (s.app a).right =
  η.app a ≫ (mi Q M mt mc mp).app (G.obj a))
variable (hn : ∀ a,
  (np.app a ≫ fst ((codes N).obj a).toSSet (J.obj (nt.obj a))) ≫
      ((JTGraphCoveredEvaluationSquares.nativePart G r).app a).map =
    η.app a ≫ mp.app (G.obj a) ≫
      fst ((codes M).obj (G.obj a)).toSSet (J.obj (mt.obj (G.obj a))))
variable (hq : ∀ a, nq.app a ≫ J.map ((JTGraphCoveredEvaluationSquares.degreePart G r).app a) =
  η.app a ≫ mq.app (G.obj a))

variable (hc : JTGraphCoveredEvaluationSquares.nativePart G r ≫
  Functor.whiskerLeft G mc = nc)
variable (nr : RawEquation Q N nt nc np nq) (mr : RawEquation Q M mt mc mp mq)

private abbrev nl := JTGraphCoveredLiftInterface.pullbackLift Q N nt nc np nq nr
private abbrev ml := JTGraphCoveredLiftInterface.pullbackLift Q M mt mc mp mq mr

include hi hn hq hc in
/-- Both complete legs give the exact fixed-Q pullback square, not just its raw image. -/
theorem pullback_square (a : I) :
    (nl Q N nt nc np nq nr).app a ≫
        (JTTargetCommaPullback.diagram W x y Q).map (r.app a) =
      s.app a ≫ (ml Q M mt mc mp mq mr).app (G.obj a) := by
  apply JTGraphCoveredComparisonEquations.fixedTarget_square Q (r.app a) (s.app a)
  · exact JTDecoratedIntervalCylinder.liftFromProjections_fst Q N
      (newD Q N nt nc np) (JTGraphCoveredLabelEvaluation.decorated Q N nt nc np nq)
      (JTGraphCoveredLabelEvaluation.nativeLeg Q N nt nc np)
      (JTGraphCoveredLabelEvaluation.raw_square Q N nt nc np nq nr) a
  · exact JTDecoratedIntervalCylinder.liftFromProjections_fst Q M
      (oldD Q M mt mc mp) (JTGraphCoveredLabelEvaluation.decorated Q M mt mc mp mq)
      (JTGraphCoveredLabelEvaluation.nativeLeg Q M mt mc mp)
      (JTGraphCoveredLabelEvaluation.raw_square Q M mt mc mp mq mr) (G.obj a)
  · exact JTDecoratedIntervalCylinder.liftFromProjections_snd Q N
      (newD Q N nt nc np) (JTGraphCoveredLabelEvaluation.decorated Q N nt nc np nq)
      (JTGraphCoveredLabelEvaluation.nativeLeg Q N nt nc np)
      (JTGraphCoveredLabelEvaluation.raw_square Q N nt nc np nq nr) a
  · exact JTDecoratedIntervalCylinder.liftFromProjections_snd Q M
      (oldD Q M mt mc mp) (JTGraphCoveredLabelEvaluation.decorated Q M mt mc mp mq)
      (JTGraphCoveredLabelEvaluation.nativeLeg Q M mt mc mp)
      (JTGraphCoveredLabelEvaluation.raw_square Q M mt mc mp mq mr) (G.obj a)
  · exact JTGraphCoveredEvaluationSquares.decorated_square Q G N M nt mt nc mc
      np mp nq mq r η s hi hn hq a
  · exact JTGraphCoveredEvaluationSquares.native_square Q G N M nt mt nc mc
      np mp r η s hi hn hc a

/-- The exact source change retains every internal necklace, followed by base reindexing. -/
def presentationMap : BoundaryNecklaceComma.Presentation (newD Q N nt nc np) ⥤
    BoundaryNecklaceComma.Presentation (oldD Q M mt mc mp) :=
  Grothendieck.map (Functor.whiskerRight s BoundaryNecklaceComma.diagram) ⋙
    Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram (oldD Q M mt mc mp)) G

include hi hn hq hc in
/-- A natural comparison on ALL internal necklaces in the unchanged original TargetComma Q. -/
def comparison : JTGraphCoveredLabelEvaluation.evaluation Q N nt nc np nq nr ⟶
    presentationMap Q G N M nt mt nc mc np mp s ⋙
      JTGraphCoveredLabelEvaluation.evaluation Q M mt mc mp mq mr := by
  rw [JTGraphCoveredLiftInterface.evaluation_eq_mapPresentation,
    JTGraphCoveredLiftInterface.evaluation_eq_mapPresentation]
  let E := JTTargetCommaPullback.diagram W x y Q
  let H := JTTargetCommaExactEvaluation.fromPresentation W x y Q
  let P := JTBoundaryNecklacePresentationCone.mapPresentation E (newD Q N nt nc np) N
    (nl Q N nt nc np nq nr) ⋙ H
  have he : Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram (newD Q N nt nc np))
      (𝟭 I) ⋙ P = P :=
    (congrArg (· ⋙ P) (Grothendieck.pre_id
      (BoundaryNecklaceComma.fiberDiagram (newD Q N nt nc np)))).trans (Functor.id_comp P)
  exact eqToHom he.symm ≫ JTBoundaryNecklaceTwoReindexComparison.comparison E
    (newD Q N nt nc np) N (nl Q N nt nc np nq nr) (𝟭 I)
    (oldD Q M mt mc mp) M (ml Q M mt mc mp mq mr) G s r
    (pullback_square Q G N M nt mt nc mc np mp nq mq r η s hi hn hq hc nr mr) H

end
end DaggerModels.PartII.JTGraphCoveredLiftComparison
