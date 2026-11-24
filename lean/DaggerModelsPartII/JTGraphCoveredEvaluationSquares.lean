import DaggerModelsPartII.JTGraphCoveredComparisonEquations
import DaggerModelsPartII.JTBoundaryNecklaceTwoReindexComparison

/-!
# Complete evaluation-leg squares from actual graph coordinates

The reduced source map must preserve the WHOLE graph-domain summand, not only
selected vertices or endpoint lines. Two exact native/coefficient equations
then give the decorated square, and the SAME-Q native target equation gives
the second square. All source boundaries are complete inverse images. No raw
equation, product Family or section is assumed for these two leg comparisons.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphCoveredEvaluationSquares

open JTParametrizedTargetFamilies (codes)
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

/-- The native operator of an actual decorated comparison after reindexing. -/
def nativePart {I K : Type} [SmallCategory I] [SmallCategory K]
    {W : Source} {x y : Vertex W} (G : I ⥤ K)
    {N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    {M : K ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ G ⋙ M) :
    codes N ⟶ G ⋙ codes M :=
  Functor.whiskerRight r
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.fst NecklaceCode SimplexCategory)

/-- Its actual coefficient operator, retaining every ordinal map. -/
def degreePart {I K : Type} [SmallCategory I] [SmallCategory K]
    {W : Source} {x y : Vertex W} (G : I ⥤ K)
    {N : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
    {M : K ⥤ DecoratedNecklaceHomDiagram.Index W x y} (r : N ⟶ G ⋙ M) :
    JTParametrizedTargetFamilyComparison.degrees N ⟶
      G ⋙ JTParametrizedTargetFamilyComparison.degrees M :=
  Functor.whiskerRight r
    (OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y) ⋙
      CategoryTheory.Prod.snd NecklaceCode SimplexCategory)

private theorem reduced_ext {I : Type} [SmallCategory I]
    {C X : I ⥤ SSet.{0}} (u : C ⟶ X)
    (e : C ⟶ (Functor.const I).obj B) (a : I) {V : Under B}
    {f g : (JTEndpointReducedCover.reduced u e).obj a ⟶ V}
    (h : (pushout.inl u e).app a ≫ f.right = (pushout.inl u e).app a ≫ g.right) :
    f = g := by
  apply Under.UnderMorphism.ext
  apply ((IsPushout.of_hasPushout u e).map ((evaluation I SSet.{0}).obj a)).hom_ext
  · exact h
  · exact (Under.w f).trans (Under.w g).symm

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
      ((nativePart G r).app a).map =
    η.app a ≫ mp.app (G.obj a) ≫
      fst ((codes M).obj (G.obj a)).toSSet (J.obj (mt.obj (G.obj a))))
variable (hq : ∀ a, nq.app a ≫ J.map ((degreePart G r).app a) =
  η.app a ≫ mq.app (G.obj a))

include hi hn hq in
/-- Actual native and coefficient equations compare the complete decorated legs. -/
theorem decorated_square (a : I) :
    (JTGraphCoveredLabelEvaluation.decorated Q N nt nc np nq).app a ≫
        (DecoratedCylinderNecklacePresentation.underDiagram W x y).map (r.app a) =
      s.app a ≫ (JTGraphCoveredLabelEvaluation.decorated Q M mt mc mp mq).app (G.obj a) := by
  apply reduced_ext
  change (ni Q N nt nc np).app a ≫
      (((JTGraphCoveredLabelEvaluation.decorated Q N nt nc np nq).app a).right ≫
        ((DecoratedCylinderNecklacePresentation.underDiagram W x y).map (r.app a)).right) =
    (ni Q N nt nc np).app a ≫ ((s.app a).right ≫
      ((JTGraphCoveredLabelEvaluation.decorated Q M mt mc mp mq).app (G.obj a)).right)
  rw [← Category.assoc, JTGraphCoveredCylinderEquations.decorated_cylinder,
    ← Category.assoc ((ni Q N nt nc np).app a), hi a,
    Category.assoc (η.app a) ((mi Q M mt mc mp).app (G.obj a)),
    JTGraphCoveredCylinderEquations.decorated_cylinder]
  exact JTGraphCoveredComparisonEquations.graph_cylinder_map
    ((nativePart G r).app a) ((degreePart G r).app a)
    (np.app a ≫ fst _ _) (nq.app a) (mp.app (G.obj a) ≫ fst _ _)
    (mq.app (G.obj a)) (η.app a) (hn a) (hq a)

variable (hc : nativePart G r ≫ Functor.whiskerLeft G mc = nc)

include hi hn hc in
/-- The exact native target equation compares the complete legs into the SAME Q. -/
theorem native_square (a : I) :
    (JTGraphCoveredLabelEvaluation.nativeLeg Q N nt nc np).app a =
      s.app a ≫ (JTGraphCoveredLabelEvaluation.nativeLeg Q M mt mc mp).app (G.obj a) := by
  apply reduced_ext
  change (ni Q N nt nc np).app a ≫
      ((JTGraphCoveredLabelEvaluation.nativeLeg Q N nt nc np).app a).right =
    (ni Q N nt nc np).app a ≫ ((s.app a).right ≫
      ((JTGraphCoveredLabelEvaluation.nativeLeg Q M mt mc mp).app (G.obj a)).right)
  rw [JTGraphCoveredComparisonEquations.native_cylinder,
    ← Category.assoc ((ni Q N nt nc np).app a), hi a, Category.assoc,
    JTGraphCoveredComparisonEquations.native_cylinder]
  have h : ((nativePart G r).app a).map ≫ (mc.app (G.obj a)).map = (nc.app a).map :=
    congrArg (fun f : (codes N).obj a ⟶ Q.code ↦ f.map) (NatTrans.congr_app hc a)
  rw [← h]
  simpa only [Category.assoc] using
    congrArg (· ≫ (mc.app (G.obj a)).map) (hn a)

end
end DaggerModels.PartII.JTGraphCoveredEvaluationSquares
