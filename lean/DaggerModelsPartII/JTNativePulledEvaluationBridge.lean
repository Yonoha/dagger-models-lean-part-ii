import DaggerModelsPartII.JTNativePulledComparisonComposition

/-!
The complete native restriction-fiber evaluation is compared with the one
strict evaluation on all restrictions into a fixed ambient source. The
comparison between the inverse equivalence and its exact copy is explicit.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativePulledEvaluationBridge

open BoundaryNecklaceComma (fiberDiagram necklaceUnder)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {A I : Type} [SmallCategory A] [SmallCategory I]
variable (E : I ⥤ Under B) (C : A ⥤ Under B)
variable (L : A ⥤ I) (ρ : C ⟶ L ⋙ E) (a : A)

private theorem sourceCode_fiber (E : I ⥤ Under B) (i : I)
    {P P' : (fiberDiagram E).obj i} (f : P ⟶ P') :
    (BoundaryNecklaceComma.sourceCode E).map
      ((Grothendieck.ι (fiberDiagram E) i).map f) = f.left := by
  change ((Grothendieck.ι (fiberDiagram E) i).map f).fiber.left = f.left
  rw [Grothendieck.ι_map]
  dsimp only
  rw [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  simp

/-- Mapping the whole Grothendieck presentation and then restricting to one
fiber has the same objects as mapping that fiber directly. -/
theorem mapPresentation_fiber_obj
    (P : (fiberDiagram C).obj a) :
    (Grothendieck.ι (fiberDiagram C) a ⋙
      JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ).obj P =
      (CostructuredArrow.map (ρ.app a) ⋙
        Grothendieck.ι (fiberDiagram E) (L.obj a)).obj P := rfl

/-- The same restriction formula holds on every internal-necklace morphism. -/
theorem mapPresentation_fiber_map
    {P P' : (fiberDiagram C).obj a} (f : P ⟶ P') :
    (Grothendieck.ι (fiberDiagram C) a ⋙
      JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ).map f =
      (CostructuredArrow.map (ρ.app a) ⋙
        Grothendieck.ι (fiberDiagram E) (L.obj a)).map f := by
  apply JTTargetCommaPullback.operator_ext
  · simp [JTBoundaryNecklacePresentationCone.mapPresentation,
      Grothendieck.ι, Grothendieck.pre, Grothendieck.map]
  · change (BoundaryNecklaceComma.sourceCode E).map
        ((JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ).map
          ((Grothendieck.ι (fiberDiagram C) a).map f)) =
      (BoundaryNecklaceComma.sourceCode E).map
        ((Grothendieck.ι (fiberDiagram E) (L.obj a)).map
          ((CostructuredArrow.map (ρ.app a)).map f))
    rw [JTBoundaryNecklacePresentationCone.mapPresentation_code]
    change (BoundaryNecklaceComma.sourceCode C).map
      ((Grothendieck.ι (fiberDiagram C) a).map f) =
        (BoundaryNecklaceComma.sourceCode E).map
          ((Grothendieck.ι (fiberDiagram E) (L.obj a)).map
            ((CostructuredArrow.map (ρ.app a)).map f))
    rw [sourceCode_fiber C a, sourceCode_fiber E (L.obj a)]
    rfl

/-- The complete presentation restriction is strict, on both objects and
all internal-necklace operators. -/
theorem mapPresentation_fiber :
    Grothendieck.ι (fiberDiagram C) a ⋙
        JTBoundaryNecklacePresentationCone.mapPresentation E C L ρ =
      CostructuredArrow.map (ρ.app a) ⋙
        Grothendieck.ι (fiberDiagram E) (L.obj a) := by
  refine CategoryTheory.Functor.ext (mapPresentation_fiber_obj E C L ρ a) ?_
  intro P P' f
  simpa using mapPresentation_fiber_map E C L ρ a f

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Index (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time)

private abbrev cylinders :=
  JTParametrizedTargetFamilies.cylinders (L := L) (time := time)
private abbrev diagram := JTTargetCommaPullback.diagram W x y Q

/-- On one whole internal-necklace fiber, the exact target evaluation is
the restriction of the one total family evaluation. -/
theorem exactFiber_eq_total (a : A) :
    (CostructuredArrow.map
        ((JTParametrizedTargetFamilies.liftNatural F).app a) ⋙
      Grothendieck.ι (fiberDiagram (diagram (W := W) (x := x) (y := y) (Q := Q)))
        (L.obj a)) ⋙ JTTargetCommaExactEvaluation.fromPresentation W x y Q =
      Grothendieck.ι (fiberDiagram (cylinders (L := L) (time := time))) a ⋙
        JTParametrizedTargetFamilies.evaluate F := by
  rw [← mapPresentation_fiber
    (diagram (W := W) (x := x) (y := y) (Q := Q))
    (cylinders (L := L) (time := time)) L
    (JTParametrizedTargetFamilies.liftNatural F) a]
  rfl

/-- The legacy inverse evaluator and the exact evaluator are related by
the existing `inverseIso`; the fiber restriction is then the total family
evaluation. No equality of the two evaluator functors is asserted. -/
def fiberEvaluationIso (a : A) :
    (CostructuredArrow.map
        ((JTParametrizedTargetFamilies.liftNatural F).app a) ⋙
      Grothendieck.ι (fiberDiagram (diagram (W := W) (x := x) (y := y) (Q := Q)))
        (L.obj a)) ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse ≅
      Grothendieck.ι (fiberDiagram (cylinders (L := L) (time := time))) a ⋙
        JTParametrizedTargetFamilies.evaluate F :=
  Functor.isoWhiskerLeft
    (CostructuredArrow.map
      ((JTParametrizedTargetFamilies.liftNatural F).app a) ⋙
        Grothendieck.ι
          (fiberDiagram (diagram (W := W) (x := x) (y := y) (Q := Q)))
          (L.obj a))
    (JTTargetCommaExactEvaluation.inverseIso W x y Q) ≪≫
      eqToIso (exactFiber_eq_total F a)

private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W
    (OrderedNecklaceVertexPoints.boundaryPoint W x y)
private abbrev T (W : Source) (x y : Vertex W) (i : Index W x y) :=
  ((pr W x y).obj i).1
private abbrev k (W : Source) (x y : Vertex W) (i : Index W x y) :=
  ((pr W x y).obj i).2
private abbrev J := GroupoidSimplex.parameter

variable (i : Index W x y) (n : SimplexCategory)
variable (c : T W x y i ⟶ Q.code)
variable (p : (T W x y i).toSSet ⊗ J.obj n ⟶ J.obj (k W x y i))
variable (hr :
  (JTParametrizedTargetLiftTransport.graph (i := i) p).right ≫
      ((DecoratedCylinderNecklacePresentation.underCocone W x y).app i).right =
    NecklaceCylinderAugmentation.augmentation (T W x y i) n ≫ c.map ≫ Q.map)

include hr in
/-- For an actual native subdivision, the legacy complete fiber evaluation
is naturally isomorphic to the restriction of the single strict family
evaluation over all subdivisions of this fixed ambient source. -/
def nativeEvaluationIso (r : Over (T W x y i)) :
    JTNativePulledCutComparison.evaluation i n c p hr r.hom ≅
      Grothendieck.ι
          (fiberDiagram
            (JTParametrizedTargetFamilies.cylinders
              (L := JTNativePulledFamilyDiagram.labels i)
              (time := JTNativePulledFamilyDiagram.time i n))) r ⋙
        JTParametrizedTargetFamilies.evaluate
          (JTNativePulledFamilyDiagram.family i n c p hr) :=
  fiberEvaluationIso (JTNativePulledFamilyDiagram.family i n c p hr) r

end
end DaggerModels.PartII.JTNativePulledEvaluationBridge
