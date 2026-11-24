import DaggerModelsPartII.JTChangingCoefficientBridgeRaw
import DaggerModelsPartII.JTCommonCoefficientFinalComma

/-!
# Both side comparisons in the original target pullback and comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTChangingCoefficientBridgePullback

open JTHigherInterleavedParameter (common)
open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgeCylinder
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} {T : NecklaceCode}
variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

private abbrev Labels (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable (z : (Labels W x y T).obj (op (bridge k n)))

abbrev bridgeIndex : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (bridge k n) z

abbrev sideIndex (e : Fin 2) : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (common k n)
    ((Labels W x y T).map (side c h n e).op z)

/-- The original decorated label operator with identity necklace code. -/
def sideArrow (e : Fin 2) : sideIndex c h n z e ⟶ bridgeIndex n z := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let a : (T, common k n) ⟶ (T, bridge k n) := (𝟙 T, side c h n e)
  refine (CategoryOfElements.homMk (P.elementsMk (op (T, bridge k n)) z)
    (P.elementsMk (op (T, common k n)) ((Labels W x y T).map (side c h n e).op z))
    a.op ?_).op
  let F := orderedNecklaceLabels W (boundaryPoint W x y)
  change (Labels W x y T).map (side c h n e).op
    ((F.map (𝟙 (op T))).app (op (bridge k n)) z) = _
  rw [F.map_id]
  rfl

theorem underDiagram_sideArrow (e : Fin 2) :
    (underDiagram W x y).map (sideArrow c h n z e) = (under T).map (side c h n e) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 T) (common k n) ≫ (value T).map (side c h n e) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

variable (s : T.toSSet ⟶ J.obj k)

def bridgeCylinder : (under T).obj (time n) ⟶ (underDiagram W x y).obj (bridgeIndex n z) :=
  Under.homMk (cylinderMap c h n T s) (cylinderMap_boundary c h n T s)

def sideCylinder (e : Fin 2) :
    (under T).obj n ⟶ (underDiagram W x y).obj (sideIndex c h n z e) :=
  Under.homMk (sideCylinderMap c h n T s e) (by
    change (boundary T).app n ≫ sideCylinderMap c h n T s e = (boundary T).app (common k n)
    by_cases he : e = 0 <;>
      simp only [sideCylinderMap, he, if_true, if_false,
        JTCommonCoefficientParameter.cylinderMap_boundary])

theorem sideCylinder_compare (e : Fin 2) :
    sideCylinder c h n z s e ≫ (underDiagram W x y).map (sideArrow c h n z e) =
      (under T).map (timeSide n e) ≫ bridgeCylinder c h n z s := by
  rw [underDiagram_sideArrow]
  apply Under.UnderMorphism.ext
  exact (cylinderMap_side c h n T s e).symm

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q
private abbrev F := BoundaryNecklaceComma.fiberDiagram (D Q)
private abbrev Fiber := CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj n)
private abbrev Original := CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

variable (U : (under T).obj (time n) ⟶ (D Q).obj (bridgeIndex n z))
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
  bridgeCylinder c h n z s)

/-- Pull the joining lift back to either side, using the original
time restriction on the native projection. -/
def sideLift (e : Fin 2) : (under T).obj n ⟶ (D Q).obj (sideIndex c h n z e) :=
  pullback.lift (sideCylinder c h n z s e)
    ((under T).map (timeSide n e) ≫ U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)) (by
      change sideCylinder c h n z s e ≫ (underCocone W x y).app (sideIndex c h n z e) = _
      have Hnat : (underDiagram W x y).map (sideArrow c h n z e) ≫
          (underCocone W x y).app (bridgeIndex n z) =
          (underCocone W x y).app (sideIndex c h n z e) := by
        simpa only [Functor.const_obj_map, Category.comp_id] using
          (underCocone W x y).naturality (sideArrow c h n z e)
      rw [← Hnat, ← Category.assoc, sideCylinder_compare, Category.assoc, ← hU]
      simp only [Category.assoc, JTTargetCommaPullback.condition])

@[reassoc]
theorem sideLift_fst (e : Fin 2) :
    sideLift c h n z s Q U hU e ≫ JTTargetCommaPullback.fst W x y Q (sideIndex c h n z e) =
      sideCylinder c h n z s e :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem sideLift_snd (e : Fin 2) :
    sideLift c h n z s Q U hU e ≫ JTTargetCommaPullback.snd W x y Q (sideIndex c h n z e) =
      (under T).map (timeSide n e) ≫ U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z) :=
  pullback.lift_snd _ _ _

theorem sideLift_compare (e : Fin 2) :
    sideLift c h n z s Q U hU e ≫ (D Q).map (sideArrow c h n z e) =
      (under T).map (timeSide n e) ≫ U := by
  apply pullback.hom_ext (f := (underCocone W x y).app (bridgeIndex n z))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
      (_ ≫ U) ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z)
    rw [Category.assoc, JTTargetCommaPullback.map_fst, sideLift_fst_assoc,
      sideCylinder_compare, Category.assoc, hU]
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z) =
      (_ ≫ U) ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)
    rw [Category.assoc, JTTargetCommaPullback.map_snd, sideLift_snd, Category.assoc]

/-- Both projections characterize the side lift, including independently
supplied lifts having the same restricted label and native projection. -/
theorem sideLift_eq (e : Fin 2)
    (V : (under T).obj n ⟶ (D Q).obj (sideIndex c h n z e))
    (hV₁ : V ≫ JTTargetCommaPullback.fst W x y Q (sideIndex c h n z e) =
      sideCylinder c h n z s e)
    (hV₂ : V ≫ JTTargetCommaPullback.snd W x y Q (sideIndex c h n z e) =
      (under T).map (timeSide n e) ≫ U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)) :
    V = sideLift c h n z s Q U hU e := by
  apply pullback.hom_ext (f := (underCocone W x y).app (sideIndex c h n z e))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · exact hV₁.trans (sideLift_fst c h n z s Q U hU e).symm
  · exact hV₂.trans (sideLift_snd c h n z s Q U hU e).symm

def sidePresentation (e : Fin 2) : Fiber (T := T) n ⥤ JTTargetCommaPullback.Presentation W x y Q :=
  CostructuredArrow.map (sideLift c h n z s Q U hU e) ⋙
    Grothendieck.ι (F Q) (sideIndex c h n z e)

def bridgePresentation (e : Fin 2) :
    Fiber (T := T) n ⥤ JTTargetCommaPullback.Presentation W x y Q :=
  CostructuredArrow.map ((under T).map (timeSide n e) ≫ U) ⋙
    Grothendieck.ι (F Q) (bridgeIndex n z)

def comparePresentation (e : Fin 2) :
    sidePresentation c h n z s Q U hU e ⟶ bridgePresentation n z Q U e := by
  let a := sideArrow c h n z e
  let G := BoundaryNecklaceComma.diagram
  have H : (G.map (sideLift c h n z s Q U hU e)).toFunctor ⋙ ((F Q).map a).toFunctor =
      (G.map ((under T).map (timeSide n e) ≫ U)).toFunctor := by
    change (G.map (sideLift c h n z s Q U hU e)).toFunctor ⋙ (G.map ((D Q).map a)).toFunctor = _
    have hh := congrArg Cat.Hom.toFunctor
      (G.map_comp (sideLift c h n z s Q U hU e) ((D Q).map a))
    change (G.map (sideLift c h n z s Q U hU e ≫ (D Q).map a)).toFunctor = _ at hh
    rw [sideLift_compare c h n z s Q U hU e] at hh
    exact hh.symm
  exact Functor.whiskerLeft (CostructuredArrow.map (sideLift c h n z s Q U hU e))
      (Grothendieck.ιNatTrans (F := F Q) a) ≫
    eqToHom (by
      change ((G.map (sideLift c h n z s Q U hU e)).toFunctor ⋙ ((F Q).map a).toFunctor) ⋙
        Grothendieck.ι (F Q) (bridgeIndex n z) = _
      rw [H]
      rfl)

/-- Both changes of label act by natural transformations in the
original comma, with the original native necklace maps. -/
def compareComma (e : Fin 2) :
    sidePresentation c h n z s Q U hU e ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse ⟶
      bridgePresentation n z Q U e ⋙ (JTTargetCommaPullback.equivalence W x y Q).inverse :=
  Functor.whiskerRight (comparePresentation c h n z s Q U hU e)
    (JTTargetCommaPullback.equivalence W x y Q).inverse

section RawGraph

open JTChangingCoefficientBridgePrism (slice vertical)
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open DaggerChosenRigidificationNecklace.NecklaceCode

private abbrev simplex (a : SimplexCategory) := SSet.stdSimplex.{0}.obj a
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- Use the whole raw comparison to give a lift into the original target
pullback with the prescribed decorated and native legs. -/
theorem exists_lift_over_raw {d : ℕ} (f : simplex b' ⟶ row W ⦋d⦌)
    (s : simplex ⦋d⦌ ⟶ J.obj k) {q : (single d).toSSet ⟶ Raw W}
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map (c ≫ h) ≫ f) s = q)
    (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
    (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)
    (E : EdgeFamilies W ⦋d⦌ (bridge k n) (SSet.stdSimplex.map (base c h n) ≫ f)
      (s ≫ J.map (slice c h n 0)) x y)
    (hL : SSet.stdSimplex.map (vertical c h n (graphIndex ⦋d⦌ k s 0)) ≫ E.left =
      term (simplex (time n)) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hR : SSet.stdSimplex.map (vertical c h n (graphIndex ⦋d⦌ k s (Fin.last d))) ≫ E.right =
      term (simplex (time n)) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W) :
    let z := JTMixedGraphOrderedLabel.orderedPoint E
    let Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y) := ⟨single d, q, qx, qy⟩
    ∃ U : (under (code d)).obj (time n) ⟶ (D Q).obj (bridgeIndex n z),
      U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
        bridgeCylinder c h n z (nativeGraphParameter s) ∧
      U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z) =
        JTHigherMixedGraphTargetLift.toNativeTarget d (time n) := by
  intro z Q
  let L := bridgeCylinder c h n z (nativeGraphParameter s)
  let N := JTHigherMixedGraphTargetLift.toNativeTarget d (time n)
  have H : L ≫ (underCocone W x y).app (bridgeIndex n z) =
      N ≫ JTTargetCommaPullback.targetMap W x y Q := by
    apply Under.UnderMorphism.ext
    exact JTChangingCoefficientBridgeRaw.whole_raw c h n f s E hq qx qy hL hR
  exact ⟨pullback.lift L N H, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

end RawGraph

end

end DaggerModels.PartII.JTChangingCoefficientBridgePullback
