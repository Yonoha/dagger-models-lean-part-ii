import DaggerModelsPartII.JTChangingCoefficientBridgeLabels
import DaggerModelsPartII.JTChangingCoefficientBridgeZigzag

/-!
# Comparing independently prescribed labels and lifts in the original comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTChangingCoefficientBridgeComparison

open JTHigherInterleavedParameter (common)
open JTChangingCoefficientBridgeOrder JTChangingCoefficientBridgeTime
open JTChangingCoefficientBridgePrism (vertical)
open JTChangingCoefficientBridgeLift (sideVertical)
open JTChangingCoefficientBridgeFamilies JTChangingCoefficientBridgeLabels
open JTChangingCoefficientBridgeCylinder JTChangingCoefficientBridgePullback
open JTChangingCoefficientBridgeZigzag
open JTProjectiveOrderedFiberComparison JTNecklaceEndpointCylinder
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement MixedGraphCylinderTraversal
open JTHigherMixedGraphTargetLift (toNativeTarget toNativeTarget_natural)
open DaggerChosenRigidificationNecklace.NecklaceCode
open OrderedNecklaceVertexPoints OrderedNecklaceLabelDiagram
open DecoratedCylinderNecklacePresentation (underDiagram)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev simplex (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J := GroupoidSimplex.parameter
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} {T : NecklaceCode}
variable {k b b' : SimplexCategory} (c : k ⟶ b) (h : b ⟶ b') (n : SimplexCategory)

private abbrev Labels (W : Source) (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

private abbrev Fiber (T : NecklaceCode) (a : SimplexCategory) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj a)

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev D := JTTargetCommaPullback.diagram W x y Q
private abbrev Original :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q

/-- An independently prescribed original label in the source order of a comparison. -/
abbrev prescribedIndex (w : (Labels W x y T).obj (op (common k n))) :
    DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (common k n) w

/-- The prescribed decorated leg of the comparison over that label. -/
def prescribedCylinder (s : T.toSSet ⟶ J.obj k)
    (w : (Labels W x y T).obj (op (common k n))) (e : Fin 2) :
    (under T).obj n ⟶ (underDiagram W x y).obj (prescribedIndex n w) :=
  Under.homMk (sideCylinderMap c h n T s e) (by
    change (boundary T).app n ≫ sideCylinderMap c h n T s e = (boundary T).app (common k n)
    by_cases he : e = 0 <;>
      simp only [sideCylinderMap, he, if_true, if_false,
        JTCommonCoefficientParameter.cylinderMap_boundary])

/-- The original target-comma functor of a prescribed side lift. -/
def prescribedComma (w : (Labels W x y T).obj (op (common k n)))
    (V : (under T).obj n ⟶ (D Q).obj (prescribedIndex n w)) : Fiber T n ⥤ Original Q :=
  CostructuredArrow.map V ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (D Q)) (prescribedIndex n w) ⋙
    (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem prescribedComma_eq
    (z : (Labels W x y T).obj (op (bridge k n))) (s : T.toSSet ⟶ J.obj k)
    (U : (under T).obj (time n) ⟶ (D Q).obj (bridgeIndex n z))
    (hU : U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
      bridgeCylinder c h n z s) (e : Fin 2)
    (w : (Labels W x y T).obj (op (common k n)))
    (hw : w = (Labels W x y T).map (side c h n e).op z)
    (V : (under T).obj n ⟶ (D Q).obj (prescribedIndex n w))
    (hV : V ≫ JTTargetCommaPullback.fst W x y Q (prescribedIndex n w) =
      prescribedCylinder c h n s w e)
    (hNative : V ≫ JTTargetCommaPullback.snd W x y Q (prescribedIndex n w) =
      (under T).map (timeSide n e) ≫ U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)) :
    prescribedComma n Q w V = sideComma c h n z Q U s hU e := by
  subst w
  have H := sideLift_eq c h n z s Q U hU e V hV hNative
  rw [H]
  rfl

section Raw

variable {d : ℕ}
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {q : (single d).toSSet ⟶ Raw W}
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target := (⟨single d, q, qx, qy⟩ : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

variable (E : (e : Fin 2) → EdgeFamilies W ⦋d⦌ (common k n) (sideRow c h n f e)
  (s ≫ J.map (sideSlice c h n e)) x y)

private abbrev sideLabel (e : Fin 2) := JTMixedGraphOrderedLabel.orderedPoint (E e)

variable (V : (e : Fin 2) →
  (under (code d)).obj n ⟶
    (D (target qx qy)).obj (prescribedIndex n (sideLabel c h n f s E e)))

/-- Independent stationary side labels and lifts over the fixed native
map compare through one original joining comma functor. Both comparisons
are natural on all internal necklace maps, and their values lie in the
same component for arbitrary internal necklaces on the two sides. -/
theorem exists_compare_prescribed
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map (c ≫ h) ≫ f) s = q)
    (hleft : ∀ e, SSet.stdSimplex.map (sideVertical c h n (graphIndex ⦋d⦌ k s 0) e) ≫
      (E e).left =
      term (simplex n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hright : ∀ e, SSet.stdSimplex.map (sideVertical c h n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫
      (E e).right =
      term (simplex n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hV : ∀ e, V e ≫ JTTargetCommaPullback.fst W x y (target qx qy)
      (prescribedIndex n (sideLabel c h n f s E e)) =
      prescribedCylinder c h n (nativeGraphParameter s) (sideLabel c h n f s E e) e)
    (hNative : ∀ e, V e ≫ JTTargetCommaPullback.snd W x y (target qx qy)
      (prescribedIndex n (sideLabel c h n f s E e)) = toNativeTarget d n) :
    let Q := target qx qy
    let G := fun e ↦ prescribedComma n Q (sideLabel c h n f s E e) (V e)
    ∃ F : Fiber (code d) (time n) ⥤ Original Q,
      (∀ e, Nonempty (G e ⟶ CostructuredArrow.map ((under (code d)).map (timeSide n e)) ⋙ F)) ∧
      ∀ P P' : Fiber (code d) n,
        Relation.EqvGen (fun A B : Original Q ↦ Nonempty (A ⟶ B))
          ((G 0).obj P) ((G 1).obj P') := by
  intro Q G
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hq qx qy
  obtain ⟨B, hB₀, hB₁, hL, hR⟩ :=
    exists_bridgeFamilies c h n hW d f s x y hx hy E hleft hright
  let z := JTMixedGraphOrderedLabel.orderedPoint B
  obtain ⟨U, hU, hN⟩ := exists_lift_over_raw c h n f s hq qx qy B hL hR
  let p := nativeGraphParameter s
  have hG (e : Fin 2) : G e = sideComma c h n z Q U p hU e := by
    refine prescribedComma_eq c h n Q z p U hU e _ ?_ (V e) (hV e) ?_
    · exact (orderedPoint_side c h n f s B e (E e) (hB₀ e) (hB₁ e)).symm
    · rw [hNative e, hN]
      exact (toNativeTarget_natural d (timeSide n e)).symm
  refine ⟨joinedComma n z Q U, ?_, ?_⟩
  · intro e
    rw [hG]
    exact ⟨compareSide c h n z Q U p hU e⟩
  · intro P P'
    rw [hG, hG]
    exact side_zigzag c h n z Q U p hU P P'

end Raw

end

end DaggerModels.PartII.JTChangingCoefficientBridgeComparison
