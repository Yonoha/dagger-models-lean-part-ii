import DaggerModelsPartII.JTFiniteCoefficientBridgeFamilies
import DaggerModelsPartII.JTFiniteCoefficientBridgePullback

/-!
# Comparing independently prescribed labels and lifts in the original comma
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeComparison

open JTHigherInterleavedParameter (common)
open JTFiniteCoefficientBridgeOrder JTFiniteCoefficientBridgeTime
open JTFiniteCoefficientBridgePrism (vertical)
open JTFiniteCoefficientBridgeVertexLift (sideVertical)
open JTFiniteCoefficientBridgeFamilies
open JTFiniteCoefficientBridgeCylinder JTFiniteCoefficientBridgePullback
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
variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (h : ∀ e, b e ⟶ b')
variable (hu : ∀ e, c e ≫ h e = u) (n : SimplexCategory)

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
    (w : (Labels W x y T).obj (op (common k n))) (e : Fin (m + 1)) :
    (under T).obj n ⟶ (underDiagram W x y).obj (prescribedIndex n w) :=
  Under.homMk (JTCommonCoefficientParameter.cylinderMap T (c e) s n)
    (JTCommonCoefficientParameter.cylinderMap_boundary T (c e) s n)

/-- The original target-comma functor of a prescribed side lift. -/
def prescribedComma (w : (Labels W x y T).obj (op (common k n)))
    (V : (under T).obj n ⟶ (D Q).obj (prescribedIndex n w)) : Fiber T n ⥤ Original Q :=
  CostructuredArrow.map V ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (D Q)) (prescribedIndex n w) ⋙
    (JTTargetCommaPullback.equivalence W x y Q).inverse

private theorem prescribedComma_eq
    (z : (Labels W x y T).obj (op (bridge k n m))) (s : T.toSSet ⟶ J.obj k)
    (U : (under T).obj (time m n) ⟶ (D Q).obj (bridgeIndex n z))
    (hU : U ≫ JTTargetCommaPullback.fst W x y Q (bridgeIndex n z) =
      bridgeCylinder c u n z s) (e : Fin (m + 1))
    (w : (Labels W x y T).obj (op (common k n)))
    (hw : w = (Labels W x y T).map (side c u h hu n e).op z)
    (V : (under T).obj n ⟶ (D Q).obj (prescribedIndex n w))
    (hV : V ≫ JTTargetCommaPullback.fst W x y Q (prescribedIndex n w) =
      prescribedCylinder c n s w e)
    (hNative : V ≫ JTTargetCommaPullback.snd W x y Q (prescribedIndex n w) =
      (under T).map (timeSide n e) ≫ U ≫ JTTargetCommaPullback.snd W x y Q (bridgeIndex n z)) :
    prescribedComma n Q w V =
      sidePresentation c u h hu n z s Q U hU e ⋙
        (JTTargetCommaPullback.equivalence W x y Q).inverse := by
  subst w
  have H := sideLift_eq c u h hu n z s Q U hU e V hV hNative
  rw [H]
  rfl

section Raw

variable {d : ℕ}
variable (f : simplex b' ⟶ row W ⦋d⦌) (s : simplex ⦋d⦌ ⟶ J.obj k)
variable {q : (single d).toSSet ⟶ Raw W}
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target := (⟨single d, q, qx, qy⟩ : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

variable (E : (e : Fin (m + 1)) → EdgeFamilies W ⦋d⦌ (common k n) (sideRow c u h hu n f e)
  (s ≫ J.map (sideSlice c n e)) x y)

private abbrev sideLabel (e : Fin (m + 1)) := JTMixedGraphOrderedLabel.orderedPoint (E e)

variable (V : (e : Fin (m + 1)) →
  (under (code d)).obj n ⟶
    (D (target qx qy)).obj (prescribedIndex n (sideLabel c u h hu n f s E e)))

/-- All independently prescribed stationary labels and lifts compare
naturally to the same joining functor through their own exact time faces. -/
theorem exists_compare_prescribed
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (hq : nativeRawGraph W d k (SSet.stdSimplex.map u ≫ f) s = q)
    (hleft : ∀ e, SSet.stdSimplex.map (sideVertical c n (graphIndex ⦋d⦌ k s 0) e) ≫
      (E e).left =
      term (simplex n) ≫ vertexPoint W x ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hright : ∀ e, SSet.stdSimplex.map (sideVertical c n (graphIndex ⦋d⦌ k s (Fin.last d)) e) ≫
      (E e).right =
      term (simplex n) ≫ vertexPoint W y ≫ JTEndpointNormalizationLifts.identityFamily W)
    (hV : ∀ e, V e ≫ JTTargetCommaPullback.fst W x y (target qx qy)
      (prescribedIndex n (sideLabel c u h hu n f s E e)) =
      prescribedCylinder c n (nativeGraphParameter s) (sideLabel c u h hu n f s E e) e)
    (hNative : ∀ e, V e ≫ JTTargetCommaPullback.snd W x y (target qx qy)
      (prescribedIndex n (sideLabel c u h hu n f s E e)) = toNativeTarget d n) :
    let Q := target qx qy
    let G := fun e ↦ prescribedComma n Q (sideLabel c u h hu n f s E e) (V e)
    ∃ F : Fiber (code d) (time m n) ⥤ Original Q,
      ∀ e, Nonempty (G e ⟶ CostructuredArrow.map ((under (code d)).map (timeSide n e)) ⋙ F) := by
  intro Q G
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hq qx qy
  obtain ⟨B, hB₀, hB₁, hL, hR⟩ :=
    exists_bridgeFamilies c u h hu n hW d f s x y hx hy E hleft hright
  let z := JTMixedGraphOrderedLabel.orderedPoint B
  obtain ⟨U, hU, hN⟩ := exists_lift_over_raw c u n f s hq qx qy B hL hR
  let p := nativeGraphParameter s
  have hG (e : Fin (m + 1)) : G e =
      sidePresentation c u h hu n z p Q U hU e ⋙
        (JTTargetCommaPullback.equivalence W x y Q).inverse := by
    refine prescribedComma_eq c u h hu n Q z p U hU e _ ?_ (V e) (hV e) ?_
    · exact (orderedPoint_side c u h hu n f s B e (E e) (hB₀ e) (hB₁ e)).symm
    · rw [hNative e, hN]
      exact (toNativeTarget_natural d (timeSide n e)).symm
  refine ⟨joinedComma n z Q U, fun e ↦ ?_⟩
  rw [hG]
  exact ⟨compareComma c u h hu n z p Q U hU e⟩

end Raw

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeComparison
