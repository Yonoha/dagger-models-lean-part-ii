import DaggerModelsPartII.JTFiniteCoefficientBridgePullback
import DaggerModelsPartII.JTFiniteCoefficientBridgeSubcollection

/-!
# Comma comparison for ordered subcollections of finite copies
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeSubcollectionComma

open JTFiniteCoefficientBridgeOrder (bridge)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgeSubcollection (coefficientOperator timeOperator)
open JTFiniteCoefficientBridgeCylinder
open JTFiniteCoefficientBridgeReindex (cylinderMap_mapCopies)
open JTNecklaceEndpointCylinder
open JTProjectiveOrderedFiberComparison
open OrderedNecklaceVertexPoints
open OrderedNecklaceLabelDiagram
open DecoratedCylinderNecklacePresentation (underDiagram underCocone)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Raw (W : SegalLocalizers.ReverseDaggerSpace.{0}) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev Labels (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)
private abbrev D (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  JTTargetCommaPullback.diagram W x y Q
private abbrev F (W : SegalLocalizers.ReverseDaggerSpace.{0})
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  BoundaryNecklaceComma.fiberDiagram (D W x y Q)

variable {W : SegalLocalizers.ReverseDaggerSpace.{0}}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)} {T : NecklaceCode}
variable {m m' : ℕ} {k b' : SimplexCategory}
variable {b : Fin (m + 1) → SimplexCategory} {b₂ : Fin (m' + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (d : ∀ e, k ⟶ b₂ e) (u : k ⟶ b')
variable (n : SimplexCategory) (j : ⦋m⦌ ⟶ ⦋m'⦌)
variable (hj : Function.Injective j.toOrderHom)
variable (hr : ∀ (e : Fin (m + 1)) (a : Fin (k.len + 1) × Fin (n.len + 1)),
  JTCommonCoefficientParameter.vertexEquiv (c e) n a =
    JTCommonCoefficientParameter.vertexEquiv (d (j.toOrderHom e)) n a)
variable (z : (Labels W x y T).obj (op (bridge k n m')))

abbrev largerIndex : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (bridge k n m') z

abbrev smallerIndex : DecoratedNecklaceHomDiagram.Index W x y :=
  OrderedLabelElements.mk W (boundaryPoint W x y) T (bridge k n m)
    ((Labels W x y T).map (coefficientOperator c d u n j hj hr).op z)

/-- The ordered label arrow induced by the actual restriction of the larger label. -/
def labelArrow : smallerIndex c d u n j hj hr z ⟶ largerIndex n z := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  let a : (T, bridge k n m) ⟶ (T, bridge k n m') :=
    (𝟙 T, coefficientOperator c d u n j hj hr)
  refine (CategoryOfElements.homMk (P.elementsMk (op (T, bridge k n m')) z)
    (P.elementsMk (op (T, bridge k n m))
      ((Labels W x y T).map (coefficientOperator c d u n j hj hr).op z))
    a.op ?_).op
  let L := orderedNecklaceLabels W (boundaryPoint W x y)
  change (Labels W x y T).map (coefficientOperator c d u n j hj hr).op
    ((L.map (𝟙 (op T))).app (op (bridge k n m')) z) = _
  rw [L.map_id]
  rfl

theorem underDiagram_labelArrow :
    (underDiagram W x y).map (labelArrow c d u n j hj hr z) =
      (under T).map (coefficientOperator c d u n j hj hr) := by
  apply Under.UnderMorphism.ext
  change nativeMap (𝟙 T) (bridge k n m) ≫
    (value T).map (coefficientOperator c d u n j hj hr) = _
  rw [nativeMap_id, Category.id_comp]
  rfl

variable (s : T.toSSet ⟶ J.obj k)

def smallerCylinder : (under T).obj (time m n) ⟶
    (underDiagram W x y).obj (smallerIndex c d u n j hj hr z) :=
  Under.homMk (cylinderMap c u n T s) (cylinderMap_boundary c u n T s)

def largerCylinder : (under T).obj (time m' n) ⟶
    (underDiagram W x y).obj (largerIndex n z) :=
  Under.homMk (cylinderMap d u n T s) (cylinderMap_boundary d u n T s)

theorem cylinder_compare :
    smallerCylinder c d u n j hj hr z s ≫
        (underDiagram W x y).map (labelArrow c d u n j hj hr z) =
      (under T).map (timeOperator n j hj) ≫ largerCylinder d u n z s := by
  rw [underDiagram_labelArrow]
  apply Under.UnderMorphism.ext
  exact cylinderMap_mapCopies c d u n j hj hr T s

variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))
variable (V : (under T).obj (time m n) ⟶
  (D W x y Q).obj (smallerIndex c d u n j hj hr z))
variable (U : (under T).obj (time m' n) ⟶ (D W x y Q).obj (largerIndex n z))
variable (hV : V ≫ JTTargetCommaPullback.fst W x y Q
    (smallerIndex c d u n j hj hr z) = smallerCylinder c d u n j hj hr z s)
variable (hU : U ≫ JTTargetCommaPullback.fst W x y Q (largerIndex n z) =
  largerCylinder d u n z s)
variable (hN : V ≫ JTTargetCommaPullback.snd W x y Q
    (smallerIndex c d u n j hj hr z) =
  (under T).map (timeOperator n j hj) ≫ U ≫
    JTTargetCommaPullback.snd W x y Q (largerIndex n z))

include hV hU hN in
/-- Equality of actual lifts from equality of decorated and native projections. -/
theorem lift_compare :
    V ≫ (D W x y Q).map (labelArrow c d u n j hj hr z) =
      (under T).map (timeOperator n j hj) ≫ U := by
  apply pullback.hom_ext (f := (underCocone W x y).app (largerIndex n z))
    (g := JTTargetCommaPullback.targetMap W x y Q)
  · change (_ ≫ _) ≫ JTTargetCommaPullback.fst W x y Q (largerIndex n z) =
      (_ ≫ U) ≫ JTTargetCommaPullback.fst W x y Q (largerIndex n z)
    rw [Category.assoc, JTTargetCommaPullback.map_fst, ← Category.assoc, hV,
      cylinder_compare c d u n j hj hr z s, Category.assoc, hU]
  · change (_ ≫ _) ≫ JTTargetCommaPullback.snd W x y Q (largerIndex n z) =
      (_ ≫ U) ≫ JTTargetCommaPullback.snd W x y Q (largerIndex n z)
    rw [Category.assoc, JTTargetCommaPullback.map_snd]
    simpa only [Category.assoc] using hN

def smallerJoinedComma :
    CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj (time m n)) ⥤
      CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  CostructuredArrow.map V ⋙
    Grothendieck.ι (F W x y Q) (smallerIndex c d u n j hj hr z) ⋙
      (JTTargetCommaPullback.equivalence W x y Q).inverse

def largerJoinedComma :
    CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj (time m' n)) ⥤
      CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  CostructuredArrow.map U ⋙
    Grothendieck.ι (F W x y Q) (largerIndex n z) ⋙
      (JTTargetCommaPullback.equivalence W x y Q).inverse

/-- The comparison before transport through the target equivalence. -/
def comparePresentation :
    CostructuredArrow.map V ⋙
        Grothendieck.ι (F W x y Q) (smallerIndex c d u n j hj hr z) ⟶
      CostructuredArrow.map ((under T).map (timeOperator n j hj) ≫ U) ⋙
        Grothendieck.ι (F W x y Q) (largerIndex n z) := by
  let a := labelArrow c d u n j hj hr z
  let G := BoundaryNecklaceComma.diagram
  have H : (G.map V).toFunctor ⋙ ((F W x y Q).map a).toFunctor =
      (G.map ((under T).map (timeOperator n j hj) ≫ U)).toFunctor := by
    change (G.map V).toFunctor ⋙ (G.map ((D W x y Q).map a)).toFunctor = _
    have hh := congrArg Cat.Hom.toFunctor (G.map_comp V ((D W x y Q).map a))
    change (G.map (V ≫ (D W x y Q).map a)).toFunctor = _ at hh
    rw [lift_compare c d u n j hj hr z s Q V U hV hU hN] at hh
    exact hh.symm
  exact Functor.whiskerLeft (CostructuredArrow.map V)
      (Grothendieck.ιNatTrans (F := F W x y Q) a) ≫
    eqToHom (by
      change ((G.map V).toFunctor ⋙ ((F W x y Q).map a).toFunctor) ⋙
        Grothendieck.ι (F W x y Q) (largerIndex n z) = _
      rw [H]
      rfl)

/-- Natural comparison of the original smaller joined comma with the time restriction
of the original larger joined comma. -/
def compareJoinedComma : smallerJoinedComma c d u n j hj hr z Q V ⟶
    CostructuredArrow.map ((under T).map (timeOperator n j hj)) ⋙
      largerJoinedComma n z Q U := by
  let G := BoundaryNecklaceComma.diagram
  have K := congrArg Cat.Hom.toFunctor
    (G.map_comp ((under T).map (timeOperator n j hj)) U)
  change CostructuredArrow.map ((under T).map (timeOperator n j hj) ≫ U) =
    CostructuredArrow.map ((under T).map (timeOperator n j hj)) ⋙
      CostructuredArrow.map U at K
  exact Functor.whiskerRight
      (comparePresentation c d u n j hj hr z s Q V U hV hU hN)
      (JTTargetCommaPullback.equivalence W x y Q).inverse ≫
    eqToHom (by simp only [largerJoinedComma, K, Functor.assoc])

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeSubcollectionComma
