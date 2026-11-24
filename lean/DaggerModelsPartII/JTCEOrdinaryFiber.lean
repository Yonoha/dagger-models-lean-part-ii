import DaggerModelsPartII.JTCylinderAugmentationWeak
import DaggerModelsPartII.JTRightAdjointOrderedFiber
import DaggerModelsPartII.JTChosenCEUnitBoundary

/-!
# Literal CE Hom and the original ordinary ordered right fiber

The CE Hom is identified with the categorical fiber of the original ordinary
JT nerve, keeping the actual ordered boundary and both original endpoint maps.
The chosen unit acts by its original ordinary adjoint on this fiber.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty Opposite Simplicial
  DaggerModels

namespace DaggerModels.PartII.JTCEOrdinaryFiber

open JTXiEndpointCollapse JTUnderlyingOrderedFibers
open JTRightAdjointOrderedFiber JTCEPlainMappingTarget
open JTChosenCEUnitBoundary JTChosenOrdinaryAdjoint
open JTStrictificationCoefficients
open OrdinaryRigidification.DaggerNerve

noncomputable section

/-- The literal evaluated CE pushout, with its original two coprojections. -/
private def cePushout (k : SimplexCategory) :
    IsPushout (cylinderInclusion.app k) (cylinderProjection.app k)
      (CE_interval.app k) (CE_boundary.app k) :=
  (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)

/-- Maps under the actual CE boundary are exactly interval-cylinder maps
with the prescribed ordered endpoint condition. -/
def ceSpanEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    ((Under.lift CE CE_boundary).obj k ⟶
      Under.mk (ordinaryBoundary X x y)) ≃
        ordinaryOrderedSpan X x y k where
  toFun f := ⟨CE_interval.app k ≫ f.right, by
    have hw := (cePushout k).w
    change cylinderInclusion.app k ≫ CE_interval.app k =
      cylinderProjection.app k ≫ CE_boundary.app k at hw
    calc
      cylinderInclusion.app k ≫ (CE_interval.app k ≫ f.right) =
          (cylinderInclusion.app k ≫ CE_interval.app k) ≫ f.right := by
            rw [Category.assoc]
      _ = (cylinderProjection.app k ≫ CE_boundary.app k) ≫ f.right := by
            rw [hw]
      _ = cylinderProjection.app k ≫ ordinaryBoundary X x y := by
            rw [Category.assoc]
            have hf := Under.w f
            change CE_boundary.app k ≫ f.right = ordinaryBoundary X x y at hf
            exact congrArg (fun t ↦ cylinderProjection.app k ≫ t) hf⟩
  invFun g := Under.homMk
    ((cePushout k).desc g.val (ordinaryBoundary X x y) g.property)
    ((cePushout k).inr_desc g.val (ordinaryBoundary X x y) g.property)
  left_inv f := by
    apply Under.UnderMorphism.ext
    change (cePushout k).desc (CE_interval.app k ≫ f.right)
      (ordinaryBoundary X x y) _ = f.right
    apply (cePushout k).hom_ext
    · rw [(cePushout k).inl_desc]
    · rw [(cePushout k).inr_desc]
      have hf := Under.w f
      change CE_boundary.app k ≫ f.right = ordinaryBoundary X x y at hf
      exact hf.symm
  right_inv g := by
    apply Subtype.ext
    exact (cePushout k).inl_desc g.val (ordinaryBoundary X x y) g.property

/-- The evaluated pushout equivalences commute with every parameter
operator, so this is a simplicial-set isomorphism. -/
def ceSpanIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    plainCEHom (Under.mk (ordinaryBoundary X x y)) ≅
      ordinaryOrderedSpanSSet X x y :=
  NatIso.ofComponents (fun k ↦ (ceSpanEquiv X x y k.unop).toIso) (by
    intro k l θ
    funext f
    apply Subtype.ext
    change CE_interval.app l.unop ≫
        ((Under.lift CE CE_boundary).map θ.unop ≫ f).right =
      intervalCylinder.map θ.unop ≫
        (CE_interval.app k.unop ≫ f.right)
    change CE_interval.app l.unop ≫ (CE.map θ.unop ≫ f.right) = _
    have h := (CE_interval.naturality θ.unop).symm
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ f.right) h)

/-- The literal CE Hom is the categorical ordered endpoint fiber of the
**original** ordinary right adjoint, with no fibrancy hypothesis. -/
def originalFiberCEIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedFiber X x y ≅
      plainCEHom (Under.mk (ordinaryBoundary X x y)) :=
  ordinaryOrderedFiberIso X x y ≪≫ (ceSpanIso X x y).symm

/-- The CE presentation reads each simplex by restricting its actual
under-boundary morphism along `CE_interval`; this is not an abstract
representability choice. -/
theorem ceSpanIso_hom_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (f : (Under.lift CE CE_boundary).obj k ⟶
      Under.mk (ordinaryBoundary X x y)) :
    ((ceSpanIso X x y).hom.app (op k) f).val =
      CE_interval.app k ≫ f.right := rfl

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

private abbrev chosenTarget (W : Source) : DaggerSSet.{0} :=
  daggerCoherentNerve.obj (rigidCoefficient (chosenT W))

/-- Literal postcomposition on a row of the **original** ordinary nerve. -/
def originalRowMap {S T : SSet.{0}} (f : S ⟶ T)
    (m : SimplexCategory) : ordinaryRow S m ⟶ ordinaryRow T m where
  app k := (OrdinaryJTRealization.nerve.map f).app (op (m, k.unop))
  naturality {k l} θ := by
    exact (OrdinaryJTRealization.nerve.map f).naturality
      (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))

/-- The two original endpoint operators commute with target
postcomposition in their specified order. -/
private theorem originalRowMap_endpoint_i {S T : SSet.{0}} (f : S ⟶ T)
    (i : Fin 2) :
    ordinaryRowEndpoint S i ≫ originalRowMap f ⦋0⦌ =
      originalRowMap f ⦋1⦌ ≫ ordinaryRowEndpoint T i := by
  apply NatTrans.ext
  funext k z
  exact congrFun ((OrdinaryJTRealization.nerve.map f).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (JTXiEndpointCollapseBoundary.ordinaryEndpoint i, 𝟙 k.unop)))) z

private theorem originalRowMap_endpoint {S T : SSet.{0}} (f : S ⟶ T) :
    ordinaryEndpointArrow S ≫
      prod.map (originalRowMap f ⦋0⦌) (originalRowMap f ⦋0⦌) =
      originalRowMap f ⦋1⦌ ≫ ordinaryEndpointArrow T := by
  apply prod.hom_ext
  · simpa only [ordinaryEndpointArrow, prod.lift_fst,
      prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        originalRowMap_endpoint_i f 0
  · simpa only [ordinaryEndpointArrow, prod.lift_snd,
      prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        originalRowMap_endpoint_i f 1

/-- The actual chosen ordinary unit sends the original constant point at
each specified vertex to the constant point at its literal image. -/
private theorem chosenVertexPoint_naturality (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    ordinaryVertexPoint (chosenT W) x y i ≫
        originalRowMap (etaOrdinary W) ⦋0⦌ =
      ordinaryVertexPoint (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 i := by
  apply NatTrans.ext
  funext k z
  change ULift.up
      ((CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (GroupoidSimplex.parameter.obj k.unop) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ sourceBoundary W x y) ≫
          etaOrdinary W) =
      ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (GroupoidSimplex.parameter.obj k.unop) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ targetBoundary W x y)
  simp only [Category.assoc]
  rw [eta_boundary]

/-- The literal ordered source point maps to the literal ordered target
point. This uses the chosen unit's actual boundary equation. -/
private theorem chosenEndpointPoint_naturality (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint (chosenT W) x y ≫
        prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
          (originalRowMap (etaOrdinary W) ⦋0⦌) =
      ordinaryEndpointPoint (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_fst]
    exact (chosenVertexPoint_naturality W x y 0).trans
      (prod.lift_fst _ _).symm
  · rw [Category.assoc, prod.map_snd, ← Category.assoc]
    simp only [ordinaryEndpointPoint, prod.lift_snd]
    exact (chosenVertexPoint_naturality W x y 1).trans
      (prod.lift_snd _ _).symm

/-- The chosen unit on the **original ordinary right-adjoint categorical
fiber**. It is defined by the actual `pullback.map` of the original nerve
rows and original endpoint points. -/
def originalUnitFiberMap (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedFiber (chosenT W) x y ⟶
      ordinaryOrderedFiber (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 :=
  pullback.map
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (ordinaryEndpointPoint (chosenT W) x y)
    (ordinaryEndpointArrow (chosenTarget W).toSSet)
    (ordinaryEndpointPoint (chosenTarget W)
      (chosenVertices W x y).1 (chosenVertices W x y).2)
    (originalRowMap (etaOrdinary W) ⦋1⦌)
    (𝟙 (Δ[0] : SSet.{0}))
    (prod.map (originalRowMap (etaOrdinary W) ⦋0⦌)
      (originalRowMap (etaOrdinary W) ⦋0⦌))
    (originalRowMap_endpoint (etaOrdinary W))
    (by simpa only [Category.id_comp] using
      chosenEndpointPoint_naturality W x y)

/-- Its first projection is literal postcomposition in the original
outer-one ordinary right-adjoint row. -/
theorem originalUnitFiberMap_fst (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    originalUnitFiberMap W x y ≫
        pullback.fst (ordinaryEndpointArrow (chosenTarget W).toSSet)
          (ordinaryEndpointPoint (chosenTarget W)
            (chosenVertices W x y).1 (chosenVertices W x y).2) =
      pullback.fst (ordinaryEndpointArrow (chosenT W).toSSet)
          (ordinaryEndpointPoint (chosenT W) x y) ≫
        originalRowMap (etaOrdinary W) ⦋1⦌ := by
  simp only [originalUnitFiberMap, pullback.map, pullback.lift_fst]

/-- Literal postcomposition on ordered cylinder maps, retaining the
chosen boundary equation rather than replacing the endpoint point. -/
private def chosenSpanMap (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedSpanSSet (chosenT W) x y ⟶
      ordinaryOrderedSpanSSet (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2 where
  app k g := ⟨g.val ≫ etaOrdinary W, by
    calc
      cylinderInclusion.app k.unop ≫ (g.val ≫ etaOrdinary W) =
          (cylinderInclusion.app k.unop ≫ g.val) ≫ etaOrdinary W := by
            rw [Category.assoc]
      _ = (cylinderProjection.app k.unop ≫ sourceBoundary W x y) ≫
          etaOrdinary W := by rw [g.property]; rfl
      _ = cylinderProjection.app k.unop ≫ targetBoundary W x y := by
            rw [Category.assoc, eta_boundary]⟩
  naturality {_ _} _ := by
    funext g
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The literal CE pushout equivalence is natural under the chosen target
unit, and its map is the checked `plainCEHomMap`. -/
private theorem ceSpanIso_chosen_naturality (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    plainCEHomMap (etaUnder W x y) ≫
        (ceSpanIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom =
      (ceSpanIso (chosenT W) x y).hom ≫ chosenSpanMap W x y := by
  apply NatTrans.ext
  funext k g
  apply Subtype.ext
  change CE_interval.app k.unop ≫ (g.right ≫ (etaUnder W x y).right) =
    (CE_interval.app k.unop ≫ g.right) ≫ etaOrdinary W
  rw [etaUnder_right]
  exact (Category.assoc _ _ _).symm

/-- The first-leg formula for the original ordinary fiber iso, using its
public projection calibration from the accepted construction. -/
private theorem originalFiberIso_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (z : (ordinaryOrderedFiber X x y).obj (op k)) :
    ((ordinaryOrderedFiberIso X x y).hom.app (op k) z).val =
      ((pullback.fst (ordinaryEndpointArrow X.toSSet)
        (ordinaryEndpointPoint X x y)).app (op k) z).down := by
  exact JTRightAdjointOrderedFiber.ordinaryOrderedFiberIso_hom_val X x y k z

/-- The accepted original fiber iso is natural for the actual chosen
ordinary unit. This verifies the value of the literal `pullback.map`, not
an alternative map defined by conjugation. -/
private theorem originalFiberIso_chosen_naturality (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    originalUnitFiberMap W x y ≫
        (ordinaryOrderedFiberIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom =
      (ordinaryOrderedFiberIso (chosenT W) x y).hom ≫
        chosenSpanMap W x y := by
  apply NatTrans.ext
  funext k z
  apply Subtype.ext
  change ((ordinaryOrderedFiberIso (chosenTarget W)
    (chosenVertices W x y).1 (chosenVertices W x y).2).hom.app k
      ((originalUnitFiberMap W x y).app k z)).val =
    ((ordinaryOrderedFiberIso (chosenT W) x y).hom.app k z).val ≫
      etaOrdinary W
  rw [originalFiberIso_val, originalFiberIso_val]
  have h := congrFun (NatTrans.congr_app
    (originalUnitFiberMap_fst W x y) k) z
  change
    ((pullback.fst (ordinaryEndpointArrow (chosenTarget W).toSSet)
      (ordinaryEndpointPoint (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2)).app k
      ((originalUnitFiberMap W x y).app k z)) =
    ((originalRowMap (etaOrdinary W) ⦋1⦌).app k)
      ((pullback.fst (ordinaryEndpointArrow (chosenT W).toSSet)
        (ordinaryEndpointPoint (chosenT W) x y)).app k z) at h
  rw [h]
  rfl

/-- Exact naturality square between the chosen original ordinary fiber
map and literal CE target postcomposition. -/
theorem originalUnitFiberMap_ce (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    originalUnitFiberMap W x y ≫
        (originalFiberCEIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom =
      (originalFiberCEIso (chosenT W) x y).hom ≫
        plainCEHomMap (etaUnder W x y) := by
  apply (cancel_mono (ceSpanIso (chosenTarget W)
    (chosenVertices W x y).1 (chosenVertices W x y).2).hom).1
  calc
    (originalUnitFiberMap W x y ≫
        (originalFiberCEIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom) ≫
        (ceSpanIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom =
      originalUnitFiberMap W x y ≫
        (ordinaryOrderedFiberIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom := by
            simp only [originalFiberCEIso, Iso.trans_hom,
              Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
              Category.comp_id]
    _ = (ordinaryOrderedFiberIso (chosenT W) x y).hom ≫
          chosenSpanMap W x y :=
            originalFiberIso_chosen_naturality W x y
    _ = ((originalFiberCEIso (chosenT W) x y).hom ≫
          plainCEHomMap (etaUnder W x y)) ≫
        (ceSpanIso (chosenTarget W)
          (chosenVertices W x y).1 (chosenVertices W x y).2).hom := by
            simp only [originalFiberCEIso, Iso.trans_hom, Iso.symm_hom,
              Category.assoc]
            rw [ceSpanIso_chosen_naturality]
            simp only [Iso.inv_hom_id_assoc]

open scoped SSet.modelCategoryQuillen in
/-- The original chosen unit induces a Kan weak equivalence on its
**strict original ordinary ordered fiber**. The proof uses the verified
CE augmentation weakness and the exact naturality square above. -/
theorem originalUnitFiberMap_GW (W : Source)
    (x y : (chosenT W).toSSet.obj (op ⦋0⦌)) :
    DaggerSSetGluing.GW (originalUnitFiberMap W x y) := by
  let e : Arrow.mk (originalUnitFiberMap W x y) ≅
      Arrow.mk (plainCEHomMap (etaUnder W x y)) :=
    Arrow.isoMk (originalFiberCEIso (chosenT W) x y)
      (originalFiberCEIso (chosenTarget W)
        (chosenVertices W x y).1 (chosenVertices W x y).2)
      (originalUnitFiberMap_ce W x y).symm
  letI : ModelCategory SSet.{0} := SSet.modelCategoryQuillen.inst
  have hCE : weakEquivalences SSet.{0}
      (plainCEHomMap (etaUnder W x y)) := by
    rw [← weakEquivalence_iff]
    exact (DaggerSSetGluing.weakEquivalence_iff_GW _).2
      (JTCylinderAugmentationWeak.etaCE_GW W x y)
  have hFiber : weakEquivalences SSet.{0}
      (originalUnitFiberMap W x y) :=
    ((weakEquivalences SSet.{0}).arrow_mk_iso_iff e).2 hCE
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).1
    ((weakEquivalence_iff _).2 hFiber)

end

end DaggerModels.PartII.JTCEOrdinaryFiber
