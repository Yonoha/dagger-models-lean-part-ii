import DaggerModelsPartII.JTUnderlyingRightComparison
import DaggerModelsPartII.JTXiStrictEndpointIso
import DaggerModelsPartII.JTEndpointObjects

/-!
# Literal ordered boundary data for the underlying JT comparison

This first leaf fixes the two actual ordered endpoint fibers and the forward
restriction map in the represented degree-one frame. The eventual fiber
isomorphism will use the already checked boundary-calibrated isomorphism
`rawXiCollapseIso` and the two original realization adjunctions. No global
isomorphism of the two right adjoints is asserted here.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTUnderlyingOrderedFibers

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
open GroupoidSimplex

universe v u

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

/-- Maps from a pushout under its boundary are exactly maps from the other
leg satisfying the given boundary equation. -/
private def pushoutFiberEquiv {C : Type u} [Category.{v} C]
    {S T B P X : C} {u : S ⟶ T} {a : S ⟶ B}
    {i : T ⟶ P} {j : B ⟶ P} (h : IsPushout u a i j) (b : B ⟶ X) :
    {d : P ⟶ X // j ≫ d = b} ≃
      {f : T ⟶ X // u ≫ f = a ≫ b} where
  toFun d := ⟨i ≫ d.val, by
    rw [← Category.assoc, h.w, Category.assoc, d.property]⟩
  invFun f := ⟨h.desc f.val b f.property, h.inr_desc f.val b f.property⟩
  left_inv d := by
    apply Subtype.ext
    apply h.hom_ext
    · simp only [h.inl_desc]
    · simp only [h.inr_desc, d.property]
  right_inv f := by
    apply Subtype.ext
    exact h.inl_desc f.val b f.property

/-- The ordered pair of actual vertices as a map from the manuscript's
literal boundary `∂Δ¹` into the forgotten dagger simplicial set. -/
def ordinaryBoundary (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : boundary ⟶ X.toSSet :=
  (JTEndpointObjects.boundaryHomEquiv X.toSSet).symm (x, y)

/-- The same ordered boundary, transported through the original free-dagger
adjunction. -/
def daggerBoundary (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : B ⟶ X :=
  (freeDaggerAdjunction.homEquiv boundary X).symm (ordinaryBoundary X x y)

/-- The dagger boundary has exactly the prescribed ordinary transpose. -/
theorem daggerBoundary_transpose (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    freeDaggerAdjunction.homEquiv boundary X (daggerBoundary X x y) =
      ordinaryBoundary X x y :=
  (freeDaggerAdjunction.homEquiv boundary X).apply_symm_apply _

/-- The degree-one dagger Hom maps satisfying the two ordered endpoint
equations before quotienting by the endpoint span. -/
def daggerOrderedSpan (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :=
  {f : frame1.obj k ⟶ X //
    rawFaces.app k ≫ f = rawEndpoints.app k ≫ daggerBoundary X x y}

/-- The corresponding ordinary maps satisfying the constant endpoint
equations in the actual `Δ¹ × Jᵏ` cylinder. -/
def ordinaryOrderedSpan (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :=
  {f : intervalCylinder.obj k ⟶ X.toSSet //
    cylinderInclusion.app k ≫ f =
      cylinderProjection.app k ≫ ordinaryBoundary X x y}

private def rawIsPushout (k : SimplexCategory) :
    IsPushout (rawFaces.app k) (rawEndpoints.app k)
      ((pushout.inl rawFaces rawEndpoints).app k)
      ((pushout.inr rawFaces rawEndpoints).app k) :=
  (IsPushout.of_hasPushout rawFaces rawEndpoints).map
    ((evaluation SimplexCategory DaggerSSet.{0}).obj k)

private def ordinaryIsPushout (k : SimplexCategory) :
    IsPushout (cylinderInclusion.app k) (cylinderProjection.app k)
      (CE_interval.app k) (CE_boundary.app k) :=
  (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)

private def rawUnderFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :=
  {d : rawCollapse.obj k ⟶ X //
    rawBoundary.app k ≫ d = daggerBoundary X x y}

private def freeUnderFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :=
  {d : CEFree.obj k ⟶ X //
    CEFreeBoundary.app k ≫ d = daggerBoundary X x y}

private def ordinaryUnderFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :=
  {d : CE.obj k ⟶ X.toSSet //
    CE_boundary.app k ≫ d = ordinaryBoundary X x y}

/-- The literal raw dagger pushout identifies its boundary-under maps with
the two specified endpoint equations. -/
private def rawFiberEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    rawUnderFiber X x y k ≃ daggerOrderedSpan X x y k :=
  pushoutFiberEquiv (rawIsPushout k) (daggerBoundary X x y)

/-- The ordinary endpoint quotient identifies boundary-under maps with
the corresponding two constant endpoint equations. -/
private def ordinaryFiberEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    ordinaryUnderFiber X x y k ≃ ordinaryOrderedSpan X x y k :=
  pushoutFiberEquiv (ordinaryIsPushout k) (ordinaryBoundary X x y)

/-- Transport boundary-under dagger maps through the checked strict
endpoint-collapse isomorphism, retaining its literal boundary calibration. -/
private def rawFreeFiberEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    rawUnderFiber X x y k ≃ freeUnderFiber X x y k where
  toFun d := ⟨(JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv ≫ d.val, by
    have hb := NatTrans.congr_app
      JTXiStrictEndpointIso.rawBoundary_rawXiCollapseIso k
    change rawBoundary.app k ≫
      (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom =
        CEFreeBoundary.app k at hb
    calc
      CEFreeBoundary.app k ≫
          ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv ≫ d.val) =
        rawBoundary.app k ≫
          ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫
            ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv ≫ d.val)) := by
              rw [← hb, Category.assoc]
      _ = rawBoundary.app k ≫
          (((JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫
            (JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv) ≫ d.val) := by
              rw [Category.assoc]
      _ = daggerBoundary X x y := by
            rw [Iso.hom_inv_id, Category.id_comp, d.property]⟩
  invFun d := ⟨(JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫ d.val, by
    have hb := NatTrans.congr_app
      JTXiStrictEndpointIso.rawBoundary_rawXiCollapseIso k
    change rawBoundary.app k ≫
      (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom =
        CEFreeBoundary.app k at hb
    calc
      rawBoundary.app k ≫
          ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫ d.val) =
        (rawBoundary.app k ≫
          (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom) ≫ d.val := by
            rw [Category.assoc]
      _ = daggerBoundary X x y := by rw [hb, d.property]⟩
  left_inv d := by
    apply Subtype.ext
    change (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫
      ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv ≫ d.val) = d.val
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  right_inv d := by
    apply Subtype.ext
    change (JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv ≫
      ((JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom ≫ d.val) = d.val
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Under the original free-dagger adjunction, the ordered boundary
condition becomes the literal ordinary boundary condition. -/
private def freeOrdinaryFiberEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    freeUnderFiber X x y k ≃ ordinaryUnderFiber X x y k where
  toFun d := ⟨freeDaggerAdjunction.homEquiv (CE.obj k) X d.val, by
    have h := congrArg (freeDaggerAdjunction.homEquiv boundary X) d.property
    change freeDaggerAdjunction.homEquiv boundary X
      (freeDagger.map (CE_boundary.app k) ≫ d.val) = _ at h
    rw [freeDaggerAdjunction.homEquiv_naturality_left,
      daggerBoundary_transpose] at h
    exact h⟩
  invFun d := ⟨(freeDaggerAdjunction.homEquiv (CE.obj k) X).symm d.val, by
    apply (freeDaggerAdjunction.homEquiv boundary X).injective
    change freeDaggerAdjunction.homEquiv boundary X
      (freeDagger.map (CE_boundary.app k) ≫
        (freeDaggerAdjunction.homEquiv (CE.obj k) X).symm d.val) = _
    rw [freeDaggerAdjunction.homEquiv_naturality_left,
      Equiv.apply_symm_apply, daggerBoundary_transpose]
    exact d.property⟩
  left_inv d := by
    apply Subtype.ext
    exact (freeDaggerAdjunction.homEquiv (CE.obj k) X).symm_apply_apply d.val
  right_inv d := by
    apply Subtype.ext
    exact (freeDaggerAdjunction.homEquiv (CE.obj k) X).apply_symm_apply d.val

/-- The endpoint-span equivalence obtained by the two actual pushouts, the
strict raw-to-free collapse isomorphism, and the original free-dagger
adjunction. -/
def orderedSpanEquiv (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    daggerOrderedSpan X x y k ≃ ordinaryOrderedSpan X x y k :=
  (((rawFiberEquiv X x y k).symm.trans
    (rawFreeFiberEquiv X x y k)).trans
      (freeOrdinaryFiberEquiv X x y k)).trans
        (ordinaryFiberEquiv X x y k)

/-- The canonical strict collapse isomorphism sends the actual first copy
to the free-adjunction unit of the ordinary endpoint quotient. -/
private theorem forwardRaw_rawIso (k : SimplexCategory) :
    forwardRaw.app k ≫
      (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom.hom =
        CE_interval.app k ≫ freeDaggerAdjunction.unit.app (CE.obj k) := by
  letI : IsIso (actualFreeCEToRaw.app k) :=
    JTXiStrictEndpointIso.actualFreeCEToRaw_app_isIso k
  let c := CEToRaw boundaryCompatibility
  have hu : freeDaggerAdjunction.unit.app (CE.obj k) ≫
      (actualFreeCEToRaw.app k).hom = c.app k := by
    have h := (freeDaggerAdjunction.homEquiv (CE.obj k)
      (rawCollapse.obj k)).apply_symm_apply (c.app k)
    rw [Adjunction.homEquiv_unit] at h
    exact h
  have hl : CE_interval.app k ≫ c.app k = forwardRaw.app k :=
    NatTrans.congr_app
      (pushout.inl_desc forwardRaw boundaryToRaw boundaryCompatibility) k
  have hcomp : (actualFreeCEToRaw.app k).hom ≫
      (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom.hom = 𝟙 _ := by
    have heq : (JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv =
        actualFreeCEToRaw.app k := rfl
    rw [← heq]
    exact congrArg DaggerSSet.Hom.hom
      (JTXiStrictEndpointIso.rawXiCollapseIso.app k).inv_hom_id
  calc
    forwardRaw.app k ≫
        (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom.hom =
      (CE_interval.app k ≫ c.app k) ≫
        (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom.hom := by rw [hl]
    _ = (CE_interval.app k ≫ freeDaggerAdjunction.unit.app (CE.obj k)) ≫
          ((actualFreeCEToRaw.app k).hom ≫
            (JTXiStrictEndpointIso.rawXiCollapseIso.app k).hom.hom) := by
          rw [← hu]
          simp only [Category.assoc]
    _ = _ := by
          rw [hcomp]
          cat_disch

/-- Restriction along the verified first-copy map of the represented
degree-one dagger JT frame. This is the forward formula in the manuscript
before imposing the constant endpoint equations. -/
def forwardRestriction (X : DaggerSSet.{0}) (k : SimplexCategory)
    (f : frame1.obj k ⟶ X) : intervalCylinder.obj k ⟶ X.toSSet :=
  forwardFrame.app k ≫ f.hom

/-- Postcomposition commutes strictly with the forward-copy restriction. -/
theorem forwardRestriction_postcompose {X Y : DaggerSSet.{0}}
    (k : SimplexCategory) (f : frame1.obj k ⟶ X) (g : X ⟶ Y) :
    forwardRestriction Y k (f ≫ g) =
      forwardRestriction X k f ≫ g.hom := by
  rfl

/-- The actual forward copy carries a dagger map with the specified ordered
raw endpoint equations to an ordinary map with the corresponding constant
boundary equations. -/
def forwardOrderedSpan (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    daggerOrderedSpan X x y k → ordinaryOrderedSpan X x y k := by
  intro f
  let hraw : IsPushout (rawFaces.app k) (rawEndpoints.app k)
      ((pushout.inl rawFaces rawEndpoints).app k)
      ((pushout.inr rawFaces rawEndpoints).app k) :=
    (IsPushout.of_hasPushout rawFaces rawEndpoints).map
      ((evaluation SimplexCategory DaggerSSet.{0}).obj k)
  let d : rawCollapse.obj k ⟶ X :=
    hraw.desc f.val (daggerBoundary X x y) f.property
  have hleft : (pushout.inl rawFaces rawEndpoints).app k ≫ d = f.val :=
    hraw.inl_desc f.val (daggerBoundary X x y) f.property
  have hright : (pushout.inr rawFaces rawEndpoints).app k ≫ d =
      daggerBoundary X x y :=
    hraw.inr_desc f.val (daggerBoundary X x y) f.property
  have hleft' : ((pushout.inl rawFaces rawEndpoints).app k).hom ≫ d.hom =
      f.val.hom := congrArg DaggerSSet.Hom.hom hleft
  have hright' : ((pushout.inr rawFaces rawEndpoints).app k).hom ≫ d.hom =
      (daggerBoundary X x y).hom := congrArg DaggerSSet.Hom.hom hright
  have hforward : forwardRaw.app k ≫ d.hom =
      forwardRestriction X k f.val := by
    change (forwardFrame.app k ≫
      ((pushout.inl rawFaces rawEndpoints).app k).hom) ≫ d.hom = _
    rw [Category.assoc]
    rw [hleft']
    rfl
  have hboundary : boundaryToRaw.app k ≫ d.hom = ordinaryBoundary X x y := by
    have ht := daggerBoundary_transpose X x y
    rw [Adjunction.homEquiv_unit] at ht
    change freeDaggerAdjunction.unit.app boundary ≫
        ((pushout.inr rawFaces rawEndpoints).app k).hom ≫ d.hom = _
    calc
      freeDaggerAdjunction.unit.app boundary ≫
          (((pushout.inr rawFaces rawEndpoints).app k).hom ≫ d.hom) =
        freeDaggerAdjunction.unit.app boundary ≫
          (daggerBoundary X x y).hom := by rw [hright']
      _ = ordinaryBoundary X x y := ht
  refine ⟨forwardRestriction X k f.val, ?_⟩
  have hc : cylinderInclusion.app k ≫ forwardRaw.app k = boundaryRaw.app k :=
    NatTrans.congr_app boundaryCompatibility k
  calc
    cylinderInclusion.app k ≫ forwardRestriction X k f.val =
        cylinderInclusion.app k ≫ (forwardRaw.app k ≫ d.hom) := by rw [hforward]
    _ = boundaryRaw.app k ≫ d.hom := by rw [← Category.assoc, hc]
    _ = cylinderProjection.app k ≫ ordinaryBoundary X x y := by
      change (cylinderProjection.app k ≫ boundaryToRaw.app k) ≫ d.hom = _
      rw [Category.assoc, hboundary]

/-- The transported equivalence is the manuscript's literal restriction to
the forward copy, not merely an abstract bijection of the two fibers. -/
theorem orderedSpanEquiv_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (f : daggerOrderedSpan X x y k) :
    (orderedSpanEquiv X x y k f).val = forwardRestriction X k f.val := by
  let d : rawCollapse.obj k ⟶ X :=
    (rawIsPushout k).desc f.val (daggerBoundary X x y) f.property
  let e := JTXiStrictEndpointIso.rawXiCollapseIso.app k
  have hleft : ((pushout.inl rawFaces rawEndpoints).app k).hom ≫ d.hom =
      f.val.hom :=
    congrArg DaggerSSet.Hom.hom
      ((rawIsPushout k).inl_desc f.val (daggerBoundary X x y) f.property)
  have hcancel : e.hom.hom ≫ e.inv.hom = 𝟙 _ :=
    congrArg DaggerSSet.Hom.hom e.hom_inv_id
  change CE_interval.app k ≫
      freeDaggerAdjunction.homEquiv (CE.obj k) X (e.inv ≫ d) =
        forwardRestriction X k f.val
  rw [Adjunction.homEquiv_unit]
  change CE_interval.app k ≫
      (freeDaggerAdjunction.unit.app (CE.obj k) ≫
        (e.inv.hom ≫ d.hom)) = _
  calc
    _ = (CE_interval.app k ≫ freeDaggerAdjunction.unit.app (CE.obj k)) ≫
          (e.inv.hom ≫ d.hom) := by rw [Category.assoc]
    _ = (forwardRaw.app k ≫ e.hom.hom) ≫
          (e.inv.hom ≫ d.hom) := by rw [forwardRaw_rawIso k]
    _ = (forwardRaw.app k ≫ (e.hom.hom ≫ e.inv.hom)) ≫ d.hom := by
          simp only [Category.assoc]
    _ = forwardRaw.app k ≫ d.hom := by
          rw [hcancel]
          cat_disch
    _ = forwardRestriction X k f.val := by
          change (forwardFrame.app k ≫
            ((pushout.inl rawFaces rawEndpoints).app k).hom) ≫ d.hom = _
          rw [Category.assoc, hleft]
          rfl

/-- The actual forward restriction is bijective on the ordered endpoint
span, with inverse supplied by the calibrated raw-to-free endpoint collapse. -/
theorem forwardOrderedSpan_bijective (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory) :
    Function.Bijective (forwardOrderedSpan X x y k) := by
  have hfun : forwardOrderedSpan X x y k = orderedSpanEquiv X x y k := by
    funext f
    apply Subtype.ext
    exact (orderedSpanEquiv_val X x y k f).symm
  rw [hfun]
  exact (orderedSpanEquiv X x y k).bijective

/-- The ordered dagger endpoint equations form an actual simplicial set,
with operators induced by the original represented dagger frame. -/
def daggerOrderedSpanSSet (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} where
  obj k := daggerOrderedSpan X x y k.unop
  map {k l} θ f := ⟨frame1.map θ.unop ≫ f.val, by
    have hf := rawFaces.naturality θ.unop
    have hb := rawEndpoints.naturality θ.unop
    calc
      rawFaces.app l.unop ≫ (frame1.map θ.unop ≫ f.val) =
        ((frame0 ⨿ frame0).map θ.unop ≫ rawFaces.app k.unop) ≫ f.val := by
          simpa only [Category.assoc] using
            congrArg (fun q ↦ q ≫ f.val) hf.symm
      _ = ((frame0 ⨿ frame0).map θ.unop ≫ rawEndpoints.app k.unop) ≫
            daggerBoundary X x y := by
          simpa only [Category.assoc] using
            congrArg (fun q ↦ (frame0 ⨿ frame0).map θ.unop ≫ q) f.property
      _ = rawEndpoints.app l.unop ≫ daggerBoundary X x y := by
          simpa only [Functor.const_obj_map, Category.comp_id] using
            congrArg (fun q ↦ q ≫ daggerBoundary X x y) hb⟩
  map_id k := by
    funext f
    apply Subtype.ext
    simp
  map_comp θ ψ := by
    funext f
    apply Subtype.ext
    simp [Functor.map_comp, Category.assoc]

/-- The ordinary constant-endpoint equations form the corresponding actual
simplicial set on the original `Δ¹ × Jᵏ` cylinder. -/
def ordinaryOrderedSpanSSet (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} where
  obj k := ordinaryOrderedSpan X x y k.unop
  map {k l} θ f := ⟨intervalCylinder.map θ.unop ≫ f.val, by
    have hf := cylinderInclusion.naturality θ.unop
    have hb := cylinderProjection.naturality θ.unop
    calc
      cylinderInclusion.app l.unop ≫ (intervalCylinder.map θ.unop ≫ f.val) =
        (boundaryCylinder.map θ.unop ≫ cylinderInclusion.app k.unop) ≫
          f.val := by
            simpa only [Category.assoc] using
              congrArg (fun q ↦ q ≫ f.val) hf.symm
      _ = (boundaryCylinder.map θ.unop ≫ cylinderProjection.app k.unop) ≫
            ordinaryBoundary X x y := by
          simpa only [Category.assoc] using
            congrArg (fun q ↦ boundaryCylinder.map θ.unop ≫ q) f.property
      _ = cylinderProjection.app l.unop ≫ ordinaryBoundary X x y := by
          simpa only [Functor.const_obj_map, Category.comp_id] using
            congrArg (fun q ↦ q ≫ ordinaryBoundary X x y) hb⟩
  map_id k := by
    funext f
    apply Subtype.ext
    simp
  map_comp θ ψ := by
    funext f
    apply Subtype.ext
    simp [Functor.map_comp, Category.assoc]

/-- The strict ordered-fiber comparison represented by first-copy
restriction is a simplicial-set isomorphism in every parameter degree. -/
def orderedSpanSSetIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerOrderedSpanSSet X x y ≅ ordinaryOrderedSpanSSet X x y :=
  NatIso.ofComponents
    (fun k ↦ (orderedSpanEquiv X x y k.unop).toIso) (by
      intro k l θ
      funext f
      apply Subtype.ext
      change (orderedSpanEquiv X x y l.unop
          ((daggerOrderedSpanSSet X x y).map θ f)).val =
        ((ordinaryOrderedSpanSSet X x y).map θ
          (orderedSpanEquiv X x y k.unop f)).val
      rw [orderedSpanEquiv_val]
      change forwardRestriction X l.unop
          ((daggerOrderedSpanSSet X x y).map θ f).val =
        intervalCylinder.map θ.unop ≫
          (orderedSpanEquiv X x y k.unop f).val
      rw [orderedSpanEquiv_val]
      change forwardFrame.app l.unop ≫
          (DaggerSSet.forget.map (frame1.map θ.unop) ≫ f.val.hom) =
        intervalCylinder.map θ.unop ≫
          (forwardFrame.app k.unop ≫ f.val.hom)
      have hn := (forwardFrame.naturality θ.unop).symm
      change forwardFrame.app l.unop ≫
          DaggerSSet.forget.map (frame1.map θ.unop) =
        intervalCylinder.map θ.unop ≫ forwardFrame.app k.unop at hn
      simpa only [Category.assoc] using
        congrArg (fun q ↦ q ≫ f.val.hom) hn)


end

end DaggerModels.PartII.JTUnderlyingOrderedFibers
