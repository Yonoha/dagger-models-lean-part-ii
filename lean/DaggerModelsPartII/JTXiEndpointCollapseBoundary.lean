import DaggerModelsPartII.JTXiEndpointCollapse
import DaggerModelsPartII.JTWalkingUnitaryWeak
import TopCatModelCategory.SSet.FundamentalGroupoid

/-!
# The boundary-compatible quotient map for the endpoint-collapsed JT frame

The first-copy map from the interval cylinder to the actual represented
frame is built from the free-dagger pushout inclusion and the retained
underlying-frame comparison. The outstanding proof identifies its boundary
restriction with the two ordered raw collapses, then proves that its free
dagger extension is an isomorphism by pushout pasting.

The map and its ordered boundary calibration are proved here. Its
invertibility is a separate pointwise pushout-pasting problem; this module
does not assert the manuscript's final strict isomorphism.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial DaggerModels

namespace DaggerModels.PartII.JTXiEndpointCollapseBoundary

open JTXiEndpointCollapse DaggerJTFrameUnderlying DaggerJTAdjunction
open GroupoidSimplex

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

/-- The ordinary coface selecting the `i`-th endpoint. -/
def ordinaryEndpoint (i : Fin 2) : (⦋0⦌ : SimplexCategory) ⟶ ⦋1⦌ :=
  SimplexCategory.const ⦋0⦌ ⦋1⦌ i

/-- The two raw reversal endpoints are precisely the images of these
ordinary cofaces; no separate orientation tag is involved. -/
theorem includedEndpoint (i : Fin 2) :
    ReverseSimplex.inclusion.map (ordinaryEndpoint i) = reversalEndpoint i := by
  apply ReverseSimplex.Hom.ext
  intro x
  rfl

/-- The canonical forward copy of every standard simplex in the native
represented reversal simplex. Naturality in the simplex operator is built
from the free adjunction's unit and the two chosen natural isomorphisms. -/
def forwardSimplexNat : SSet.stdSimplex.{0} ⟶
    ReverseSimplex.inclusion ⋙ (reversalSimplex ⋙ DaggerSSet.forget) :=
  (Functor.rightUnitor SSet.stdSimplex).inv ≫
    Functor.whiskerLeft SSet.stdSimplex FreeDaggerPushout.adjunction.unit ≫
    (Functor.associator SSet.stdSimplex FreeDaggerPushout.functor
      DaggerSSet.forget).inv ≫
    Functor.whiskerRight
      (Functor.whiskerLeft SSet.stdSimplex FreeDaggerPushout.isoFreeDagger.hom)
      DaggerSSet.forget ≫
    Functor.whiskerRight reversalSimplexFreeIso.inv DaggerSSet.forget ≫
    (Functor.associator ReverseSimplex.inclusion reversalSimplex
      DaggerSSet.forget).hom

/-- The degree-one component used in the strict endpoint quotient. -/
def forwardSimplex : interval ⟶ underlyingSimplex.obj m1 :=
  forwardSimplexNat.app ⦋1⦌

/-- The forward interval cylinder, mapped into the naturally varying
ordinary product parameter of the horizontal degree-one frame. -/
def forwardParameter : intervalCylinder ⟶
    parameterProduct (underlyingSimplex.obj m1) :=
  Functor.whiskerRight
    (NatTrans.prod'
      ((Functor.const SimplexCategory).map forwardSimplex)
      (𝟙 parameter))
    (MonoidalCategory.tensor SSet.{0})

/-- Restriction of the actual two-variable underlying-frame parameter. -/
def frameParameter1 : SimplexCategory ⥤ SSet.{0} :=
  CategoryTheory.Prod.sectR m1 SimplexCategory ⋙ frameParameter

/-- The constant-first-factor product and the restricted two-variable product
have the same values and simplex operators. -/
def parameterSliceIso :
    parameterProduct (underlyingSimplex.obj m1) ≅ frameParameter1 :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro k l f
    simp [parameterProduct, frameParameter1, frameParameter])

/-- The actual forward copy in the literal represented dagger JT frame,
after forgetting dagger. -/
def forwardFrame : intervalCylinder ⟶ frame1 ⋙ DaggerSSet.forget :=
  forwardParameter ≫ parameterSliceIso.hom ≫
    (Functor.isoWhiskerLeft
      (CategoryTheory.Prod.sectR m1 SimplexCategory)
      frameUnderlyingIso).inv ≫
    (Functor.associator (CategoryTheory.Prod.sectR m1 SimplexCategory)
      frame DaggerSSet.forget).inv

/-- The corresponding forward point cylinder at the zero horizontal frame. -/
def zeroCylinder : SimplexCategory ⥤ SSet.{0} :=
  parameterProduct (Δ[0] : SSet.{0})

def forwardParameter0 : zeroCylinder ⟶
    parameterProduct (underlyingSimplex.obj m0) :=
  Functor.whiskerRight
    (NatTrans.prod'
      ((Functor.const SimplexCategory).map (forwardSimplexNat.app ⦋0⦌))
      (𝟙 parameter))
    (MonoidalCategory.tensor SSet.{0})

def frameParameter0 : SimplexCategory ⥤ SSet.{0} :=
  CategoryTheory.Prod.sectR m0 SimplexCategory ⋙ frameParameter

def parameterSliceIso0 :
    parameterProduct (underlyingSimplex.obj m0) ≅ frameParameter0 :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro k l f
    simp [parameterProduct, frameParameter0, frameParameter])

def forwardFrame0 : zeroCylinder ⟶ frame0 ⋙ DaggerSSet.forget :=
  forwardParameter0 ≫ parameterSliceIso0.hom ≫
    (Functor.isoWhiskerLeft
      (CategoryTheory.Prod.sectR m0 SimplexCategory)
      frameUnderlyingIso).inv ≫
    (Functor.associator (CategoryTheory.Prod.sectR m0 SimplexCategory)
      frame DaggerSSet.forget).inv

/-- Restrict the full reversal-JT index to ordinary simplex maps in its
first coordinate, retaining every ordinary parameter operator. -/
def ordinaryPair : SimplexCategory × SimplexCategory ⥤ DaggerIndex :=
  ReverseSimplex.inclusion.prod (𝟭 SimplexCategory)

def ordinaryPairParameter :
    SimplexCategory × SimplexCategory ⥤ SSet.{0} :=
  (SSet.stdSimplex.{0}.prod parameter) ⋙ MonoidalCategory.tensor SSet.{0}

def ordinaryPairUnderlying :
    SimplexCategory × SimplexCategory ⥤ SSet.{0} :=
  (ordinaryPair ⋙ frame) ⋙ DaggerSSet.forget

/-- The forward-copy map before transporting to the literal frame. -/
def forwardPairParameter : ordinaryPairParameter ⟶
    ((ReverseSimplex.inclusion ⋙ underlyingSimplex).prod parameter) ⋙
      MonoidalCategory.tensor SSet.{0} :=
  Functor.whiskerRight (NatTrans.prod forwardSimplexNat (𝟙 parameter))
    (MonoidalCategory.tensor SSet.{0})

def pairParameterIso :
    ((ReverseSimplex.inclusion ⋙ underlyingSimplex).prod parameter) ⋙
        MonoidalCategory.tensor SSet.{0} ≅ ordinaryPair ⋙ frameParameter :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro p q f
    simp [ordinaryPair, frameParameter])

/-- Full two-variable naturality of the forward copy. Its horizontal
components are the two endpoint naturality squares needed below. -/
def forwardPair : ordinaryPairParameter ⟶ ordinaryPairUnderlying :=
  forwardPairParameter ≫ pairParameterIso.hom ≫
    (Functor.isoWhiskerLeft ordinaryPair frameUnderlyingIso).inv ≫
    (Functor.associator ordinaryPair frame DaggerSSet.forget).inv

private theorem forwardPair_zero_app (k : SimplexCategory) :
    forwardPair.app (⦋0⦌, k) = forwardFrame0.app k := rfl

private theorem forwardPair_one_app (k : SimplexCategory) :
    forwardPair.app (⦋1⦌, k) = forwardFrame.app k := rfl

/-- The forward interval-cylinder copy inside the actual raw collapse. -/
def forwardRaw : intervalCylinder ⟶ rawCollapse ⋙ DaggerSSet.forget :=
  forwardFrame ≫
    Functor.whiskerRight (pushout.inl rawFaces rawEndpoints) DaggerSSet.forget

/-- The constant ordered boundary inside the raw dagger pushout. -/
def boundaryToRaw : (Functor.const SimplexCategory).obj boundary ⟶
    rawCollapse ⋙ DaggerSSet.forget :=
  (Functor.const SimplexCategory).map
      (freeDaggerAdjunction.unit.app boundary) ≫
    (Functor.constComp SimplexCategory B DaggerSSet.forget).inv ≫
    Functor.whiskerRight rawBoundary DaggerSSet.forget

/-- The collapsed boundary cylinder inside the raw dagger pushout. -/
def boundaryRaw : boundaryCylinder ⟶ rawCollapse ⋙ DaggerSSet.forget :=
  cylinderProjection ≫ boundaryToRaw

/-- Exact equality that the two ordered raw endpoint relations must prove.
The proof can be checked after precomposition with the two maps in
`SSet.boundary₁.isColimitRightTensor (parameter.obj k)`. -/
def BoundaryCompatibility : Prop :=
  cylinderInclusion ≫ forwardRaw = boundaryRaw

/-- The first concrete triangle needed at endpoint `i`: the forward-copy
map takes the ordinary coface to the actual raw frame coface. -/
def FrameEndpointSquare (i : Fin 2) : Prop :=
  ∀ k : SimplexCategory,
    ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫ cylinderInclusion.app k ≫ forwardFrame.app k =
      forwardFrame0.app k ≫
        DaggerSSet.forget.map ((frameEndpoint i).app k)

/-- The second concrete triangle needed at endpoint `i`: the projection
of the ordinary boundary cylinder is the literal dagger endpoint collapse. -/
def ProjectionEndpointSquare (i : Fin 2) : Prop :=
  ∀ k : SimplexCategory,
    ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫ cylinderProjection.app k ≫
        freeDaggerAdjunction.unit.app boundary =
      forwardFrame0.app k ≫
        DaggerSSet.forget.map ((endpointCollapse i).app k)

/-- The zero-frame normalization needed for both projection squares. It
compares the forward point cylinder with the literal frame augmentation. -/
def ForwardZeroProjection : Prop :=
  ∀ k : SimplexCategory,
    forwardFrame0.app k ≫
        DaggerSSet.forget.map (frame0Projection.app k) =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (parameter.obj k) ≫
        freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0})

/-- The original free dagger zero-simplex is terminal even after forgetting
dagger, because the forgetful functor is a right adjoint. -/
private def freeZeroUnderlyingIsTerminal :
    IsTerminal (freeDagger.obj (Δ[0] : SSet.{0})).toSSet := by
  letI : PreservesLimits DaggerSSet.forget.{0} :=
    DaggerSSet.forget_preservesLimits
  exact JTWalkingUnitaryWeak.freeZeroIsTerminal.isTerminalObj
    DaggerSSet.forget _

/-- Every map from the zero cylinder to the underlying free dagger point
agrees with the literal frame augmentation. -/
theorem forwardZeroProjection : ForwardZeroProjection := by
  intro k
  exact freeZeroUnderlyingIsTerminal.hom_ext _ _

private theorem boundaryVertexMap_zero :
    boundaryVertexMap 0 = SSet.boundary₁.ι₀ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₀_ι]
  rw [SSet.stdSimplex.δ_one]
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

private theorem boundaryVertexMap_one :
    boundaryVertexMap 1 = SSet.boundary₁.ι₁ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₁_ι]
  rw [SSet.stdSimplex.δ_zero]
  simp only [SSet.yonedaEquiv_comp, boundaryVertexMap, Equiv.apply_symm_apply]
  rfl

private theorem boundaryVertexMap_eq (i : Fin 2) :
    boundaryVertexMap i =
      if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁ := by
  fin_cases i
  · simpa using boundaryVertexMap_zero
  · simpa using boundaryVertexMap_one

/-- The native boundary inclusion followed by `∂Δ¹ → Δ¹` is the ordinary
coface selected by the same ordered vertex. -/
private theorem boundaryIota_std (i : Fin 2) :
    (if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ≫
        (SSet.boundary 1).ι = SSet.stdSimplex.map (ordinaryEndpoint i) := by
  fin_cases i
  · change SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι =
        SSet.stdSimplex.map (ordinaryEndpoint 0)
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    apply SSet.yonedaEquiv.injective
    rfl
  · change SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι =
        SSet.stdSimplex.map (ordinaryEndpoint 1)
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    apply SSet.yonedaEquiv.injective
    rfl

private theorem forwardPair_endpoint (i : Fin 2) (k : SimplexCategory) :
    (SSet.stdSimplex.map (ordinaryEndpoint i) ⊗ₘ
        𝟙 (parameter.obj k)) ≫ forwardFrame.app k =
      forwardFrame0.app k ≫
        DaggerSSet.forget.map ((frameEndpoint i).app k) := by
  have h := forwardPair.naturality
    (show (⦋0⦌, k) ⟶ (⦋1⦌, k) from (ordinaryEndpoint i, 𝟙 k))
  rw [forwardPair_zero_app, forwardPair_one_app] at h
  simpa [ordinaryPairParameter, ordinaryPairUnderlying, ordinaryPair,
    frameEndpoint, endpointSection, includedEndpoint i] using h

theorem frameEndpointSquare (i : Fin 2) : FrameEndpointSquare i := by
  intro k
  have hι := boundaryIota_std i
  have h := forwardPair_endpoint i k
  change ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
      parameter.obj k) ≫
        ((SSet.boundary 1).ι ⊗ₘ 𝟙 (parameter.obj k)) ≫
          forwardFrame.app k = _
  rw [MonoidalCategory.tensorHom_id, ← Category.assoc,
    ← MonoidalCategory.comp_whiskerRight, hι]
  simpa only [MonoidalCategory.tensorHom_id] using h

/-- The boundary projection triangle follows from terminality of the
underlying free dagger point and naturality of the free adjunction unit. -/
theorem projectionEndpointSquare (i : Fin 2) : ProjectionEndpointSquare i := by
  intro k
  let e : (Δ[0] : SSet.{0}) ⟶ boundary :=
    if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁
  have he : e = boundaryVertexMap i := (boundaryVertexMap_eq i).symm
  have hfst := CartesianMonoidalCategory.whiskerRight_fst e (parameter.obj k)
  have hunit : boundaryVertexMap i ≫ freeDaggerAdjunction.unit.app boundary =
      freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0}) ≫
        DaggerSSet.forget.map (freeDagger.map (boundaryVertexMap i)) := by
    simpa only [Functor.id_map, Functor.comp_map] using
      freeDaggerAdjunction.unit.naturality (boundaryVertexMap i)
  have hzero := forwardZeroProjection k
  change (e ▷ parameter.obj k) ≫ cylinderProjection.app k ≫
      freeDaggerAdjunction.unit.app boundary =
    forwardFrame0.app k ≫
      DaggerSSet.forget.map ((endpointCollapse i).app k)
  calc
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (parameter.obj k) ≫ e ≫ freeDaggerAdjunction.unit.app boundary := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫ freeDaggerAdjunction.unit.app boundary) hfst
    _ = CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
          (parameter.obj k) ≫ freeDaggerAdjunction.unit.app (Δ[0] : SSet.{0}) ≫
            DaggerSSet.forget.map (freeDagger.map (boundaryVertexMap i)) := by
          rw [he]
          simpa only [Category.assoc] using
            congrArg (fun t ↦ CartesianMonoidalCategory.fst
              (Δ[0] : SSet.{0}) (parameter.obj k) ≫ t) hunit
    _ = forwardFrame0.app k ≫
          DaggerSSet.forget.map (frame0Projection.app k) ≫
            DaggerSSet.forget.map (freeDagger.map (boundaryVertexMap i)) := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫
              DaggerSSet.forget.map (freeDagger.map (boundaryVertexMap i))) hzero.symm
    _ = forwardFrame0.app k ≫
          DaggerSSet.forget.map ((endpointCollapse i).app k) := by
          simp [endpointCollapse]

/-- Precomposing the raw pushout condition with either coproduct summand
gives the exact ordered face relation. -/
private theorem rawEndpointCondition (i : Fin 2) :
    frameEndpoint i ≫ pushout.inl rawFaces rawEndpoints =
      endpointCollapse i ≫ pushout.inr rawFaces rawEndpoints := by
  have h := pushout.condition (f := rawFaces) (g := rawEndpoints)
  fin_cases i
  · simpa [rawFaces, rawEndpoints] using
      congrArg (fun t ↦ (coprod.inl : frame0 ⟶ frame0 ⨿ frame0) ≫ t) h
  · simpa [rawFaces, rawEndpoints] using
      congrArg (fun t ↦ (coprod.inr : frame0 ⟶ frame0 ⨿ frame0) ≫ t) h

private theorem boundaryToRaw_app (k : SimplexCategory) :
    boundaryToRaw.app k =
      freeDaggerAdjunction.unit.app boundary ≫
        DaggerSSet.forget.map ((pushout.inr rawFaces rawEndpoints).app k) := by
  simp [boundaryToRaw, rawBoundary]
  cat_disch

/-- The remaining endpoint equation after restricting the boundary cylinder
to one of its two coproduct summands. This definition is an obligation, not
a hypothesis in the final statement. -/
def EndpointRelation (i : Fin 2) : Prop :=
  ∀ k : SimplexCategory,
    ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫
        (cylinderInclusion.app k ≫ forwardRaw.app k) =
      ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫ boundaryRaw.app k

/-- Combine the two actual frame triangles with the raw pushout equation. -/
theorem endpointRelation (i : Fin 2) : EndpointRelation i := by
  intro k
  let e : (Δ[0] : SSet.{0}) ⟶ boundary :=
    if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁
  let j : frame1.obj k ⟶ rawCollapse.obj k :=
    (pushout.inl rawFaces rawEndpoints).app k
  let b : B ⟶ rawCollapse.obj k :=
    (pushout.inr rawFaces rawEndpoints).app k
  have hf := frameEndpointSquare i k
  have hp := projectionEndpointSquare i k
  have hr := NatTrans.congr_app (rawEndpointCondition i) k
  have hr' : DaggerSSet.forget.map ((frameEndpoint i).app k) ≫
        DaggerSSet.forget.map j =
      DaggerSSet.forget.map ((endpointCollapse i).app k) ≫
        DaggerSSet.forget.map b := by
    simpa only [NatTrans.comp_app, Functor.map_comp] using
      congrArg DaggerSSet.forget.map hr
  change (e ▷ parameter.obj k) ≫
      (cylinderInclusion.app k ≫ forwardRaw.app k) =
    (e ▷ parameter.obj k) ≫ boundaryRaw.app k
  calc
    _ = (e ▷ parameter.obj k) ≫ cylinderInclusion.app k ≫
          forwardFrame.app k ≫ DaggerSSet.forget.map j := by
          simp [forwardRaw, j]
    _ = forwardFrame0.app k ≫
          DaggerSSet.forget.map ((frameEndpoint i).app k) ≫
            DaggerSSet.forget.map j := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫ DaggerSSet.forget.map j) hf
    _ = forwardFrame0.app k ≫
          DaggerSSet.forget.map ((endpointCollapse i).app k) ≫
            DaggerSSet.forget.map b := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ forwardFrame0.app k ≫ t) hr'
    _ = (e ▷ parameter.obj k) ≫ cylinderProjection.app k ≫
          freeDaggerAdjunction.unit.app boundary ≫ DaggerSSet.forget.map b := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ t ≫ DaggerSSet.forget.map b) hp.symm
    _ = (e ▷ parameter.obj k) ≫ boundaryRaw.app k := by
          simp [boundaryRaw, boundaryToRaw_app, b]

/-- The native right-tensor binary-coproduct property reduces the full
boundary compatibility to exactly two ordered endpoint equations. -/
theorem boundaryCompatibility_of_endpointRelations
    (h0 : EndpointRelation 0) (h1 : EndpointRelation 1) :
    BoundaryCompatibility := by
  apply NatTrans.ext
  funext k
  change cylinderInclusion.app k ≫ forwardRaw.app k = boundaryRaw.app k
  apply SSet.boundary₁.hom_ext_rightTensor
  · exact h0 k
  · exact h1 k

/-- Actual boundary equality for the candidate strict quotient map. -/
theorem boundaryCompatibility : BoundaryCompatibility :=
  boundaryCompatibility_of_endpointRelations (endpointRelation 0) (endpointRelation 1)

/-- The ordinary natural quotient map provided by the pushout, conditional
only on the exact two-endpoint relation above. -/
def CEToRaw (h : BoundaryCompatibility) :
    CE ⟶ rawCollapse ⋙ DaggerSSet.forget :=
  pushout.desc forwardRaw boundaryToRaw h

/-- The dagger-compatible extension of the ordinary quotient map. The
adjunction makes its compatibility with parameter operators automatic. -/
def freeCEToRaw (h : BoundaryCompatibility) : CEFree ⟶ rawCollapse where
  app k := (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj k)).symm
    ((CEToRaw h).app k)
  naturality k l f := by
    apply (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj l)).injective
    change (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj l))
        (freeDagger.map (CE.map f) ≫
          (freeDaggerAdjunction.homEquiv (CE.obj l) (rawCollapse.obj l)).symm
            ((CEToRaw h).app l)) =
      (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj l))
        ((freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj k)).symm
          ((CEToRaw h).app k) ≫ rawCollapse.map f)
    rw [freeDaggerAdjunction.homEquiv_naturality_left,
      freeDaggerAdjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact (CEToRaw h).naturality f

/-- Ordered boundary calibration required of the free quotient map. -/
def BoundaryCalibration (h : BoundaryCompatibility) : Prop :=
  CEFreeBoundary ≫ freeCEToRaw h = rawBoundary

/-- The literal natural dagger map supplied by the proved boundary square. -/
def actualFreeCEToRaw : CEFree ⟶ rawCollapse :=
  freeCEToRaw boundaryCompatibility

/-- The literal map restricts to the prescribed ordered boundary
inclusion. This is a separate equality from its eventual invertibility. -/
theorem actualBoundaryCalibration :
    CEFreeBoundary ≫ actualFreeCEToRaw = rawBoundary := by
  apply NatTrans.ext
  funext k
  apply (freeDaggerAdjunction.homEquiv boundary (rawCollapse.obj k)).injective
  have hdesc : CE_boundary.app k ≫ (CEToRaw boundaryCompatibility).app k =
      boundaryToRaw.app k := by
    exact NatTrans.congr_app
      (pushout.inr_desc forwardRaw boundaryToRaw boundaryCompatibility) k
  calc
    (freeDaggerAdjunction.homEquiv boundary (rawCollapse.obj k))
        ((CEFreeBoundary ≫ actualFreeCEToRaw).app k) =
      CE_boundary.app k ≫ (CEToRaw boundaryCompatibility).app k := by
        change (freeDaggerAdjunction.homEquiv boundary (rawCollapse.obj k))
          (𝟙 _ ≫ freeDagger.map (CE_boundary.app k) ≫
            (freeDaggerAdjunction.homEquiv (CE.obj k) (rawCollapse.obj k)).symm
              ((CEToRaw boundaryCompatibility).app k)) = _
        simp only [Category.id_comp]
        rw [freeDaggerAdjunction.homEquiv_naturality_left,
          Equiv.apply_symm_apply]
    _ = boundaryToRaw.app k := hdesc
    _ = (freeDaggerAdjunction.homEquiv boundary (rawCollapse.obj k))
          (rawBoundary.app k) := by
        rw [boundaryToRaw_app]
        simpa using (freeDaggerAdjunction.homEquiv_naturality_right
          (𝟙 B) (rawBoundary.app k)).symm

end

end DaggerModels.PartII.JTXiEndpointCollapseBoundary
