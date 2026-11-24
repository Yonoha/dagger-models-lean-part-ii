import DaggerModelsPartII.JTRightAdjointOrderedFiber
import DaggerModelsPartII.JTXiOrdinaryLatching
import DaggerModelsPartII.JTCEJoyalResolution
import DaggerModelsPartII.ArrowReedyCornerInterchange
import DaggerModelsPartII.StrictFrameMappingFibration
import NativeJoyalMappingTensor
import NativeJoyalFirstFactorization
import NativeIhomRelativeSectionsWeak
import NativeSimplicialPushoutTensorMono
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# The literal ordinary endpoint mapping arrow

This module develops the original ordinary JT interval parameter as an
arrow-valued cosimplicial object. Its relative Reedy corner is the cartesian
pushout tensor of the ordered interval boundary with the actual groupoid
parameter latching map. The intended consumer is the original right nerve
endpoint arrow into a quasicategory.

The literal original right-nerve endpoint arrow is identified with
precomposition along this interval-boundary map. Its mapping-space arrow
is a Kan fibration into every quasicategory.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial MonoidalCategory
  MonoidalClosed
  HomotopicalAlgebra MorphismProperty DaggerModels

namespace DaggerModels.PartII.JTOrdinaryEndpointFibration

open JTXiEndpointCollapse JTXiEndpointCollapseBoundary
  GroupoidSimplex JTParameterLatchingMono

noncomputable section

section OriginalCoefficient

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

private local instance : ModelCategory SSet.{0} := ordinaryJoyalModel
private local instance : CategoryWithWeakEquivalences SSet.{0} :=
  ordinaryJoyalModel.categoryWithWeakEquivalences
private local instance : ModelCategory SSet.{0}ᵒᵖ := inferInstance
private local instance : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
  (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
private local instance : ModelCategory
    (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
  simplicialReedyModelCategory SSet.{0}ᵒᵖ

private local instance (A : SSet.{0}) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft A) :=
  (ihom.adjunction A).leftAdjoint_preservesColimits

private local instance (A : SSet.{0}) :
    PreservesLimitsOfSize.{0, 0} (tensorLeft A).op :=
  preservesLimitsOfSize_op (tensorLeft A)

/-- The literal ordered endpoint inclusion. -/
def j : boundary ⟶ interval := (SSet.boundary 1).ι

instance : Mono j := by
  dsimp only [j]
  infer_instance

/-- The arrow-valued cartesian tensor functor for an arbitrary simplicial
map. The corner of its image of a parameter map is the native pushout tensor. -/
def tensorArrowFunctor {A B : SSet.{0}} (u : A ⟶ B) :
    SSet.{0} ⥤ Arrow SSet.{0} where
  obj K := Arrow.mk (u ▷ K)
  map {K L} f := Arrow.homMk (A ◁ f) (B ◁ f)
    (MonoidalCategory.whisker_exchange u f).symm
  map_id K := by
    apply Arrow.hom_ext
    · change A ◁ 𝟙 K = 𝟙 (A ⊗ K)
      exact (tensorLeft A).map_id K
    · change B ◁ 𝟙 K = 𝟙 (B ⊗ K)
      exact (tensorLeft B).map_id K
  map_comp f g := by
    apply Arrow.hom_ext
    · change A ◁ (f ≫ g) = (A ◁ f) ≫ (A ◁ g)
      exact (tensorLeft A).map_comp f g
    · change B ◁ (f ≫ g) = (B ◁ f) ≫ (B ◁ g)
      exact (tensorLeft B).map_comp f g

/-- The literal boundary cylinder of the original ordinary parameter. -/
def source : SimplexCategory ⥤ SSet.{0} :=
  boundaryCylinder

/-- The literal interval cylinder of the original ordinary parameter. -/
def target : SimplexCategory ⥤ SSet.{0} :=
  intervalCylinder

/-- The actual ordered boundary inclusion in the original parameter. -/
def endpointFaces : source ⟶ target :=
  cylinderInclusion

/-- The two actual endpoint maps of the uncollapsed ordinary interval
parameter, with no change to the chosen vertex order. -/
private theorem boundary_coface (i : Fin 2) :
    (if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ≫ j =
      SSet.stdSimplex.map (ordinaryEndpoint i) := by
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

/-- The boundary-tensor map restricts on each ordered component to the
same ordinary coface used by the original two-index right nerve. -/
theorem endpointFaces_coface (i : Fin 2) (k : SimplexCategory) :
    ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫ endpointFaces.app k =
      SSet.stdSimplex.map (ordinaryEndpoint i) ▷ parameter.obj k := by
  change ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
      parameter.obj k) ≫
        ((SSet.boundary 1).ι ⊗ₘ 𝟙 (parameter.obj k)) = _
  rw [MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_whiskerRight]
  change ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ≫ j) ▷
    parameter.obj k = _
  rw [boundary_coface]

/-- The literal boundary cylinder is the two ordered point cylinders by
the native colimit property of `∂Δ[1]`, degree by degree. -/
private def boundaryHomEquiv (S : SSet.{0}) (k : SimplexCategory) :
    (source.obj k ⟶ S) ≃
      ((zeroCylinder.obj k ⟶ S) × (zeroCylinder.obj k ⟶ S)) where
  toFun f :=
    (((SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫ f),
      ((SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫ f))
  invFun p := (SSet.boundary₁.isColimitRightTensor
      (parameter.obj k)).desc (BinaryCofan.mk p.1 p.2)
  left_inv f := by
    apply SSet.boundary₁.hom_ext_rightTensor
    · change (SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫
          (SSet.boundary₁.isColimitRightTensor (parameter.obj k)).desc
            (BinaryCofan.mk
              ((SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫ f)
              ((SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫ f)) =
          (SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫ f
      rw [SSet.boundary₁.whiskerRight_ι₀_isColimitRightTensor_desc]
      rfl
    · change (SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫
          (SSet.boundary₁.isColimitRightTensor (parameter.obj k)).desc
            (BinaryCofan.mk
              ((SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫ f)
              ((SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫ f)) =
          (SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫ f
      rw [SSet.boundary₁.whiskerRight_ι₁_isColimitRightTensor_desc]
      rfl
  right_inv p := by
    apply Prod.ext
    · change (SSet.boundary₁.ι₀ ▷ parameter.obj k) ≫
          (SSet.boundary₁.isColimitRightTensor (parameter.obj k)).desc
            (BinaryCofan.mk p.1 p.2) = p.1
      rw [SSet.boundary₁.whiskerRight_ι₀_isColimitRightTensor_desc]
      rfl
    · change (SSet.boundary₁.ι₁ ▷ parameter.obj k) ≫
          (SSet.boundary₁.isColimitRightTensor (parameter.obj k)).desc
            (BinaryCofan.mk p.1 p.2) = p.2
      rw [SSet.boundary₁.whiskerRight_ι₁_isColimitRightTensor_desc]
      rfl

/-- The boundary Hom simplicial set is the explicit pointwise pair of the
two actual degree-zero Hom rows, in the native vertex order. -/
private def boundaryMappingPairIso (S : SSet.{0}) :
    EndpointMappingFiber.mapping (Z := S) source ≅
      FunctorToTypes.prod
        (EndpointMappingFiber.mapping (Z := S) zeroCylinder)
        (EndpointMappingFiber.mapping (Z := S) zeroCylinder) :=
  NatIso.ofComponents
    (fun k ↦ (boundaryHomEquiv S k.unop).toIso)
    (by
      intro k l θ
      funext f
      apply Prod.ext
      · change (SSet.boundary₁.ι₀ ▷ parameter.obj l.unop) ≫
            (source.map θ.unop ≫ f) =
          zeroCylinder.map θ.unop ≫
            ((SSet.boundary₁.ι₀ ▷ parameter.obj k.unop) ≫ f)
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun g ↦ g ≫ f)
          (MonoidalCategory.whisker_exchange SSet.boundary₁.ι₀
            (parameter.map θ.unop))
      · change (SSet.boundary₁.ι₁ ▷ parameter.obj l.unop) ≫
            (source.map θ.unop ≫ f) =
          zeroCylinder.map θ.unop ≫
            ((SSet.boundary₁.ι₁ ▷ parameter.obj k.unop) ≫ f)
        rw [← Category.assoc, ← Category.assoc]
        exact congrArg (fun g ↦ g ≫ f)
          (MonoidalCategory.whisker_exchange SSet.boundary₁.ι₁
            (parameter.map θ.unop)))

/-- The same ordered boundary comparison with the categorical product
required by the literal original endpoint arrow. -/
private def boundaryMappingIso (S : SSet.{0}) :
    EndpointMappingFiber.mapping (Z := S) source ≅
      EndpointMappingFiber.mapping (Z := S) zeroCylinder ⨯
        EndpointMappingFiber.mapping (Z := S) zeroCylinder :=
  boundaryMappingPairIso S ≪≫
    (FunctorToTypes.binaryProductIso
      (EndpointMappingFiber.mapping (Z := S) zeroCylinder)
      (EndpointMappingFiber.mapping (Z := S) zeroCylinder)).symm

/-- The native ordinary right-nerve row is the Hom from the literal
constant-first-factor parameter cylinder, for either horizontal index. -/
private def ordinaryRowParameterIso (S : SSet.{0})
    (m : SimplexCategory) :
    JTRightAdjointOrderedFiber.ordinaryRow S m ≅
      EndpointMappingFiber.mapping (Z := S)
        (parameterProduct (SSet.stdSimplex.obj m)) :=
  NatIso.ofComponents
    (fun k ↦ (show
      ULift (OrdinaryJTRealization.tFunctor.obj (m, k.unop) ⟶ S) ≃
        ((parameterProduct (SSet.stdSimplex.obj m)).obj k.unop ⟶ S) from
      { toFun := ULift.down
        invFun := ULift.up
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }).toIso)
    (by
      intro k l θ
      ext f
      change (SSet.stdSimplex.map (𝟙 m) ⊗ₘ parameter.map θ.unop) ≫
          f.down =
        (𝟙 (SSet.stdSimplex.obj m) ⊗ₘ parameter.map θ.unop) ≫ f.down
      have hm : SSet.stdSimplex.map (𝟙 m) =
          𝟙 (SSet.stdSimplex.obj m) := SSet.stdSimplex.map_id m
      rw [hm])

/-- The original degree-one right-nerve row is Hom from the exact retained
ordinary interval cylinder. -/
private def ordinaryTargetIso (S : SSet.{0}) :
    JTRightAdjointOrderedFiber.ordinaryRow S ⦋1⦌ ≅
      EndpointMappingFiber.mapping (Z := S) target :=
  ordinaryRowParameterIso S ⦋1⦌

/-- The corresponding degree-zero row is Hom from the exact retained
point cylinder. -/
private def ordinaryZeroIso (S : SSet.{0}) :
    JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ≅
      EndpointMappingFiber.mapping (Z := S) zeroCylinder :=
  ordinaryRowParameterIso S ⦋0⦌

/-- The original categorical product of the two degree-zero rows is
canonically the Hom from the ordered boundary cylinder. -/
private def ordinaryBoundaryIso (S : SSet.{0}) :
    JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⨯
      JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ≅
        EndpointMappingFiber.mapping (Z := S) source :=
  prod.mapIso (ordinaryZeroIso S) (ordinaryZeroIso S) ≪≫
    (boundaryMappingIso S).symm

/-- Precomposition along the actual interval boundary before comparison
with the original right-nerve endpoint arrow. -/
private def nativeEndpointArrow (S : SSet.{0}) :
    EndpointMappingFiber.mapping (Z := S) target ⟶
      EndpointMappingFiber.mapping (Z := S) source :=
  EndpointMappingFiber.precomp (Z := S) endpointFaces

/-- A literal component check: the boundary-tensor restriction is exactly
the original right-nerve coface, including its native `ULift`. -/
private theorem originalEndpoint_component (S : SSet.{0})
    (i : Fin 2) (k : SimplexCategory)
    (f : (JTRightAdjointOrderedFiber.ordinaryRow S ⦋1⦌).obj (op k)) :
    ((if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁) ▷
        parameter.obj k) ≫ endpointFaces.app k ≫ f.down =
      ((JTRightAdjointOrderedFiber.ordinaryRowEndpoint S i).app (op k) f).down := by
  rw [← Category.assoc, endpointFaces_coface]
  change (SSet.stdSimplex.map (ordinaryEndpoint i) ▷
      parameter.obj k) ≫ f.down =
    (OrdinaryJTRealization.tFunctor.map
      (show (⦋0⦌, k) ⟶ (⦋1⦌, k) from
        (ordinaryEndpoint i, 𝟙 k))) ≫ f.down
  rw [OrdinaryJTRealization.tFunctor_map, parameter.map_id,
    MonoidalCategory.tensorHom_id]

private theorem binaryProductIso_fst_app (Z : SSet.{0})
    (k : SimplexCategoryᵒᵖ) (z : (Z ⨯ Z).obj k) :
    ((FunctorToTypes.binaryProductIso Z Z).hom.app k z).1 =
      (Limits.prod.fst (X := Z)).app k z := by
  exact congrFun (NatTrans.congr_app
    (FunctorToTypes.binaryProductIso_hom_comp_fst Z Z) k) z

private theorem binaryProductIso_snd_app (Z : SSet.{0})
    (k : SimplexCategoryᵒᵖ) (z : (Z ⨯ Z).obj k) :
    ((FunctorToTypes.binaryProductIso Z Z).hom.app k z).2 =
      (Limits.prod.snd (Y := Z)).app k z := by
  exact congrFun (NatTrans.congr_app
    (FunctorToTypes.binaryProductIso_hom_comp_snd Z Z) k) z

/-- The original endpoint arrow becomes literal boundary precomposition
after the native right-row and ordered-boundary product identifications. -/
private theorem originalEndpoint_square (S : SSet.{0}) :
    (ordinaryTargetIso S).hom ≫ nativeEndpointArrow S =
      JTRightAdjointOrderedFiber.ordinaryEndpointArrow S ≫
        (ordinaryBoundaryIso S).hom := by
  let Z := EndpointMappingFiber.mapping (Z := S) zeroCylinder
  have hPair :
      (ordinaryTargetIso S).hom ≫ nativeEndpointArrow S ≫
          (boundaryMappingPairIso S).hom =
        JTRightAdjointOrderedFiber.ordinaryEndpointArrow S ≫
          (prod.mapIso (ordinaryZeroIso S) (ordinaryZeroIso S)).hom ≫
          (FunctorToTypes.binaryProductIso Z Z).hom := by
    apply NatTrans.ext
    funext k f
    apply Prod.ext
    · dsimp [NatTrans.comp_app, ordinaryTargetIso, ordinaryZeroIso,
        ordinaryRowParameterIso, nativeEndpointArrow, boundaryMappingPairIso,
        boundaryHomEquiv, EndpointMappingFiber.precomp,
        JTRightAdjointOrderedFiber.ordinaryEndpointArrow]
      change _ = ((FunctorToTypes.binaryProductIso Z Z).hom.app k
        ((prod.map (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom).app k
          ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f))).1
      rw [binaryProductIso_fst_app]
      have hm := congrFun (NatTrans.congr_app
        (prod.map_fst (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom) k)
        ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)
      change (prod.fst : Z ⨯ Z ⟶ Z).app k
          ((prod.map (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom).app k
            ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)) =
        (ordinaryZeroIso S).hom.app k
          ((prod.fst : JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⨯
              JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⟶
              JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌).app k
            ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)) at hm
      rw [hm]
      have hl := congrFun (NatTrans.congr_app
        (prod.lift_fst
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 0)
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 1)) k) f
      change (prod.fst : JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⨯
          JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⟶
          JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌).app k
          ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f) =
        (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 0).app k f at hl
      rw [hl]
      change _ = ((JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 0).app k f).down
      change ((SSet.boundary₁.ι₀ ▷ parameter.obj k.unop) ≫
          endpointFaces.app k.unop) ≫ f.down =
        ((JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 0).app k f).down
      simpa only [Category.assoc] using
        originalEndpoint_component S 0 k.unop f
    · dsimp [NatTrans.comp_app, ordinaryTargetIso, ordinaryZeroIso,
        ordinaryRowParameterIso, nativeEndpointArrow, boundaryMappingPairIso,
        boundaryHomEquiv, EndpointMappingFiber.precomp,
        JTRightAdjointOrderedFiber.ordinaryEndpointArrow]
      change _ = ((FunctorToTypes.binaryProductIso Z Z).hom.app k
        ((prod.map (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom).app k
          ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f))).2
      rw [binaryProductIso_snd_app]
      have hm := congrFun (NatTrans.congr_app
        (prod.map_snd (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom) k)
        ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)
      change (prod.snd : Z ⨯ Z ⟶ Z).app k
          ((prod.map (ordinaryZeroIso S).hom (ordinaryZeroIso S).hom).app k
            ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)) =
        (ordinaryZeroIso S).hom.app k
          ((prod.snd : JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⨯
              JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⟶
              JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌).app k
            ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f)) at hm
      rw [hm]
      have hl := congrFun (NatTrans.congr_app
        (prod.lift_snd
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 0)
          (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 1)) k) f
      change (prod.snd : JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⨯
          JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌ ⟶
          JTRightAdjointOrderedFiber.ordinaryRow S ⦋0⦌).app k
          ((JTRightAdjointOrderedFiber.ordinaryEndpointArrow S).app k f) =
        (JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 1).app k f at hl
      rw [hl]
      change _ = ((JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 1).app k f).down
      change ((SSet.boundary₁.ι₁ ▷ parameter.obj k.unop) ≫
          endpointFaces.app k.unop) ≫ f.down =
        ((JTRightAdjointOrderedFiber.ordinaryRowEndpoint S 1).app k f).down
      simpa only [Category.assoc] using
        originalEndpoint_component S 1 k.unop f
  apply (cancel_mono (boundaryMappingPairIso S).hom).mp
  calc
    (ordinaryTargetIso S).hom ≫ nativeEndpointArrow S ≫
        (boundaryMappingPairIso S).hom =
      JTRightAdjointOrderedFiber.ordinaryEndpointArrow S ≫
        (prod.mapIso (ordinaryZeroIso S) (ordinaryZeroIso S)).hom ≫
        (FunctorToTypes.binaryProductIso Z Z).hom := hPair
    _ = (JTRightAdjointOrderedFiber.ordinaryEndpointArrow S ≫
        (ordinaryBoundaryIso S).hom) ≫
          (boundaryMappingPairIso S).hom := by
      dsimp [ordinaryBoundaryIso, boundaryMappingIso]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      dsimp only [Z]

/-- An Arrow isomorphism pins the proven categorical-product arrow to the
literal precomposition arrow, without changing either original endpoint. -/
private def originalEndpointArrowIso (S : SSet.{0}) :
    Arrow.mk (JTRightAdjointOrderedFiber.ordinaryEndpointArrow S) ≅
      Arrow.mk (nativeEndpointArrow S) :=
  Arrow.isoMk (ordinaryTargetIso S) (ordinaryBoundaryIso S)
    (originalEndpoint_square S)

/-- The exact interval-boundary arrow in every cosimplicial degree. -/
def parameterArrow : SimplexCategory ⥤ Arrow SSet.{0} where
  obj k := Arrow.mk (endpointFaces.app k)
  map {k l} f := Arrow.homMk (source.map f) (target.map f)
    (endpointFaces.naturality f)
  map_id k := by
    apply Arrow.hom_ext
    · exact source.map_id k
    · exact target.map_id k
  map_comp f g := by
    apply Arrow.hom_ext
    · simp only [Arrow.homMk_left, Arrow.comp_left, Functor.map_comp]
    · simp only [Arrow.homMk_right, Arrow.comp_right, Functor.map_comp]

/-- The literal interval-boundary diagram agrees with the cartesian
arrow-tensor functor evaluated on the actual groupoid parameter. -/
private def parameterArrowTensorIso :
    parameterArrow ≅ parameter ⋙ tensorArrowFunctor j :=
  NatIso.ofComponents
    (fun k ↦ Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      change 𝟙 _ ≫ j ▷ parameter.obj k =
        endpointFaces.app k ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
      change j ▷ parameter.obj k =
        (j ⊗ₘ 𝟙 (parameter.obj k))
      rw [MonoidalCategory.tensorHom_id]))
    (by
      intro k l f
      apply Arrow.hom_ext
      · change source.map f = boundary ◁ parameter.map f
        rfl
      · change target.map f = interval ◁ parameter.map f
        rfl)

/-- The actual proper-face diagram in the category of ordered interval
boundary arrows. -/
private def faceArrowDiagram (n : ℕ) :
    (MatchingIndex n)ᵒᵖ ⥤ Arrow SSet.{0} :=
  (matchingProjection n).leftOp ⋙ parameterArrow

/-- Its canonical cocone into the degree-`n` original parameter arrow. -/
private def faceArrowCocone (n : ℕ) : Cocone (faceArrowDiagram n) where
  pt := parameterArrow.obj ⦋n⦌
  ι :=
    { app := fun s ↦ parameterArrow.map s.unop.obj.hom.unop
      naturality := by
        intro s t f
        change parameterArrow.map f.unop.hom.right.unop ≫
            parameterArrow.map t.unop.obj.hom.unop =
          parameterArrow.map s.unop.obj.hom.unop ≫ 𝟙 _
        rw [Category.comp_id, ← parameterArrow.map_comp]
        exact parameterArrow.congr_map
          (congrArg Quiver.Hom.unop (StructuredArrow.w f.unop.hom)) }

/-- The actual proper-face Arrow latching map, with both source and
pushout-corner components retained. -/
private def faceArrowLatchingMap (n : ℕ) :
    colimit (faceArrowDiagram n) ⟶ parameterArrow.obj ⦋n⦌ :=
  colimit.desc _ (faceArrowCocone n)

/-- Opposite matching of the Arrow diagram is the actual proper-face
Arrow colimit, without an objectwise approximation. -/
private def faceArrowMatchingIso (n : ℕ) :
    (matchingFunctor n).obj parameterArrow.op ≅
      op (colimit (faceArrowDiagram n)) :=
  limit.isoLimitCone ⟨coneOfCoconeLeftOp
    (F := matchingProjection n ⋙ parameterArrow.op)
    (colimit.cocone (faceArrowDiagram n)),
    isLimitConeOfCoconeLeftOp _
      (colimit.isColimit (faceArrowDiagram n))⟩

/-- The native opposite matching comparison is the opposite of the
proper-face Arrow latching map, in every degree including zero. -/
private theorem faceArrowMatchingIso_comp (n : ℕ) :
    (matchingComparison n).app parameterArrow.op ≫
      (faceArrowMatchingIso n).hom = (faceArrowLatchingMap n).op := by
  apply Quiver.Hom.unop_inj
  apply (colimit.isColimit (faceArrowDiagram n)).hom_ext
  intro s
  apply Quiver.Hom.op_inj
  rw [op_comp, op_comp]
  simp only [Quiver.Hom.op_unop]
  have hfac : (colimit.cocone (faceArrowDiagram n)).ι.app s ≫
      faceArrowLatchingMap n = (faceArrowCocone n).ι.app s :=
    colimit.ι_desc (faceArrowCocone n) s
  conv_rhs => rw [← op_comp, hfac]
  change ((matchingComparison n).app parameterArrow.op ≫
      (faceArrowMatchingIso n).hom) ≫
      (colimit.ι (faceArrowDiagram n) s).op =
    (parameterArrow.map s.unop.obj.hom.unop).op
  rw [Category.assoc]
  have hlim : (faceArrowMatchingIso n).hom ≫
      (colimit.ι (faceArrowDiagram n) s).op =
        limit.π (matchingProjection n ⋙ parameterArrow.op) s.unop :=
    limit.isoLimitCone_hom_π
      ⟨coneOfCoconeLeftOp
        (F := matchingProjection n ⋙ parameterArrow.op)
        (colimit.cocone (faceArrowDiagram n)),
        isLimitConeOfCoconeLeftOp _
          (colimit.isColimit (faceArrowDiagram n))⟩ s.unop
  rw [hlim]
  exact limit.lift_π _ _

/-- The same proper-face diagram after the canonical literal-to-tensor
Arrow comparison. -/
private def faceArrowTensorIso (n : ℕ) :
    faceArrowDiagram n ≅
      faceDiagram n ⋙ tensorArrowFunctor j :=
  Functor.isoWhiskerLeft (matchingProjection n).leftOp
    parameterArrowTensorIso

/-- The boundary-tensor image of the actual scalar face colimit cocone. -/
private def faceTensorLeftCocone (n : ℕ) :
    Cocone ((faceDiagram n ⋙ tensorArrowFunctor j) ⋙
      Arrow.leftFunc) :=
  (tensorLeft boundary).mapCocone (colimit.cocone (faceDiagram n))

/-- The interval-tensor image of the same face colimit cocone. -/
private def faceTensorRightCocone (n : ℕ) :
    Cocone ((faceDiagram n ⋙ tensorArrowFunctor j) ⋙
      Arrow.rightFunc) :=
  (tensorLeft interval).mapCocone (colimit.cocone (faceDiagram n))

private def faceTensorLeftIsColimit (n : ℕ) :
    IsColimit (faceTensorLeftCocone n) :=
  isColimitOfPreserves (tensorLeft boundary)
    (colimit.isColimit (faceDiagram n))

private def faceTensorRightIsColimit (n : ℕ) :
    IsColimit (faceTensorRightCocone n) :=
  isColimitOfPreserves (tensorLeft interval)
    (colimit.isColimit (faceDiagram n))

/-- Mathlib's comma-category pointwise colimit, specialized only to this
face diagram of cartesian tensor arrows. -/
private def faceTensorArrowCocone (n : ℕ) :
    Cocone (faceDiagram n ⋙ tensorArrowFunctor j) :=
  Comma.coconeOfPreserves
    (faceDiagram n ⋙ tensorArrowFunctor j)
    (faceTensorLeftIsColimit n) (faceTensorRightCocone n)

private def faceTensorArrowIsColimit (n : ℕ) :
    IsColimit (faceTensorArrowCocone n) :=
  Comma.coconeOfPreservesIsColimit
    (faceDiagram n ⋙ tensorArrowFunctor j)
    (faceTensorLeftIsColimit n) (faceTensorRightIsColimit n)

/-- The point arrow of the native comma-category face colimit is the
same ordered inclusion tensored with the actual scalar face colimit. -/
private theorem faceTensorArrowCocone_hom (n : ℕ) :
    (faceTensorArrowCocone n).pt.hom =
      j ▷ colimit (faceDiagram n) := by
  apply (faceTensorLeftIsColimit n).hom_ext
  intro s
  have hs := Arrow.w ((faceTensorArrowCocone n).ι.app s)
  change (boundary ◁ colimit.ι (faceDiagram n) s) ≫
      (faceTensorArrowCocone n).pt.hom =
    (j ▷ (faceDiagram n).obj s) ≫
      (interval ◁ colimit.ι (faceDiagram n) s) at hs
  exact hs.trans
    (MonoidalCategory.whisker_exchange j
      (colimit.ι (faceDiagram n) s)).symm

private def faceTensorArrowCoconePointIso (n : ℕ) :
    (faceTensorArrowCocone n).pt ≅
      (tensorArrowFunctor j).obj (colimit (faceDiagram n)) :=
  Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
    exact (faceTensorArrowCocone_hom n).symm)

/-- The Mathlib comma colimit cocone is the image of the scalar face
colimit cocone, after the explicit point-arrow identity. -/
private def faceTensorArrowCoconeIso (n : ℕ) :
    faceTensorArrowCocone n ≅
      (tensorArrowFunctor j).mapCocone (colimit.cocone (faceDiagram n)) :=
  Cocones.ext (faceTensorArrowCoconePointIso n) (by
    intro s
    apply Arrow.hom_ext
    · rfl
    · rfl)

private def faceTensorArrowMappedIsColimit (n : ℕ) :
    IsColimit ((tensorArrowFunctor j).mapCocone
      (colimit.cocone (faceDiagram n))) :=
  (faceTensorArrowIsColimit n).ofIsoColimit
    (faceTensorArrowCoconeIso n)

/-- The specific face-diagram colimit comparison for the cartesian
tensor-Arrow functor; no global colimit-preservation instance is asserted. -/
private def faceTensorArrowColimitIso (n : ℕ) :
    colimit (faceDiagram n ⋙ tensorArrowFunctor j) ≅
      (tensorArrowFunctor j).obj (colimit (faceDiagram n)) :=
  IsColimit.coconePointUniqueUpToIso
    (colimit.isColimit (faceDiagram n ⋙ tensorArrowFunctor j))
    (faceTensorArrowMappedIsColimit n)

/-- The literal face-Arrow colimit is the interval-boundary tensor arrow
on the scalar proper-face colimit. -/
private def faceArrowColimitIso (n : ℕ) :
    colimit (faceArrowDiagram n) ≅
      (tensorArrowFunctor j).obj (colimit (faceDiagram n)) :=
  HasColimit.isoOfNatIso (faceArrowTensorIso n) ≪≫
    faceTensorArrowColimitIso n

private theorem faceArrowColimitIso_ι (n : ℕ)
    (s : (MatchingIndex n)ᵒᵖ) :
    colimit.ι (faceArrowDiagram n) s ≫ (faceArrowColimitIso n).hom =
      (faceArrowTensorIso n).hom.app s ≫
        (tensorArrowFunctor j).map (colimit.ι (faceDiagram n) s) := by
  change (colimit.ι (faceArrowDiagram n) s ≫
      (HasColimit.isoOfNatIso (faceArrowTensorIso n)).hom) ≫
        (faceTensorArrowColimitIso n).hom = _
  rw [HasColimit.isoOfNatIso_ι_hom, Category.assoc]
  have hcol := IsColimit.comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (faceDiagram n ⋙ tensorArrowFunctor j))
    (faceTensorArrowMappedIsColimit n) s
  change colimit.ι (faceDiagram n ⋙ tensorArrowFunctor j) s ≫
      (faceTensorArrowColimitIso n).hom =
        (tensorArrowFunctor j).map (colimit.ι (faceDiagram n) s) at hcol
  rw [hcol]

/-- The face-Arrow colimit comparison carries the actual Arrow latching
map to the scalar face-latching map under the tensor-Arrow functor. -/
private theorem faceArrowLatching_square (n : ℕ) :
    (faceArrowColimitIso n).hom ≫
        (tensorArrowFunctor j).map (faceLatchingMap n) =
      faceArrowLatchingMap n ≫
        (parameterArrowTensorIso.app ⦋n⦌).hom := by
  apply (colimit.isColimit (faceArrowDiagram n)).hom_ext
  intro s
  rw [← Category.assoc]
  change (colimit.ι (faceArrowDiagram n) s ≫
      (faceArrowColimitIso n).hom) ≫
        (tensorArrowFunctor j).map (faceLatchingMap n) = _
  rw [faceArrowColimitIso_ι]
  have hfac : colimit.ι (faceDiagram n) s ≫ faceLatchingMap n =
      (faceCocone n).ι.app s := colimit.ι_desc (faceCocone n) s
  calc
    (faceArrowTensorIso n).hom.app s ≫
        (tensorArrowFunctor j).map (colimit.ι (faceDiagram n) s) ≫
          (tensorArrowFunctor j).map (faceLatchingMap n) =
      (faceArrowTensorIso n).hom.app s ≫
        (tensorArrowFunctor j).map
          (colimit.ι (faceDiagram n) s ≫ faceLatchingMap n) := by
            rw [(tensorArrowFunctor j).map_comp]
    _ = (faceArrowTensorIso n).hom.app s ≫
        (tensorArrowFunctor j).map (parameter.map s.unop.obj.hom.unop) := by
          rw [hfac]
          rfl
    _ = colimit.ι (faceArrowDiagram n) s ≫
        (faceArrowLatchingMap n ≫
          (parameterArrowTensorIso.app ⦋n⦌).hom) := by
          have hfacArrow : colimit.ι (faceArrowDiagram n) s ≫
              faceArrowLatchingMap n = (faceArrowCocone n).ι.app s :=
            colimit.ι_desc (faceArrowCocone n) s
          rw [← Category.assoc, hfacArrow]
          exact (parameterArrowTensorIso.hom.naturality
            s.unop.obj.hom.unop).symm

/-- Every actual groupoid-parameter operator is an original Joyal weak map. -/
theorem parameter_map_weak {k l : SimplexCategory} (f : k ⟶ l) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (parameter.map f) := by
  let P := DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
  have hl : P (terminal.from (parameter.obj l)) :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial
      (terminal.from (parameter.obj l))
      (augmentation_trivialFibration l)).2
  have hk : P (terminal.from (parameter.obj k)) :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial
      (terminal.from (parameter.obj k))
      (augmentation_trivialFibration k)).2
  have h : parameter.map f ≫ terminal.from (parameter.obj l) =
      terminal.from (parameter.obj k) := terminalIsTerminal.hom_ext _ _
  exact P.of_postcomp (parameter.map f)
    (terminal.from (parameter.obj l)) hl (by rwa [h])

/-- The ordered-boundary diagram has original Joyal weak structure maps. -/
theorem source_map_weak {k l : SimplexCategory} (f : k ⟶ l) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (source.map f) := by
  change DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
    (boundary ◁ parameter.map f)
  exact DaggerNativeJoyalMappingTensor.weak_whiskerLeft
    boundary (parameter.map f) (parameter_map_weak f)

/-- The interval diagram has original Joyal weak structure maps. -/
theorem target_map_weak {k l : SimplexCategory} (f : k ⟶ l) :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (target.map f) := by
  change DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
    (interval ◁ parameter.map f)
  exact DaggerNativeJoyalMappingTensor.weak_whiskerLeft
    interval (parameter.map f) (parameter_map_weak f)

/-- The same source weak structure maps in the opposite original model. -/
private theorem source_op_maps_weak {k l : SimplexCategoryᵒᵖ}
    (f : k ⟶ l) :
    weakEquivalences SSet.{0}ᵒᵖ (source.op.map f) := by
  rw [weakEquivalences_op]
  change weakEquivalences SSet.{0} (source.map f.unop)
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithWeakEquivalences.weakEquivalences
    (source.map f.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  exact source_map_weak f.unop

/-- The same target weak structure maps in the opposite original model. -/
private theorem target_op_maps_weak {k l : SimplexCategoryᵒᵖ}
    (f : k ⟶ l) :
    weakEquivalences SSet.{0}ᵒᵖ (target.op.map f) := by
  rw [weakEquivalences_op]
  change weakEquivalences SSet.{0} (target.map f.unop)
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithWeakEquivalences.weakEquivalences
    (target.map f.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelWeak]
  exact target_map_weak f.unop

/-- Reedy fibrancy of the actual parameter in the opposite original Joyal
model; this reproduces only the short proof of a private retained lemma. -/
private theorem parameter_op_isFibrant : IsFibrant parameter.op := by
  apply (reedyFibrant_iff_matchingComparison _).mpr
  intro n
  apply ((fibrations SSet.{0}ᵒᵖ).cancel_right_of_respectsIso
    ((matchingComparison n).app parameter.op)
    (JTXiOrdinaryLatching.parameterMatchingIso n).hom).mp
  rw [JTXiOrdinaryLatching.parameterMatchingIso_comp, fibrations_op]
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
    (faceLatchingMap n)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact faceLatchingMap_mono n

/-- Tensoring with a fixed simplicial set preserves original Joyal
cofibrations, because those cofibrations are exactly monomorphisms. -/
private theorem tensor_op_preservesFibrations (A : SSet.{0})
    {K L : SSet.{0}ᵒᵖ} (f : K ⟶ L)
    (hf : fibrations SSet.{0}ᵒᵖ f) :
    fibrations SSet.{0}ᵒᵖ ((tensorLeft A).op.map f) := by
  rw [fibrations_op] at hf ⊢
  change cofibrations SSet.{0} f.unop at hf
  have hm : Mono f.unop := by
    change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      f.unop at hf
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof] at hf
    exact hf
  letI : Mono f.unop := hm
  have hA : Mono (A ◁ f.unop) :=
    DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono A f.unop
  change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
    (A ◁ f.unop)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact hA

/-- The source frame is Reedy fibrant in the opposite original Joyal model. -/
private theorem source_op_isFibrant : IsFibrant source.op := by
  letI : IsFibrant parameter.op := parameter_op_isFibrant
  change IsFibrant (parameter.op ⋙ (tensorLeft boundary).op)
  exact reedyFibrant_comp parameter.op (tensorLeft boundary).op
    (tensor_op_preservesFibrations boundary)

/-- The target frame is Reedy fibrant in the opposite original Joyal model. -/
private theorem target_op_isFibrant : IsFibrant target.op := by
  letI : IsFibrant parameter.op := parameter_op_isFibrant
  change IsFibrant (parameter.op ⋙ (tensorLeft interval).op)
  exact reedyFibrant_comp parameter.op (tensorLeft interval).op
    (tensor_op_preservesFibrations interval)

/-- The exact native pushout tensor of the ordered endpoint inclusion and
the groupoid-parameter face-latching map in degree `n`. -/
private def faceTensor (n : ℕ) :
    SSet.PushoutTensor j (faceLatchingMap n) :=
  ReducedCylinder.tensorSquare j (faceLatchingMap n)

/-- The source component of the required projective Arrow latching square
is an original Joyal cofibration, expressed as its native monomorphism. -/
private theorem faceTensor_source_mono (n : ℕ) :
    Mono (boundary ◁ faceLatchingMap n) := by
  letI : Mono (faceLatchingMap n) := faceLatchingMap_mono n
  exact DaggerNativeIhomRelativeSectionsWeak.left_tensor_mono
    boundary (faceLatchingMap n)

/-- The actual relative corner is also an original Joyal cofibration once
the categorical interchange identifies it with this native map. -/
private theorem faceTensor_corner_mono (n : ℕ) :
    Mono (faceTensor n).ι := by
  letI : Mono (faceLatchingMap n) := faceLatchingMap_mono n
  exact DaggerNativeSimplicialPushoutTensorMono.mono_ι
    j (faceLatchingMap n) (faceTensor n)

/-- The proper-face Arrow latching map is the tensor-Arrow image of the
scalar proper-face latching map, as an isomorphism of actual arrows. -/
private def faceArrowLatchingArrowIso (n : ℕ) :
    Arrow.mk (faceArrowLatchingMap n) ≅
      Arrow.mk ((tensorArrowFunctor j).map (faceLatchingMap n)) :=
  Arrow.isoMk (faceArrowColimitIso n)
    (parameterArrowTensorIso.app ⦋n⦌) (faceArrowLatching_square n)

private theorem faceTensor_corner_eq (n : ℕ) :
    ProjectiveArrowFactorization.corner
      ((tensorArrowFunctor j).map (faceLatchingMap n)) =
        (faceTensor n).ι := by
  apply pushout.hom_ext
  · change pushout.inl (j ▷ (colimit (faceDiagram n)))
        (boundary ◁ faceLatchingMap n) ≫
          ProjectiveArrowFactorization.corner
            ((tensorArrowFunctor j).map (faceLatchingMap n)) =
      (faceTensor n).inl ≫ (faceTensor n).ι
    rw [ProjectiveArrowFactorization.corner, pushout.inl_desc]
    exact (faceTensor n).inl_ι.symm
  · change pushout.inr (j ▷ (colimit (faceDiagram n)))
        (boundary ◁ faceLatchingMap n) ≫
          ProjectiveArrowFactorization.corner
            ((tensorArrowFunctor j).map (faceLatchingMap n)) =
      (faceTensor n).inr ≫ (faceTensor n).ι
    rw [ProjectiveArrowFactorization.corner, pushout.inr_desc]
    exact (faceTensor n).inr_ι.symm

/-- Both parts of the actual projective Arrow cofibration are original
Joyal cofibrations: the boundary tensor map and the pushout corner. -/
private theorem tensorArrow_projective (n : ℕ) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((tensorArrowFunctor j).map (faceLatchingMap n)) := by
  constructor
  · change cofibrations SSet.{0} (boundary ◁ faceLatchingMap n)
    change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      (boundary ◁ faceLatchingMap n)
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof]
    exact faceTensor_source_mono n
  · rw [faceTensor_corner_eq]
    change (DaggerNativeOriginalJoyalSmithModelData.modelData.model).categoryWithCofibrations.cofibrations
      (faceTensor n).ι
    rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelCof,
      DaggerNativeFullWeakSmithGenerators.boundary_cof]
    exact faceTensor_corner_mono n

private theorem faceArrow_projective (n : ℕ) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations
      (faceArrowLatchingMap n) := by
  exact (ProjectiveArrowFactorization.projectiveArrowCofibrations
    (C := SSet.{0})).arrow_mk_iso_iff
      (faceArrowLatchingArrowIso n) |>.2 (tensorArrow_projective n)

/-- The relative matching map to a terminal Arrow diagram is the native
absolute matching comparison after its canonical terminal pullback. -/
private def faceTerminalMatchingArrowIso (n : ℕ) :
    Arrow.mk ((relativeMatchingMap n
      (terminal.from parameterArrow.op)).unop) ≅
        Arrow.mk (((matchingComparison n).app parameterArrow.op).unop) := by
  let D := parameterArrow.op
  let T := ⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow SSet.{0})ᵒᵖ)
  let f : D ⟶ T := terminal.from D
  letI : PreservesLimit (Functor.empty.{0} _)
      (matchingFunctor (C := (Arrow SSet.{0})ᵒᵖ) n) := by
    unfold matchingFunctor
    infer_instance
  have hT : IsTerminal ((matchingFunctor n).obj T) :=
    terminalIsTerminal.isTerminalObj (matchingFunctor n) T
  have hTn : IsTerminal (T.obj (op ⦋n⦌)) :=
    terminalIsTerminal.isTerminalObj
      ((evaluation _ (Arrow SSet.{0})ᵒᵖ).obj (op ⦋n⦌)) T
  letI : IsIso ((matchingComparison n).app T) :=
    isIso_of_isTerminal hTn hT _
  let π := pullback.fst ((matchingFunctor n).map f)
    ((matchingComparison n).app T)
  letI : IsIso π := pullback_fst_iso_of_right_iso _ _
  let e : (pullback ((matchingFunctor n).map f)
      ((matchingComparison n).app T)).unop ≅
        ((matchingFunctor n).obj D).unop := (asIso π).unop.symm
  have hπ : relativeMatchingMap n f ≫ π =
      (matchingComparison n).app D := pullback.lift_fst _ _ _
  refine Arrow.isoMk e (Iso.refl _) ?_
  have hπ' := congrArg Quiver.Hom.unop hπ
  change π.unop ≫ (relativeMatchingMap n f).unop =
    ((matchingComparison n).app D).unop at hπ'
  change e.hom ≫ ((matchingComparison n).app D).unop =
    (relativeMatchingMap n f).unop ≫ 𝟙 _
  rw [Category.comp_id, ← hπ', ← Category.assoc]
  have he : e.hom ≫ π.unop = 𝟙 _ := by
    change (inv π).unop ≫ π.unop = 𝟙 _
    rw [← unop_comp, IsIso.hom_inv_id, unop_id]
  rw [he, Category.id_comp]

/-- The opposite absolute matching comparison is the actual Arrow
face-latching map after the canonical face-colimit isomorphism. -/
private def faceMatchingArrowIso (n : ℕ) :
    Arrow.mk (((matchingComparison n).app parameterArrow.op).unop) ≅
      Arrow.mk (faceArrowLatchingMap n) := by
  let e := faceArrowMatchingIso n
  refine Arrow.isoMk e.unop.symm (Iso.refl _) ?_
  have h := congrArg Quiver.Hom.unop (faceArrowMatchingIso_comp n)
  change e.hom.unop ≫
      (((matchingComparison n).app parameterArrow.op).unop) =
        faceArrowLatchingMap n at h
  change e.unop.symm.hom ≫ faceArrowLatchingMap n =
    (((matchingComparison n).app parameterArrow.op).unop) ≫ 𝟙 _
  rw [Category.comp_id, ← h, ← Category.assoc]
  have he : e.unop.symm.hom ≫ e.hom.unop = 𝟙 _ := by
    change e.inv.unop ≫ e.hom.unop = 𝟙 _
    rw [← unop_comp, Iso.hom_inv_id, unop_id]
  rw [he, Category.id_comp]

/-- The literal parameter-Arrow diagram has the full projective Arrow
matching condition to the terminal diagram in all degrees. -/
private theorem parameterArrow_terminal_projective (n : ℕ) :
    ProjectiveArrowFactorization.projectiveArrowCofibrations
      ((relativeMatchingMap n (terminal.from parameterArrow.op)).unop) := by
  let e := faceTerminalMatchingArrowIso n ≪≫
    faceMatchingArrowIso n ≪≫ faceArrowLatchingArrowIso n
  exact (ProjectiveArrowFactorization.projectiveArrowCofibrations
    (C := SSet.{0})).arrow_mk_iso_iff e |>.2 (tensorArrow_projective n)

/-- The ordered endpoint-face natural transformation has the relative
Reedy cofibration required by strict Hom mapping, including degree zero. -/
private theorem endpointFaces_relativeCofibration (n : ℕ) :
    cofibrations SSet.{0}
      ((relativeMatchingMap n (NatTrans.op endpointFaces)).unop) := by
  have h := ArrowReedyCornerInterchange.structure_relativeCofibration
    parameterArrow.op parameterArrow_terminal_projective n
  change cofibrations SSet.{0}
    ((relativeMatchingMap n (NatTrans.op endpointFaces)).unop) at h
  exact h

/-- A quasicategory is fibrant in the original ordinary Joyal model. -/
private theorem isFibrant_of_quasicategory (S : SSet.{0})
    [S.Quasicategory] : IsFibrant S := by
  apply (isFibrant_iff_of_isTerminal (terminal.from S)
    (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))).mpr
  rw [fibration_iff]
  change ordinaryJoyalModel.categoryWithFibrations.fibrations (terminal.from S)
  rw [DaggerNativeOriginalJoyalSmithModelData.modelData.modelFib,
    DaggerNativeFullWeakSmithGenerators.boundary_cof]
  exact DaggerNativeJoyalWeakTrivialFibrationSpan.terminal_candidate S

end OriginalCoefficient

open scoped SSet.modelCategoryQuillen

/-- For a quasicategory, the literal ordered endpoint arrow of the original
ordinary JT right nerve is a Kan fibration. The coefficient Reedy argument
uses the original ordinary Joyal model; the mapping simplicial sets retain
the native Kan-model fibration predicate. -/
theorem ordinaryEndpointArrow_fibration (S : SSet.{0}) [S.Quasicategory] :
    Fibration (JTRightAdjointOrderedFiber.ordinaryEndpointArrow S) := by
  letI : ModelCategory SSet.{0} := ordinaryJoyalModel
  letI : CategoryWithCofibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithCofibrations
  letI : CategoryWithFibrations SSet.{0} :=
    ordinaryJoyalModel.categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0} :=
    ordinaryJoyalModel.categoryWithWeakEquivalences
  letI : ModelCategory SSet.{0}ᵒᵖ := inferInstance
  letI : CategoryWithFibrations SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithFibrations
  letI : CategoryWithWeakEquivalences SSet.{0}ᵒᵖ :=
    (inferInstance : ModelCategory SSet.{0}ᵒᵖ).categoryWithWeakEquivalences
  letI : ModelCategory (SimplexCategoryᵒᵖ ⥤ SSet.{0}ᵒᵖ) :=
    simplicialReedyModelCategory SSet.{0}ᵒᵖ
  letI : IsFibrant S := isFibrant_of_quasicategory S
  letI : IsFibrant target.op := target_op_isFibrant
  letI : IsFibrant source.op := source_op_isFibrant
  have hrel : reedyMatchingProperty (fibrations SSet.{0}ᵒᵖ)
      (NatTrans.op endpointFaces) := by
    intro n
    rw [fibrations_op]
    exact endpointFaces_relativeCofibration n
  have hstrict := StrictFrameMappingFibration.strictMapping_map_fibration S
    (D := target.op) (E := source.op)
    (fun g ↦ target_op_maps_weak g)
    (fun g ↦ source_op_maps_weak g)
    (NatTrans.op endpointFaces) hrel
  letI : CategoryWithFibrations SSet.{0} :=
    SSet.modelCategoryQuillen.instCategoryWithFibrations
  have hnative : Fibration (nativeEndpointArrow S) := by
    change Fibration ((StrictFrameMappingWeak.strictMapping S).map
      (NatTrans.op endpointFaces))
    exact hstrict
  exact (fibration_iff _).mpr
    (((fibrations SSet.{0}).arrow_mk_iso_iff
      (originalEndpointArrowIso S)).2 ((fibration_iff _).mp hnative))

end

end DaggerModels.PartII.JTOrdinaryEndpointFibration
