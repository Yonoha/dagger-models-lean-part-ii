import DaggerModelsPartII.DiagramMappingRepresentable
import DaggerModelsPartII.DiagramMappingPrecompFibration
import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import DaggerModelsPartII.JTReversalInput
import DaggerModelsPartII.JTRealizationDiagonal
import DaggerModelsPartII.JTXiEndpointCollapseBoundary
import DaggerModelsPartII.JTProjectiveOrderedFiberComparison
import TopCatModelCategory.SSet.FundamentalGroupoid
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The literal endpoint arrow of an injectively fibrant reversal space

The original endpoint arrow is the checked literal arrow in
`JTProjectiveOrderedFiberComparison`. The proof transfers a mapping-space
fibration induced by the actual free-dagger one-boundary to precisely that
arrow. The private tensor--Yoneda identification uses the existing
`representableTensorHomEquiv` and preserves the ordered coface calibration.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTInjectiveOrderedEndpointFibration

open SegalLocalizers
open JTReversalInput JTRealizationDiagonal
open JTXiEndpointCollapseBoundary
open JTProjectiveOrderedFiberComparison

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}

/-- The actual discrete free-dagger boundary object. -/
private def freeBoundary : Source :=
  ReversalDiscreteFreeColimits.discreteFree.obj (SSet.boundary 1).toSSet

/-- The boundary inclusion after the actual Part I free functor and
discretization. -/
private def freeBoundaryInclusion :
    freeBoundary ⟶ daggerSimplex 1 :=
  ReversalDiscreteFreeColimits.discreteFree.map (SSet.boundary 1).ι

/-- The two ordered boundary legs are the actual free zero-simplices. -/
private def freeBoundaryLeg (i : Fin 2) :
    daggerSimplex 0 ⟶ freeBoundary :=
  ReversalDiscreteFreeColimits.discreteFree.map
    (if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁)

/-- The literal free boundary inclusion is monic in the reversal-diagram
category. -/
private theorem freeBoundaryInclusion_mono : Mono freeBoundaryInclusion := by
  change Mono
    (ReversalDiscreteFreeColimits.discreteFree.map (SSet.boundary 1).ι)
  exact ReversalDiscreteFreeColimits.map_mono (SSet.boundary 1).ι

/-- The actual discrete-free functor preserves the binary coproduct of
the two ordered boundary vertices. -/
private theorem discreteFree_preservesBinaryCoproduct :
    PreservesColimitsOfShape (Discrete WalkingPair)
      ReversalDiscreteFreeColimits.discreteFree.{0} := by
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      DaggerSSet.toPresheaf.{0} :=
    daggerSSetEquivalencePresheaf.toAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      (SimplicialObject.const (Type 0)) :=
    (CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      ((Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
        (SimplicialObject.const (Type 0))) := inferInstance
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      discreteDagger.{0} := by
    change PreservesColimitsOfShape (Discrete WalkingPair)
      (DaggerSSet.toPresheaf.{0} ⋙
        (Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
          (SimplicialObject.const (Type 0)))
    infer_instance
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      freeDagger.{0} :=
    freeDaggerAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  change PreservesColimitsOfShape (Discrete WalkingPair)
    (freeDagger.{0} ⋙ discreteDagger.{0})
  infer_instance

/-- The literal free boundary is the coproduct of two free zero-simplices. -/
private def freeBoundaryIsColimit :
    IsColimit (BinaryCofan.mk (freeBoundaryLeg 0) (freeBoundaryLeg 1)) := by
  letI : PreservesColimitsOfShape (Discrete WalkingPair)
      ReversalDiscreteFreeColimits.discreteFree.{0} :=
    discreteFree_preservesBinaryCoproduct
  change IsColimit (BinaryCofan.mk
      (ReversalDiscreteFreeColimits.discreteFree.map SSet.boundary₁.ι₀)
      (ReversalDiscreteFreeColimits.discreteFree.map SSet.boundary₁.ι₁))
  exact mapIsColimitOfPreservesOfIsColimit
    ReversalDiscreteFreeColimits.discreteFree _ _ SSet.boundary₁.isColimit

/-- Strict mapping spaces carry that actual coproduct to an ordered
binary product cone. -/
private def freeBoundaryMappingIsLimit (W : Source) :
    IsLimit (BinaryFan.mk
      (diagramMappingPrecomp (freeBoundaryLeg 0) W)
      (diagramMappingPrecomp (freeBoundaryLeg 1) W)) := by
  letI : PreservesLimitsOfShape (Discrete WalkingPair)
      (diagramMappingSource W) :=
    diagramMappingSource_preservesLimitsOfShape (Discrete WalkingPair) W
  have h := mapIsLimitOfPreservesOfIsLimit (diagramMappingSource W)
    (freeBoundaryLeg 0).op (freeBoundaryLeg 1).op
      (BinaryCofan.IsColimit.op freeBoundaryIsColimit)
  change IsLimit (BinaryFan.mk
    (diagramMappingPrecomp (freeBoundaryLeg 0) W)
    (diagramMappingPrecomp (freeBoundaryLeg 1) W)) at h
  exact h

/-- The ordered target of boundary precomposition is the product of the
two actual free-zero mapping rows. -/
private def freeBoundaryMappingIso (W : Source) :
    diagramMappingSpace freeBoundary W ≅
      diagramMappingSpace (daggerSimplex 0) W ⨯
        diagramMappingSpace (daggerSimplex 0) W :=
  IsLimit.conePointUniqueUpToIso (freeBoundaryMappingIsLimit W)
    (limit.isLimit (pair _ _))

private theorem freeBoundaryMappingIso_fst (W : Source) :
    (freeBoundaryMappingIso W).hom ≫ prod.fst =
      diagramMappingPrecomp (freeBoundaryLeg 0) W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (freeBoundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.left⟩

private theorem freeBoundaryMappingIso_snd (W : Source) :
    (freeBoundaryMappingIso W).hom ≫ prod.snd =
      diagramMappingPrecomp (freeBoundaryLeg 1) W :=
  IsLimit.conePointUniqueUpToIso_hom_comp (freeBoundaryMappingIsLimit W)
    (limit.isLimit (pair _ _)) ⟨WalkingPair.right⟩

/-- The boundary legs followed by the inclusion are precisely the two
original cofaces, in zero--one order. -/
private theorem freeBoundaryLeg_inclusion (i : Fin 2) :
    freeBoundaryLeg i ≫ freeBoundaryInclusion =
      SegalRepresentables.freeSimplices.map (ordinaryEndpoint i) := by
  fin_cases i
  · change ReversalDiscreteFreeColimits.discreteFree.map SSet.boundary₁.ι₀ ≫
        ReversalDiscreteFreeColimits.discreteFree.map (SSet.boundary 1).ι =
      ReversalDiscreteFreeColimits.discreteFree.map
        (SSet.stdSimplex.map (ordinaryEndpoint 0))
    rw [← Functor.map_comp, SSet.boundary₁.ι₀_ι]
    rw [SSet.stdSimplex.δ_one]
    congr 1
  · change ReversalDiscreteFreeColimits.discreteFree.map SSet.boundary₁.ι₁ ≫
        ReversalDiscreteFreeColimits.discreteFree.map (SSet.boundary 1).ι =
      ReversalDiscreteFreeColimits.discreteFree.map
        (SSet.stdSimplex.map (ordinaryEndpoint 1))
    rw [← Functor.map_comp, SSet.boundary₁.ι₁_ι]
    rw [SSet.stdSimplex.δ_zero]
    congr 1

/-- The previously proved tensor--Yoneda equivalence assembles into the
literal mapping-space isomorphism, with evaluation at the representing identity. -/
private def explicitRepresentableMappingIso (W : Source)
    (c : ReverseSimplex) :
    diagramMappingSpace
        ((simplicialYoneda.{0, 0} ReverseSimplex).obj c) W ≅ W.obj (op c) :=
  NatIso.ofComponents
    (fun q ↦ ((representableTensorHomEquiv c
      (SSet.stdSimplex.obj q.unop) W).trans SSet.yonedaEquiv).toIso)
    (by
      intro q r g
      funext η
      have h := congrFun ((η.app (op c)).naturality g)
        (ULift.up (𝟙 c),
          SSet.stdSimplex.objEquiv.symm (𝟙 q.unop))
      simpa [diagramMappingSpace, diagramTensor,
        representableTensorHomEquiv, representableTensorHomTo,
        SSet.yonedaEquiv, SSet.stdSimplex.map_apply] using h)

/-- The explicit isomorphism evaluates a transformation at the identity
of the representing reversal object and the identity simplex. -/
private theorem explicitRepresentableMappingIso_apply (W : Source)
    (c : ReverseSimplex) (q : SimplexCategory)
    (η : (diagramMappingSpace
      ((simplicialYoneda.{0, 0} ReverseSimplex).obj c) W).obj (op q)) :
    ((explicitRepresentableMappingIso W c).hom.app
      (op q)) η =
      (η.app (op c)).app (op q)
        (ULift.up (𝟙 c),
          SSet.stdSimplex.objEquiv.symm (𝟙 q)) := by
  rfl

/-- Enriched Yoneda is natural in the original reversal representing
object; no discrete free-dagger comparison is involved in this step. -/
private theorem explicitRepresentableMappingIso_natural (W : Source)
    {c d : ReverseSimplex} (f : c ⟶ d) :
    diagramMappingPrecomp
        ((simplicialYoneda.{0, 0} ReverseSimplex).map f) W ≫
        (explicitRepresentableMappingIso W c).hom =
      (explicitRepresentableMappingIso W d).hom ≫
        W.map f.op := by
  apply NatTrans.ext
  funext q
  cases q with
  | op q =>
    funext η
    change ((explicitRepresentableMappingIso W c).hom.app
        (op q)) ((diagramMappingPrecomp
          ((simplicialYoneda.{0, 0} ReverseSimplex).map f) W).app
            (op q) η) =
      (W.map f.op).app (op q)
        (((explicitRepresentableMappingIso W d).hom.app
          (op q)) η)
    rw [explicitRepresentableMappingIso_apply W c q,
      explicitRepresentableMappingIso_apply W d q]
    have h := congrFun
      (NatTrans.congr_app (η.naturality f.op) (op q))
      (ULift.up (𝟙 d), SSet.stdSimplex.objEquiv.symm (𝟙 q))
    simpa only [diagramMappingPrecomp, diagramTensor,
      simplicialYoneda, FunctorToTypes.naturality] using h

/-- Naturality of the actual free-simplex mapping identification under an
ordinary outer simplex operator. The right-hand map is the original
reversal-indexed structure map of `W`. -/
private def explicitFreeSimplexMappingIso (W : Source) (n : ℕ) :
    diagramMappingSpace (daggerSimplex n) W ≅ W.obj (op (⟨n⟩ : ReverseSimplex)) :=
  ((diagramMappingSource W).mapIso
    (SegalRepresentables.freeSimplexRepresentable n).op).symm ≪≫
      explicitRepresentableMappingIso W ⟨n⟩

private theorem freeSimplexMappingIso_natural (W : Source)
    {m n : SimplexCategory} (f : m ⟶ n) :
    diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
        (explicitFreeSimplexMappingIso W m.len).hom =
      (explicitFreeSimplexMappingIso W n.len).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op := by
  let e := SegalRepresentables.freeSimplicesRepresentable.{0}
  have hnat := e.inv.naturality f
  have hpre :
      diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
        diagramMappingPrecomp (e.inv.app m) W =
      diagramMappingPrecomp (e.inv.app n) W ≫
        diagramMappingPrecomp
          ((ReverseSimplex.inclusion ⋙
            simplicialYoneda.{0, 0} ReverseSimplex).map f) W := by
    rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
    exact congrArg (fun z ↦ diagramMappingPrecomp z W) hnat.symm
  change diagramMappingPrecomp (SegalRepresentables.freeSimplices.map f) W ≫
      diagramMappingPrecomp (e.inv.app m) W ≫
        (explicitRepresentableMappingIso W (ReverseSimplex.inclusion.obj m)).hom =
    diagramMappingPrecomp (e.inv.app n) W ≫
      (explicitRepresentableMappingIso W (ReverseSimplex.inclusion.obj n)).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op
  rw [← Category.assoc, hpre]
  have hrep := explicitRepresentableMappingIso_natural W
    (ReverseSimplex.inclusion.map f)
  change diagramMappingPrecomp
      ((ReverseSimplex.inclusion ⋙
        simplicialYoneda.{0, 0} ReverseSimplex).map f) W ≫
        (explicitRepresentableMappingIso W
          (ReverseSimplex.inclusion.obj m)).hom =
      (explicitRepresentableMappingIso W
        (ReverseSimplex.inclusion.obj n)).hom ≫
        W.map (ReverseSimplex.inclusion.map f).op at hrep
  simpa only [Category.assoc] using congrArg
    (fun z ↦ diagramMappingPrecomp (e.inv.app n) W ≫ z) hrep

/-- The checked raw-row restriction is identity on every inner simplicial
degree, so it transports the actual reversal coface without changing it. -/
private theorem rowRestriction_endpoint (W : Source) (i : Fin 2) :
    (rowRestrictionIso W ⦋1⦌).inv ≫ endpoint W i =
      W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint i)).op ≫
        (rowRestrictionIso W ⦋0⦌).inv := by
  apply NatTrans.ext
  funext q x
  dsimp [rowRestrictionIso, endpoint, row,
    JTRealizationDiagonal.ordinaryCurry, JTReversalInput.ordinaryInput]
  simp

/-- The chosen free-simplex mapping isomorphism followed by the raw-row
restriction isomorphism. -/
private def freeSimplexRowIso (W : Source) (n : ℕ) :
    diagramMappingSpace (daggerSimplex n) W ≅ row W ⦋n⦌ :=
  explicitFreeSimplexMappingIso W n ≪≫ (rowRestrictionIso W ⦋n⦌).symm

/-- A product of the two actual free-simplex mapping isomorphisms. -/
private def endpointTargetIso (W : Source) :
    diagramMappingSpace freeBoundary W ≅ row W ⦋0⦌ ⨯ row W ⦋0⦌ :=
  freeBoundaryMappingIso W ≪≫
    prod.mapIso (freeSimplexRowIso W 0)
      (freeSimplexRowIso W 0)

/-- The boundary mapping fibration is the literal source endpoint arrow,
including the original order of its two cofaces. -/
private def endpointArrowIso (W : Source) :
    Arrow.mk (diagramMappingPrecomp freeBoundaryInclusion W) ≅
      Arrow.mk (endpointArrow W) :=
  Arrow.isoMk (freeSimplexRowIso W 1) (endpointTargetIso W) (by
    apply prod.hom_ext
    · change ((freeSimplexRowIso W 1).hom ≫ endpointArrow W) ≫ prod.fst =
        (diagramMappingPrecomp freeBoundaryInclusion W ≫
          (endpointTargetIso W).hom) ≫ prod.fst
      simp only [Category.assoc, endpointArrow, prod.lift_fst,
        endpointTargetIso, Iso.trans_hom, prod.mapIso_hom, prod.map_fst]
      rw [← Category.assoc (freeBoundaryMappingIso W).hom prod.fst
        (freeSimplexRowIso W 0).hom,
        freeBoundaryMappingIso_fst]
      rw [← Category.assoc (diagramMappingPrecomp freeBoundaryInclusion W)
        (diagramMappingPrecomp (freeBoundaryLeg 0) W)
        (freeSimplexRowIso W 0).hom,
        ← diagramMappingPrecomp_comp, freeBoundaryLeg_inclusion]
      change ((explicitFreeSimplexMappingIso W 1).hom ≫
          (rowRestrictionIso W ⦋1⦌).inv) ≫ endpoint W 0 =
        diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 0)) W ≫
          ((explicitFreeSimplexMappingIso W 0).hom ≫
            (rowRestrictionIso W ⦋0⦌).inv)
      have hn : diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 0)) W ≫
          (explicitFreeSimplexMappingIso W 0).hom =
        (explicitFreeSimplexMappingIso W 1).hom ≫
          W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 0)).op := by
        simpa only [SimplexCategory.len_mk] using
          (freeSimplexMappingIso_natural W (ordinaryEndpoint 0))
      calc
        ((explicitFreeSimplexMappingIso W 1).hom ≫
            (rowRestrictionIso W ⦋1⦌).inv) ≫ endpoint W 0 =
          (explicitFreeSimplexMappingIso W 1).hom ≫
            ((rowRestrictionIso W ⦋1⦌).inv ≫ endpoint W 0) :=
              Category.assoc _ _ _
        _ = (explicitFreeSimplexMappingIso W 1).hom ≫
            (W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 0)).op ≫
              (rowRestrictionIso W ⦋0⦌).inv) := by
                rw [rowRestriction_endpoint W 0]
        _ = ((explicitFreeSimplexMappingIso W 1).hom ≫
            W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 0)).op) ≫
              (rowRestrictionIso W ⦋0⦌).inv :=
                (Category.assoc _ _ _).symm
        _ = (diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 0)) W ≫
              (explicitFreeSimplexMappingIso W 0).hom) ≫
                (rowRestrictionIso W ⦋0⦌).inv := by rw [hn]
        _ = diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 0)) W ≫
              ((explicitFreeSimplexMappingIso W 0).hom ≫
                (rowRestrictionIso W ⦋0⦌).inv) := Category.assoc _ _ _
    · change ((freeSimplexRowIso W 1).hom ≫ endpointArrow W) ≫ prod.snd =
        (diagramMappingPrecomp freeBoundaryInclusion W ≫
          (endpointTargetIso W).hom) ≫ prod.snd
      simp only [Category.assoc, endpointArrow, prod.lift_snd,
        endpointTargetIso, Iso.trans_hom, prod.mapIso_hom, prod.map_snd]
      rw [← Category.assoc (freeBoundaryMappingIso W).hom prod.snd
        (freeSimplexRowIso W 0).hom,
        freeBoundaryMappingIso_snd]
      rw [← Category.assoc (diagramMappingPrecomp freeBoundaryInclusion W)
        (diagramMappingPrecomp (freeBoundaryLeg 1) W)
        (freeSimplexRowIso W 0).hom,
        ← diagramMappingPrecomp_comp, freeBoundaryLeg_inclusion]
      change ((explicitFreeSimplexMappingIso W 1).hom ≫
          (rowRestrictionIso W ⦋1⦌).inv) ≫ endpoint W 1 =
        diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 1)) W ≫
          ((explicitFreeSimplexMappingIso W 0).hom ≫
            (rowRestrictionIso W ⦋0⦌).inv)
      have hn : diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 1)) W ≫
          (explicitFreeSimplexMappingIso W 0).hom =
        (explicitFreeSimplexMappingIso W 1).hom ≫
          W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 1)).op := by
        simpa only [SimplexCategory.len_mk] using
          (freeSimplexMappingIso_natural W (ordinaryEndpoint 1))
      calc
        ((explicitFreeSimplexMappingIso W 1).hom ≫
            (rowRestrictionIso W ⦋1⦌).inv) ≫ endpoint W 1 =
          (explicitFreeSimplexMappingIso W 1).hom ≫
            ((rowRestrictionIso W ⦋1⦌).inv ≫ endpoint W 1) :=
              Category.assoc _ _ _
        _ = (explicitFreeSimplexMappingIso W 1).hom ≫
            (W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 1)).op ≫
              (rowRestrictionIso W ⦋0⦌).inv) := by
                rw [rowRestriction_endpoint W 1]
        _ = ((explicitFreeSimplexMappingIso W 1).hom ≫
            W.map (ReverseSimplex.inclusion.map (ordinaryEndpoint 1)).op) ≫
              (rowRestrictionIso W ⦋0⦌).inv :=
                (Category.assoc _ _ _).symm
        _ = (diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 1)) W ≫
              (explicitFreeSimplexMappingIso W 0).hom) ≫
                (rowRestrictionIso W ⦋0⦌).inv := by rw [hn]
        _ = diagramMappingPrecomp
            (SegalRepresentables.freeSimplices.map (ordinaryEndpoint 1)) W ≫
              ((explicitFreeSimplexMappingIso W 0).hom ≫
                (rowRestrictionIso W ⦋0⦌).inv) := Category.assoc _ _ _)

/-- Injective fibrancy gives the actual boundary-precomposition Kan
fibration, prior to the ordered representable calibration. -/
theorem boundaryPrecomp_fibration (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) :
    Fibration (diagramMappingPrecomp freeBoundaryInclusion W) := by
  letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsFibrant W := hW
  letI : Mono freeBoundaryInclusion := freeBoundaryInclusion_mono
  exact InjectiveKanDiagram.diagramMappingPrecomp_isFibration
    ReverseSimplexᵒᵖ freeBoundaryInclusion W

/-- The original ordered endpoint arrow of an injectively fibrant reversal
space is a Kan fibration. No Segal or ordinary-completeness premise is used. -/
theorem endpointArrow_fibration (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) : Fibration (endpointArrow W) := by
  have h : HomotopicalAlgebra.fibrations SSet.{0}
      (diagramMappingPrecomp freeBoundaryInclusion W) :=
    (fibration_iff _).mp (boundaryPrecomp_fibration W hW)
  exact (fibration_iff _).mpr
    (((HomotopicalAlgebra.fibrations SSet.{0}).arrow_mk_iso_iff
      (endpointArrowIso W)).mp h)

end

end DaggerModels.PartII.JTInjectiveOrderedEndpointFibration
