import OrdinaryWalkingPrecompletionExchange
import OrdinaryCoherentPrecompletionResolution
import OrdinarySegalCotensorPointEvaluation
import OrdinarySegalCotensorSimplexCalibration
import OrdinarySegalVerticalPrecompletionNaturality
import OrdinarySegalMappingTargetSquares

/-!
# The selected endpoint of the walking precompletion exchange

The selected endpoint is vertex zero of the original `E[1]`. The comparison
is first stated on the entire outer parameter diagram, then diagonally.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial HomotopicalAlgebra MonoidalCategory MonoidalClosed
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryWalkingPrecompletionExchangeEndpoint

open OrdinaryCSSLocalization (Space)
open OrdinaryWalkingPrecompletionExchange
open OrdinaryCoherentPrecompletionResolution
open OrdinarySegalCotensorParameterNaturality (mappingIso_natural_parameter)

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev E₁ : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev zero : J := op ⦋0⦌
private abbrev v₀ : (Δ[0] : SSet.{0}) ⟶ E₁ :=
  JTParameterContraction.parameterVertex ⦋1⦌ 0

private abbrev discrete := OrdinaryCSSLocalization.discrete
private abbrev cotensor := OrdinarySegalHorizontalCotensor.cotensor
private abbrev F := OrdinarySegalCotensorMappingIso.mappingIso
private abbrev Z := OrdinarySegalCotensorZeroIso.mappingIso

private theorem level_pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (q : J) (t : (diagramMappingSpace (discrete.obj L) W).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPrecomp (discrete.map f) W).app q t) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv L W q.unop) t := by
  have h := congrFun
    (NatTrans.congr_app (OrdinaryDiscreteMapping.mappingIso_natural f W) q) t
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem fubini_level (K A : SSet.{0}) (W : Space)
    (q : J) (t : (diagramMappingSpace (discrete.obj A) (cotensor K W)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
        ((F K A W).hom.app q t) =
      uncurry ((OrdinaryDiscreteMapping.levelEquiv A (cotensor K W) q.unop) t ≫
        (OrdinarySegalCotensorMappingIso.rowIso K W q).hom) := by
  change (OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop)
      ((OrdinaryDiscreteMapping.levelEquiv (K ⊗ A) W q.unop).symm
        (uncurry ((OrdinaryDiscreteMapping.levelEquiv A (cotensor K W) q.unop) t ≫
          (OrdinarySegalCotensorMappingIso.rowIso K W q).hom))) = _
  exact Equiv.apply_symm_apply _ _

/-- The degree-zero representable isomorphism and strict Fubini have the
same actual right-unitor boundary. -/
private theorem rightUnitFubini (K : SSet.{0}) (W : Space) :
    (OrdinarySegalWalkingEvaluation.simplexMappingIso (cotensor K W) 0).hom ≫
        (Z K W).hom =
      (F K (Δ[0] : SSet.{0}) W).hom ≫
        diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W := by
  rw [OrdinarySegalCotensorSimplexCalibration.mappingIso_simplex_hom K W 0]
  rw [OrdinarySegalCotensorZeroIso.mappingIso_hom]

/-- Strict Fubini at the point parameter is the actual left-unitor map
after evaluating the point cotensor. -/
private theorem leftUnitFubini (K : SSet.{0}) (W : Space) :
    (F (Δ[0] : SSet.{0}) K W).inv ≫
        diagramMappingPostcomp (discrete.obj K)
          (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom =
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W := by
  have h : diagramMappingPostcomp (discrete.obj K)
        (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom =
      (F (Δ[0] : SSet.{0}) K W).hom ≫
        diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W := by
    apply NatTrans.ext
    funext q t
    apply (OrdinaryDiscreteMapping.levelEquiv K W q.unop).injective
    change (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPostcomp (discrete.obj K)
          (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom).app q t) =
      (OrdinaryDiscreteMapping.levelEquiv K W q.unop)
        ((diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W).app q
          ((F (Δ[0] : SSet.{0}) K W).hom.app q t))
    rw [level_pre, fubini_level]
    let g := (OrdinaryDiscreteMapping.levelEquiv K
      (cotensor (Δ[0] : SSet.{0}) W) q.unop) t
    change g ≫
        ((flipFunctor J J (Type 0)).map
          (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom).app q =
      (SSet.stdSimplex.leftUnitor K).inv ≫
        uncurry (g ≫
          (OrdinarySegalCotensorMappingIso.rowIso
            (Δ[0] : SSet.{0}) W q).hom)
    apply NatTrans.ext
    funext m x
    rfl
  calc
    (F (Δ[0] : SSet.{0}) K W).inv ≫
        diagramMappingPostcomp (discrete.obj K)
          (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom =
      (F (Δ[0] : SSet.{0}) K W).inv ≫
        ((F (Δ[0] : SSet.{0}) K W).hom ≫
          diagramMappingPrecomp
            (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W) := by rw [h]
    _ = diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W := by
          simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Degree-zero cotensor Fubini is natural in the whole target map. -/
private theorem zeroIso_post (K : SSet.{0}) {U V : Space} (g : U ⟶ V) :
    (OrdinarySegalHorizontalCotensor.post K g).app zero ≫ (Z K V).hom =
      (Z K U).hom ≫ diagramMappingPostcomp (discrete.obj K) g := by
  rw [OrdinarySegalCotensorZeroIso.mappingIso_hom,
    OrdinarySegalCotensorZeroIso.mappingIso_hom]
  exact (OrdinarySegalMappingTargetSquares.pre_post
    (discrete.map (SSet.stdSimplex.rightUnitor K).inv) g).symm

/-- The selected vertex commutes with braiding and the two actual
standard-simplex unitors. -/
private theorem selectedVertexTensor (K : SSet.{0}) :
    (SSet.stdSimplex.leftUnitor K).inv ≫
        (v₀ ▷ K) ≫ (β_ E₁ K).hom =
      (SSet.stdSimplex.rightUnitor K).inv ≫ (K ◁ v₀) := by
  apply NatTrans.ext
  funext q x
  rfl

private theorem postcomp_comp (A : Space) {U V X : Space}
    (f : U ⟶ V) (g : V ⟶ X) :
    diagramMappingPostcomp A (f ≫ g) =
      diagramMappingPostcomp A f ≫ diagramMappingPostcomp A g := by
  change (diagramMappingTarget A).map (f ≫ g) =
    (diagramMappingTarget A).map f ≫ (diagramMappingTarget A).map g
  exact (diagramMappingTarget A).map_comp f g

/-- The literal chosen evaluation of the walking horizontal parameter. -/
def selectedEvaluation (W : Space) :
    OrdinarySegalHorizontalCotensor.cotensor E₁ W ⟶ W :=
  OrdinarySegalCotensorPointEvaluation.evaluation E₁ W v₀

/-- Postcompose every original outer resolution stage with the same
selected evaluation, then retain horizontal degree zero. -/
def iteratedEvaluationResolution (W : Space) :
    iteratedZeroResolution W ⟶
      OrdinarySegalResolutionMappingFibers.rowResolution W 0 :=
  Functor.whiskerRight
    (OrdinarySegalVerticalPrecompletionNaturality.resolutionPost
      (selectedEvaluation W))
    ((evaluation J SSet.{0}).obj zero)

/-- The exact selected endpoint square on the original outer diagram. -/
theorem outer_endpoint_square (W : Space) :
    evaluationResolution W ≫ endpointResolution W =
      (outerExchangeIso W).hom ≫ iteratedEvaluationResolution W := by
  apply NatTrans.ext
  funext q
  have he := OrdinaryCoherentCompletenessCriterion.evaluation_endpoint
    ((OrdinarySegalPrecompletion.resolution W).obj q)
  change
      (OrdinarySegalCoherentArrowImage.coherentEvaluation
        ((OrdinarySegalPrecompletion.resolution W).obj q) ≫
        OrdinaryCoherentCompletenessCriterion.endpoint
          ((OrdinarySegalPrecompletion.resolution W).obj q)) =
      (outerExchangeIso W).hom.app q ≫
        ((OrdinarySegalVerticalPrecompletionNaturality.resolutionPost
          (selectedEvaluation W)).app q).app zero
  rw [he]
  let K : SSet.{0} := GroupoidSimplex.parameter.obj q.unop
  let R := cotensor K W
  let A := discrete.obj K
  let F₀ := F K (Δ[0] : SSet.{0}) W
  let F₁ := F K E₁ W
  let G₀ := F (Δ[0] : SSet.{0}) K W
  let G₁ := F E₁ K W
  let B := OrdinarySegalCotensorRowSwitch.braidMappingIso K E₁ W
  let ZW := Z K W
  let ZB := Z K (cotensor E₁ W)
  let p := diagramMappingPrecomp (discrete.map v₀) R
  let s := (OrdinarySegalWalkingEvaluation.simplexMappingIso R 0).hom
  let j := (OrdinarySegalHorizontalCotensor.post K (selectedEvaluation W)).app zero
  have hsource : (p ≫ s) ≫ ZW.hom =
      F₁.hom ≫
        diagramMappingPrecomp (discrete.map (K ◁ v₀)) W ≫
          diagramMappingPrecomp
            (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W := by
    dsimp only [p, s, ZW, F₀, F₁]
    rw [Category.assoc, rightUnitFubini K W, ← Category.assoc,
      OrdinarySegalCotensorMappingIso.mappingIso_natural_source K v₀ W]
    simp only [Category.assoc]
  have hpost : j ≫ ZW.hom =
      ZB.hom ≫ diagramMappingPostcomp A (selectedEvaluation W) := by
    dsimp only [j, ZW, ZB, A]
    exact zeroIso_post K (selectedEvaluation W)
  have hfubini : G₁.inv ≫
      diagramMappingPostcomp A
        (OrdinarySegalHorizontalCotensor.pre v₀ W) =
      diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫ G₀.inv := by
    apply (cancel_mono G₀.hom).mp
    calc
      (G₁.inv ≫ diagramMappingPostcomp A
          (OrdinarySegalHorizontalCotensor.pre v₀ W)) ≫ G₀.hom =
        G₁.inv ≫ (G₁.hom ≫
          diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W) := by
            rw [Category.assoc]
            exact congrArg (fun t ↦ G₁.inv ≫ t)
              (mappingIso_natural_parameter v₀ K W)
      _ = diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W := by
          dsimp only [G₁]
          simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      _ = (diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫
          G₀.inv) ≫ G₀.hom := by
            dsimp only [G₀]
            simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hevaluation : G₁.inv ≫
      diagramMappingPostcomp A (selectedEvaluation W) =
      diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫
        diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W := by
    change G₁.inv ≫ diagramMappingPostcomp A
        (OrdinarySegalHorizontalCotensor.pre v₀ W ≫
          (OrdinarySegalHorizontalCotensorPoint.pointIso W).hom) = _
    rw [postcomp_comp, ← Category.assoc, hfubini, Category.assoc]
    exact congrArg
      (fun t ↦ diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫ t)
      (leftUnitFubini K W)
  have hbraid : B.hom ≫
      diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫
        diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W =
      diagramMappingPrecomp (discrete.map (K ◁ v₀)) W ≫
        diagramMappingPrecomp
          (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W := by
    dsimp only [B]
    change diagramMappingPrecomp (discrete.map (β_ E₁ K).hom) W ≫
        diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫
          diagramMappingPrecomp
            (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W = _
    simp only [← Category.assoc]
    rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
      ← discrete.map_comp, ← discrete.map_comp,
      ← diagramMappingPrecomp_comp, ← discrete.map_comp]
    exact congrArg (fun t ↦ diagramMappingPrecomp (discrete.map t) W)
      (selectedVertexTensor K)
  have hexchange : (outerExchangeIso W).hom.app q =
      F₁.hom ≫ B.hom ≫ G₁.inv ≫ ZB.inv := rfl
  have htarget : ((outerExchangeIso W).hom.app q ≫ j) ≫ ZW.hom =
      F₁.hom ≫ B.hom ≫ G₁.inv ≫
        diagramMappingPostcomp A (selectedEvaluation W) := by
    rw [hexchange]
    simp only [Category.assoc]
    rw [hpost]
    dsimp only [ZB]
    simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono ZW.hom).mp
  change (p ≫ s) ≫ ZW.hom =
    ((outerExchangeIso W).hom.app q ≫ j) ≫ ZW.hom
  calc
    (p ≫ s) ≫ ZW.hom =
        F₁.hom ≫
          diagramMappingPrecomp (discrete.map (K ◁ v₀)) W ≫
            diagramMappingPrecomp
              (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W := hsource
    _ = F₁.hom ≫ B.hom ≫
          diagramMappingPrecomp (discrete.map (v₀ ▷ K)) W ≫
            diagramMappingPrecomp
              (discrete.map (SSet.stdSimplex.leftUnitor K).inv) W := by
            simpa only [Category.assoc] using congrArg (fun t ↦ F₁.hom ≫ t)
              hbraid.symm
    _ = F₁.hom ≫ B.hom ≫ G₁.inv ≫
          diagramMappingPostcomp A (selectedEvaluation W) := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ F₁.hom ≫ B.hom ≫ t) hevaluation.symm
    _ = ((outerExchangeIso W).hom.app q ≫ j) ≫ ZW.hom := htarget.symm

/-- The diagonal endpoint square retains the literal row-zero action of
the corrected precompletion functor. -/
theorem diagonal_endpoint_square (W : Space) :
    diagonalFunctor.map (evaluationResolution W) ≫ diagonalEndpoint W =
      (diagonalExchangeIso W).hom ≫
        (OrdinarySegalVerticalPrecompletionNaturality.precompletionMap
          (selectedEvaluation W)).app zero := by
  have h := congrArg (fun f ↦ diagonalFunctor.map f) (outer_endpoint_square W)
  simpa only [Functor.map_comp, diagonalEndpoint, diagonalExchangeIso,
    OrdinarySegalVerticalPrecompletionNaturality.precompletionMap]
    using h

#print axioms outer_endpoint_square
#print axioms diagonal_endpoint_square

end

end DaggerModels.PartII.OrdinaryWalkingPrecompletionExchangeEndpoint
