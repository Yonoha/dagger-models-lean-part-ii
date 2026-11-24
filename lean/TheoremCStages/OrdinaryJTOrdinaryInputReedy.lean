import OrdinaryJTOrdinaryInputSegal
import OrdinaryDiscreteMapping
import OrdinarySpaceReedyInjective
import DaggerModelsPartII.ReedyCoefficientChange
import DaggerModelsPartII.StandardSimplexFrame
import DaggerModelsPartII.ReedyFibrantDiagrams
import DaggerModelsPartII.DiagramMappingPrecompFibration
import NativeBisimplicialHorizontalMapping

/-!
# Reedy fibrancy of the literal ordinary JT input

The ordinary discrete-source mapping functor preserves limits. Its
standard-simplex diagram is the original ordinary input. Consequently
the Reedy matching comparison is the mapped boundary inclusion, which
the checked free-restriction comparison carries to the same reversal
diagram W.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
  HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTOrdinaryInputReedy

noncomputable section

private abbrev Space := OrdinaryCSSLocalization.Space
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev discrete := OrdinaryCSSLocalization.discrete
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}
private abbrev input (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj
    (JTReversalInput.ordinaryInput.obj W)

private instance : PreservesColimitsOfSize.{0, 0} discrete := by
  letI : PreservesColimitsOfSize.{0, 0}
      (SimplicialObject.const (Type 0)) :=
    CategoryTheory.Limits.preservesColimits_const
      (D := SimplexCategoryᵒᵖ)
  change PreservesColimitsOfSize.{0, 0}
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ
      (Type 0) SSet.{0}).obj (SimplicialObject.const (Type 0)))
  infer_instance

private instance : PreservesLimitsOfSize.{0, 0} discrete.op :=
  preservesLimitsOfSize_op discrete

private instance (X : Space) :
    PreservesLimitsOfSize.{0, 0} (diagramMappingSource X) :=
  ⟨fun {J} _ ↦ by
    letI : HasColimitsOfShape Jᵒᵖ SSet.{0} := inferInstance
    exact diagramMappingSource_preservesLimitsOfShape J X⟩

/-- Contravariant mapping out of an ordinary vertically discrete
horizontal simplicial set. -/
def mappingFunctor (X : Space) : SSet.{0}ᵒᵖ ⥤ SSet.{0} :=
  discrete.op ⋙ diagramMappingSource X

private instance (X : Space) :
    PreservesLimitsOfSize.{0, 0} (mappingFunctor X) := by
  dsimp [mappingFunctor]
  infer_instance

/-- The native horizontal Yoneda comparison respects every ordinary
simplex operator. -/
private theorem horizontalSimplex_natural (X : Space)
    {m n : SimplexCategory} (f : m ⟶ n) :
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre
        (SSet.stdSimplex.map f) X ≫
        (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso
          X m.len).hom =
      (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso
          X n.len).hom ≫ X.map f.op := by
  apply NatTrans.ext
  funext q g
  change SSet.yonedaEquiv (SSet.stdSimplex.map f ≫ g) =
    (X.flip.obj q).map f.op (SSet.yonedaEquiv g)
  exact SSet.yonedaEquiv_map_comp f g

/-- The standard-simplex mapping diagram is the literal ordinary
simplicial space. -/
def standardMappingIso (X : Space) :
    SSet.stdSimplex.{0}.op ⋙ mappingFunctor X ≅ X := by
  refine NatIso.ofComponents
    (fun q ↦
      OrdinaryDiscreteMapping.mappingIso
        (SSet.stdSimplex.obj q.unop) X ≪≫
      DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso
        X q.unop.len) ?_
  intro m n f
  let u := SSet.stdSimplex.map f.unop
  let a (q : SimplexCategoryᵒᵖ) :=
    OrdinaryDiscreteMapping.mappingIso
      (SSet.stdSimplex.obj q.unop) X
  let b (q : SimplexCategoryᵒᵖ) :=
    DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso
      X q.unop.len
  have h₁ := OrdinaryDiscreteMapping.mappingIso_natural u X
  have h₂ := horizontalSimplex_natural X f.unop
  change diagramMappingPrecomp (discrete.map u) X ≫
      (a n).hom ≫ (b n).hom =
    (a m).hom ≫ (b m).hom ≫ X.map f
  change diagramMappingPrecomp (discrete.map u) X ≫ (a n).hom =
    (a m).hom ≫
      DaggerNativeBisimplicialHorizontalMapping.horizontalPre u X at h₁
  change
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre u X ≫
        (b n).hom =
      (b m).hom ≫ X.map f at h₂
  calc
    diagramMappingPrecomp (discrete.map u) X ≫
        (a n).hom ≫ (b n).hom =
      ((a m).hom ≫
        DaggerNativeBisimplicialHorizontalMapping.horizontalPre u X) ≫
          (b n).hom := by
            simpa only [Category.assoc] using
              congrArg (fun z ↦ z ≫ (b n).hom) h₁
    _ = (a m).hom ≫
        (DaggerNativeBisimplicialHorizontalMapping.horizontalPre u X ≫
          (b n).hom) := Category.assoc _ _ _
    _ = (a m).hom ≫ ((b m).hom ≫ X.map f) := by rw [h₂]
    _ = (a m).hom ≫ (b m).hom ≫ X.map f := by
      rw [← Category.assoc]

/-- The matching object is mapping out of the literal standard
boundary after ordinary vertical discretization. -/
def boundaryMappingIso (X : Space) (n : ℕ) :
    (matchingFunctor n).obj X ≅
      diagramMappingSpace (discrete.obj (SSet.boundary n).toSSet) X :=
  (matchingFunctor n).mapIso (standardMappingIso X).symm ≪≫
    (ReedyCoefficientChange.matchingObjectIso
      (mappingFunctor X) n SSet.stdSimplex.{0}.op).symm ≪≫
    (mappingFunctor X).mapIso (matchingBoundaryIso.{0} n)

/-- The matching comparison is the ordinary discrete boundary
restriction after the standard-simplex mapping identification. -/
theorem boundaryMappingIso_comp (X : Space) (n : ℕ) :
    (matchingComparison n).app X ≫ (boundaryMappingIso X n).hom =
      (standardMappingIso X).inv.app (op ⦋n⦌) ≫
        diagramMappingPrecomp (discrete.map (SSet.boundary n).ι) X := by
  let M := mappingFunctor X
  let e := standardMappingIso X
  let c := ReedyCoefficientChange.matchingObjectIso
    M n SSet.stdSimplex.{0}.op
  let b := matchingBoundaryIso.{0} n
  have hnat := (matchingComparison n).naturality e.inv
  have hcomp := ReedyCoefficientChange.matchingComparison_map
    M n SSet.stdSimplex.{0}.op
  change (matchingComparison n).app X ≫
      (((matchingFunctor n).mapIso e.symm).hom ≫
        c.inv ≫ M.map b.hom) =
    e.inv.app (op ⦋n⦌) ≫ M.map (SSet.boundary n).ι.op
  have h₁ : (matchingComparison n).app X ≫
        (matchingFunctor n).map e.inv =
      e.inv.app (op ⦋n⦌) ≫
        (matchingComparison n).app
          (SSet.stdSimplex.{0}.op ⋙ M) := hnat.symm
  have h₂ : (matchingComparison n).app
        (SSet.stdSimplex.{0}.op ⋙ M) ≫ c.inv =
      M.map ((matchingComparison n).app SSet.stdSimplex.{0}.op) := by
    rw [← hcomp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  calc
    (matchingComparison n).app X ≫
        (((matchingFunctor n).mapIso e.symm).hom ≫
          c.inv ≫ M.map b.hom) =
      ((matchingComparison n).app X ≫
        (matchingFunctor n).map e.inv) ≫ c.inv ≫ M.map b.hom := by
          rfl
    _ = (e.inv.app (op ⦋n⦌) ≫
        (matchingComparison n).app
          (SSet.stdSimplex.{0}.op ⋙ M)) ≫ c.inv ≫ M.map b.hom := by
            rw [h₁]
    _ = e.inv.app (op ⦋n⦌) ≫
        ((matchingComparison n).app
          (SSet.stdSimplex.{0}.op ⋙ M) ≫ c.inv) ≫ M.map b.hom := by
            simp only [Category.assoc]
    _ = e.inv.app (op ⦋n⦌) ≫
        M.map ((matchingComparison n).app SSet.stdSimplex.{0}.op) ≫
          M.map b.hom := by rw [h₂]
    _ = e.inv.app (op ⦋n⦌) ≫
        M.map ((matchingComparison n).app SSet.stdSimplex.{0}.op ≫
          b.hom) := by rw [← M.map_comp]
    _ = e.inv.app (op ⦋n⦌) ≫ M.map (SSet.boundary n).ι.op := by
      rw [matchingBoundaryIso_comp]

/-- The ordinary matching arrow is isomorphic to literal ordinary
discrete-source boundary restriction. -/
def ordinaryBoundaryArrowIso (X : Space) (n : ℕ) :
    Arrow.mk ((matchingComparison n).app X) ≅
      Arrow.mk (diagramMappingPrecomp
        (discrete.map (SSet.boundary n).ι) X) :=
  Arrow.isoMk ((standardMappingIso X).symm.app (op ⦋n⦌))
    (boundaryMappingIso X n) (boundaryMappingIso_comp X n).symm

/-- The same matching arrow is isomorphic to precomposition by the
original free dagger boundary inclusion into the same reversal W. -/
def freeBoundaryArrowIso (W : Source) (n : ℕ) :
    Arrow.mk ((matchingComparison n).app (input W)) ≅
      Arrow.mk (diagramMappingPrecomp
        (free.map (SSet.boundary n).ι) W) :=
  ordinaryBoundaryArrowIso (input W) n ≪≫
    Arrow.isoMk
      (OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso
        (Δ[n] : SSet.{0}) W)
      (OrdinaryFreeRestrictionEnriched.freeDiscreteMappingIso
        (SSet.boundary n).toSSet W)
      (OrdinaryFreeRestrictionCalibration.freeDiscreteMappingIso_natural
        (SSet.boundary n).ι W).symm

/-- Injective fibrancy of the original reversal diagram gives every
ordinary Reedy matching comparison as a Kan fibration. -/
theorem ordinaryInput_matching_fibration (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) (n : ℕ) :
    fibrations SSet.{0} ((matchingComparison n).app (input W)) := by
  letI : ModelCategory Source :=
    InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI : IsFibrant W := hW
  letI : Mono (SSet.boundary n).ι := inferInstance
  letI : Mono (free.map (SSet.boundary n).ι) :=
    ReversalDiscreteFreeColimits.map_mono (SSet.boundary n).ι
  have hf : fibrations SSet.{0}
      (diagramMappingPrecomp (free.map (SSet.boundary n).ι) W) :=
    (fibration_iff _).mp
      (InjectiveKanDiagram.diagramMappingPrecomp_isFibration
        ReverseSimplexᵒᵖ (free.map (SSet.boundary n).ι) W)
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff
    (freeBoundaryArrowIso W n)).mpr hf

/-- The literal ordinary input is fibrant in the Kan Reedy model. -/
theorem ordinaryInput_reedyFibrant (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) :
    @IsFibrant Space _
      OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations _
      (input W) := by
  letI : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel
  exact (reedyFibrant_iff_matchingComparison (input W)).mpr
    (ordinaryInput_matching_fibration W hW)

/-- The literal ordinary input is also fibrant in the ordinary injective
Kan diagram model used by the actual CSS localization. -/
theorem ordinaryInput_injectiveFibrant (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ;
      IsFibrant W) :
    @IsFibrant Space _
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations _
      (input W) := by
  have hR := ordinaryInput_reedyFibrant W hW
  letI : ModelCategory Space := OrdinarySpaceReedyInjective.reedyModel
  have hf :
      OrdinarySpaceReedyInjective.reedyModel.categoryWithFibrations.fibrations
        (terminal.from (input W)) :=
    (fibration_iff _).mp hR
  have hi :
      OrdinarySpaceReedyInjective.injectiveModel.categoryWithFibrations.fibrations
        (terminal.from (input W)) := by
    rw [← OrdinarySpaceReedyInjective.fibrations_eq]
    exact hf
  letI : ModelCategory Space := OrdinarySpaceReedyInjective.injectiveModel
  exact (fibration_iff _).mpr hi

#print axioms standardMappingIso
#print axioms boundaryMappingIso
#print axioms ordinaryBoundaryArrowIso
#print axioms freeBoundaryArrowIso
#print axioms ordinaryInput_reedyFibrant
#print axioms ordinaryInput_injectiveFibrant

end

end DaggerModels.PartII.OrdinaryJTOrdinaryInputReedy
