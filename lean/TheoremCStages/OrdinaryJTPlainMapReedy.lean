import OrdinaryJTRightNerveReedy
import OrdinaryJTMappingCornerComparison
import DaggerModelsPartII.ReedyCoefficientChange

/-!
# Relative Reedy fibrations of ordinary JT mapping rows

For an original Joyal fibration of targets, the induced map of entire
ordinary JT mapping-row diagrams is a Reedy fibration in the native Kan
model. The matching corner is the literal mapping corner for the boundary
inclusion. The comparison uses `StandardSimplexFrame.matchingBoundaryIso`,
`ReedyCoefficientChange.matchingObjectIso`, and the checked
`OrdinaryJTMappingCornerComparison.corner_fibration`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryJTPlainMapReedy

open OrdinaryJTMappingFunctor OrdinaryJTMappingFrameWeak
open OrdinaryJTMappingCornerFibration OrdinaryJTRightNerveReedy

noncomputable section

private def ordinaryJoyalModel : ModelCategory SSet.{0} :=
  DaggerActualDCHRightInducedAndMainTheoremD.ordinaryJoyalModel.{0}

/-- Postcomposition in the original Joyal target, natural in the horizontal
coefficient. -/
def mappingPostNat {X Y : SSet.{0}} (p : X ⟶ Y) :
    mappingFunctor X ⟶ mappingFunctor Y where
  app A := mappingPost p A.unop
  naturality A B f := by
    apply NatTrans.ext
    funext k z
    rfl

/-- The map of the full ordinary JT right-nerve Hom-row diagrams. -/
def plainMap {X Y : SSet.{0}} (p : X ⟶ Y) : plainSpace X ⟶ plainSpace Y :=
  Functor.whiskerLeft SSet.stdSimplex.{0}.op (mappingPostNat p)

/-- The literal degree component of the postcomposition map. -/
theorem plainMap_app {X Y : SSet.{0}} (p : X ⟶ Y) (n : ℕ) :
    (plainMap p).app (op ⦋n⦌) = mappingPost p (SSet.stdSimplex.obj ⦋n⦌) := rfl

/-- Naturality of the coefficient-change matching comparison in the
coefficient functor itself. -/
private theorem matchingObjectIso_coeff_naturality
    {C D : Type*} [Category C] [Category D]
    [HasLimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} D]
    (F G : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F]
    [PreservesLimitsOfSize.{0, 0} G] (η : F ⟶ G)
    (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    η.app ((matchingFunctor n).obj W) ≫
        (ReedyCoefficientChange.matchingObjectIso G n W).hom =
      (ReedyCoefficientChange.matchingObjectIso F n W).hom ≫
        (matchingFunctor n).map (Functor.whiskerLeft W η) := by
  apply limit.hom_ext
  intro s
  let πC := limit.π (matchingProjection n ⋙ W) s
  let πF := limit.π ((matchingProjection n ⋙ W) ⋙ F) s
  let πG := limit.π ((matchingProjection n ⋙ W) ⋙ G) s
  have hF :
      (ReedyCoefficientChange.matchingObjectIso F n W).hom ≫ πF = F.map πC :=
    preservesLimitIso_hom_π F (matchingProjection n ⋙ W) s
  have hG :
      (ReedyCoefficientChange.matchingObjectIso G n W).hom ≫ πG = G.map πC :=
    preservesLimitIso_hom_π G (matchingProjection n ⋙ W) s
  have hM :
      (matchingFunctor n).map (Functor.whiskerLeft W η) ≫ πG =
        πF ≫ η.app ((matchingProjection n ⋙ W).obj s) :=
    limMap_π (Functor.whiskerLeft (matchingProjection n) (Functor.whiskerLeft W η)) s
  calc
    (η.app ((matchingFunctor n).obj W) ≫
        (ReedyCoefficientChange.matchingObjectIso G n W).hom) ≫ πG =
      η.app ((matchingFunctor n).obj W) ≫ G.map πC := by
        rw [Category.assoc, hG]
    _ = F.map πC ≫ η.app ((matchingProjection n ⋙ W).obj s) :=
      (η.naturality πC).symm
    _ = ((ReedyCoefficientChange.matchingObjectIso F n W).hom ≫
        (matchingFunctor n).map (Functor.whiskerLeft W η)) ≫ πG := by
      rw [Category.assoc, hM, ← Category.assoc, hF]

/-- The matching object of the mapped standard-simplex diagram is exactly
the ordinary JT mapping row on the original simplex boundary. -/
def matchingBoundaryMappingIso (X : SSet.{0}) (n : ℕ) :
    (matchingFunctor n).obj (plainSpace X) ≅
      mapping X (SSet.boundary n).toSSet :=
  (ReedyCoefficientChange.matchingObjectIso
      (mappingFunctor X) n SSet.stdSimplex.{0}.op).symm ≪≫
    (mappingFunctor X).mapIso (matchingBoundaryIso.{0} n)

/-- The boundary matching isomorphism commutes with target
postcomposition. -/
theorem matchingBoundaryMappingIso_naturality {X Y : SSet.{0}}
    (p : X ⟶ Y) (n : ℕ) :
    (matchingFunctor n).map (plainMap p) ≫
        (matchingBoundaryMappingIso Y n).hom =
      (matchingBoundaryMappingIso X n).hom ≫
        mappingPost p (SSet.boundary n).toSSet := by
  let eX := ReedyCoefficientChange.matchingObjectIso
    (mappingFunctor X) n SSet.stdSimplex.{0}.op
  let eY := ReedyCoefficientChange.matchingObjectIso
    (mappingFunctor Y) n SSet.stdSimplex.{0}.op
  let b := matchingBoundaryIso.{0} n
  have h := matchingObjectIso_coeff_naturality
    (mappingFunctor X) (mappingFunctor Y) (mappingPostNat p)
    n SSet.stdSimplex.{0}.op
  have h' : (matchingFunctor n).map (plainMap p) ≫ eY.inv =
      eX.inv ≫ (mappingPostNat p).app
        ((matchingFunctor n).obj SSet.stdSimplex.{0}.op) := by
    change (matchingFunctor n).map
        (Functor.whiskerLeft SSet.stdSimplex.{0}.op (mappingPostNat p)) ≫ eY.inv =
      eX.inv ≫ (mappingPostNat p).app
        ((matchingFunctor n).obj SSet.stdSimplex.{0}.op)
    apply (cancel_mono eY.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change (matchingFunctor n).map (plainMap p) ≫
      (eY.inv ≫ (mappingFunctor Y).map b.hom) =
    (eX.inv ≫ (mappingFunctor X).map b.hom) ≫
      (mappingPostNat p).app (op (SSet.boundary n).toSSet)
  rw [← Category.assoc, h', Category.assoc]
  exact congrArg (fun t ↦ eX.inv ≫ t)
    ((mappingPostNat p).naturality b.hom).symm

/-- Under the boundary matching isomorphism, the matching comparison is
literal restriction along the original boundary inclusion. -/
theorem matchingBoundaryMappingIso_comp (X : SSet.{0}) (n : ℕ) :
    (matchingComparison n).app (plainSpace X) ≫
        (matchingBoundaryMappingIso X n).hom =
      restriction X (SSet.boundary n).ι := by
  let F := mappingFunctor X
  let e := ReedyCoefficientChange.matchingObjectIso F n SSet.stdSimplex.{0}.op
  let b := matchingBoundaryIso.{0} n
  have h := ReedyCoefficientChange.matchingComparison_map F n SSet.stdSimplex.{0}.op
  have h' : (matchingComparison n).app (plainSpace X) ≫ e.inv =
      F.map ((matchingComparison n).app SSet.stdSimplex.{0}.op) := by
    change (matchingComparison n).app (SSet.stdSimplex.{0}.op ⋙ F) ≫ e.inv =
      F.map ((matchingComparison n).app SSet.stdSimplex.{0}.op)
    rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  change (matchingComparison n).app (plainSpace X) ≫
      (e.inv ≫ F.map b.hom) = F.map (SSet.boundary n).ι.op
  rw [← Category.assoc, h', ← F.map_comp, matchingBoundaryIso_comp]

/-- The relative matching target is the literal ordinary JT mapping
corner target, including the original pullback and boundary inclusion. -/
def relativeMatchingTargetIso {X Y : SSet.{0}} (p : X ⟶ Y) (n : ℕ) :
    pullback ((matchingFunctor n).map (plainMap p))
        ((matchingComparison n).app (plainSpace Y)) ≅
      pullback (restriction Y (SSet.boundary n).ι)
        (mappingPost p (SSet.boundary n).toSSet) :=
  pullbackSymmetry ((matchingFunctor n).map (plainMap p))
      ((matchingComparison n).app (plainSpace Y)) ≪≫
    asIso (pullback.map _ _ _ _
      (𝟙 _) (matchingBoundaryMappingIso X n).hom
      (matchingBoundaryMappingIso Y n).hom
      (matchingBoundaryMappingIso_comp Y n)
      (matchingBoundaryMappingIso_naturality p n))

/-- The full relative matching arrow of the ordinary JT right nerve is
isomorphic to the checked literal two-variable mapping corner. -/
def relativeMatchingCornerIso {X Y : SSet.{0}}
    (p : X ⟶ Y) (n : ℕ) :
    Arrow.mk (relativeMatchingMap n (plainMap p)) ≅
      Arrow.mk (corner p (SSet.boundary n).ι) := by
  refine Arrow.isoMk (Iso.refl _) (relativeMatchingTargetIso p n) ?_
  apply pullback.hom_ext
  · simpa [relativeMatchingTargetIso, relativeMatchingMap, corner, pullback.map]
      using (plainMap_app p n).symm
  · simpa [relativeMatchingTargetIso, relativeMatchingMap, corner, pullback.map]
      using (matchingBoundaryMappingIso_comp X n).symm

/-- A fibration in the original Joyal model induces a native Kan Reedy
fibration of the entire ordinary JT right-nerve Hom-row map. -/
theorem plainMap_relativeReedyFibration {X Y : SSet.{0}} (p : X ⟶ Y)
    (hp : ordinaryJoyalModel.categoryWithFibrations.fibrations p) :
    reedyMatchingProperty (fibrations SSet.{0}) (plainMap p) := by
  intro n
  haveI : Mono (SSet.boundary n).ι := inferInstance
  exact ((fibrations SSet.{0}).arrow_mk_iso_iff
    (relativeMatchingCornerIso p n)).mpr
      ((fibration_iff _).mp
        (OrdinaryJTMappingCornerComparison.corner_fibration p hp
          (SSet.boundary n).ι))

#print axioms mappingPostNat
#print axioms matchingBoundaryMappingIso_comp
#print axioms relativeMatchingCornerIso
#print axioms plainMap_relativeReedyFibration

end
end DaggerModels.PartII.OrdinaryJTPlainMapReedy
