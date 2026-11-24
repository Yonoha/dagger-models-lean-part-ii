import DaggerModelsPartII.TwoBeadSegalLocality
import DaggerModelsPartII.DiagramMappingSpace
import ChosenNecklaceMapInclusion
import NativeSSetFibrationsOverBaseWeakPullbacks
import Mathlib.CategoryTheory.LiftingProperties.Limits
import NativeSimplicialReplacementWeightsChange
import NativeFamilyWeak
import OriginalProductBeadExtension

/-!
# Ordered native necklace label diagrams

The functors and natural transformation retain every endpoint-preserving native
necklace operator, including collapsed beads. Ordered labels are literal
point-set pullbacks over one given boundary point. Under the original injective
Segal fibrancy assumption, restriction is a Kan trivial fibration in each code,
and its full simplicial-replacement map is weak on the diagonal.

This compares two ordered label bars. It does not identify either bar with the
actual JT flag bar or prove weakness of the chosen `gTilde` fiber map. In
particular, the strict pullback for a zero-length necklace is not asserted to
compute a derived fiber.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.TwoBeadSegalLocality
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode

/-- Complete each native necklace to its ambient simplex on all native maps. -/
def ambientSimplex : NCode ⥤ SSet.{0} where
  obj T := Δ[T.len]
  map f := DaggerOriginalProductGadget.ambientSimplexMap f.map
  map_id T := DaggerOriginalProductGadget.ambientSimplexMap_id T
  map_comp f g :=
    DaggerOriginalProductGadget.ambientSimplexMap_comp f.map g.map

/-- The original inclusion is natural for collapsed beads as well as refinements. -/
def inclusionNatural : simplicialFunctor.{0} ⟶ ambientSimplex where
  app T := T.inclusion
  naturality {_ _} f := map_inclusion f.map

/-- The common ordered pair of endpoint objects. -/
def boundary : Source := F.obj Δ[0] ⨿ F.obj Δ[0]

/-- The first and last vertex of the native necklace as an ordered boundary map. -/
def boundaryNecklace (T : NCode) : boundary ⟶ F.obj T.toSSet :=
  coprod.desc (F.map (SSet.yonedaEquiv.symm T.first))
    (F.map (SSet.yonedaEquiv.symm T.last))

/-- The first and last vertex of the ambient simplex. -/
def boundarySimplex (T : NCode) : boundary ⟶ F.obj (Δ[T.len] : SSet.{0}) :=
  boundaryNecklace T ≫ F.map T.inclusion

/-- All necklace operators preserve the common ordered boundary. -/
theorem boundaryNecklace_natural {T U : NCode} (f : T ⟶ U) :
    boundaryNecklace T ≫ F.map f.map = boundaryNecklace U := by
  apply coprod.hom_ext
  · simp only [boundaryNecklace, coprod.inl_desc_assoc, coprod.inl_desc]
    rw [← F.map_comp]
    congr 1
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using f.first
  · simp only [boundaryNecklace, coprod.inr_desc_assoc, coprod.inr_desc]
    rw [← F.map_comp]
    congr 1
    apply SSet.yonedaEquiv.injective
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using f.last

/-- Restriction of ambient simplex labels to native necklace labels. -/
def restriction (W : Source) (T : NCode) :
    diagramMappingSpace (F.obj (ambientSimplex.obj T)) W ⟶
      diagramMappingSpace (F.obj (simplicialFunctor.{0}.obj T)) W :=
  diagramMappingPrecomp (F.map (inclusionNatural.app T)) W

/-- All strict native necklace labels, with every native operator acting by precomposition. -/
def necklaceLabels (W : Source) : NCodeᵒᵖ ⥤ SSet.{0} where
  obj T := diagramMappingSpace (F.obj T.unop.toSSet) W
  map {T U} f := diagramMappingPrecomp (F.map f.unop.map) W
  map_id T := by
    change diagramMappingPrecomp (F.map (𝟙 T.unop.toSSet)) W = _
    calc
      diagramMappingPrecomp (F.map (𝟙 T.unop.toSSet)) W =
          diagramMappingPrecomp (𝟙 (F.obj T.unop.toSSet)) W :=
        congrArg (fun h => diagramMappingPrecomp h W) (F.map_id _)
      _ = 𝟙 _ := diagramMappingPrecomp_id _ W
  map_comp {T U V} f g := by
    change diagramMappingPrecomp (F.map ((f ≫ g).unop.map)) W = _
    rw [unop_comp]
    change diagramMappingPrecomp (F.map (g.unop.map ≫ f.unop.map)) W = _
    rw [Functor.map_comp, diagramMappingPrecomp_comp]

/-- All ambient simplex labels, under the same native necklace operators. -/
def simplexLabels (W : Source) : NCodeᵒᵖ ⥤ SSet.{0} where
  obj T := diagramMappingSpace (F.obj (ambientSimplex.obj T.unop)) W
  map {T U} f := diagramMappingPrecomp (F.map (ambientSimplex.map f.unop)) W
  map_id T := by
    change diagramMappingPrecomp (F.map (ambientSimplex.map (𝟙 T.unop))) W = _
    calc
      diagramMappingPrecomp (F.map (ambientSimplex.map (𝟙 T.unop))) W =
          diagramMappingPrecomp (F.map (𝟙 (ambientSimplex.obj T.unop))) W :=
        congrArg (fun h => diagramMappingPrecomp (F.map h) W)
          (ambientSimplex.map_id _)
      _ = diagramMappingPrecomp (𝟙 (F.obj (ambientSimplex.obj T.unop))) W :=
        congrArg (fun h => diagramMappingPrecomp h W) (F.map_id _)
      _ = 𝟙 _ := diagramMappingPrecomp_id _ W
  map_comp {T U V} f g := by
    change diagramMappingPrecomp (F.map (ambientSimplex.map ((f ≫ g).unop))) W = _
    rw [unop_comp, Functor.map_comp, Functor.map_comp,
      diagramMappingPrecomp_comp]

/-- The fixed-code restrictions assemble on the entire native opposite category. -/
def restrictionNatural (W : Source) : simplexLabels W ⟶ necklaceLabels W where
  app T := restriction W T.unop
  naturality {T U} f := by
    change diagramMappingPrecomp (F.map (ambientSimplex.map f.unop)) W ≫
      diagramMappingPrecomp (F.map U.unop.inclusion) W =
        diagramMappingPrecomp (F.map T.unop.inclusion) W ≫
          diagramMappingPrecomp (F.map f.unop.map) W
    rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp]
    have h := congrArg (fun q => F.map q) (inclusionNatural.naturality f.unop)
    simp only [Functor.map_comp] at h
    change F.map f.unop.map ≫ F.map T.unop.inclusion =
      F.map U.unop.inclusion ≫ F.map (ambientSimplex.map f.unop) at h
    exact congrArg (fun q => diagramMappingPrecomp q W) h.symm
 
/-- The common mapping space for the ordered pair of boundary vertices. -/
def boundaryLabels (W : Source) : SSet.{0} := diagramMappingSpace boundary W

/-- Every native necklace label restricts to the same ordered boundary. -/
def necklaceBoundaryRestriction (W : Source) :
    necklaceLabels W ⟶ (Functor.const NCodeᵒᵖ).obj (boundaryLabels W) where
  app T := diagramMappingPrecomp (boundaryNecklace T.unop) W
  naturality {T U} f := by
    change diagramMappingPrecomp (F.map f.unop.map) W ≫
      diagramMappingPrecomp (boundaryNecklace U.unop) W =
        diagramMappingPrecomp (boundaryNecklace T.unop) W ≫ 𝟙 _
    rw [Category.comp_id, ← diagramMappingPrecomp_comp]
    exact congrArg (fun h => diagramMappingPrecomp h W)
      (boundaryNecklace_natural f.unop)

/-- Every ambient simplex label restricts to the same ordered boundary. -/
def simplexBoundaryRestriction (W : Source) :
    simplexLabels W ⟶ (Functor.const NCodeᵒᵖ).obj (boundaryLabels W) where
  app T := diagramMappingPrecomp (boundarySimplex T.unop) W
  naturality {T U} f := by
    change diagramMappingPrecomp (F.map (ambientSimplex.map f.unop)) W ≫
      diagramMappingPrecomp (boundarySimplex U.unop) W =
        diagramMappingPrecomp (boundarySimplex T.unop) W ≫ 𝟙 _
    rw [Category.comp_id, ← diagramMappingPrecomp_comp]
    exact congrArg (fun h => diagramMappingPrecomp h W)
      (by
        calc
          boundarySimplex U.unop ≫ F.map (ambientSimplex.map f.unop) =
              boundaryNecklace U.unop ≫ F.map
                (U.unop.inclusion ≫ ambientSimplex.map f.unop) := by
                  simp only [boundarySimplex, Functor.map_comp, Category.assoc]
          _ = boundaryNecklace U.unop ≫ F.map
                (f.unop.map ≫ T.unop.inclusion) := by
                  have hh := (inclusionNatural.naturality f.unop).symm
                  change U.unop.inclusion ≫ ambientSimplex.map f.unop =
                    f.unop.map ≫ T.unop.inclusion at hh
                  exact congrArg (fun h => boundaryNecklace U.unop ≫ F.map h) hh
          _ = boundarySimplex T.unop := by
                  rw [Functor.map_comp, ← Category.assoc,
                    boundaryNecklace_natural]
                  rfl)

/-- Boundary restriction commutes with the full necklace-to-simplex comparison. -/
theorem restriction_boundary (W : Source) (T : NCode) :
    restriction W T ≫ diagramMappingPrecomp (boundaryNecklace T) W =
      diagramMappingPrecomp (boundarySimplex T) W := by
  change diagramMappingPrecomp (F.map T.inclusion) W ≫
    diagramMappingPrecomp (boundaryNecklace T) W = _
  rw [← diagramMappingPrecomp_comp]
  rfl

/-- Point-set ordered fibers of a label diagram over a specified common boundary point. -/
def orderedLabelDiagram (B : SSet.{0})
    (L : NCodeᵒᵖ ⥤ SSet.{0})
    (r : L ⟶ (Functor.const NCodeᵒᵖ).obj B)
    (b : (Δ[0] : SSet.{0}) ⟶ B) : NCodeᵒᵖ ⥤ SSet.{0} where
  obj T := pullback (r.app T) b
  map {T U} f :=
    pullback.map (r.app T) b (r.app U) b
      (L.map f) (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using (r.naturality f).symm)
      (by simp)
  map_id T := by
    apply pullback.hom_ext
    · simp
    · simp
  map_comp {T U V} f g := by
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc]

/-- Native ordered necklace labels at an actual, explicitly given boundary point. -/
def orderedNecklaceLabels (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) : NCodeᵒᵖ ⥤ SSet.{0} :=
  orderedLabelDiagram (boundaryLabels W) (necklaceLabels W)
    (necklaceBoundaryRestriction W) b

/-- Ordered ambient simplex labels at the same boundary point. -/
def orderedSimplexLabels (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) : NCodeᵒᵖ ⥤ SSet.{0} :=
  orderedLabelDiagram (boundaryLabels W) (simplexLabels W)
    (simplexBoundaryRestriction W) b

/-- Restrict ordered simplex labels to native necklace labels at one fixed boundary point. -/
def orderedRestriction (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    orderedSimplexLabels W b ⟶ orderedNecklaceLabels W b where
  app T :=
    pullback.map ((simplexBoundaryRestriction W).app T) b
      ((necklaceBoundaryRestriction W).app T) b
      ((restrictionNatural W).app T) (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using
        (restriction_boundary W T.unop).symm)
      (by simp)
  naturality {T U} f := by
    apply pullback.hom_ext
    · simp [orderedSimplexLabels, orderedNecklaceLabels, orderedLabelDiagram,
        Category.assoc, (restrictionNatural W).naturality f]
    · simp [orderedSimplexLabels, orderedNecklaceLabels, orderedLabelDiagram,
        Category.assoc]

/-- The ordered restriction is the literal base change of the fixed-code restriction. -/
theorem orderedRestriction_isPullback (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (T : NCode) :
    IsPullback ((orderedRestriction W b).app (op T))
      (pullback.fst ((simplexBoundaryRestriction W).app (op T)) b)
      (pullback.fst ((necklaceBoundaryRestriction W).app (op T)) b)
      (restriction W T) := by
  let p := (simplexBoundaryRestriction W).app (op T)
  let q := (necklaceBoundaryRestriction W).app (op T)
  let f := restriction W T
  have h : f ≫ q = p := restriction_boundary W T
  have heq : ((orderedRestriction W b).app (op T)) =
      DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver p q f h b := by
    apply pullback.hom_ext
    · simp [orderedRestriction, restrictionNatural, orderedSimplexLabels,
        orderedNecklaceLabels, orderedLabelDiagram,
        DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver,
        p, q, f]
    · simp [orderedRestriction, restrictionNatural, orderedSimplexLabels,
        orderedNecklaceLabels, orderedLabelDiagram,
        DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver,
        p, q, f]
  rw [heq]
  exact DaggerNativeSSetFibrationsOverBaseWeakPullbacks.mapOver_isPullback p q f h b

/-- Every ordered component remains a Kan trivial fibration by actual base change. -/
theorem orderedRestriction_trivialFibration (W : Source)
    (hW : @IsFibrant Source _ injectiveSegalModel.categoryWithFibrations _ W)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (T : NCode) :
    trivialFibrations SSet.{0} ((orderedRestriction W b).app (op T)) := by
  letI : (trivialFibrations SSet.{0}).IsStableUnderBaseChange := by
    rw [← rlp_eq_of_wfs (cofibrations SSet.{0}) (trivialFibrations SSet.{0})]
    infer_instance
  exact (trivialFibrations SSet.{0}).of_isPullback
    (orderedRestriction_isPullback W b T).flip
    (necklace_mapping_trivialFibration T W hW)

/-- The full simplicial-replacement map on the ordered label diagrams. -/
def orderedBarMap (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    DaggerBisimplicialDiagonal.diag
        (DaggerNativeSimplicialReplacement.replacement (orderedSimplexLabels W b)) ⟶
      DaggerBisimplicialDiagonal.diag
        (DaggerNativeSimplicialReplacement.replacement (orderedNecklaceLabels W b)) :=
  DaggerNativeSimplicialReplacementWeightsChange.diagonalChange
    (orderedRestriction W b)

/-- A row of the weighted change is the exact family of component restrictions. -/
theorem orderedChange_row (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W)
    (q : SimplexCategoryᵒᵖ) :
    (DaggerNativeSimplicialReplacementWeightsChange.changeWeights
      (orderedRestriction W b)).app q =
        DaggerNativeFamilyWeak.familyMap
          (fun c : (nerve NCodeᵒᵖ).obj q =>
            (orderedRestriction W b).app
              (DaggerNativeSimplicialReplacementCells.first c)) := by
  ext k x
  rfl

/-- Entire ordered label bars compare weakly across every native operator. -/
theorem orderedBarMap_weak (W : Source)
    (hW : @IsFibrant Source _ injectiveSegalModel.categoryWithFibrations _ W)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    DaggerSSetGluing.GW (orderedBarMap W b) := by
  apply DaggerOriginalDiagonalGeometric.diagMap_geometric_row
  intro q
  rw [orderedChange_row]
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  apply DaggerNativeFamilyWeak.familyMap_weak
  intro c
  exact ((mem_trivialFibrations_iff _).1
    (orderedRestriction_trivialFibration W hW b
      (DaggerNativeSimplicialReplacementCells.first c).unop)).2

end
end DaggerModels.PartII.OrderedNecklaceLabelDiagram
