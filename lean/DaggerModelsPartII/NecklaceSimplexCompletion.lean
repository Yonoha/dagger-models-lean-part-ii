import DaggerModelsPartII.OrderedNecklaceLabelDiagram
import OriginalProductBeadConstantNat

/-!
# Native necklace ambient completion

The full endpoint-preserving necklace category admits an ambient one-bead completion.
Its unit and endpoint-edge legs act on the literal ambient simplex label weights,
including zero-length necklaces. No arbitrary weighted-bar or index-category
contractibility statement is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.ReversalDiscreteFreeColimits

namespace DaggerModels.PartII.OrderedNecklaceLabelDiagram

noncomputable section

private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode

/-- The native necklace maps to its one-bead ambient completion, including length zero. -/
def completionUnitComponent (T : NCode) : T ⟶ single T.len where
  map := T.inclusion ≫ (singleIso T.len).inv
  first := by
    change (singleIso T.len).inv.app _ (T.inclusion.app _ T.first) =
      (single T.len).first
    have h := congrFun
      (NatTrans.congr_app (singleIso T.len).hom_inv_id (op ⦋0⦌))
      (single T.len).first
    change (singleIso T.len).inv.app _
      ((singleIso T.len).hom.app _ (single T.len).first) =
        (single T.len).first at h
    rw [singleIso_first_eq_inclusion_first T] at h
    exact h
  last := by
    change (singleIso T.len).inv.app _ (T.inclusion.app _ T.last) =
      (single T.len).last
    have h := congrFun
      (NatTrans.congr_app (singleIso T.len).hom_inv_id (op ⦋0⦌))
      (single T.len).last
    change (singleIso T.len).inv.app _
      ((singleIso T.len).hom.app _ (single T.len).last) =
        (single T.len).last at h
    rw [singleIso_last_eq_inclusion_last T] at h
    exact h

/-- The ambient completion of every native endpoint-preserving necklace map. -/
def completionMap {T U : NCode} (f : T ⟶ U) : single T.len ⟶ single U.len where
  map := (singleIso T.len).hom ≫ ambientSimplex.map f ≫
    (singleIso U.len).inv
  first := by
    change (singleIso U.len).inv.app _
      ((ambientSimplex.map f).app _
        ((singleIso T.len).hom.app _ (single T.len).first)) =
          (single U.len).first
    rw [singleIso_first_eq_inclusion_first T]
    change (singleIso U.len).inv.app _
      ((ambientSimplexMap f.map).app _ (T.inclusion.app _ T.first)) = _
    rw [ambientSimplexMap_first f]
    exact (completionUnitComponent U).first
  last := by
    change (singleIso U.len).inv.app _
      ((ambientSimplex.map f).app _
        ((singleIso T.len).hom.app _ (single T.len).last)) =
          (single U.len).last
    rw [singleIso_last_eq_inclusion_last T]
    change (singleIso U.len).inv.app _
      ((ambientSimplexMap f.map).app _ (T.inclusion.app _ T.last)) = _
    rw [ambientSimplexMap_last f]
    exact (completionUnitComponent U).last

/-- The completion endofunctor on the full native necklace category. -/
def completion : NCode ⥤ NCode where
  obj T := single T.len
  map f := completionMap f
  map_id T := by
    apply NecklaceCode.Hom.ext
    change (singleIso T.len).hom ≫
      ambientSimplexMap (𝟙 (T.toSSet : SSet.{0})) ≫
        (singleIso T.len).inv = 𝟙 ((single T.len).toSSet : SSet.{0})
    rw [ambientSimplexMap_id]
    simp
  map_comp f g := by
    apply NecklaceCode.Hom.ext
    change (singleIso _).hom ≫ ambientSimplexMap (f.map ≫ g.map) ≫
        (singleIso _).inv =
      ((singleIso _).hom ≫ ambientSimplexMap f.map ≫ (singleIso _).inv) ≫
        ((singleIso _).hom ≫ ambientSimplexMap g.map ≫ (singleIso _).inv)
    rw [ambientSimplexMap_comp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The native inclusion is a natural transformation into completion. -/
def completionUnit : 𝟭 NCode ⟶ completion where
  app := completionUnitComponent
  naturality := by
    intro T U f
    apply NecklaceCode.Hom.ext
    change f.map ≫ (U.inclusion ≫ (singleIso U.len).inv) =
      (T.inclusion ≫ (singleIso T.len).inv) ≫
        ((singleIso T.len).hom ≫ ambientSimplexMap f.map ≫
          (singleIso U.len).inv)
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    conv_lhs => rw [← Category.assoc]
    rw [← ambientSimplexMap_fac]
    simp only [Category.assoc]

/-- The literal endpoint edge of each ambient simplex, including the degenerate edge at zero. -/
def completionEdgeComponent (T : NCode) : single 1 ⟶ single T.len where
  map := (singleIso 1).hom ≫ edgeToAmbient T ≫ (singleIso T.len).inv
  first := by
    change (singleIso T.len).inv.app _
      ((edgeToAmbient T).app _
        ((singleIso 1).hom.app _ (single 1).first)) =
          (single T.len).first
    rw [singleOne_first, edgeToAmbient_first]
    rw [← inclusion_first_std T]
    exact (completionUnitComponent T).first
  last := by
    change (singleIso T.len).inv.app _
      ((edgeToAmbient T).app _
        ((singleIso 1).hom.app _ (single 1).last)) =
          (single T.len).last
    rw [singleOne_last, edgeToAmbient_last]
    rw [← inclusion_last_std T]
    exact (completionUnitComponent T).last

/-- The endpoint edge is natural under every native necklace operator. -/
def completionEdge : (Functor.const NCode).obj (single 1) ⟶ completion where
  app := completionEdgeComponent
  naturality := by
    intro T U f
    apply NecklaceCode.Hom.ext
    change 𝟙 ((single 1).toSSet : SSet.{0}) ≫
      ((singleIso 1).hom ≫ edgeToAmbient U ≫ (singleIso U.len).inv) =
        ((singleIso 1).hom ≫ edgeToAmbient T ≫ (singleIso T.len).inv) ≫
          ((singleIso T.len).hom ≫ ambientSimplexMap f.map ≫
            (singleIso U.len).inv)
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← edgeToAmbient_naturality f]
    simp only [Category.assoc]

/-- Under ambient completion the unit acts as the literal identity simplex map. -/
theorem ambientSimplex_map_completionUnit (T : NCode) :
    ambientSimplex.map (completionUnitComponent T) =
      𝟙 (Δ[T.len] : SSet.{0}) := by
  change ambientSimplexMap (completionUnitComponent T).map = _
  apply (ambientSimplexMap_unique (completionUnitComponent T).map (𝟙 _) ?_).symm
  change T.inclusion ≫ 𝟙 _ =
    (T.inclusion ≫ (singleIso T.len).inv) ≫ (single T.len).inclusion
  rw [← singleIso_hom T.len]
  simp only [Category.comp_id, Category.assoc, Iso.inv_hom_id]

/-- Under ambient completion the edge is the literal endpoint edge of the simplex. -/
theorem ambientSimplex_map_completionEdge (T : NCode) :
    ambientSimplex.map (completionEdgeComponent T) = edgeToAmbient T := by
  change ambientSimplexMap (completionEdgeComponent T).map = _
  apply (ambientSimplexMap_unique (completionEdgeComponent T).map
    (edgeToAmbient T) ?_).symm
  change (single 1).inclusion ≫ edgeToAmbient T =
    ((singleIso 1).hom ≫ edgeToAmbient T ≫ (singleIso T.len).inv) ≫
      (single T.len).inclusion
  rw [← singleIso_hom 1, ← singleIso_hom T.len]
  calc
    (singleIso 1).hom ≫ edgeToAmbient T =
        ((singleIso 1).hom ≫ edgeToAmbient T) ≫
          ((singleIso T.len).inv ≫ (singleIso T.len).hom) := by simp
    _ = ((singleIso 1).hom ≫ edgeToAmbient T ≫
          (singleIso T.len).inv) ≫ (singleIso T.len).hom := by
      simp only [Category.assoc]

/-- In the opposite direction the unit acts identically on ambient simplex labels. -/
theorem simplexLabels_map_completionUnit
    (W : ReverseDaggerSpace.{0}) (T : NCode) :
    (simplexLabels W).map (completionUnitComponent T).op =
      𝟙 ((simplexLabels W).obj (op T)) := by
  change diagramMappingPrecomp
    (discreteFree.{0}.map (ambientSimplex.map (completionUnitComponent T))) W = _
  rw [ambientSimplex_map_completionUnit T]
  have hmap : discreteFree.{0}.map (𝟙 (Δ[T.len] : SSet.{0})) =
      𝟙 (discreteFree.{0}.obj (Δ[T.len] : SSet.{0})) :=
    (discreteFree.{0}).map_id _
  rw [hmap]
  exact diagramMappingPrecomp_id _ W

/-- The other opposite leg acts by the literal endpoint edge on labels. -/
theorem simplexLabels_map_completionEdge
    (W : ReverseDaggerSpace.{0}) (T : NCode) :
    (simplexLabels W).map (completionEdgeComponent T).op =
      diagramMappingPrecomp (discreteFree.{0}.map (edgeToAmbient T)) W := by
  change diagramMappingPrecomp
    (discreteFree.{0}.map (ambientSimplex.map (completionEdgeComponent T))) W = _
  rw [ambientSimplex_map_completionEdge T]

end
end DaggerModels.PartII.OrderedNecklaceLabelDiagram
