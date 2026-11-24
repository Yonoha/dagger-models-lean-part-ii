import OrdinarySegalSpineTwoPullback
import OrdinarySegalWalkingEvaluation
import DaggerModelsPartII.DiagramMappingLimits

/-!
# Degree-two spine with standard edge and vertex objects

The already checked spine-part pullback is transported across the three
geometric part isomorphisms. This places its legs on the actual mapping
spaces from `Δ[1]` and `Δ[0]`. The leg maps here are defined by this
transport; their calibration to the two literal coface maps is the next
incidence calculation required for Rezk's displayed unit squares.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinarySegalUnitSquares

open OrdinaryCSSLocalization OrdinarySegalSpineTwoPullback SpineOuterFacePushout

noncomputable section

private abbrev mapSpace (K : SSet.{0}) (W : Space) :=
  diagramMappingSpace (discrete.obj K) W

/-- Contravariant mapping-space transport along an actual simplicial-set iso. -/
def mapSpaceIso {K L : SSet.{0}} (e : K ≅ L) (W : Space) :
    mapSpace K W ≅ mapSpace L W :=
  ((diagramMappingSource W).mapIso (discrete.mapIso e).op).symm

def firstEdgeIso (W : Space) :
    mapSpace (firstSpinePart 0 : SSet.{0}) W ≅ mapSpace (Δ[1] : SSet.{0}) W :=
  mapSpaceIso firstPartIso W

def lastEdgeIso (W : Space) :
    mapSpace (lastSpinePart 0 : SSet.{0}) W ≅ mapSpace (Δ[1] : SSet.{0}) W :=
  mapSpaceIso lastPartIso W

def commonVertexIso (W : Space) :
    mapSpace (middleSpinePart 0 : SSet.{0}) W ≅ mapSpace (Δ[0] : SSet.{0}) W :=
  mapSpaceIso middlePartIso W

/-- The first edge's shared-vertex restriction, with its standard source
and target objects and the actual geometric incidence by transport. -/
def firstVertex (W : Space) :
    mapSpace (Δ[1] : SSet.{0}) W ⟶ mapSpace (Δ[0] : SSet.{0}) W :=
  (firstEdgeIso W).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.Subcomplex.homOfLE
        (inf_le_left : middleSpinePart.{0} 0 ≤ firstSpinePart 0))) W ≫
      (commonVertexIso W).hom

/-- The second edge's shared-vertex restriction under the other incidence. -/
def lastVertex (W : Space) :
    mapSpace (Δ[1] : SSet.{0}) W ⟶ mapSpace (Δ[0] : SSet.{0}) W :=
  (lastEdgeIso W).inv ≫
    diagramMappingPrecomp
      (discrete.map (SSet.Subcomplex.homOfLE
        (inf_le_right : middleSpinePart.{0} 0 ≤ lastSpinePart 0))) W ≫
      (commonVertexIso W).hom

private def partsToEdges (W : Space) :
    pullback
        (diagramMappingPrecomp
          (discrete.map (SSet.Subcomplex.homOfLE
            (inf_le_left : middleSpinePart.{0} 0 ≤ firstSpinePart 0))) W)
        (diagramMappingPrecomp
          (discrete.map (SSet.Subcomplex.homOfLE
            (inf_le_right : middleSpinePart.{0} 0 ≤ lastSpinePart 0))) W) ⟶
      pullback (firstVertex W) (lastVertex W) :=
  pullback.map _ _ _ _
    (firstEdgeIso W).hom (lastEdgeIso W).hom (commonVertexIso W).hom
    (by simp only [firstVertex, Iso.hom_inv_id_assoc])
    (by simp only [lastVertex, Iso.hom_inv_id_assoc])

private theorem partsToEdges_isIso (W : Space) : IsIso (partsToEdges W) := by
  dsimp only [partsToEdges]
  infer_instance

/-- The degree-two spine mapping space is the pullback of two standard
edge mapping spaces over a standard vertex mapping space. -/
def spineTwoEdgesIso (W : Space) :
    mapSpace (DaggerNativeStandardSpineInner.spine 2 : SSet.{0}) W ≅
      pullback (firstVertex W) (lastVertex W) := by
  letI : IsIso (partsToEdges W) := partsToEdges_isIso W
  exact mappingPartsIso W ≪≫ asIso (partsToEdges W)

theorem spineTwoEdgesIso_first (W : Space) :
    (spineTwoEdgesIso W).hom ≫ pullback.fst (firstVertex W) (lastVertex W) =
      diagramMappingPrecomp
          (discrete.map (SSet.Subcomplex.homOfLE
            (inf_le_left : firstSpinePart.{0} 0 ≤
              DaggerNativeStandardSpineInner.spine 2))) W ≫
        (firstEdgeIso W).hom := by
  simp only [spineTwoEdgesIso, Iso.trans_hom, asIso_hom, partsToEdges,
    Category.assoc, pullback.map, pullback.lift_fst]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ (firstEdgeIso W).hom) (mappingPartsIso_first W)

theorem spineTwoEdgesIso_last (W : Space) :
    (spineTwoEdgesIso W).hom ≫ pullback.snd (firstVertex W) (lastVertex W) =
      diagramMappingPrecomp
          (discrete.map (SSet.Subcomplex.homOfLE
            (inf_le_left : lastSpinePart.{0} 0 ≤
              DaggerNativeStandardSpineInner.spine 2))) W ≫
        (lastEdgeIso W).hom := by
  simp only [spineTwoEdgesIso, Iso.trans_hom, asIso_hom, partsToEdges,
    Category.assoc, pullback.map, pullback.lift_snd]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ (lastEdgeIso W).hom) (mappingPartsIso_last W)

#print axioms mapSpaceIso
#print axioms spineTwoEdgesIso
#print axioms spineTwoEdgesIso_first
#print axioms spineTwoEdgesIso_last

end

end DaggerModels.PartII.OrdinarySegalUnitSquares
