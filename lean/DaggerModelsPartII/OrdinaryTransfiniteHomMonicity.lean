import OriginalOrdinaryHomTransfiniteReconciled
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# Transfinite closure of ordinary local Hom monomorphisms

The original ordinary moving-endpoint Hom diagram and its actual final
colimit cocone furnish a transfinite composition of the exact Hom map.
Successor Hom monomorphisms remain monic after both endpoint casts.
-/

set_option autoImplicit false

open CategoryTheory Limits MorphismProperty DaggerModels OriginalOrdinaryMovingHomColimits

universe u

namespace DaggerModels.OriginalOrdinaryHomTransfinite

noncomputable section

variable {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
variable {X Y : SimplicialCat.{u, u}} {f : X ⟶ Y}
variable (h : CategoryTheory.TransfiniteCompositionOfShape J f)
variable (hmono : ∀ j, ¬IsMax j →
  OriginalOrdinaryHomRetracts.localHomProperty
    (monomorphisms SSet.{u}) (h.F.map (homOfLE (Order.le_succ j))))

include hmono in
/-- The original successor Hom map is monic after both endpoint transports. -/
theorem successor_hom_mono (x y : X.Obj) (j : J) (hj : ¬IsMax j) :
    Mono ((homDiagram h x y).map (homOfLE (Order.le_succ j))) := by
  change Mono (castMap (h.F.map (homOfLE (Order.le_succ j)))
    (movingObj h x j) (movingObj h y j)
    (movingObj h x (Order.succ j)) (movingObj h y (Order.succ j))
    (moving_naturality h x (homOfLE (Order.le_succ j)))
    (moving_naturality h y (homOfLE (Order.le_succ j))))
  dsimp [castMap, OriginalOrdinaryEndpointTransport.transport]
  letI : Mono ((h.F.map (homOfLE (Order.le_succ j))).map
    (movingObj h x j) (movingObj h y j)) :=
    hmono j hj (movingObj h x j) (movingObj h y j)
  exact mono_comp _ _

/-- The Hom map of the full original arrow has the literal simplicial-set
transfinite record obtained from the existing moving-Hom cocone. -/
def homMonoTransfinite (x y : X.Obj) :
    (monomorphisms SSet.{u}).TransfiniteCompositionOfShape J (f.map x y) where
  F := homDiagram h x y
  isoBot := isoBot h x y
  isWellOrderContinuous := homWellOrderContinuous h x y
  incl := (homCocone h x y).ι
  isColimit := finalIsColimit h x y
  fac := hom_fac h x y
  map_mem := successor_hom_mono h hmono x y

include h hmono in
/-- Every original Hom map of the full transfinite arrow is monic. -/
theorem localHomMono_of_transfinite :
    OriginalOrdinaryHomRetracts.localHomProperty (monomorphisms SSet.{u}) f :=
  fun x y ↦ (monomorphisms SSet.{u}).transfiniteCompositionsOfShape_le J
    (f.map x y) (homMonoTransfinite h hmono x y).mem

end

/-- The original ordinary local Hom monomorphism class is closed under each
common-universe transfinite shape. -/
instance localHomMono_transfiniteOfShape (J : Type u)
    [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    MorphismProperty.IsStableUnderTransfiniteCompositionOfShape
      (OriginalOrdinaryHomRetracts.localHomProperty (monomorphisms SSet.{u})) J where
  le _ _ _ hf := localHomMono_of_transfinite
    hf.some.toTransfiniteCompositionOfShape hf.some.map_mem

/-- The original ordinary local Hom monomorphism class is transfinite-stable
at the common universe. -/
instance localHomMono_transfinite :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      (OriginalOrdinaryHomRetracts.localHomProperty (monomorphisms SSet.{u})) where
  isStableUnderTransfiniteCompositionOfShape _ _ _ _ _ := inferInstance

/-- All common-universe transfinite composites of ordinary local Hom
monomorphisms remain in the same original local Hom class. -/
theorem transfiniteCompositions_le_localHomMono :
    MorphismProperty.transfiniteCompositions.{u}
      (OriginalOrdinaryHomRetracts.localHomProperty (monomorphisms SSet.{u})) ≤
        OriginalOrdinaryHomRetracts.localHomProperty (monomorphisms SSet.{u}) :=
  MorphismProperty.transfiniteCompositions_le _

end DaggerModels.OriginalOrdinaryHomTransfinite
