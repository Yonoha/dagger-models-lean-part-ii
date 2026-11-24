import DaggerModelsPartII.JTSupportedPathZeroTransport

/-!
# Reindexed transport of a complete endpoint inverse image

Reuse search: `JTSupportedPathZeroTransport.lift/lift_fst/lift_snd`
construct the natural map of full pullbacks after reindexing;
`JTEndpointReducedCover.descend/descend_cylinder` descend a compatible
cylinder and fixed-boundary cocone through the canonical reduced pushout.
The old pushout identity is `pushout.condition`.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits DaggerModels

namespace DaggerModels.PartII.JTReindexedEndpointCoverTransport

noncomputable section

variable {I J : Type} [SmallCategory I] [SmallCategory J]
variable (G : J ⥤ I) {B : SSet.{0}}
variable {oldA oldX oldY : I ⥤ SSet.{0}}
variable (oldπ : oldY ⟶ oldX) (d : oldA ⟶ oldX)
variable (e : oldA ⟶ (Functor.const I).obj B)
variable {newA newX newY : J ⥤ SSet.{0}}
variable (newπ : newY ⟶ newX) (d' : newA ⟶ newX)
variable (e' : newA ⟶ (Functor.const J).obj B)
variable (n : newX ⟶ G ⋙ oldX) (η : newY ⟶ G ⋙ oldY)
variable (a : newA ⟶ G ⋙ oldA)
variable (hπ : η ≫ Functor.whiskerLeft G oldπ = newπ ≫ n)
variable (hd : d' ≫ n = a ≫ Functor.whiskerLeft G d)
variable (he : ∀ p : J, a.app p ≫ e.app (G.obj p) = e'.app p)

private abbrev newCovered := pullback newπ d'
private abbrev oldCovered := pullback oldπ d
private abbrev newU := pullback.fst newπ d'
private abbrev newV := pullback.snd newπ d'
private abbrev oldU := pullback.fst oldπ d
private abbrev oldV := pullback.snd oldπ d

include n η a hπ hd
private theorem boundary_map_square :
    (newU newπ d' ≫ η) ≫ Functor.whiskerLeft G oldπ =
      (newV newπ d' ≫ a) ≫ Functor.whiskerLeft G d := by
  calc
    _ = (newU newπ d' ≫ newπ) ≫ n := by
      rw [Category.assoc, hπ, ← Category.assoc]
    _ = (newV newπ d' ≫ d') ≫ n :=
      congrArg (· ≫ n) (pullback.condition :
        pullback.fst newπ d' ≫ newπ = pullback.snd newπ d' ≫ d')
    _ = _ := by rw [Category.assoc, hd, ← Category.assoc]

/-- The complete new inverse-image boundary maps into the reindexed old
inverse-image boundary, retaining both graph and endpoint coordinates. -/
def boundaryMap : newCovered newπ d' ⟶ G ⋙ oldCovered oldπ d :=
  JTSupportedPathZeroTransport.lift G oldπ d
    (newU newπ d' ≫ η) (newV newπ d' ≫ a)
    (boundary_map_square G oldπ d newπ d' n η a hπ hd)

theorem boundaryMap_graph :
    boundaryMap G oldπ d newπ d' n η a hπ hd ≫
      Functor.whiskerLeft G (oldU oldπ d) = newU newπ d' ≫ η :=
  JTSupportedPathZeroTransport.lift_fst G oldπ d
    (newU newπ d' ≫ η) (newV newπ d' ≫ a)
    (boundary_map_square G oldπ d newπ d' n η a hπ hd)

theorem boundaryMap_endpoint :
    boundaryMap G oldπ d newπ d' n η a hπ hd ≫
      Functor.whiskerLeft G (oldV oldπ d) = newV newπ d' ≫ a :=
  JTSupportedPathZeroTransport.lift_snd G oldπ d
    (newU newπ d' ≫ η) (newV newπ d' ≫ a)
    (boundary_map_square G oldπ d newπ d' n η a hπ hd)

private abbrev oldCollapse := JTEndpointReducedPullbackCover.collapse oldπ d e
private abbrev newCollapse := JTEndpointReducedPullbackCover.collapse newπ d' e'
private abbrev oldReduced := JTEndpointReducedPullbackCover.reduced oldπ d e
private abbrev newReduced := JTEndpointReducedPullbackCover.reduced newπ d' e'
private abbrev oldInl := pushout.inl (oldU oldπ d) (oldCollapse oldπ d e)
private abbrev oldInr := pushout.inr (oldU oldπ d) (oldCollapse oldπ d e)
private abbrev newInl := pushout.inl (newU newπ d') (newCollapse newπ d' e')
private abbrev newInr := pushout.inr (newU newπ d') (newCollapse newπ d' e')

include n η a hπ hd he in
theorem boundaryMap_collapse :
    boundaryMap G oldπ d newπ d' n η a hπ hd ≫
      Functor.whiskerLeft G (oldCollapse oldπ d e) =
      newCollapse newπ d' e' := by
  rw [oldCollapse, newCollapse, JTEndpointReducedPullbackCover.collapse,
    Functor.whiskerLeft_comp, ← Category.assoc, boundaryMap_endpoint]
  apply NatTrans.ext
  funext p
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app] using
    congrArg ((newV newπ d').app p ≫ ·) (he p)

private def cylinderLeg : newY ⟶
    (G ⋙ oldReduced oldπ d e) ⋙ Under.forget B :=
  η ≫ Functor.whiskerLeft G (oldInl oldπ d e)

include n η a hπ hd he in
private theorem sourceCocone :
    newU newπ d' ≫ cylinderLeg G oldπ d e η =
      newCollapse newπ d' e' ≫
        JTEndpointReducedCover.boundary (G ⋙ oldReduced oldπ d e) := by
  have hc := congrArg (Functor.whiskerLeft G)
    (pushout.condition (f := oldU oldπ d) (g := oldCollapse oldπ d e))
  calc
    _ = (newU newπ d' ≫ η) ≫
        Functor.whiskerLeft G (oldInl oldπ d e) :=
      (Category.assoc _ _ _).symm
    _ = (boundaryMap G oldπ d newπ d' n η a hπ hd ≫
        Functor.whiskerLeft G (oldU oldπ d)) ≫
          Functor.whiskerLeft G (oldInl oldπ d e) := by
      rw [boundaryMap_graph]
    _ = boundaryMap G oldπ d newπ d' n η a hπ hd ≫
        (Functor.whiskerLeft G (oldU oldπ d) ≫
          Functor.whiskerLeft G (oldInl oldπ d e)) := Category.assoc _ _ _
    _ = boundaryMap G oldπ d newπ d' n η a hπ hd ≫
        (Functor.whiskerLeft G (oldCollapse oldπ d e) ≫
          Functor.whiskerLeft G (oldInr oldπ d e)) := by
      rw [← Functor.whiskerLeft_comp, hc, Functor.whiskerLeft_comp]
    _ = (boundaryMap G oldπ d newπ d' n η a hπ hd ≫
        Functor.whiskerLeft G (oldCollapse oldπ d e)) ≫
          Functor.whiskerLeft G (oldInr oldπ d e) := (Category.assoc _ _ _).symm
    _ = _ := by
      rw [boundaryMap_collapse G oldπ d e newπ d' e' n η a hπ hd he]
      rfl

/-- Transport of the entire reduced endpoint cylinder under reindexing.
The source boundary is the full inverse image of the old endpoint line. -/
def sourceChange : newReduced newπ d' e' ⟶ G ⋙ oldReduced oldπ d e :=
  JTEndpointReducedCover.descend (newU newπ d') (newCollapse newπ d' e')
    (G ⋙ oldReduced oldπ d e) (cylinderLeg G oldπ d e η)
    (sourceCocone G oldπ d e newπ d' e' n η a hπ hd he)

include n η a hπ hd he in
theorem sourceChange_cylinder (p : J) :
    (newInl newπ d' e').app p ≫
      ((sourceChange G oldπ d e newπ d' e' n η a hπ hd he).app p).right =
    η.app p ≫ (oldInl oldπ d e).app (G.obj p) :=
  JTEndpointReducedCover.descend_cylinder (newU newπ d')
    (newCollapse newπ d' e') (G ⋙ oldReduced oldπ d e)
    (cylinderLeg G oldπ d e η)
    (sourceCocone G oldπ d e newπ d' e' n η a hπ hd he) p

include n η a hπ hd he in
theorem sourceChange_boundary (p : J) :
    (newInr newπ d' e').app p ≫
      ((sourceChange G oldπ d e newπ d' e' n η a hπ hd he).app p).right =
    (oldInr oldπ d e).app (G.obj p) :=
  Under.w ((sourceChange G oldπ d e newπ d' e' n η a hπ hd he).app p)

end
end DaggerModels.PartII.JTReindexedEndpointCoverTransport
