import DaggerModelsPartII.JTBoundaryNecklacePresentationTimeChange

/-! Compare complete evaluations after two independent changes of index. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.JTBoundaryNecklaceTwoReindexComparison

open BoundaryNecklaceComma (diagram fiberDiagram)
open JTBoundaryNecklacePresentationCone (mapPresentation)

noncomputable section

variable {I J K A C : Type}
variable [SmallCategory I] [SmallCategory J] [SmallCategory K]
variable [SmallCategory A] [SmallCategory C]
variable (E : I ⥤ Under JTXiEndpointCollapse.boundary)
variable (F : J ⥤ Under JTXiEndpointCollapse.boundary) (L : J ⥤ I)
variable (p : F ⟶ L ⋙ E) (G : A ⥤ J)

/-- The whiskered lift with an explicit associator evaluates on the exact
reindexed presentation, without reducing any concrete family of choices. -/
theorem evaluation_reindex
    (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    mapPresentation E (G ⋙ F) (G ⋙ L)
        (Functor.whiskerLeft G p ≫ (Functor.associator G L E).inv) ⋙ H =
      Grothendieck.pre (fiberDiagram F) G ⋙ (mapPresentation E F L p ⋙ H) := by
  have hp : Functor.whiskerLeft G p ≫ (Functor.associator G L E).inv =
      Functor.whiskerLeft G p := by
    apply NatTrans.ext
    funext a
    exact Category.comp_id _
  rw [hp, JTBoundaryNecklacePresentationTransport.mapPresentation_reindex]
  rfl

variable (F' : K ⥤ Under JTXiEndpointCollapse.boundary) (M : K ⥤ I)
variable (q : F' ⟶ M ⋙ E) (G' : A ⥤ K)
variable (s : G ⋙ F ⟶ G' ⋙ F') (r : G ⋙ L ⟶ G' ⋙ M)
variable (h : ∀ a, p.app (G.obj a) ≫ E.map (r.app a) =
  s.app a ≫ q.app (G'.obj a))

/-- A full source and label comparison between two reindexed evaluations.
Both functors keep all internal necklaces; no pointwise-only replacement is used. -/
def comparison (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    Grothendieck.pre (fiberDiagram F) G ⋙ (mapPresentation E F L p ⋙ H) ⟶
      (Grothendieck.map (Functor.whiskerRight s diagram) ⋙
        Grothendieck.pre (fiberDiagram F') G') ⋙ (mapPresentation E F' M q ⋙ H) := by
  let p₀ : G ⋙ F ⟶ (G ⋙ L) ⋙ E :=
    Functor.whiskerLeft G p ≫ (Functor.associator G L E).inv
  let q₀ : G' ⋙ F' ⟶ (G' ⋙ M) ⋙ E :=
    Functor.whiskerLeft G' q ≫ (Functor.associator G' M E).inv
  have h₀ : ∀ a, p₀.app a ≫ E.map (r.app a) = s.app a ≫ q₀.app a := by
    intro a
    simpa only [p₀, q₀, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id] using h a
  let ρ := Grothendieck.map (Functor.whiskerRight s diagram)
  let P' := Grothendieck.pre (fiberDiagram F') G'
  let E' := mapPresentation E F' M q ⋙ H
  let c := JTBoundaryNecklacePresentationTransport.comparisonWithSourceChange
    E p₀ q₀ s r h₀ H
  exact eqToHom (evaluation_reindex E F L p G H).symm ≫ c ≫
    Functor.whiskerLeft ρ (eqToHom (evaluation_reindex E F' M q G' H)) ≫
      (Functor.associator ρ P' E').inv

end
end DaggerModels.PartII.JTBoundaryNecklaceTwoReindexComparison
