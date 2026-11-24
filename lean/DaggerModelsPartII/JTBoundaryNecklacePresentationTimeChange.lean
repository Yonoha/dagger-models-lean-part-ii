import DaggerModelsPartII.JTBoundaryNecklacePresentationTransport

/-! A change of both cylinder and label in the full internal-necklace presentation. -/

set_option autoImplicit false

open CategoryTheory DaggerModels

namespace DaggerModels.PartII.JTBoundaryNecklacePresentationTransport

open BoundaryNecklaceComma (diagram fiberDiagram necklaceUnder sourceCode)
open JTBoundaryNecklacePresentationCone (mapPresentation)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I J : Type} [SmallCategory I] [SmallCategory J]
variable (E : I ⥤ Under B) {F : J ⥤ Under B} {L : J ⥤ I}

section Reindexed

variable {K : Type} [SmallCategory K]
variable (G : K ⥤ J) {F₀ : K ⥤ Under B} {L₀ : K ⥤ I}
variable (p₀ : F ⟶ L ⋙ E) (q₀ : F₀ ⟶ L₀ ⋙ E)
variable (r₀ : G ⋙ F ⟶ F₀) (α₀ : G ⋙ L ⟶ L₀)
variable (h₀ : ∀ i, p₀.app (G.obj i) ≫ E.map (α₀.app i) = r₀.app i ≫ q₀.app i)

private theorem sourceChange_code {P P' : BoundaryNecklaceComma.Presentation (G ⋙ F)}
    (f : P ⟶ P') :
    ((Grothendieck.map (Functor.whiskerRight r₀ diagram)).map f).fiber.left =
      f.fiber.left := by
  exact JTBoundaryNecklacePresentationCone.mapPresentation_code
    F₀ (G ⋙ F) (𝟭 K) r₀ f

private def reindexedComponent (P : BoundaryNecklaceComma.Presentation (G ⋙ F)) :
    ((Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram F) G) ⋙
      mapPresentation E F L p₀).obj P ⟶
    ((Grothendieck.map (Functor.whiskerRight r₀ diagram)) ⋙
      mapPresentation E F₀ L₀ q₀).obj P :=
  ⟨α₀.app P.base, CostructuredArrow.homMk (𝟙 P.fiber.left) (by
    change necklaceUnder.map (𝟙 P.fiber.left) ≫
        ((P.fiber.hom ≫ r₀.app P.base) ≫ q₀.app P.base) =
      (P.fiber.hom ≫ p₀.app (G.obj P.base)) ≫ E.map (α₀.app P.base)
    rw [necklaceUnder.map_id, Category.id_comp]
    calc
      _ = P.fiber.hom ≫ (r₀.app P.base ≫ q₀.app P.base) :=
        Category.assoc _ _ _
      _ = P.fiber.hom ≫ (p₀.app (G.obj P.base) ≫ E.map (α₀.app P.base)) :=
        congrArg (P.fiber.hom ≫ ·) (h₀ P.base).symm
      _ = _ := (Category.assoc _ _ _).symm)⟩

/-- Compare a reindexed old presentation with a source and label change. -/
def comparisonReindexedWithSourceChange :
    Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram F) G ⋙
        mapPresentation E F L p₀ ⟶
      Grothendieck.map (Functor.whiskerRight r₀ diagram) ⋙
        mapPresentation E F₀ L₀ q₀ where
  app := reindexedComponent E G p₀ q₀ r₀ α₀ h₀
  naturality {P P'} f := by
    apply JTTargetCommaPullback.operator_ext
    · exact α₀.naturality f.base
    · change (sourceCode E).map (_ ≫ _) = (sourceCode E).map (_ ≫ _)
      rw [(sourceCode E).map_comp, (sourceCode E).map_comp,
        Functor.comp_map (Grothendieck.pre (BoundaryNecklaceComma.fiberDiagram F) G)
          (mapPresentation E F L p₀) f,
        Functor.comp_map (Grothendieck.map (Functor.whiskerRight r₀ diagram))
          (mapPresentation E F₀ L₀ q₀) f,
        JTBoundaryNecklacePresentationCone.mapPresentation_code E F L p₀,
        JTBoundaryNecklacePresentationCone.mapPresentation_code E F₀ L₀ q₀]
      change f.fiber.left ≫ 𝟙 P'.fiber.left = 𝟙 P.fiber.left ≫
        ((Grothendieck.map (Functor.whiskerRight r₀ diagram)).map f).fiber.left
      rw [sourceChange_code G r₀ f, Category.comp_id, Category.id_comp]

end Reindexed

/-- Compare presentations over the same base after changing both the source
and the label, and applying a fixed evaluation functor. -/
def comparisonWithSourceChange {I A C : Type}
    [SmallCategory I] [SmallCategory A] [SmallCategory C]
    (E : I ⥤ Under JTXiEndpointCollapse.boundary)
    {D D' : A ⥤ Under JTXiEndpointCollapse.boundary} {L M : A ⥤ I}
    (p : D ⟶ L ⋙ E) (q : D' ⟶ M ⋙ E) (s : D ⟶ D') (r : L ⟶ M)
    (h : ∀ a, p.app a ≫ E.map (r.app a) = s.app a ≫ q.app a)
    (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    mapPresentation E D L p ⋙ H ⟶
      Grothendieck.map (Functor.whiskerRight s diagram) ⋙ (mapPresentation E D' M q ⋙ H) := by
  let P := mapPresentation E D L p
  let D₀ := mapPresentation E D' M q
  let ρ := Grothendieck.map (Functor.whiskerRight s diagram)
  let u := comparisonReindexedWithSourceChange E (𝟭 A) (F₀ := D') (L₀ := M) p q s r h
  let e := (congrArg (· ⋙ P) (Grothendieck.pre_id (fiberDiagram D))).trans (Functor.id_comp P)
  exact Functor.whiskerRight (eqToHom e.symm ≫ u) H ≫ (Functor.associator ρ D₀ H).hom

end
end DaggerModels.PartII.JTBoundaryNecklacePresentationTransport
