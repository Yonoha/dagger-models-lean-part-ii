import DaggerModelsPartII.JTBoundaryNecklacePresentationCone

/-! A natural cone from the full cylinder presentation to a varying target presentation. -/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTVariablePresentationCone

open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode evaluation)
open JTBoundaryNecklacePresentationCone (mapPresentation mapPresentation_code)
open JTTargetCommaPullback (nativeArrow map_nativeArrow operator_ext)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I J : Type} [SmallCategory I] [SmallCategory J]
variable (E : I ⥤ Under B) (F : J ⥤ Under B) (labels : J ⥤ I)
variable (lift : F ⟶ labels ⋙ E)
variable (D : J ⥤ BoundaryNecklaceComma.Presentation E)
variable (α : labels ⟶ D ⋙ Grothendieck.forget (fiberDiagram E))
variable (β : F ⟶ D ⋙ sourceCode E ⋙ necklaceUnder)
variable (h : ∀ j, lift.app j ≫ E.map (α.app j) =
  β.app j ≫ (D.obj j).fiber.hom)

private def component (P : BoundaryNecklaceComma.Presentation F) :
    (mapPresentation E F labels lift).obj P ⟶ D.obj P.base := by
  let f := P.fiber.hom ≫ β.app P.base
  refine ⟨α.app P.base, CostructuredArrow.homMk (nativeArrow f) ?_⟩
  apply Under.UnderMorphism.ext
  change (necklaceUnder.map (nativeArrow f) ≫ (D.obj P.base).fiber.hom).right =
    ((P.fiber.hom ≫ lift.app P.base) ≫ E.map (α.app P.base)).right
  rw [map_nativeArrow]
  calc
    (f ≫ (D.obj P.base).fiber.hom).right =
      (P.fiber.hom ≫ (β.app P.base ≫ (D.obj P.base).fiber.hom)).right := by
        rw [Category.assoc]
    _ = (P.fiber.hom ≫ (lift.app P.base ≫ E.map (α.app P.base))).right := by
      rw [← h]
    _ = ((P.fiber.hom ≫ lift.app P.base) ≫ E.map (α.app P.base)).right := by
      rw [Category.assoc]

/-- A varying presentation cone retains the actual inner necklace operator. -/
def cone : mapPresentation E F labels lift ⟶
    Grothendieck.forget (fiberDiagram F) ⋙ D where
  app := component E F labels lift D α β h
  naturality {P P'} f := by
    apply operator_ext
    · exact α.naturality f.base
    · change (sourceCode E).map (_ ≫ _) = (sourceCode E).map (_ ≫ _)
      rw [Functor.map_comp, Functor.map_comp]
      rw [mapPresentation_code]
      change f.fiber.left ≫ nativeArrow (P'.fiber.hom ≫ β.app P'.base) =
        nativeArrow (P.fiber.hom ≫ β.app P.base) ≫
          (sourceCode E).map (D.map f.base)
      apply NecklaceCode.Hom.ext
      change (necklaceUnder.map f.fiber.left ≫
        (P'.fiber.hom ≫ β.app P'.base)).right =
          ((P.fiber.hom ≫ β.app P.base) ≫
            necklaceUnder.map ((sourceCode E).map (D.map f.base))).right
      have he := (evaluation F).naturality f
      change necklaceUnder.map f.fiber.left ≫ P'.fiber.hom =
        P.fiber.hom ≫ F.map f.base at he
      have hb := β.naturality f.base
      change F.map f.base ≫ β.app P'.base =
        β.app P.base ≫ necklaceUnder.map ((sourceCode E).map (D.map f.base)) at hb
      have hc : necklaceUnder.map f.fiber.left ≫
          (P'.fiber.hom ≫ β.app P'.base) =
        (P.fiber.hom ≫ β.app P.base) ≫
          necklaceUnder.map ((sourceCode E).map (D.map f.base)) := by
        rw [← Category.assoc, he, Category.assoc, hb, ← Category.assoc]
      exact congrArg (fun u ↦ u.right) hc

theorem cone_base (P : BoundaryNecklaceComma.Presentation F) :
    ((cone E F labels lift D α β h).app P).base = α.app P.base := rfl

theorem cone_native_map (P : BoundaryNecklaceComma.Presentation F) :
    ((cone E F labels lift D α β h).app P).fiber.left.map =
      (P.fiber.hom ≫ β.app P.base).right := rfl

end

end DaggerModels.PartII.JTVariablePresentationCone
