import DaggerModelsPartII.JTCylinderOverTargetBaseChange

/-!
# Composition of time-cylinder comparison squares
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels

namespace DaggerModels.PartII.JTCylinderOverTargetBaseChangeComp

open JTCylinderOverTargetBaseChange
open BoundaryNecklaceComma (necklaceUnder)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {i'' i' i : I} {A'' A' A : Under B}
variable (p'' : A'' ⟶ E.obj i'') (p' : A' ⟶ E.obj i') (p : A ⟶ E.obj i)
variable (k : A'' ⟶ A') (g : A' ⟶ A) (b : i'' ⟶ i') (a : i' ⟶ i)
variable (hb : p'' ≫ E.map b = k ≫ p') (ha : p' ≫ E.map a = g ≫ p)

include hb ha in
theorem square_comp : p'' ≫ E.map (b ≫ a) = (k ≫ g) ≫ p := by
  rw [E.map_comp, ← Category.assoc, hb, Category.assoc, ha, Category.assoc]

private theorem target_comp :
    CostructuredArrow.map k ⋙ CostructuredArrow.map g ⋙ CostructuredArrow.map p ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i =
      CostructuredArrow.map (k ≫ g) ⋙ CostructuredArrow.map p ⋙
        Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram E) i := by
  let G := BoundaryNecklaceComma.diagram
  have H := congrArg Cat.Hom.toFunctor (G.map_comp k g)
  change CostructuredArrow.map (k ≫ g) =
    CostructuredArrow.map k ⋙ CostructuredArrow.map g at H
  rw [H, Functor.assoc]

/-- The comparison of a composite square is the composite of the comparisons. -/
theorem comparisonOfSquare_comp :
    comparisonOfSquare E p'' p (k ≫ g) (b ≫ a) (square_comp E p'' p' p k g b a hb ha) =
      comparisonOfSquare E p'' p' k b hb ≫
        Functor.whiskerLeft (CostructuredArrow.map k)
          (comparisonOfSquare E p' p g a ha) ≫ eqToHom (target_comp E p k g) := by
  ext : 1
  funext P
  apply JTTargetCommaPullback.operator_ext
  · simp only [comparisonOfSquare_base, NatTrans.comp_app, Functor.whiskerLeft_app,
      Grothendieck.comp_base, eqToHom_app, Grothendieck.base_eqToHom]
    change b ≫ a = b ≫ a ≫ 𝟙 i
    rw [Category.comp_id]
  · change (BoundaryNecklaceComma.sourceCode E).map
        ((comparisonOfSquare E p'' p (k ≫ g) (b ≫ a) (square_comp E p'' p' p k g b a hb ha)).app P) =
      (BoundaryNecklaceComma.sourceCode E).map
        ((comparisonOfSquare E p'' p' k b hb ≫
          Functor.whiskerLeft (CostructuredArrow.map k)
            (comparisonOfSquare E p' p g a ha) ≫ eqToHom (target_comp E p k g)).app P)
    simp only [comparisonOfSquare_code, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.map_comp, eqToHom_app, eqToHom_map]
    change 𝟙 P.left = 𝟙 P.left ≫ 𝟙 P.left ≫ 𝟙 P.left
    rw [Category.id_comp, Category.id_comp]


end

end DaggerModels.PartII.JTCylinderOverTargetBaseChangeComp
