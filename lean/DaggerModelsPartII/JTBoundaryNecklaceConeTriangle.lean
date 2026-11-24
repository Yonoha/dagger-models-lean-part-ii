import DaggerModelsPartII.JTBoundaryNecklaceConeReindex

/-!
# Comparing two cones over original necklace presentations
-/

set_option autoImplicit false

open CategoryTheory Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklaceConeTriangle

open BoundaryNecklaceComma (necklaceUnder sourceCode)
open JTBoundaryNecklacePresentationCone (cone cone_base cone_native_map)
open JTCylinderOverTargetBaseChange (comparisonOfSquare comparisonOfSquare_base
  comparisonOfSquare_code)
open JTBoundaryNecklaceConeReindex (mapCone)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

/-- The comparison of a commuting square agrees with the two cone legs when
their original decorated and native maps agree. -/
theorem cone_triangle {I : Type} [SmallCategory I] (E : I ⥤ Under B)
    {i₁ i₂ : I} {A₁ A₂ : Under B} {U₁ U₂ : BoundaryNecklaceComma.Presentation E}
    (p₁ : A₁ ⟶ E.obj i₁) (p₂ : A₂ ⟶ E.obj i₂)
    (g : A₁ ⟶ A₂) (a : i₁ ⟶ i₂) (h : p₁ ≫ E.map a = g ≫ p₂)
    (b₁ : i₁ ⟶ U₁.base) (b₂ : i₂ ⟶ U₂.base)
    (c₁ : A₁ ⟶ necklaceUnder.obj U₁.fiber.left)
    (c₂ : A₂ ⟶ necklaceUnder.obj U₂.fiber.left)
    (h₁ : p₁ ≫ E.map b₁ = c₁ ≫ U₁.fiber.hom)
    (h₂ : p₂ ≫ E.map b₂ = c₂ ≫ U₂.fiber.hom) (d : U₁ ⟶ U₂)
    (hBase : a ≫ b₂ = b₁ ≫ d.base) (hCode : g ≫ c₂ = c₁ ≫ necklaceUnder.map d.fiber.left) :
    comparisonOfSquare E p₁ p₂ g a h ≫
        Functor.whiskerLeft (CostructuredArrow.map g) (cone E p₂ U₂ b₂ c₂ h₂) =
      cone E p₁ U₁ b₁ c₁ h₁ ≫ (Functor.const _).map d := by
  ext : 1
  funext P
  apply JTTargetCommaPullback.operator_ext
  · simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.const_map_app,
      Grothendieck.comp_base, comparisonOfSquare_base, cone_base]
    exact hBase
  · let N := sourceCode E
    change N.map ((comparisonOfSquare E p₁ p₂ g a h).app P ≫
        (cone E p₂ U₂ b₂ c₂ h₂).app ((CostructuredArrow.map g).obj P)) =
      N.map ((cone E p₁ U₁ b₁ c₁ h₁).app P ≫ d)
    simp only [Functor.map_comp, N, comparisonOfSquare_code]
    apply NecklaceCode.Hom.ext
    change ((cone E p₂ U₂ b₂ c₂ h₂).app ((CostructuredArrow.map g).obj P)).fiber.left.map =
      (((cone E p₁ U₁ b₁ c₁ h₁).app P).fiber.left ≫ d.fiber.left).map
    rw [cone_native_map]
    have hr := cone_native_map E p₁ U₁ b₁ c₁ h₁ P
    change ((P.hom ≫ g) ≫ c₂).right =
      ((cone E p₁ U₁ b₁ c₁ h₁).app P).fiber.left.map ≫ d.fiber.left.map
    rw [hr]
    rw [Category.assoc]
    exact congrArg
      (fun v : A₁ ⟶ necklaceUnder.obj U₂.fiber.left ↦ (P.hom ≫ v).right) hCode |>.trans
        (congrArg (fun v : necklaceUnder.obj P.left ⟶ necklaceUnder.obj U₂.fiber.left ↦ v.right)
          (Category.assoc P.hom c₁ (necklaceUnder.map d.fiber.left)).symm)

section Slice

variable {J J' C D : Type*} [Category* J] [Category* J'] [Category* C] [Category* D]

/-- Mapping compatible cone comparisons preserves their original triangle. -/
theorem mapCone_triangle (M : J ⥤ J') {F : J ⥤ C} {F' : J' ⥤ C}
    {X X' : C} (τ : F ⟶ (Functor.const J).obj X)
    (τ' : F' ⟶ (Functor.const J').obj X') (α : F ⟶ M ⋙ F') (d : X ⟶ X')
    (h : α ≫ Functor.whiskerLeft M τ' = τ ≫ (Functor.const J).map d)
    (K : C ⥤ D) {Y Y' : D} (k : K.obj X ⟶ Y) (k' : K.obj X' ⟶ Y') (d' : Y ⟶ Y')
    (hk : K.map d ≫ k' = k ≫ d') :
    Functor.whiskerRight α K ≫ Functor.whiskerLeft M (mapCone τ' K k') =
      mapCone τ K k ≫ (Functor.const J).map d' := by
  ext : 1
  funext P
  have hp : α.app P ≫ τ'.app (M.obj P) = τ.app P ≫ d := NatTrans.congr_app h P
  simp only [mapCone, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.constComp_hom_app, Functor.const_map_app, Category.id_comp]
  rw [← Functor.map_comp_assoc, hp, Functor.map_comp_assoc, hk, Category.assoc]

/-- A triangle of cone maps gives a natural transformation of slice functors. -/
def overHom {F F' : J ⥤ C} {X : C}
    (τ : F ⟶ (Functor.const J).obj X) (τ' : F' ⟶ (Functor.const J).obj X)
    (α : F ⟶ F') (h : α ≫ τ' = τ) :
    Over.lift F τ ⟶ Over.lift F' τ' where
  app P := Over.homMk (α.app P) (NatTrans.congr_app h P)
  naturality := by
    intro P P' f
    apply CostructuredArrow.hom_ext
    exact α.naturality f

end Slice

end

end DaggerModels.PartII.JTBoundaryNecklaceConeTriangle
