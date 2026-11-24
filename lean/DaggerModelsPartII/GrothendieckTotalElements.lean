import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The actual degreewise-Elements Grothendieck construction is total Elements

Objects and both morphism components are only reassociated. The original
label and its full operator equation are retained without replacement.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial
open scoped Prod

namespace DaggerModels.PartII.GrothendieckTotalElements

noncomputable section

variable {C : Type} [SmallCategory C] {D : Type} [SmallCategory D] (G : C ⥤ D ⥤ Type)

/-- The actual category of elements at each entire simplicial-set value. -/
def elementDiagram : C ⥤ Cat.{0,0} := G ⋙ Functor.elementsFunctor

/-- The original full two-index coefficient presheaf. -/
def totalDiagram : C × D ⥤ Type := Functor.uncurry.obj G

private theorem eqToHom_val {X : D ⥤ Type} {a b : X.Elements} (h : a = b) :
    (eqToHom h : a ⟶ b).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- Reassociate the SAME base, degree, label and both actual operator components. -/
def toTotal : Grothendieck (elementDiagram G) ⥤ (totalDiagram G).Elements where
  obj X := ⟨(X.base, X.fiber.1), X.fiber.2⟩
  map f := ⟨f.base ×ₘ f.fiber.val, f.fiber.property⟩
  map_id X := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (eqToHom _ :
        (NatTrans.mapElements (G.map (𝟙 X.base))).obj X.fiber ⟶ X.fiber).val =
          𝟙 X.fiber.1
      rw [eqToHom_val (X := G.obj X.base)]
      rfl
  map_comp {X Y Z} f g := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hc : (NatTrans.mapElements (G.map (f.base ≫ g.base))).obj X.fiber =
          (NatTrans.mapElements (G.map g.base)).obj
            ((NatTrans.mapElements (G.map f.base)).obj X.fiber) := by
        rw [G.map_comp]
        rfl
      change (eqToHom hc ≫ (NatTrans.mapElements (G.map g.base)).map f.fiber ≫
        g.fiber).val = f.fiber.val ≫ g.fiber.val
      simp only [CategoryOfElements.comp_val]
      rw [eqToHom_val (X := G.obj Z.base)]
      exact Category.id_comp (f.fiber.val ≫ g.fiber.val)

/-- The inverse repacks the SAME label and the SAME two-index operator equation. -/
def fromTotal : (totalDiagram G).Elements ⥤ Grothendieck (elementDiagram G) where
  obj X := ⟨X.1.1, ⟨X.1.2, X.2⟩⟩
  map f := ⟨f.val.1, ⟨f.val.2, f.property⟩⟩
  map_id X := by
    refine Grothendieck.ext _ _ ?base ?fiber
    case base => rfl
    case fiber =>
      apply Subtype.ext
      simp only [eqToHom_refl, Category.id_comp]
      have hi : (NatTrans.mapElements (G.map (𝟙 X.1.1))).obj ⟨X.1.2, X.2⟩ =
          (⟨X.1.2, X.2⟩ : (G.obj X.1.1).Elements) := by
        rw [G.map_id]
        rfl
      change 𝟙 X.1.2 = (eqToHom hi :
        (NatTrans.mapElements (G.map (𝟙 X.1.1))).obj ⟨X.1.2, X.2⟩ ⟶ ⟨X.1.2, X.2⟩).val
      rw [eqToHom_val (X := G.obj X.1.1)]
      rfl
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext _ _ ?base ?fiber
    case base => rfl
    case fiber =>
      apply Subtype.ext
      simp only [eqToHom_refl, Category.id_comp]
      let sf : (NatTrans.mapElements (G.map f.val.1)).obj ⟨X.1.2, X.2⟩ ⟶
          (⟨Y.1.2, Y.2⟩ : (G.obj Y.1.1).Elements) := ⟨f.val.2, f.property⟩
      let sg : (NatTrans.mapElements (G.map g.val.1)).obj ⟨Y.1.2, Y.2⟩ ⟶
          (⟨Z.1.2, Z.2⟩ : (G.obj Z.1.1).Elements) := ⟨g.val.2, g.property⟩
      have hc : (NatTrans.mapElements (G.map (f.val.1 ≫ g.val.1))).obj ⟨X.1.2, X.2⟩ =
          (NatTrans.mapElements (G.map g.val.1)).obj
            ((NatTrans.mapElements (G.map f.val.1)).obj ⟨X.1.2, X.2⟩) := by
        rw [G.map_comp]
        rfl
      change f.val.2 ≫ g.val.2 = (eqToHom hc ≫
        (NatTrans.mapElements (G.map g.val.1)).map sf ≫ sg).val
      simp only [CategoryOfElements.comp_val]
      rw [eqToHom_val (X := G.obj Z.1.1)]
      exact (Category.id_comp (f.val.2 ≫ g.val.2)).symm

private theorem to_from : toTotal G ⋙ fromTotal G = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj => rintro ⟨c, ⟨q, x⟩⟩; rfl
  case h_map =>
    rintro ⟨c, ⟨q, x⟩⟩ ⟨d, ⟨r, y⟩⟩ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

private theorem from_to : fromTotal G ⋙ toTotal G = 𝟭 _ := by
  refine CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj => rintro ⟨⟨c, q⟩, x⟩; rfl
  case h_map =>
    rintro ⟨⟨c, q⟩, x⟩ ⟨⟨d, r⟩, y⟩ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- A full equivalence of the actual Grothendieck and original total Elements categories. -/
def equivalence : Grothendieck (elementDiagram G) ≌ (totalDiagram G).Elements where
  functor := toTotal G
  inverse := fromTotal G
  unitIso := (eqToIso (to_from G)).symm
  counitIso := eqToIso (from_to G)
  functor_unitIso_comp := by
    rintro ⟨c, ⟨q, x⟩⟩
    change (toTotal G).map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    rw [(toTotal G).map_id, Category.id_comp]

/-- The first-index projection is exactly the original Grothendieck projection. -/
theorem forget_square :
    toTotal G ⋙ CategoryOfElements.π (totalDiagram G) ⋙
        CategoryTheory.Prod.fst C D =
      Grothendieck.forget (elementDiagram G) := rfl

/-- The second-index projection keeps the original full simplex operator. -/
theorem toTotal_map_degree {X Y : Grothendieck (elementDiagram G)} (f : X ⟶ Y) :
    ((toTotal G).map f).val.2 = f.fiber.val := rfl

end

end DaggerModels.PartII.GrothendieckTotalElements
