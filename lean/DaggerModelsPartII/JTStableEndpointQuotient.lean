import DaggerModelsPartII.JTEndpointReducedCover
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images

/-! A quotient retaining every restriction detected along the original diagram. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTStableEndpointQuotient

noncomputable section

scoped instance : HasImages SSet.{0} :=
  inferInstanceAs (HasImages (SimplexCategoryᵒᵖ ⥤ Type))

variable {I : Type} [SmallCategory I] {B : SSet.{0}}
variable (X : I ⥤ Under B) (Y : I → Under B)
variable (q : ∀ p, X.obj p ⟶ Y p)

abbrev Ends (p : I) := Σ r : I, p ⟶ r

abbrev factors (p : I) : Ends p → SSet.{0} :=
  fun a ↦ (Y a.1).right

private def restriction {p p' : I} (a : p ⟶ p') :
    ∏ᶜ factors Y p ⟶ ∏ᶜ factors Y p' :=
  Pi.lift fun b ↦ Pi.π (factors Y p) ⟨b.1, a ≫ b.2⟩

private theorem restriction_π {p p' : I} (a : p ⟶ p') (b : Ends p') :
    restriction Y a ≫ Pi.π (factors Y p') b = Pi.π (factors Y p) ⟨b.1, a ≫ b.2⟩ :=
  Pi.lift_π _ _

def products : I ⥤ SSet.{0} where
  obj p := ∏ᶜ factors Y p
  map f := restriction Y f
  map_id p := by
    apply Pi.hom_ext
    intro b
    rw [restriction_π, Category.id_comp, Category.id_comp]
  map_comp f g := by
    apply Pi.hom_ext
    intro b
    rw [restriction_π, Category.assoc (restriction Y f), restriction_π,
      restriction_π, Category.assoc f g]

def probes : X ⋙ Under.forget B ⟶ products Y where
  app p := Pi.lift fun a ↦ (X.map a.2 ≫ q a.1).right
  naturality {p p'} a := by
    apply Pi.hom_ext
    intro b
    change (X.map a).right ≫ Pi.lift _ ≫ Pi.π (factors Y p') b =
      Pi.lift _ ≫ restriction Y a ≫ Pi.π (factors Y p') b
    rw [Pi.lift_π, restriction_π, Pi.lift_π, X.map_comp]
    rfl

private theorem probes_π (p : I) (a : Ends p) :
    (probes X Y q).app p ≫ Pi.π (factors Y p) a = (X.map a.2 ≫ q a.1).right :=
  Pi.lift_π _ _

private def paired : I ⥤ Arrow SSet.{0} where
  obj p := Arrow.mk ((probes X Y q).app p)
  map f := Arrow.homMk' (X.map f).right ((products Y).map f) ((probes X Y q).naturality f)
  map_id p := by
    ext : 1
    · exact congrArg (fun f ↦ f.right) (X.map_id p)
    · exact (products Y).map_id p
  map_comp f g := by
    ext : 1
    · exact congrArg (fun f ↦ f.right) (X.map_comp f g)
    · exact (products Y).map_comp f g

abbrev images := paired X Y q ⋙ Limits.im

private def quotientRight : X ⋙ Under.forget B ⟶ images X Y q where
  app p := factorThruImage ((probes X Y q).app p)
  naturality _ _ f := (image.factor_map ((paired X Y q).map f)).symm

/-- The images of all future observations form a diagram under the same ordered boundary. -/
def diagram : I ⥤ Under B :=
  Under.lift (images X Y q) (JTEndpointReducedCover.boundary X ≫ quotientRight X Y q)

/-- The canonical quotient is natural along all original arrows. -/
def quotient : X ⟶ diagram X Y q where
  app p := Under.homMk ((quotientRight X Y q).app p) rfl
  naturality _ _ f := Under.UnderMorphism.ext ((quotientRight X Y q).naturality f)

instance quotient_epi (p : I) : Epi ((quotient X Y q).app p).right := by
  change Epi (factorThruImage ((probes X Y q).app p))
  infer_instance

theorem quotient_right (p : I) :
    ((quotient X Y q).app p).right = factorThruImage ((probes X Y q).app p) := rfl

/-- Every objectwise quotient reached along an original arrow can be recovered. -/
def observation (p : I) (a : Ends p) : (diagram X Y q).obj p ⟶ Y a.1 :=
  Under.homMk (image.ι ((probes X Y q).app p) ≫ Pi.π (factors Y p) a) (by
    change ((X.obj p).hom ≫ factorThruImage ((probes X Y q).app p)) ≫
      image.ι ((probes X Y q).app p) ≫ Pi.π (factors Y p) a = _
    rw [Category.assoc, ← Category.assoc (factorThruImage _) (image.ι _),
      image.fac, probes_π]
    exact Under.w (X.map a.2 ≫ q a.1))

theorem quotient_observation (p : I) (a : Ends p) :
    (quotient X Y q).app p ≫ observation X Y q p a = X.map a.2 ≫ q a.1 := by
  apply Under.UnderMorphism.ext
  change factorThruImage ((probes X Y q).app p) ≫
      image.ι ((probes X Y q).app p) ≫ Pi.π (factors Y p) a = _
  rw [image.fac_assoc, probes_π]

theorem observation_id (p : I) :
    (quotient X Y q).app p ≫ observation X Y q p ⟨p, 𝟙 p⟩ = q p := by
  rw [quotient_observation, X.map_id, Category.id_comp]

/-- The simultaneous quotient identifies exactly the maps equal after
all original outgoing observations. -/
theorem quotient_eq_iff {A : Under B} (p : I) (f g : A ⟶ X.obj p) :
    f ≫ (quotient X Y q).app p = g ≫ (quotient X Y q).app p ↔
      ∀ a : Ends p, f ≫ X.map a.2 ≫ q a.1 = g ≫ X.map a.2 ≫ q a.1 := by
  constructor
  · intro h a
    have he := congrArg (fun k ↦ k ≫ observation X Y q p a) h
    simpa only [Category.assoc, quotient_observation] using he
  · intro h
    apply Under.UnderMorphism.ext
    apply (cancel_mono (image.ι ((probes X Y q).app p))).mp
    apply Pi.hom_ext
    intro a
    change (f.right ≫ factorThruImage ((probes X Y q).app p)) ≫
        image.ι ((probes X Y q).app p) ≫ Pi.π (factors Y p) a =
      (g.right ≫ factorThruImage ((probes X Y q).app p)) ≫
        image.ι ((probes X Y q).app p) ≫ Pi.π (factors Y p) a
    simp only [Category.assoc, image.fac_assoc, probes_π]
    exact congrArg (fun k ↦ k.right) (h a)


variable {V : I ⥤ Under B} (e : X ⟶ V)
variable (r : ∀ p, Y p ⟶ V.obj p) (h : ∀ p, q p ≫ r p = e.app p)

include h in
private theorem component_factor (p : I) :
    (quotient X Y q).app p ≫ (observation X Y q p ⟨p, 𝟙 p⟩ ≫ r p) = e.app p := by
  rw [← Category.assoc, observation_id, h]

include h in
/-- A factored natural traversal on the original diagram descends naturally
to the simultaneous quotient, even if the individual quotients do not. -/
def factor : diagram X Y q ⟶ V where
  app p := observation X Y q p ⟨p, 𝟙 p⟩ ≫ r p
  naturality {p p'} f := by
    let l := (quotient X Y q).app p
    letI : Epi l := by
      constructor
      intro Z u v he
      apply Under.UnderMorphism.ext
      exact (cancel_epi l.right).mp (congrArg (fun k ↦ k.right) he)
    apply (cancel_epi l).mp
    change l ≫ (diagram X Y q).map f ≫ (observation X Y q p' ⟨p', 𝟙 p'⟩ ≫ r p') =
      l ≫ (observation X Y q p ⟨p, 𝟙 p⟩ ≫ r p) ≫ V.map f
    rw [← Category.assoc l ((diagram X Y q).map f), ← (quotient X Y q).naturality f,
      Category.assoc, component_factor X Y q e r h, ← Category.assoc l,
      component_factor X Y q e r h]
    exact e.naturality f

theorem quotient_factor :
    quotient X Y q ≫ factor X Y q e r h = e := by
  apply NatTrans.ext
  funext p
  exact component_factor X Y q e r h p

end

end DaggerModels.PartII.JTStableEndpointQuotient
