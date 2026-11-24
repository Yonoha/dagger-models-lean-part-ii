import DaggerModelsPartII.JTTargetCommaPullbackComparison
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-! The original necklace pullback presentation fibers over the native target slice. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativePresentationFibers

open BoundaryNecklaceComma (Presentation necklaceUnder sourceCode)

noncomputable section

variable {I : Type} [SmallCategory I]
variable {T : NecklaceCode} (E : I ⥤ Under JTXiEndpointCollapse.boundary)
variable (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T))

private def nativeArrow {S T : NecklaceCode} (f : necklaceUnder.obj S ⟶ necklaceUnder.obj T) :
    S ⟶ T :=
  let h : (f.right.app (op ⦋0⦌) S.first, f.right.app (op ⦋0⦌) S.last) =
      (T.first, T.last) := by
    have hw := Under.w f
    change JTNecklaceEndpointCylinder.endpointInclusion S ≫ f.right =
      JTNecklaceEndpointCylinder.endpointInclusion T at hw
    rw [JTNecklaceEndpointCylinder.endpointInclusion,
      JTGeneralOrderedFiberWeak.orderedBoundary_natural] at hw
    exact (JTEndpointObjects.boundaryHomEquiv _).symm.injective hw
  ⟨f.right, congrArg Prod.fst h, congrArg Prod.snd h⟩

private def nativeMap (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T))
    {P : Presentation E} : P.fiber.left ⟶ T :=
  nativeArrow (P.fiber.hom ≫ q.app P.base)

private theorem nativeMap_naturality (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T))
    {P P' : Presentation E} (f : P ⟶ P') :
    f.fiber.left ≫ nativeMap E q (P := P') = nativeMap E q (P := P) := by
  apply NecklaceCode.Hom.ext
  have h : necklaceUnder.map f.fiber.left ≫ P'.fiber.hom = P.fiber.hom ≫ E.map f.base :=
    CostructuredArrow.w f.fiber
  have hq : E.map f.base ≫ q.app P'.base = q.app P.base :=
    (q.naturality f.base).trans (Category.comp_id _)
  have hs : necklaceUnder.map f.fiber.left ≫ (P'.fiber.hom ≫ q.app P'.base) =
      P.fiber.hom ≫ q.app P.base := by
    rw [← Category.assoc, h, Category.assoc, hq]
  exact congrArg (fun a ↦ a.right) hs

/-- Retain the exact native code and map supplied by the original presentation. -/
def projection (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T)) :
    Presentation E ⥤ Over T :=
  Over.lift (sourceCode E) {
    app _ := nativeMap E q
    naturality {_ _} f := (nativeMap_naturality E q f).trans (Category.comp_id _).symm }

variable {E q} {V : Presentation E} {P : Over T}
variable (g : P ⟶ (projection E q).obj V)

private def restriction : Presentation E :=
  ⟨V.base, CostructuredArrow.mk (necklaceUnder.map g.left ≫ V.fiber.hom)⟩

private theorem projection_restriction : (projection E q).obj (restriction g) = P := by
  have h : nativeMap E q (P := restriction g) = P.hom := by
    calc
      _ = g.left ≫ nativeMap E q (P := V) := by
        apply NecklaceCode.Hom.ext
        exact congrArg (fun a : necklaceUnder.obj P.left ⟶ necklaceUnder.obj T ↦ a.right)
          (Category.assoc (necklaceUnder.map g.left) V.fiber.hom (q.app V.base))
      _ = _ := Over.w g
  change Over.mk (nativeMap E q (P := restriction g)) = P
  rw [h]
  rcases P with ⟨a, ⟨⟨⟩⟩, f⟩
  rfl

private def restrictionArrow : restriction g ⟶ V :=
  ⟨𝟙 _, CostructuredArrow.homMk g.left (by
    change necklaceUnder.map g.left ≫ V.fiber.hom =
      (necklaceUnder.map g.left ≫ V.fiber.hom) ≫ E.map (𝟙 V.base)
    rw [E.map_id]
    exact (Category.comp_id _).symm)⟩

private theorem lift_of_code {A B : Presentation E} {S S' : Over T}
    {g' : S ⟶ S'} {f : A ⟶ B}
    (hA : (projection E q).obj A = S) (hB : (projection E q).obj B = S')
    (h : HEq f.fiber.left g'.left) : (projection E q).IsHomLift g' f := by
  subst S S'
  apply IsHomLift.of_fac' _ _ _ rfl rfl
  apply Over.OverMorphism.ext
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using eq_of_heq h

private def factor {U : Presentation E} (h : (projection E q).obj U ⟶ P)
    (f : U ⟶ V) (hf : f.fiber.left = h.left ≫ g.left) :
    U ⟶ restriction g :=
  ⟨f.base, CostructuredArrow.homMk h.left (by
    change necklaceUnder.map h.left ≫ necklaceUnder.map g.left ≫ V.fiber.hom =
      U.fiber.hom ≫ E.map f.base
    rw [← Category.assoc, ← necklaceUnder.map_comp, ← hf]
    exact CostructuredArrow.w f.fiber)⟩

private theorem restriction_cartesian :
    (projection E q).IsStronglyCartesian g (restrictionArrow g) := by
  letI : (projection E q).IsHomLift g (restrictionArrow g) :=
    lift_of_code (projection_restriction g) rfl (HEq.rfl : HEq g.left g.left)
  refine { universal_property' := ?_ }
  intro U h f hf
  have he : (projection E q).map f = h ≫ g := (IsHomLift.eq_of_isHomLift _ _ _).symm
  have hc : f.fiber.left = h.left ≫ g.left := congrArg (fun a ↦ a.left) he
  refine ⟨factor g h f hc, ⟨lift_of_code rfl (projection_restriction g)
    (HEq.rfl : HEq h.left h.left), ?_⟩, ?_⟩
  · apply JTTargetCommaPullback.operator_ext
    · exact Category.comp_id _
    · change (sourceCode E).map (factor g h f hc ≫ restrictionArrow g) = _
      rw [(sourceCode E).map_comp]
      exact hc.symm
  · rintro a ⟨ha, hh⟩
    apply JTTargetCommaPullback.operator_ext
    · have hb := congrArg (fun k : U ⟶ V ↦ k.base) hh
      change a.base ≫ 𝟙 _ = f.base at hb
      simpa only [Category.comp_id] using hb
    · have hh := congrArg (fun k ↦ k.left) (IsHomLift.fac' (projection E q) h a)
      simp only [Over.comp_left, Over.eqToHom_left] at hh
      change a.fiber.left = 𝟙 _ ≫ h.left ≫ 𝟙 _ at hh
      change a.fiber.left = h.left
      simpa only [Category.id_comp, Category.comp_id] using hh

/-- Restricting the whole traversal gives Cartesian lifts over every native arrow. -/
theorem isFibered (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T)) :
    (projection E q).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun _ _ g ↦
    ⟨restriction g, restrictionArrow g, restriction_cartesian g⟩

end
end DaggerModels.PartII.JTNativePresentationFibers
