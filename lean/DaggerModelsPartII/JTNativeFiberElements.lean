import DaggerModelsPartII.JTNativePresentationFibers
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-! The strict fiber is the category of complete lifts of a fixed native map. -/

set_option autoImplicit false

open CategoryTheory Limits DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTNativeFiberElements

open BoundaryNecklaceComma (Presentation necklaceUnder)
open JTNativePresentationFibers (projection)
open Functor IsHomLift

noncomputable section

variable {I : Type} [SmallCategory I]
variable {T : NecklaceCode} (E : I ⥤ Under JTXiEndpointCollapse.boundary)
variable (q : E ⟶ (Functor.const I).obj (necklaceUnder.obj T))
variable (P : Over T)

private abbrev mapsOver := Over.lift E q

/-- The actual lifts of the whole given native map, with the original endpoints. -/
def lifts : I ⥤ Type :=
  mapsOver E q ⋙ coyoneda.obj (Opposite.op ((Over.post necklaceUnder).obj P))

private abbrev C := (lifts E q P).Elements
private abbrev F := Fiber (projection E q) P

private theorem native_eq (i : I)
    (a : (lifts E q P).obj i) :
    (projection E q).obj (⟨i, CostructuredArrow.mk a.left⟩ : Presentation E) = P := by
  have h := Over.w a
  change a.left ≫ q.app i = necklaceUnder.map P.hom at h
  have hhom : ((projection E q).obj
      (⟨i, CostructuredArrow.mk a.left⟩ : Presentation E)).hom = P.hom :=
    NecklaceCode.Hom.ext (congrArg (fun f ↦ f.right) h)
  rcases P with ⟨S, ⟨⟨⟩⟩, p⟩
  change Over.mk _ = Over.mk p
  exact congrArg Over.mk hhom

private def object (A : C E q P) : F E q P :=
  ⟨⟨A.fst, CostructuredArrow.mk A.snd.left⟩, native_eq E q P A.fst A.snd⟩

private def arrow {A B : C E q P} (f : A ⟶ B) :
    (object E q P A).val ⟶ (object E q P B).val :=
  ⟨f.val, CostructuredArrow.homMk (𝟙 P.left) (by
    have h : A.snd.left ≫ E.map f.val = B.snd.left :=
      congrArg (fun g ↦ g.left) f.property
    change necklaceUnder.map (𝟙 P.left) ≫ B.snd.left = A.snd.left ≫ E.map f.val
    rw [necklaceUnder.map_id, Category.id_comp, h])⟩

private theorem arrow_lift {A B : C E q P} (f : A ⟶ B) :
    IsHomLift (projection E q) (𝟙 P) (arrow E q P f) := by
  apply IsHomLift.of_fac' _ _ _ (object E q P A).property (object E q P B).property
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, Over.eqToHom_left]
  change 𝟙 P.left = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
  simp only [Category.id_comp]

/-- Recover each actual presentation with the specified original native source. -/
def toFiber : C E q P ⥤ F E q P where
  obj := object E q P
  map f := ⟨arrow E q P f, arrow_lift E q P f⟩
  map_id A := by
    apply Fiber.hom_ext
    apply JTTargetCommaPullback.operator_ext
    · rfl
    · exact ((BoundaryNecklaceComma.sourceCode E).map_id (object E q P A).val).symm
  map_comp f g := by
    apply Fiber.hom_ext
    apply JTTargetCommaPullback.operator_ext
    · rfl
    · change (𝟙 P.left) = (BoundaryNecklaceComma.sourceCode E).map
        (arrow E q P f ≫ arrow E q P g)
      rw [(BoundaryNecklaceComma.sourceCode E).map_comp]
      exact (Category.id_comp _).symm

private theorem mapsOver_arrow {A B : C E q P} (f : object E q P A ⟶ object E q P B) :
    f.val.fiber.left = 𝟙 P.left := by
  letI : IsHomLift (projection E q) (𝟙 P) f.val := f.property
  have h := congrArg (fun k ↦ k.left) (IsHomLift.fac' (projection E q) (𝟙 P) f.val)
  simp only [Over.comp_left, Over.eqToHom_left] at h
  change f.val.fiber.left = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ at h
  simpa only [Category.id_comp] using h

private instance toFiber_full : (toFiber E q P).Full where
  map_surjective {A B} f := by
    let a : A.fst ⟶ B.fst := f.val.base
    have w : necklaceUnder.map f.val.fiber.left ≫ B.snd.left = A.snd.left ≫ E.map a :=
      CostructuredArrow.w f.val.fiber
    rw [mapsOver_arrow E q P f] at w
    have w' : B.snd.left = A.snd.left ≫ E.map a := by
      rw [necklaceUnder.map_id P.left] at w
      exact (Category.id_comp (B.snd.left : necklaceUnder.obj P.left ⟶ E.obj B.fst)).symm.trans w
    refine ⟨⟨a, Over.OverMorphism.ext w'.symm⟩, ?_⟩
    apply Fiber.hom_ext
    exact JTTargetCommaPullback.operator_ext rfl (mapsOver_arrow E q P f).symm

private instance toFiber_faithful : (toFiber E q P).Faithful where
  map_injective {A B} f g h := by
    apply CategoryOfElements.ext
    exact congrArg (fun a : object E q P A ⟶ object E q P B ↦ a.val.base) h

private theorem has_lift (A : F E q P) : ∃ B, (toFiber E q P).obj B = A := by
  rcases A with ⟨⟨i, Y⟩, hY⟩
  let L := (⟨i, Y⟩ : Presentation E)
  have hs : Y.left = P.left := congrArg (fun a : Over T ↦ a.left) hY
  let hf : necklaceUnder.obj P.left ⟶ E.obj i :=
    eqToHom (congrArg necklaceUnder.obj hs.symm) ≫ Y.hom
  have hh : hf ≫ q.app i = necklaceUnder.map P.hom := by
    have he : eqToHom hs.symm ≫ ((projection E q).obj L).hom = P.hom := by
      change eqToHom (congrArg (fun a : Over T ↦ a.left) hY).symm ≫
        ((projection E q).obj L).hom = P.hom
      rw [← Over.eqToHom_left]
      exact Over.w (eqToHom hY.symm)
    apply Under.UnderMorphism.ext
    have h := congrArg (fun f : P.left ⟶ T ↦ (necklaceUnder.map f).right) he
    change (necklaceUnder.map (eqToHom hs.symm ≫ ((projection E q).obj L).hom)).right =
      (necklaceUnder.map P.hom).right at h
    rw [necklaceUnder.map_comp, eqToHom_map] at h
    change (eqToHom _ ≫ (Y.hom ≫ q.app i)).right = _ at h
    exact (congrArg (fun f : necklaceUnder.obj P.left ⟶ necklaceUnder.obj T ↦ f.right)
      (Category.assoc _ _ _)).trans h
  refine ⟨⟨i, Over.homMk hf hh⟩, ?_⟩
  apply Subtype.ext
  change (⟨i, CostructuredArrow.mk hf⟩ : Presentation E) = ⟨i, Y⟩
  congr 1
  rcases Y with ⟨S, ⟨⟨⟩⟩, a⟩
  change S = P.left at hs
  subst S
  dsimp only [hf]
  rw [eqToHom_refl, Category.id_comp]
  rfl

/-- Fixing the native code and its map leaves exactly the category of all complete lifts. -/
def equivalence : C E q P ≌ F E q P := by
  letI : (toFiber E q P).EssSurj := Functor.essSurj_of_surj (has_lift E q P)
  letI : (toFiber E q P).IsEquivalence := {}
  exact (toFiber E q P).asEquivalence

end
end DaggerModels.PartII.JTNativeFiberElements
