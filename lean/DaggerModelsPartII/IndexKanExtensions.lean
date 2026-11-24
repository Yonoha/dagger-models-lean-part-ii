import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Limits

/-! Pointwise change of index on simplicial presheaves and its action on representables. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory

universe v w

namespace DaggerModels.PartII

noncomputable section

variable {C D : Type v} [SmallCategory C] [SmallCategory D]

/-- A presheaf of sets viewed as a presheaf of discrete simplicial sets. -/
def discretePresheaf (C : Type v) [SmallCategory C] :
    (Cᵒᵖ ⥤ Type (max v w)) ⥤ (Cᵒᵖ ⥤ SSet.{max v w}) :=
  (whiskeringRight _ _ _).obj (Functor.const SimplexCategoryᵒᵖ)

/-- The simplicial presheaves represented by objects of the index category. -/
def simplicialYoneda (C : Type v) [SmallCategory C] :
    C ⥤ (Cᵒᵖ ⥤ SSet.{max v w}) :=
  uliftYoneda.{max v w} ⋙ discretePresheaf C

variable (F : C ⥤ D)

local instance leftKanExtensions :
    ∀ W : Cᵒᵖ ⥤ SSet.{max v w}, F.op.HasLeftKanExtension W := by
  intro W
  letI : HasColimitsOfSize.{v, v} SSet.{max v w} := hasColimitsOfSizeShrink.{v, v, w, w} _
  letI : F.op.HasPointwiseLeftKanExtension W := fun _ ↦ inferInstance
  infer_instance

local instance rightKanExtensions :
    ∀ W : Cᵒᵖ ⥤ SSet.{max v w}, F.op.HasRightKanExtension W := by
  intro W
  letI : HasLimitsOfSize.{v, v} SSet.{max v w} := hasLimitsOfSizeShrink.{v, v, w, w} _
  letI : F.op.HasPointwiseRightKanExtension W := fun _ ↦ inferInstance
  infer_instance

/-- Restriction of simplicial presheaves along the opposite of the index functor. -/
def restrictIndex : (Dᵒᵖ ⥤ SSet.{max v w}) ⥤ (Cᵒᵖ ⥤ SSet.{max v w}) :=
  (whiskeringLeft _ _ _).obj F.op

/-- Extension of simplicial presheaves by pointwise left Kan extension. -/
def extendIndexLeft : (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ (Dᵒᵖ ⥤ SSet.{max v w}) :=
  F.op.lan

/-- Extension of simplicial presheaves by pointwise right Kan extension. -/
def extendIndexRight : (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ (Dᵒᵖ ⥤ SSet.{max v w}) :=
  F.op.ran

/-- Left extension is left adjoint to restriction. -/
def extendIndexLeftAdjunction : extendIndexLeft F ⊣ restrictIndex F :=
  F.op.lanAdjunction _

/-- Restriction is left adjoint to right extension. -/
def extendIndexRightAdjunction : restrictIndex F ⊣ extendIndexRight F :=
  F.op.ranAdjunction _

@[simp]
theorem restrictIndex_obj_obj (W : Dᵒᵖ ⥤ SSet.{max v w}) (c : C) :
    ((restrictIndex F).obj W).obj (op c) = W.obj (op (F.obj c)) := rfl

/-- Surjectivity on objects gives preservation and reflection of every levelwise
morphism property, in particular Kan weak equivalences, Kan fibrations and monomorphisms. -/
theorem restrictIndex_levelwise_iff (hF : Function.Surjective F.obj)
    (P : MorphismProperty SSet.{max v w}) {W W' : Dᵒᵖ ⥤ SSet.{max v w}} (f : W ⟶ W') :
    P.functorCategory Cᵒᵖ ((restrictIndex F).map f) ↔ P.functorCategory Dᵒᵖ f := by
  constructor
  · intro hf d
    obtain ⟨c, hc⟩ := hF d.unop
    have h := hf (op c)
    change P (f.app (op (F.obj c))) at h
    have hd : op (F.obj c) = d := congrArg op hc
    change P (f.app d)
    rw [← hd]
    exact h
  · intro hf c
    exact hf (F.op.obj c)

/-- Left extension sends the simplicial representable at `c` to that at `F.obj c`,
naturally in `c`. -/
def extendIndexLeft_simplicialYoneda :
    simplicialYoneda.{v, w} C ⋙ extendIndexLeft.{v, w} F ≅
      F ⋙ simplicialYoneda.{v, w} D := by
  let discrete := (Functor.const SimplexCategoryᵒᵖ : Type (max v w) ⥤ SSet.{max v w})
  let comparison := discrete.lanCompIsoOfPreserves F.op
  let yonedaComparison := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{w} F
  exact (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft _ comparison.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight yonedaComparison.symm _ ≪≫
    Functor.associator _ _ _

/-- Under the comparison on representables, the unit acts on each simplex
of the discrete value by applying the original index functor to the morphism. -/
theorem extendIndexLeft_unit_simplicialYoneda (c a : C) (n : SimplexCategoryᵒᵖ)
    (f : a ⟶ c) :
    (((extendIndexLeftAdjunction.{v, w} F).unit.app ((simplicialYoneda.{v, w} C).obj c) ≫
      (restrictIndex.{v, w} F).map ((extendIndexLeft_simplicialYoneda.{v, w} F).hom.app c)).app
      (op a)).app n (ULift.up f) = ULift.up (F.map f) := by
  let G : Type (max v w) ⥤ SSet.{max v w} := Functor.const SimplexCategoryᵒᵖ
  let X := (uliftYoneda.{max v w} (C := C)).obj c
  letI : G.PreservesLeftKanExtension X F.op := by
    dsimp [G, X]
    infer_instance
  have h₁ := G.leftKanExtensionCompIsoOfPreserves_inv_fac_app X F.op (op a)
  have h₂ := (F.op.lan.obj X).descOfIsLeftKanExtension_fac_app
    (F.op.lanUnit.app X) _ (uliftYonedaMap.{w} F c) (op a)
  have h₃ := congrFun (congrArg (fun g ↦ g.app n) h₁) (ULift.up f)
  have h₄ := congrFun h₂ (ULift.up f)
  dsimp [G, X] at h₃ h₄
  rw [show (extendIndexLeftAdjunction.{v, w} F).unit = F.op.lanUnit from
    F.op.lanAdjunction_unit _]
  simpa [extendIndexLeft_simplicialYoneda, simplicialYoneda, discretePresheaf,
    lanCompIsoOfPreserves, Presheaf.compULiftYonedaIsoULiftYonedaCompLan,
    uliftYonedaMap] using congrArg
      (fun z ↦ (((Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{w} F).inv.app c).app
        (op (F.obj a))) z) h₃ |>.trans h₄

/-- A faithful index functor gives a levelwise monomorphism at each representable unit. -/
theorem extendIndexLeft_unit_simplicialYoneda_mono [F.Faithful] (c : C) :
    Mono ((extendIndexLeftAdjunction.{v, w} F).unit.app ((simplicialYoneda.{v, w} C).obj c)) := by
  let η := (extendIndexLeftAdjunction.{v, w} F).unit.app ((simplicialYoneda.{v, w} C).obj c)
  let e := (restrictIndex.{v, w} F).map ((extendIndexLeft_simplicialYoneda.{v, w} F).hom.app c)
  haveI : Mono (η ≫ e) := by
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro a
    obtain ⟨a⟩ := a
    apply (NatTrans.mono_iff_mono_app _).mpr
    intro n
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro ⟨f⟩ ⟨g⟩ h
    change ((η ≫ e).app (op a)).app n (ULift.up f) =
      ((η ≫ e).app (op a)).app n (ULift.up g) at h
    rw [extendIndexLeft_unit_simplicialYoneda F, extendIndexLeft_unit_simplicialYoneda F] at h
    exact congrArg ULift.up (F.map_injective (congrArg ULift.down h))
  exact mono_of_mono_fac (rfl : η ≫ e = η ≫ e)

/-- Levelwise product of a simplicial presheaf with a fixed simplicial set. -/
def simplicialPresheafProductRight (C : Type v) [SmallCategory C] (K : SSet.{max v w}) :
    (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ (Cᵒᵖ ⥤ SSet.{max v w}) :=
  (whiskeringRight _ _ _).obj (tensorRight K)

local instance tensorRight_preservesColimits (K : SSet.{max v w}) :
    PreservesColimitsOfSize.{v, v} (tensorRight K) := by
  letI : BraidedCategory SSet.{max v w} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{v, v} (tensorLeft K) :=
    (ihom.adjunction K).leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight K)

local instance tensorRight_preservesLeftKanExtensions (K : SSet.{max v w}) :
    (tensorRight K).PreservesLeftKanExtensions F.op := by
  intro V
  letI : HasColimitsOfSize.{v, v} SSet.{max v w} := hasColimitsOfSizeShrink.{v, v, w, w} _
  letI : F.op.HasPointwiseLeftKanExtension V := fun _ ↦ inferInstance
  letI : (tensorRight K).PreservesPointwiseLeftKanExtension V F.op :=
    fun _ ↦ inferInstance
  infer_instance

/-- Left extension commutes with levelwise product by a fixed simplicial set. -/
def extendIndexLeft_productRight (K : SSet.{max v w}) :
    simplicialPresheafProductRight.{v, w} C K ⋙ extendIndexLeft.{v, w} F ≅
      extendIndexLeft.{v, w} F ⋙ simplicialPresheafProductRight.{v, w} D K :=
  ((tensorRight K).lanCompIsoOfPreserves F.op).symm

/-- After transporting along the product comparison, the unit of the left
extension at `V × K` is the levelwise product of the unit at `V` with `K`. -/
theorem extendIndexLeft_unit_productRight (V : Cᵒᵖ ⥤ SSet.{max v w}) (K : SSet.{max v w}) :
    (extendIndexLeftAdjunction.{v, w} F).unit.app
        ((simplicialPresheafProductRight.{v, w} C K).obj V) ≫
      (restrictIndex.{v, w} F).map ((extendIndexLeft_productRight.{v, w} F K).hom.app V) =
    (simplicialPresheafProductRight.{v, w} C K).map
      ((extendIndexLeftAdjunction.{v, w} F).unit.app V) := by
  rw [show (extendIndexLeftAdjunction.{v, w} F).unit = F.op.lanUnit from F.op.lanAdjunction_unit _]
  apply NatTrans.ext
  funext c
  exact (tensorRight K).leftKanExtensionCompIsoOfPreserves_inv_fac_app V F.op c

end

end DaggerModels.PartII
