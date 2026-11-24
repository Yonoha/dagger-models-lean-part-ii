import DaggerModelsPartII.OrderedSimplexLabelAugmentation
import DaggerModelsPartII.ReplacementTotalElements
import NerveHomotopy

/-! The literal one-edge inclusion into the original two-index simplex labels. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedSingleEdgeElements

open OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W)

local notation "coeffs" => orderedSimplexLabels W b
local notation "El" => Functor.Elements (ReplacementTotalElements.totalPresheaf coeffs)
local notation "one" => op (single 1)
local notation "aug" => orderedSimplexLabelAugmentation W b

private theorem total_map {i j : El} (f : i ⟶ j) :
    ((coeffs).obj j.fst.1).map f.val.2
      (((coeffs).map f.val.1).app i.fst.2 i.snd) = j.snd :=
  f.property

/-- Place the literal ordered one-edge label at its original two indices. -/
def inclusion : ((coeffs).obj one).Elements ⥤ El where
  obj i := ⟨(one, i.fst), i.snd⟩
  map {i j} f := ⟨(𝟙 one, f.val), by
    change ((coeffs).obj one).map f.val (((coeffs).map (𝟙 one)).app i.fst i.snd) = j.snd
    rw [(coeffs).map_id]
    exact f.property⟩
  map_id _ := rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    apply Prod.ext
    · exact (Category.id_comp _).symm
    · rfl

/-- Evaluate a complete original simplex label at the distinguished edge. -/
def retract : El ⥤ ((coeffs).obj one).Elements where
  obj i := ⟨i.fst.2, ((aug).app i.fst.1).app i.fst.2 i.snd⟩
  map {i j} f := ⟨f.val.2, by
    change ((coeffs).obj one).map f.val.2 (((aug).app i.fst.1).app i.fst.2 i.snd) =
      ((aug).app j.fst.1).app j.fst.2 j.snd
    have h₁ := congrFun (NatTrans.congr_app ((aug).naturality f.val.1) i.fst.2) i.snd
    have h₂ := congrFun (((aug).app j.fst.1).naturality f.val.2)
      (((coeffs).map f.val.1).app i.fst.2 i.snd)
    change ((aug).app j.fst.1).app i.fst.2
      (((coeffs).map f.val.1).app i.fst.2 i.snd) =
        ((aug).app i.fst.1).app i.fst.2 i.snd at h₁
    change ((aug).app j.fst.1).app j.fst.2
      (((coeffs).obj j.fst.1).map f.val.2 (((coeffs).map f.val.1).app i.fst.2 i.snd)) =
        ((coeffs).obj one).map f.val.2
          (((aug).app j.fst.1).app i.fst.2 (((coeffs).map f.val.1).app i.fst.2 i.snd)) at h₂
    rw [← h₁, ← h₂, total_map W b f]⟩
  map_id _ := rfl
  map_comp _ _ := rfl

local notation "unitIso" => orderedCompletionUnitIso W b

private def complete : El ⥤ El where
  obj i := ⟨((completion.op).obj i.fst.1, i.fst.2), ((unitIso).inv.app i.fst.1).app i.fst.2 i.snd⟩
  map {i j} f := ⟨((completion.op).map f.val.1, f.val.2), by
    change ((coeffs).obj ((completion.op).obj j.fst.1)).map f.val.2
      (((coeffs).map ((completion.op).map f.val.1)).app i.fst.2
        (((unitIso).inv.app i.fst.1).app i.fst.2 i.snd)) =
      ((unitIso).inv.app j.fst.1).app j.fst.2 j.snd
    have h₁ := congrFun (NatTrans.congr_app ((unitIso).inv.naturality f.val.1) i.fst.2) i.snd
    have h₂ := congrFun (((unitIso).inv.app j.fst.1).naturality f.val.2)
      (((coeffs).map f.val.1).app i.fst.2 i.snd)
    change ((unitIso).inv.app j.fst.1).app i.fst.2
      (((coeffs).map f.val.1).app i.fst.2 i.snd) =
        ((coeffs).map ((completion.op).map f.val.1)).app i.fst.2
          (((unitIso).inv.app i.fst.1).app i.fst.2 i.snd) at h₁
    change ((unitIso).inv.app j.fst.1).app j.fst.2
      (((coeffs).obj j.fst.1).map f.val.2 (((coeffs).map f.val.1).app i.fst.2 i.snd)) =
        ((coeffs).obj ((completion.op).obj j.fst.1)).map f.val.2
          (((unitIso).inv.app j.fst.1).app i.fst.2
            (((coeffs).map f.val.1).app i.fst.2 i.snd)) at h₂
    rw [← h₁, ← h₂, total_map W b f]⟩
  map_id i := by
    apply CategoryOfElements.ext
    exact Prod.ext ((completion.op).map_id i.fst.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext ((completion.op).map_comp f.val.1 g.val.1) rfl

private def toOriginal : complete W b ⟶ 𝟭 El where
  app i := ⟨((NatTrans.op completionUnit).app i.fst.1, 𝟙 i.fst.2), by
    change ((coeffs).obj i.fst.1).map (𝟙 i.fst.2)
      (((unitIso).hom.app i.fst.1).app i.fst.2
        (((unitIso).inv.app i.fst.1).app i.fst.2 i.snd)) = i.snd
    rw [FunctorToTypes.map_id_apply]
    exact congrFun (NatTrans.congr_app
      (NatTrans.congr_app (unitIso).inv_hom_id i.fst.1) i.fst.2) i.snd⟩
  naturality {i j} f := by
    apply CategoryOfElements.ext
    exact Prod.ext ((NatTrans.op completionUnit).naturality f.val.1)
      ((Category.comp_id _).trans (Category.id_comp _).symm)

private def toEdge : complete W b ⟶ retract W b ⋙ inclusion W b where
  app i := ⟨((NatTrans.op completionEdge).app i.fst.1, 𝟙 i.fst.2), by
    change ((coeffs).obj one).map (𝟙 i.fst.2)
      (((orderedCompletionEdgeNat W b).app i.fst.1).app i.fst.2
        (((unitIso).inv.app i.fst.1).app i.fst.2 i.snd)) =
      ((aug).app i.fst.1).app i.fst.2 i.snd
    rw [FunctorToTypes.map_id_apply]
    rfl⟩
  naturality {i j} f := by
    apply CategoryOfElements.ext
    exact Prod.ext ((NatTrans.op completionEdge).naturality f.val.1)
      ((Category.comp_id _).trans (Category.id_comp _).symm)

private theorem inclusion_retract : inclusion W b ⋙ retract W b = 𝟭 _ := by
  have h (i : ((coeffs).obj one).Elements) :
      (inclusion W b ⋙ retract W b).obj i = i := by
    refine Functor.Elements.ext ((inclusion W b ⋙ retract W b).obj i) i rfl ?_
    rw [eqToHom_refl, FunctorToTypes.map_id_apply]
    change ((aug).app one).app i.fst i.snd = i.snd
    rw [orderedSimplexLabelAugmentation_single_one]
    rfl
  refine CategoryTheory.Functor.ext h ?_
  intro i j f
  apply CategoryOfElements.ext
  have hc {a z : ((coeffs).obj one).Elements} (e : a = z) :
      (eqToHom e : a ⟶ z).val = eqToHom (congrArg Sigma.fst e) := by
    cases e
    rfl
  simp only [CategoryOfElements.comp_val, hc]
  change f.val = eqToHom _ ≫ f.val ≫ eqToHom _
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

/-- The actual one-edge inclusion is a Kan weak equivalence of nerves. -/
theorem inclusion_weak : WeakEquivalence (nerveMap (inclusion W b)) :=
  (weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW (inclusion W b) (retract W b)
      (Relation.EqvGen.rel _ _ ⟨eqToHom (inclusion_retract W b)⟩)
      (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨toEdge W b⟩))
        (Relation.EqvGen.rel _ _ ⟨toOriginal W b⟩)))

end

end DaggerModels.PartII.OrderedSingleEdgeElements
