import DaggerModelsPartII.NecklaceSimplexCompletion

/-!
# Ordered ambient simplex label augmentation

For every actual boundary point, the ambient completion unit gives an isomorphism
on the ordered simplex label fiber. Its inverse and the literal endpoint edge
give a natural augmentation to the value at the one-bead edge. No fibrancy
hypothesis or weighted-bar weak-equivalence claim is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget
open DaggerModels.PartII.SegalLocalizers

namespace DaggerModels.PartII.OrderedNecklaceLabelDiagram

noncomputable section

private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev Source := ReverseDaggerSpace.{0}

/-- The ordered pullback map induced by the completion unit is an isomorphism. -/
theorem orderedSimplexLabels_completionUnit_isIso (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (T : NCode) :
    IsIso ((orderedSimplexLabels W b).map (completionUnitComponent T).op) := by
  haveI : IsIso ((simplexLabels W).map (completionUnitComponent T).op) := by
    rw [simplexLabels_map_completionUnit W T]
    exact IsIso.id _
  dsimp only [orderedSimplexLabels, orderedLabelDiagram]
  infer_instance

/-- The componentwise inverse is retained as a typed isomorphism. -/
def orderedCompletionUnitComponentIso (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (T : NCode) :
    (orderedSimplexLabels W b).obj (op (single T.len)) ≅
      (orderedSimplexLabels W b).obj (op T) := by
  letI := orderedSimplexLabels_completionUnit_isIso W b T
  exact asIso ((orderedSimplexLabels W b).map (completionUnitComponent T).op)

/-- The opposite completion unit transports the ordered labels naturally. -/
def orderedCompletionUnitNat (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    completion.op ⋙ orderedSimplexLabels W b ⟶ orderedSimplexLabels W b :=
  Functor.whiskerRight (NatTrans.op completionUnit) (orderedSimplexLabels W b)

/-- The completion unit is an isomorphism of ordered label diagrams. -/
def orderedCompletionUnitIso (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    completion.op ⋙ orderedSimplexLabels W b ≅ orderedSimplexLabels W b := by
  letI : IsIso (orderedCompletionUnitNat W b) :=
    (NatTrans.isIso_iff_isIso_app _).2 (by
      intro T
      change IsIso ((orderedSimplexLabels W b).map
        (completionUnitComponent T.unop).op)
      exact orderedSimplexLabels_completionUnit_isIso W b T.unop)
  exact asIso (orderedCompletionUnitNat W b)

/-- The literal endpoint edge acts naturally on ordered completed labels. -/
def orderedCompletionEdgeNat (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    completion.op ⋙ orderedSimplexLabels W b ⟶
      (Functor.const NCodeᵒᵖ).obj
        ((orderedSimplexLabels W b).obj (op (single 1))) where
  app T := (orderedSimplexLabels W b).map (completionEdgeComponent T.unop).op
  naturality {T U} f := by
    let L := orderedSimplexLabels W b
    have h := (NatTrans.op completionEdge).naturality f
    change (completion.map f.unop).op ≫ (completionEdgeComponent U.unop).op =
      (completionEdgeComponent T.unop).op ≫ 𝟙 _ at h
    change L.map (completion.map f.unop).op ≫
      L.map (completionEdgeComponent U.unop).op =
        L.map (completionEdgeComponent T.unop).op ≫ 𝟙 _
    calc
      L.map (completion.map f.unop).op ≫
          L.map (completionEdgeComponent U.unop).op =
        L.map ((completion.map f.unop).op ≫
          (completionEdgeComponent U.unop).op) := (L.map_comp _ _).symm
      _ = L.map ((completionEdgeComponent T.unop).op ≫ 𝟙 _) :=
        congrArg (fun q => L.map q) h
      _ = L.map (completionEdgeComponent T.unop).op ≫ 𝟙 _ := by simp

/-- The ordered ambient labels augment to their value at the literal endpoint edge. -/
def orderedSimplexLabelAugmentation (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    orderedSimplexLabels W b ⟶
      (Functor.const NCodeᵒᵖ).obj
        ((orderedSimplexLabels W b).obj (op (single 1))) :=
  (orderedCompletionUnitIso W b).inv ≫ orderedCompletionEdgeNat W b

/-- The augmentation component has the required inverse-unit then edge form. -/
theorem orderedSimplexLabelAugmentation_app (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (T : NCode) :
    (orderedSimplexLabelAugmentation W b).app (op T) =
      (orderedCompletionUnitComponentIso W b T).inv ≫
        (orderedSimplexLabels W b).map (completionEdgeComponent T).op := by
  have hIso : (orderedCompletionUnitIso W b).app (op T) =
      orderedCompletionUnitComponentIso W b T := by
    apply Iso.ext
    rfl
  change ((orderedCompletionUnitIso W b).app (op T)).inv ≫
    (orderedSimplexLabels W b).map (completionEdgeComponent T).op = _
  rw [hIso]

/-- At the one-bead edge the unit and endpoint edge are the same native map. -/
theorem completionEdgeComponent_single_one :
    completionEdgeComponent.{0} (single 1) =
      completionUnitComponent.{0} (single 1) := by
  apply NecklaceCode.Hom.ext
  change (singleIso.{0} 1).hom ≫ edgeToAmbient.{0} (single 1) ≫
      (singleIso.{0} 1).inv = (single 1).inclusion ≫ (singleIso.{0} 1).inv
  rw [singleIso_hom 1]
  have hedge : edgeToAmbient.{0} (single 1) = 𝟙 (Δ[1] : SSet.{0}) := by
    apply simplex01_hom_ext 1
    · rw [edgeToAmbient_first]
      rfl
    · rw [edgeToAmbient_last]
      rfl
  calc
    (single 1).inclusion ≫ edgeToAmbient.{0} (single 1) ≫ (singleIso.{0} 1).inv =
        (single 1).inclusion ≫ (𝟙 (Δ[1] : SSet.{0})) ≫
          (singleIso.{0} 1).inv :=
      congrArg (fun q => (single 1).inclusion ≫ q ≫ (singleIso.{0} 1).inv) hedge
    _ = (single 1).inclusion ≫ (singleIso.{0} 1).inv := by
      cat_disch

/-- The chosen one-bead value is fixed by the augmentation. -/
theorem orderedSimplexLabelAugmentation_single_one (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    (orderedSimplexLabelAugmentation W b).app (op (single 1)) =
      𝟙 ((orderedSimplexLabels W b).obj (op (single 1))) := by
  rw [orderedSimplexLabelAugmentation_app, completionEdgeComponent_single_one]
  change (orderedCompletionUnitComponentIso W b (single 1)).inv ≫
    (orderedCompletionUnitComponentIso W b (single 1)).hom = 𝟙 _
  exact Iso.inv_hom_id _

end
end DaggerModels.PartII.OrderedNecklaceLabelDiagram
