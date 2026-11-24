import DaggerModelsPartII.OrderedSimplexLabelAugmentation
import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.WeightedReplacementHomotopy
import NerveHomotopy

/-!
# The full ordered simplex-label bar contracts to its endpoint-edge value

The coefficient at every chain is the entire simplicial label weight. The
contraction uses the two natural legs from ambient completion, with the
completion-unit leg an isomorphism on this particular ordered weight. No
contractibility of the native necklace category or arbitrary weights is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerNativeSimplicialReplacement
open DaggerNativeSimplicialReplacementCells
open DaggerNativeSimplicialReplacementReindex
open DaggerNativeSimplicialReplacementWeightsChange
open DaggerModels.PartII.SegalLocalizers
open DaggerModels.PartII.JTProjectiveOrderedFiberComparison
open DaggerModels.PartII.OrderedSimplexEndpointFiber
open DaggerModels.PartII.OrderedNecklaceVertexPoints
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrderedLabelBarContraction

noncomputable section

open DaggerModels.PartII.OrderedNecklaceLabelDiagram
open DaggerModels.PartII.WeightedReplacementHomotopy

private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev Source := ReverseDaggerSpace.{0}
private abbrev L (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) := orderedSimplexLabels W b
private abbrev bar (M : NCodeᵒᵖ ⥤ SSet.{0}) : SSet.{0} :=
  DaggerBisimplicialDiagonal.diag (replacement M)
private abbrev c : NCodeᵒᵖ := op (single 1)

/-- The literal constant chain at one object, in every outer degree. -/
private def constantChain (d : NCodeᵒᵖ) (q : SimplexCategoryᵒᵖ) :
    Chain (C := NCodeᵒᵖ) q :=
  (Functor.const (Fin (q.unop.len + 1))).obj d

/-- Reinsert an entire coefficient simplex on the constant chain at `d`. -/
def barConstantChainSection (M : NCodeᵒᵖ ⥤ SSet.{0}) (d : NCodeᵒᵖ) :
    M.obj d ⟶ bar M where
  app q x := ⟨constantChain d q, x⟩
  naturality {q r} β := by
    funext x
    change (⟨constantChain d r, (M.obj d).map β x⟩ : Cell M r r) =
      (bar M).map β ⟨constantChain d q, x⟩
    rw [DaggerBisimplicialDiagonal.diag_map_other_order]
    change (⟨constantChain d r, (M.obj d).map β x⟩ : Cell M r r) =
      ⟨(nerve NCodeᵒᵖ).map β (constantChain d q),
        (M.map (initialArrow β (constantChain d q))).app r
          ((M.obj d).map β x)⟩
    have hchain : (nerve NCodeᵒᵖ).map β (constantChain d q) =
        constantChain d r := by
      refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro i j f
      rfl
    have hinit : initialArrow β (constantChain d q) = 𝟙 d := rfl
    have hmap : M.map (𝟙 d) = 𝟙 (M.obj d) := M.map_id d
    rw [hinit, hmap]
    change (⟨constantChain d r, (M.obj d).map β x⟩ : Cell M r r) =
      ⟨(nerve NCodeᵒᵖ).map β (constantChain d q), (M.obj d).map β x⟩
    exact Sigma.ext hchain.symm HEq.rfl

/-- The actual augmentation of the whole native ordered-label replacement. -/
def orderedBarAugmentation (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    bar (L W b) ⟶ (L W b).obj c :=
  diagonalAugmentation (L W b) (orderedSimplexLabelAugmentation W b)

/-- At the selected edge, augmentation after the constant-chain section is identity. -/
theorem barSection_augmentation (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    barConstantChainSection (L W b) c ≫ orderedBarAugmentation W b =
      𝟙 ((L W b).obj c) := by
  apply NatTrans.ext
  funext q x
  change ((orderedSimplexLabelAugmentation W b).app c).app q x = x
  rw [orderedSimplexLabelAugmentation_single_one]
  rfl

/-- Change of the full parameter weight preserves composition on every cell. -/
private theorem diagonalChange_comp {M N P : NCodeᵒᵖ ⥤ SSet.{0}}
    (f : M ⟶ N) (g : N ⟶ P) :
    diagonalChange f ≫ diagonalChange g = diagonalChange (f ≫ g) := by
  apply NatTrans.ext
  rfl

/-- Change by the identity weight map is the literal identity of the full bar. -/
private theorem diagonalChange_id (M : NCodeᵒᵖ ⥤ SSet.{0}) :
    diagonalChange (𝟙 M) = 𝟙 (bar M) := by
  apply NatTrans.ext
  rfl

/-- The ordered completion unit gives an isomorphism of whole weighted bars. -/
def barCompletionIso (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    bar (completion.op ⋙ L W b) ≅ bar (L W b) where
  hom := diagonalChange (orderedCompletionUnitIso W b).hom
  inv := diagonalChange (orderedCompletionUnitIso W b).inv
  hom_inv_id := by
    rw [diagonalChange_comp, Iso.hom_inv_id, diagonalChange_id]
  inv_hom_id := by
    rw [diagonalChange_comp, Iso.inv_hom_id, diagonalChange_id]

/-- Reindexing every chain by completion, retaining its entire coefficient. -/
private def u (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    bar (completion.op ⋙ L W b) ⟶ bar (L W b) :=
  diagonalReindex completion.op (L W b)

/-- The unit-leg weighted homotopy has endpoint `barCompletionIso.hom`. -/
private def unitHomotopy (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    SSet.Homotopy (u W b) (barCompletionIso W b).hom := by
  let h := weightedReindexHomotopy (NatTrans.op completionUnit) (L W b)
  refine h.congr rfl ?_
  have hid : diagonalReindex (𝟭 NCodeᵒᵖ) (L W b) = 𝟙 _ := by
    apply NatTrans.ext
    rfl
  change diagonalChange (orderedCompletionUnitNat W b) ≫
    diagonalReindex (𝟭 NCodeᵒᵖ) (L W b) =
      diagonalChange (orderedCompletionUnitIso W b).hom
  rw [hid]
  rfl

/-- On ordered weights, the unit then the augmentation is the endpoint-edge map. -/
private theorem unit_augmentation_edge (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    orderedCompletionUnitNat W b ≫ orderedSimplexLabelAugmentation W b =
      orderedCompletionEdgeNat W b := by
  change (orderedCompletionUnitIso W b).hom ≫
    ((orderedCompletionUnitIso W b).inv ≫ orderedCompletionEdgeNat W b) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The edge-leg endpoint is the augmentation followed by the constant-chain section. -/
private def edgeHomotopy (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    SSet.Homotopy (u W b)
      ((barCompletionIso W b).hom ≫ orderedBarAugmentation W b ≫
        barConstantChainSection (L W b) c) := by
  let h := weightedReindexHomotopy (NatTrans.op completionEdge) (L W b)
  refine h.congr rfl ?_
  apply NatTrans.ext
  funext q x
  rcases x with ⟨chain, z⟩
  change (⟨chain ⋙ ((Functor.const NCode).obj (single 1)).op,
      ((L W b).map ((NatTrans.op completionEdge).app (first chain))).app q z⟩ :
        Cell (L W b) q q) =
    ⟨constantChain c q,
      (((orderedCompletionUnitIso W b).hom.app (first chain) ≫
        (orderedSimplexLabelAugmentation W b).app (first chain)).app q z)⟩
  have hchain : chain ⋙ ((Functor.const NCode).obj (single 1)).op =
      constantChain c q := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    rfl
  have hcoeff := congrFun
    (NatTrans.congr_app
      (NatTrans.congr_app (unit_augmentation_edge W b) (first chain)) q) z
  apply Sigma.ext hchain
  exact heq_of_eq hcoeff.symm

/-- The exact two-leg contraction, after the existing realization-singular functor. -/
private def contractionAfterR (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    SSet.Homotopy
      (DaggerNerveHomotopy.R.map (barCompletionIso W b).hom)
      (DaggerNerveHomotopy.R.map
        ((barCompletionIso W b).hom ≫ orderedBarAugmentation W b ≫
          barConstantChainSection (L W b) c)) := by
  let hη := (unitHomotopy W b).toTop.toSSet
  let hν := (edgeHomotopy W b).toTop.toSSet
  exact hη.symm.trans hν

/-- The actual augmentation is a homotopy equivalence after realization-singular. -/
def orderedBarAugmentationHomotopyEquiv (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    SSet.HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (bar (L W b)))
      (DaggerNerveHomotopy.R.obj ((L W b).obj c)) where
  hom := DaggerNerveHomotopy.R.map (orderedBarAugmentation W b)
  inv := DaggerNerveHomotopy.R.map (barConstantChainSection (L W b) c)
  homInvId := by
    let h := (contractionAfterR W b).precomp
      (DaggerNerveHomotopy.R.map (barCompletionIso W b).inv)
    have hleft :
        DaggerNerveHomotopy.R.map (barCompletionIso W b).inv ≫
          DaggerNerveHomotopy.R.map (barCompletionIso W b).hom = 𝟙 _ := by
      rw [← DaggerNerveHomotopy.R.map_comp, Iso.inv_hom_id,
        DaggerNerveHomotopy.R.map_id]
    have hright :
        DaggerNerveHomotopy.R.map (barCompletionIso W b).inv ≫
          DaggerNerveHomotopy.R.map
            ((barCompletionIso W b).hom ≫ orderedBarAugmentation W b ≫
              barConstantChainSection (L W b) c) =
        DaggerNerveHomotopy.R.map (orderedBarAugmentation W b) ≫
          DaggerNerveHomotopy.R.map (barConstantChainSection (L W b) c) := by
      rw [← DaggerNerveHomotopy.R.map_comp]
      have hh : (barCompletionIso W b).inv ≫
          ((barCompletionIso W b).hom ≫ orderedBarAugmentation W b ≫
            barConstantChainSection (L W b) c) =
          orderedBarAugmentation W b ≫ barConstantChainSection (L W b) c := by
        rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rw [hh, DaggerNerveHomotopy.R.map_comp]
    exact (h.congr hleft hright).symm
  invHomId := by
    apply SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq
    rw [← DaggerNerveHomotopy.R.map_comp, barSection_augmentation,
      DaggerNerveHomotopy.R.map_id]

/-- Kan weak equivalence of the realized-singular full ordered bar augmentation. -/
theorem orderedBarAugmentation_afterR_W (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    SSet.KanComplex.W
      (DaggerNerveHomotopy.R.map (orderedBarAugmentation W b)) :=
  SSet.KanComplex.W.homotopyEquivHom (orderedBarAugmentationHomotopyEquiv W b)

/-- The actual full ordered bar augmentation is weak with no fibrancy premise on W. -/
theorem orderedBarAugmentation_weak (W : Source)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) :
    WeakEquivalence (orderedBarAugmentation W b) := by
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  exact orderedBarAugmentation_afterR_W W b

/-- The full ordered label bar maps to the unchanged chosen raw endpoint fiber. -/
def orderedBarToChosenFiber (W : Source)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    bar (L W (boundaryPoint W x y)) ⟶
      ChosenHomotopyFiberComparison.chosenFiber (endpointArrow W) (point W x y) :=
  orderedBarAugmentation W (boundaryPoint W x y) ≫
    orderedSingleToChosenFiber W x y

/-- Under the retained underlying injective Kan fibrancy this actual composite is weak. -/
theorem orderedBarToChosenFiber_weak (W : Source)
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (x y : (row W ⦋0⦌).obj (op ⦋0⦌)) :
    WeakEquivalence (orderedBarToChosenFiber W x y) := by
  haveI : WeakEquivalence
      (orderedBarAugmentation W (boundaryPoint W x y)) :=
    orderedBarAugmentation_weak W (boundaryPoint W x y)
  haveI : WeakEquivalence (orderedSingleToChosenFiber W x y) :=
    orderedSingleToChosenFiber_weak W hW x y
  dsimp only [orderedBarToChosenFiber]
  infer_instance

end
end DaggerModels.PartII.OrderedLabelBarContraction
