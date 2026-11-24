import DaggerModelsPartII.JTComposedPrismLabels
import DaggerModelsPartII.JTWhiskerEdgeCoefficient
import DaggerModelsPartII.JTJointEndpointRelativeLift

/-! Exact realization formulas on arbitrary covered graph domains. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTWhiskerEdgeGraphRaw

open JTProjectiveOrderedFiberComparison (row)
open JTNecklaceLabelRealization (realizedLabel realizedLabel_natural_k realizedLabel_natural_X)
open ReversalDiscreteFreeColimits

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev D := discreteFree.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) {X : SSet.{0}} {T : NecklaceCode} {k l : SimplexCategory}

/-- Coefficient restriction preserves raw evaluation on an arbitrary graph domain. -/
theorem coefficient_reindex (α : k ⟶ l) (h : X ⟶ T.toSSet) (p : X ⟶ J.obj k)
    (c : std.obj l ⟶ diagramMappingSpace (D.obj T.toSSet) W) :
    lift h (p ≫ J.map α) ≫ realizedLabel T.toSSet W l (SSet.yonedaEquiv c) =
      lift h p ≫ realizedLabel T.toSSet W k (SSet.yonedaEquiv (std.map α ≫ c)) := by
  have hp : lift h (p ≫ J.map α) = lift h p ≫ (𝟙 T.toSSet ⊗ₘ J.map α) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, Category.comp_id, lift_fst]
    · simp only [Category.assoc, tensorHom_snd, lift_snd_assoc, lift_snd]
  rw [hp, Category.assoc, realizedLabel_natural_k, SSet.yonedaEquiv_map_comp]
  rfl

/-- Restriction to either native piece is valid on every covered graph simplex. -/
theorem native_restrict {S : NecklaceCode} (i : S.toSSet ⟶ T.toSSet)
    (h : X ⟶ S.toSSet) (p : X ⟶ J.obj k)
    (c : std.obj k ⟶ diagramMappingSpace (D.obj T.toSSet) W) :
    lift (h ≫ i) p ≫ realizedLabel T.toSSet W k (SSet.yonedaEquiv c) =
      lift h p ≫ realizedLabel S.toSSet W k
        (SSet.yonedaEquiv (c ≫ diagramMappingPrecomp (D.map i) W)) := by
  have hp : lift (h ≫ i) p = lift h p ≫ (i ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, lift_fst_assoc, lift_fst]
    · simp only [Category.assoc, tensorHom_snd, Category.comp_id, lift_snd]
  rw [hp, Category.assoc, realizedLabel_natural_X, SSet.yonedaEquiv_comp]
  rfl

/-- An edge whose coefficient is the identity on a face has constant joint raw
value whenever the entire graph parameter factors through that face. -/
theorem identity_edge (z : Vertex W) (u : k ⟶ l) (e : std.obj l ⟶ row W ⦋1⦌)
    (he : std.map u ≫ e = JTJointEndpointRelativeLift.identityOnFace W z)
    (h : X ⟶ (NecklaceCode.single 1).toSSet) (p : X ⟶ J.obj k) :
    lift h (p ≫ J.map u) ≫
        realizedLabel (NecklaceCode.single 1).toSSet W l
          (SSet.yonedaEquiv (e ≫ TwoBeadEndpointLabel.edgeLabelFromRow W)) =
      h ≫ term (NecklaceCode.single 1).toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  rw [coefficient_reindex]
  have hc := JTWhiskerEdgeCoefficient.onFace W u z e he
  rw [hc]
  have hr := JTComposedPrismLabels.rawProduct_constant W z (NecklaceCode.single 1)
    (snd (NecklaceCode.single 1).toSSet (J.obj k))
  dsimp only [JTComposedPrismLabels.rawProduct, JTBinaryPrismRealization.realizeProduct] at hr
  rw [lift_fst_snd, Category.id_comp] at hr
  rw [hr, lift_fst_assoc]

end
end DaggerModels.PartII.JTWhiskerEdgeGraphRaw
