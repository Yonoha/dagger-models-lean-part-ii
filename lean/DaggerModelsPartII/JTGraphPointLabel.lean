import DaggerModelsPartII.JTGraphLiftTransport
import DaggerModelsPartII.JTParameterZero
import ChosenNecklaceIntervalSingle

/-!
# Ordered labels at a degenerate native boundary descend to degree zero
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphPointLabel

open NecklaceCode OrderedNecklaceLabelDiagram ReversalDiscreteFreeColimits
open JTProjectiveOrderedFiberComparison JTGraphLiftTransport

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}

/-- Coincidence of the two ordered vertices forces the code to be a point. -/
theorem length_eq_zero_of_endpoints_eq (T : NecklaceCode)
    (h : NecklaceCode.first.{0} T = NecklaceCode.last.{0} T) : T.len = 0 := by
  have hv := congrArg (fun a ↦ (T.verticesEquiv a).down.val) h
  simpa only [NecklaceCode.first, NecklaceCode.last, Equiv.apply_symm_apply,
    Fin.val_last] using hv.symm

private theorem restriction_mono (W : Source) (T : NecklaceCode) (h : T.len = 0) :
    Mono ((necklaceBoundaryRestriction W).app (op T)) := by
  have hc : T = single 0 :=
    (code_eq_point_of_zero T h).trans (code_eq_point_of_zero (single 0) rfl).symm
  let e : T.toSSet ≅ (Δ[0] : SSet.{0}) :=
    eqToIso (congrArg NecklaceCode.toSSet hc) ≪≫ singleIso 0
  let v : (Δ[0] : SSet.{0}) ⟶ T.toSSet := SSet.yonedaEquiv.symm T.first
  have hv : v = e.inv :=
    (IsTerminal.ofIso SSet.stdSimplex.isTerminalObj₀ e.symm).hom_ext _ _
  letI : IsIso v := by
    rw [hv]
    infer_instance
  let s : F.obj T.toSSet ⟶ boundary := inv (F.map v) ≫ coprod.inl
  have hs : s ≫ boundaryNecklace T = 𝟙 _ := by
    change (inv (F.map v) ≫ coprod.inl) ≫
      coprod.desc (F.map v) (F.map (SSet.yonedaEquiv.symm T.last)) = 𝟙 _
    rw [Category.assoc, coprod.inl_desc, IsIso.inv_hom_id]
  have hh : diagramMappingPrecomp (boundaryNecklace T) W ≫
      diagramMappingPrecomp s W = 𝟙 _ := by
    rw [← diagramMappingPrecomp_comp, hs, diagramMappingPrecomp_id]
  change Mono (diagramMappingPrecomp (boundaryNecklace T) W)
  constructor
  intro A f g hfg
  have hfg' := congrArg (fun u : A ⟶ diagramMappingSpace boundary W ↦
    u ≫ diagramMappingPrecomp s W) hfg
  simpa only [Category.assoc, hh, Category.comp_id] using hfg'

/-- An ordered label on a zero-length code is determined by its boundary. -/
theorem label_subsingleton (W : Source) (T : NecklaceCode) (h : T.len = 0)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (k : SimplexCategory) :
    Subsingleton (((orderedNecklaceLabels W b).obj (op T)).obj (op k)) := by
  let r := (necklaceBoundaryRestriction W).app (op T)
  haveI : Mono r := restriction_mono W T h
  constructor
  intro a a'
  change (a : (pullback r b).obj (op k)) = a'
  apply SSet.yonedaEquiv.symm.injective
  apply (cancel_mono (pullback.snd r b)).mp
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The original label of a degenerate code is pulled back from degree zero. -/
theorem descends_zero (W : Source) (T : NecklaceCode)
    (h : NecklaceCode.first.{0} T = NecklaceCode.last.{0} T)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W b).obj (op T)).obj (op k)) :
    ∃ z₀ : ((orderedNecklaceLabels W b).obj (op T)).obj (op ⦋0⦌),
      ((orderedNecklaceLabels W b).obj (op T)).map
        (SimplexCategory.isTerminalZero.from k).op z₀ = z := by
  let L := (orderedNecklaceLabels W b).obj (op T)
  refine ⟨L.map (SimplexCategory.const ⦋0⦌ k 0).op z, ?_⟩
  exact (label_subsingleton W T (length_eq_zero_of_endpoints_eq T h) b k).elim _ _

end

end DaggerModels.PartII.JTGraphPointLabel
