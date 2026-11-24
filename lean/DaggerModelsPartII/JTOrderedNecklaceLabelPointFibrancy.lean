import DaggerModelsPartII.JTGraphPointLabel

/-!
# Fibrancy of an inhabited ordered label space on a point necklace

An actual label on a zero-length code determines a vertex. Every simplex of
the ordered label space is then unique, so the space is terminal and fibrant.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrderedNecklaceLabelPointFibrancy

open OrderedNecklaceLabelDiagram

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- An actual label on a point necklace makes its ordered label space terminal. -/
def labelIsTerminal (W : Source) (T : NecklaceCode) (h : T.len = 0)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W b).obj (op T)).obj (op k)) :
    IsTerminal ((orderedNecklaceLabels W b).obj (op T)) := by
  let L := (orderedNecklaceLabels W b).obj (op T)
  let z₀ : L.obj (op ⦋0⦌) := L.map (SimplexCategory.const ⦋0⦌ k 0).op z
  apply IsTerminal.ofUniqueHom
    (fun X ↦ SSet.stdSimplex.isTerminalObj₀.from X ≫ SSet.yonedaEquiv.symm z₀)
  intro X f
  apply NatTrans.ext
  funext n
  funext s
  exact (JTGraphPointLabel.label_subsingleton W T h b n.unop).elim _ _

/-- An inhabited ordered label space on a zero-length code is Kan fibrant. -/
theorem label_isFibrant (W : Source) (T : NecklaceCode) (h : T.len = 0)
    (b : (Δ[0] : SSet.{0}) ⟶ boundaryLabels W) (k : SimplexCategory)
    (z : ((orderedNecklaceLabels W b).obj (op T)).obj (op k)) :
    IsFibrant ((orderedNecklaceLabels W b).obj (op T)) := by
  let X := (orderedNecklaceLabels W b).obj (op T)
  let hX : IsTerminal X := labelIsTerminal W T h b k z
  haveI : IsIso (terminal.from X) := by
    let e := hX.uniqueUpToIso (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))
    have he : terminal.from X = e.hom := terminalIsTerminal.hom_ext _ _
    rw [he]
    infer_instance
  change Fibration (terminal.from X)
  infer_instance

end

end DaggerModels.PartII.JTOrderedNecklaceLabelPointFibrancy
