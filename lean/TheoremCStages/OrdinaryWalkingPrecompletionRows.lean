import OrdinaryWalkingPrecompletionLabels
import OrdinarySegalVerticalPrecompletion
import DaggerModelsPartII.JTCodiscreteParameterPairing

/-!
# The corrected precompletion of the discrete walking groupoid, row by row

At horizontal degree `n`, a vertical `q`-simplex is a map
`E[q] ⊗ Δ[n] ⟶ E[1]`. Its codiscrete target makes this exactly a function
`Fin (q+1) → (Fin (n+1) → Fin 2)`, with the actual vertical operators.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinaryWalkingPrecompletionRows

open OrdinaryCSSLocalization (walkingSpace)
open OrdinaryWalkingPrecompletionLabels
open DaggerOriginalCodiscreteNerveInjective (codiscreteNerve)

noncomputable section

private abbrev E (q : SimplexCategory) := GroupoidSimplex.parameter.obj q
private abbrev T (n : SimplexCategory) := Fin (n.len + 1) → Fin 2
private abbrev P := OrdinarySegalVerticalPrecompletion.precompletion walkingSpace

/-- A simplex of a codiscrete nerve is its full list of vertex labels. -/
def codiscreteSimplexEquiv (S : Type) (q : SimplexCategory) :
    (codiscreteNerve.obj S).obj (op q) ≃ (Fin (q.len + 1) → S) where
  toFun z i := (z.obj i).as
  invFun φ := Codiscrete.functor φ
  left_inv z := by
    apply nerve.ext_of_isThin
    funext i
    exact Codiscrete.ext rfl
  right_inv φ := by
    funext i
    rfl

/-- The actual zero-simplices of `E[q] ⊗ Δ[n]` are the two vertex coordinates. -/
def productLabelEquiv (n q : SimplexCategory) :
    ((E q ⊗ SSet.stdSimplex.obj n).obj (op ⦋0⦌) → Fin 2) ≃
      (Fin (q.len + 1) → T n) where
  toFun φ i j := φ ((parameterVertexEquiv q).symm i,
    SSet.stdSimplex.obj₀Equiv.symm j)
  invFun ψ z := ψ (parameterVertexEquiv q z.1) (SSet.stdSimplex.obj₀Equiv z.2)
  left_inv φ := by
    funext z
    rcases z with ⟨x, y⟩
    simp only [Equiv.symm_apply_apply]
  right_inv ψ := by
    funext i j
    simp only [Equiv.apply_symm_apply]

/-- The levelwise comparison keeps every word coordinate before reassembling the nerve. -/
def rowWordEquiv (n q : SimplexCategory) :
    (P.obj (op n)).obj (op q) ≃ (Fin (q.len + 1) → T n) :=
  (OrdinaryDiscreteMapping.levelEquiv
      (E q ⊗ SSet.stdSimplex.obj n) walkingSpace q).trans
    ((walkingHomEquiv (E q ⊗ SSet.stdSimplex.obj n)).trans
      (productLabelEquiv n q))

/-- The levelwise comparison retains the original completed-simplex target. -/
def rowLevelEquiv (n q : SimplexCategory) :
    (P.obj (op n)).obj (op q) ≃ (codiscreteNerve.obj (T n)).obj (op q) :=
  (rowWordEquiv n q).trans (codiscreteSimplexEquiv (T n) q).symm

private theorem parameterVertexEquiv_map {q r : SimplexCategory}
    (θ : r ⟶ q) (x : (E r).obj (op ⦋0⦌)) :
    parameterVertexEquiv q ((GroupoidSimplex.parameter.map θ).app (op ⦋0⦌) x) =
      θ.toOrderHom (parameterVertexEquiv r x) := by
  exact DaggerModels.PartII.JTCodiscreteParameterPairing.coord_map θ (op ⦋0⦌) x 0

private theorem level_parameter {A B : SSet.{0}} (f : A ⟶ B)
    (q : SimplexCategoryᵒᵖ)
    (s : (diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj B)
      walkingSpace).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv A walkingSpace q.unop)
        ((diagramMappingPrecomp (OrdinaryCSSLocalization.discrete.map f)
          walkingSpace).app q s) =
      f ≫ (OrdinaryDiscreteMapping.levelEquiv B walkingSpace q.unop) s := by
  have h := congrFun
    (NatTrans.congr_app
      (OrdinaryDiscreteMapping.mappingIso_natural f walkingSpace) q) s
  simpa only [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalPre,
    Equiv.coe_fn_mk] using h

private theorem level_vertical (A : SSet.{0})
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r)
    (s : (diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj A)
      walkingSpace).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv A walkingSpace r.unop)
        ((diagramMappingSpace (OrdinaryCSSLocalization.discrete.obj A)
          walkingSpace).map α s) =
      (OrdinaryDiscreteMapping.levelEquiv A walkingSpace q.unop) s := by
  have h := congrFun
    ((OrdinaryDiscreteMapping.mappingIso A walkingSpace).hom.naturality α) s
  simpa [OrdinaryDiscreteMapping.mappingIso,
    OrdinaryDiscreteMapping.levelEquiv,
    DaggerNativeBisimplicialHorizontalMapping.horizontalMapping,
    OrdinaryCSSLocalization.walkingSpace,
    OrdinaryCSSLocalization.discrete] using h

private theorem level_map (n : SimplexCategory)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (s : (P.obj (op n)).obj q) :
    (OrdinaryDiscreteMapping.levelEquiv
      (E r.unop ⊗ SSet.stdSimplex.obj n) walkingSpace r.unop)
        ((P.obj (op n)).map α s) =
      (GroupoidSimplex.parameter.map α.unop ▷ SSet.stdSimplex.obj n) ≫
        (OrdinaryDiscreteMapping.levelEquiv
          (E q.unop ⊗ SSet.stdSimplex.obj n) walkingSpace q.unop) s := by
  let f := GroupoidSimplex.parameter.map α.unop ▷ SSet.stdSimplex.obj n
  let u := ((OrdinarySegalHorizontalCotensor.pre
    (GroupoidSimplex.parameter.map α.unop) walkingSpace).app (op n)).app q s
  change (OrdinaryDiscreteMapping.levelEquiv
      (E r.unop ⊗ SSet.stdSimplex.obj n) walkingSpace r.unop)
        ((diagramMappingSpace
          (OrdinaryCSSLocalization.discrete.obj
            (E r.unop ⊗ SSet.stdSimplex.obj n)) walkingSpace).map α u) = _
  rw [level_vertical]
  exact level_parameter f q s

private theorem rowLevelEquiv_map (n : SimplexCategory)
    {q r : SimplexCategoryᵒᵖ} (α : q ⟶ r) (s : (P.obj (op n)).obj q) :
    rowLevelEquiv n r.unop ((P.obj (op n)).map α s) =
      (codiscreteNerve.obj (T n)).map α (rowLevelEquiv n q.unop s) := by
  apply (codiscreteSimplexEquiv (T n) r.unop).injective
  funext i j
  change (rowWordEquiv n r.unop ((P.obj (op n)).map α s)) i j =
    (rowWordEquiv n q.unop s) (α.unop.toOrderHom i) j
  change (walkingHomEquiv _
      ((OrdinaryDiscreteMapping.levelEquiv
        (E r.unop ⊗ SSet.stdSimplex.obj n) walkingSpace r.unop)
        ((P.obj (op n)).map α s)))
      ((parameterVertexEquiv r.unop).symm i, SSet.stdSimplex.obj₀Equiv.symm j) = _
  have h := congrArg (fun t ↦ (walkingHomEquiv
      (E r.unop ⊗ SSet.stdSimplex.obj n) t)
      ((parameterVertexEquiv r.unop).symm i, SSet.stdSimplex.obj₀Equiv.symm j))
    (level_map n α s)
  refine h.trans ?_
  have hpre := congrFun
    (walkingHomEquiv_pre
      (GroupoidSimplex.parameter.map α.unop ▷ SSet.stdSimplex.obj n)
      ((OrdinaryDiscreteMapping.levelEquiv
        (E q.unop ⊗ SSet.stdSimplex.obj n) walkingSpace q.unop) s))
    ((parameterVertexEquiv r.unop).symm i, SSet.stdSimplex.obj₀Equiv.symm j)
  refine hpre.trans ?_
  change (walkingHomEquiv (E q.unop ⊗ SSet.stdSimplex.obj n)
      ((OrdinaryDiscreteMapping.levelEquiv
        (E q.unop ⊗ SSet.stdSimplex.obj n) walkingSpace q.unop) s))
      (((GroupoidSimplex.parameter.map α.unop ▷ SSet.stdSimplex.obj n).app (op ⦋0⦌))
        ((parameterVertexEquiv r.unop).symm i, SSet.stdSimplex.obj₀Equiv.symm j)) =
    (walkingHomEquiv (E q.unop ⊗ SSet.stdSimplex.obj n)
      ((OrdinaryDiscreteMapping.levelEquiv
        (E q.unop ⊗ SSet.stdSimplex.obj n) walkingSpace q.unop) s))
      ((parameterVertexEquiv q.unop).symm (α.unop.toOrderHom i),
        SSet.stdSimplex.obj₀Equiv.symm j)
  apply congrArg (walkingHomEquiv (E q.unop ⊗ SSet.stdSimplex.obj n)
    ((OrdinaryDiscreteMapping.levelEquiv
      (E q.unop ⊗ SSet.stdSimplex.obj n) walkingSpace q.unop) s))
  change (((GroupoidSimplex.parameter.map α.unop).app (op ⦋0⦌))
      ((parameterVertexEquiv r.unop).symm i), SSet.stdSimplex.obj₀Equiv.symm j) = _
  apply Prod.ext
  · apply (parameterVertexEquiv q.unop).injective
    rw [parameterVertexEquiv_map]
    simp only [Equiv.apply_symm_apply]
  · rfl

/-- Every vertical operator agrees with restriction of the finite vertex word. -/
def rowIso (n : SimplexCategory) :
    P.obj (op n) ≅ codiscreteNerve.obj (T n) :=
  NatIso.ofComponents (fun q ↦ (rowLevelEquiv n q.unop).toIso) (by
    intro q r α
    funext s
    exact rowLevelEquiv_map n α s)

/-- The row is Kan, as it is the nerve of a nonempty codiscrete groupoid. -/
theorem row_kan (n : SimplexCategory) : (P.obj (op n)).KanComplex := by
  let p : codiscreteNerve.obj (T n) ⟶ (⊤_ SSet.{0}) := terminal.from _
  have : Nonempty (T n) := ⟨fun _ ↦ 0⟩
  have hp := DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    p terminalIsTerminal
  haveI : Fibration p := (fibration_iff p).mpr hp.1
  haveI : Fibration ((rowIso n).hom ≫ p) := inferInstance
  have : IsFibrant (P.obj (op n)) :=
    (isFibrant_iff_of_isTerminal ((rowIso n).hom ≫ p) terminalIsTerminal).mpr
      inferInstance
  infer_instance

/-- The row map to the terminal simplex is a weak equivalence. -/
theorem row_toTerminal_weak (n : SimplexCategory) :
    WeakEquivalence (terminal.from (P.obj (op n))) := by
  have : Nonempty (T n) := ⟨fun _ ↦ 0⟩
  let p : codiscreteNerve.obj (T n) ⟶ (⊤_ SSet.{0}) := terminal.from _
  have hp := DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration
    p terminalIsTerminal
  haveI : WeakEquivalence p := (weakEquivalence_iff p).mpr hp.2
  have h : (rowIso n).hom ≫ p = terminal.from (P.obj (op n)) :=
    terminalIsTerminal.hom_ext _ _
  rw [← h]
  infer_instance

#print axioms rowLevelEquiv
#print axioms rowIso
#print axioms row_kan
#print axioms row_toTerminal_weak

end

end DaggerModels.PartII.OrdinaryWalkingPrecompletionRows
