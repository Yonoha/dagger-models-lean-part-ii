import DaggerModelsPartII.JTEndpointRowGraphOperators

/-! The joint normalization spaces of all exact endpoint-preserving mixed graphs. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTEndpointRowGraphNormalization

open OrdinaryJTRealization (realization)
open JTReversalInput JTProjectiveOrderedFiberComparison JTMixedGraphEndpointLifts
open JTEndpointRowGraphResolution JTEndpointRowGraphOperators
open JTRowGraphNormalizationDiagram (coefficient leftEndpoint rightEndpoint point_at_weak)
open JTOrdinaryGraphNormalizationSpace JTFixedLiftSpacePrecomp

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (m : SimplexCategory) := SSet.stdSimplex.{0}.obj m
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {W : Source} {d : ℕ} {q : Δ ⦋d⦌ ⟶ realization.obj (ordinaryInput.obj W)}
variable {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (hx : SSet.yonedaEquiv (vertex ⦋d⦌ 0 ≫ q) = rawVertex W x)
variable (hy : SSet.yonedaEquiv (vertex ⦋d⦌ (Fin.last d) ≫ q) = rawVertex W y)

include hx in
private theorem leftRaw (A : Resolution q) :
    SSet.yonedaEquiv (vertex (horizontalDegree A) 0 ≫ value q A.base.unop) =
      rawVertex W x := by
  rw [rawVertex_restrict, A.base.unop.hom.2.1]
  exact hx

include hy in
private theorem rightRaw (A : Resolution q) :
    SSet.yonedaEquiv
      (vertex (horizontalDegree A) (Fin.last (horizontalDegree A).len) ≫
        value q A.base.unop) = rawVertex W y := by
  have h : A.base.unop.hom.1.toOrderHom (Fin.last (horizontalDegree A).len) = Fin.last d :=
    A.base.unop.hom.2.2
  rw [rawVertex_restrict, h]
  exact hy

private abbrev coeff (A : Resolution q) := graphCoefficient A

/-- The left endpoint square of an exact mixed graph. -/
abbrev leftAt (A : Resolution q) :=
  leftSquare W (horizontalDegree A) (graph A).obj.degree (coeff A) (graph A).obj.parameter x
    (leftEndpoint (W := W) (d := (horizontalDegree A).len) (q := value q A.base.unop)
      (x := x) (leftRaw hx A) (graph A))

/-- The right endpoint square of an exact mixed graph. -/
abbrev rightAt (A : Resolution q) :=
  rightSquare W (horizontalDegree A) (graph A).obj.degree (coeff A) (graph A).obj.parameter y
    (rightEndpoint (W := W) (d := (horizontalDegree A).len) (q := value q A.base.unop)
      (y := y) (rightRaw hy A) (graph A))

/-- The marked coefficient vertex over a given horizontal vertex. -/
abbrev vertexAt (A : Resolution q) (i : Fin ((horizontalDegree A).len + 1)) :=
  vertex (graph A).obj.degree
    (graphIndex (horizontalDegree A) (graph A).obj.degree (graph A).obj.parameter i)

/-- A mixed arrow preserves the marked left vertex. -/
theorem leftVertex_map {A B : Resolution q} (f : A ⟶ B) :
    vertexAt B 0 ≫ SSet.stdSimplex.map (operator f) = vertexAt A 0 := by
  rw [vertexAt, markedVertex_map, f.base.unop.left.2.1]

/-- A mixed arrow preserves the marked right vertex. -/
theorem rightVertex_map {A B : Resolution q} (f : A ⟶ B) :
    vertexAt B (Fin.last (horizontalDegree B).len) ≫ SSet.stdSimplex.map (operator f) =
      vertexAt A (Fin.last (horizontalDegree A).len) := by
  rw [vertexAt, markedVertex_map, f.base.unop.left.2.2]

/-- A mixed arrow preserves the full left endpoint base map. -/
theorem leftBase_map {A B : Resolution q} (f : A ⟶ B) :
    SSet.stdSimplex.map (operator f) ≫
      prod.lift (term (Δ (graph A).obj.degree) ≫ vertexPoint W x)
        (coeff A ≫ rowVertex W (horizontalDegree A) 0) =
    prod.lift (term (Δ (graph B).obj.degree) ≫ vertexPoint W x)
        (coeff B ≫ rowVertex W (horizontalDegree B) 0) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst]
    rw [← Category.assoc]
    rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.stdSimplex.map (operator f) ≫ term (Δ (graph A).obj.degree))
      (term (Δ (graph B).obj.degree))]
  · have h := coefficientAtVertex_map f 0
    rw [f.base.unop.left.2.1] at h
    simpa only [Category.assoc, prod.lift_snd] using h

/-- A mixed arrow preserves the full right endpoint base map. -/
theorem rightBase_map {A B : Resolution q} (f : A ⟶ B) :
    SSet.stdSimplex.map (operator f) ≫
      prod.lift (coeff A ≫ rowVertex W (horizontalDegree A) (Fin.last (horizontalDegree A).len))
        (term (Δ (graph A).obj.degree) ≫ vertexPoint W y) =
    prod.lift (coeff B ≫ rowVertex W (horizontalDegree B) (Fin.last (horizontalDegree B).len))
        (term (Δ (graph B).obj.degree) ≫ vertexPoint W y) := by
  apply prod.hom_ext
  · have h := coefficientAtVertex_map f (Fin.last (horizontalDegree B).len)
    rw [f.base.unop.left.2.2] at h
    simpa only [Category.assoc, prod.lift_fst] using h
  · simp only [Category.assoc, prod.lift_snd]
    rw [← Category.assoc]
    rw [SSet.stdSimplex.isTerminalObj₀.hom_ext
      (SSet.stdSimplex.map (operator f) ≫ term (Δ (graph A).obj.degree))
      (term (Δ (graph B).obj.degree))]

private abbrev leftMap {A B : Resolution q} (f : A ⟶ B) :=
  precomp (leftAt hx B) (leftAt hx A) (SSet.stdSimplex.map (operator f))
    (leftVertex_map f) (leftBase_map f)

private abbrev rightMap {A B : Resolution q} (f : A ⟶ B) :=
  precomp (rightAt hy B) (rightAt hy A) (SSet.stdSimplex.map (operator f))
    (rightVertex_map f) (rightBase_map f)

private theorem underlying_id (A : Resolution q) :
    SSet.stdSimplex.{0}.map (operator (𝟙 A)) = 𝟙 (Δ (graph A).obj.degree) := by
  rw [operator_id]
  exact SSet.stdSimplex.{0}.map_id _

private theorem underlying_comp {A B C : Resolution q} (f : A ⟶ B) (g : B ⟶ C) :
    SSet.stdSimplex.{0}.map (operator g) ≫ SSet.stdSimplex.map (operator f) =
      SSet.stdSimplex.map (operator (f ≫ g)) := by
  rw [operator_comp]
  exact (SSet.stdSimplex.{0}.map_comp _ _).symm

/-- Restriction acts on both complete lift spaces in every time degree. -/
def spaces : Resolution q ⥤ SSet.{0} where
  obj A := (SSet.ihomToPullbackFiber (leftAt hx A) : SSet.{0}) ⨯
    (SSet.ihomToPullbackFiber (rightAt hy A) : SSet.{0})
  map f := prod.map (leftMap hx f) (rightMap hy f)
  map_id A := by
    have hL : leftMap hx (𝟙 A) = 𝟙 _ :=
      precomp_id_of_eq _ _ (underlying_id A) _ _
    have hR : rightMap hy (𝟙 A) = 𝟙 _ :=
      precomp_id_of_eq _ _ (underlying_id A) _ _
    rw [hL, hR, prod.map_id_id]
  map_comp f g := by
    have hL : leftMap hx f ≫ leftMap hx g = leftMap hx (f ≫ g) :=
      precomp_comp_of_fac _ _ _ _ _ _ (underlying_comp f g) _ _ _ _ _ _
    have hR : rightMap hy f ≫ rightMap hy g = rightMap hy (f ≫ g) :=
      precomp_comp_of_fac _ _ _ _ _ _ (underlying_comp f g) _ _ _ _ _ _
    rw [← hL, ← hR]
    apply prod.hom_ext <;> simp

/-- The actual normalization spaces remain weakly contractible over all horizontal sources. -/
theorem spaces_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (A : Resolution q) : GW (pointMap ((spaces hx hy).obj A)) := by
  letI : WeakEquivalence (term ((spaces hx hy).obj A)) :=
    point_at_weak (d := (horizontalDegree A).len) (leftRaw hx A) (rightRaw hy A) hW (graph A)
  let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso pointIsTerminal
  rw [← pointIsTerminal.hom_ext (term ((spaces hx hy).obj A) ≫ e.hom) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- The domain with independently chosen graphs and all their normalization simplices. -/
abbrev NormalizationIndex :=
  (GrothendieckTotalElements.totalDiagram (spaces hx hy)).Elementsᵒᵖ

theorem normalizationIndex_point_GW
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    GW (pointMap (nerve (NormalizationIndex hx hy))) :=
  SynchronizedSimplicialParameters.index_point_GW_of _ (JTEndpointRowGraphResolution.point_GW q)
    (spaces_point_GW hx hy hW)

end
end DaggerModels.PartII.JTEndpointRowGraphNormalization
