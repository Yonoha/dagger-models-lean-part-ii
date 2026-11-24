import DaggerModelsPartII.JTMixedGraphEndpointLifts
import DaggerModelsPartII.JTInterleavedParameter
import DaggerModelsPartII.ParameterVertexLiftSpace

/-!
# Ordinary mixed graph endpoint normalization spaces

The two original coefficient squares retain their ordered base maps and their
specified degenerate faces. Their fixed-square lift spaces are Kan and weakly
contractible. Zero simplices encode exactly the strict edge families.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTOrdinaryGraphNormalizationSpace

open JTProjectiveOrderedFiberComparison JTEndpointNormalizationLifts
open JTMixedGraphEndpointLifts

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev J (k : SimplexCategory) := GroupoidSimplex.parameter.obj k

private theorem graphEndpoint (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
    (i : Fin (m.len + 1)) (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex m i ≫ rawGraph W m k f s) =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) :
    vertex k (graphIndex m k s i) ≫ f ≫ rowVertex W m i = vertexPoint W x := by
  have h := JTRawVertexRecovery.rawZeroGeneratorVertex_injective W
    ((rawGraph_vertex W m k f s i).symm.trans hx)
  apply SSet.yonedaEquiv.injective
  simpa only [graphRowVertex, vertexPoint, Equiv.apply_symm_apply] using h

/-- The literal left ordinary coefficient square at the graph-selected vertex. -/
def leftSquare (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
    (x : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hx : SSet.yonedaEquiv (vertex m 0 ≫ rawGraph W m k f s) =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x) :
    CommSq (vertexPoint W x ≫ identityFamily W)
      (vertex k (graphIndex m k s 0)) (endpointArrow W)
      (prod.lift (SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W x)
        (f ≫ rowVertex W m 0)) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, endpointArrow, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    have h : vertex k (graphIndex m k s 0) ≫
        SSet.stdSimplex.isTerminalObj₀.from (Δ k) = 𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simp only [← Category.assoc, h, Category.id_comp]
  · simp only [Category.assoc, endpointArrow, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    exact (graphEndpoint W m k f s 0 x hx).symm

/-- The literal right ordinary coefficient square at the graph-selected vertex. -/
def rightSquare (W : Source) (m k : SimplexCategory)
    (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
    (y : (row W ⦋0⦌).obj (op ⦋0⦌))
    (hy : SSet.yonedaEquiv (vertex m (Fin.last m.len) ≫ rawGraph W m k f s) =
      JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y) :
    CommSq (vertexPoint W y ≫ identityFamily W)
      (vertex k (graphIndex m k s (Fin.last m.len))) (endpointArrow W)
      (prod.lift (f ≫ rowVertex W m (Fin.last m.len))
        (SSet.stdSimplex.isTerminalObj₀.from (Δ k) ≫ vertexPoint W y)) := by
  constructor
  apply prod.hom_ext
  · simp only [Category.assoc, endpointArrow, prod.lift_fst]
    rw [identityFamily_endpoint, Category.comp_id]
    exact (graphEndpoint W m k f s (Fin.last m.len) y hy).symm
  · simp only [Category.assoc, endpointArrow, prod.lift_snd]
    rw [identityFamily_endpoint, Category.comp_id]
    have h : vertex k (graphIndex m k s (Fin.last m.len)) ≫
        SSet.stdSimplex.isTerminalObj₀.from (Δ k) = 𝟙 (Δ[0] : SSet.{0}) :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    simp only [← Category.assoc, h, Category.id_comp]

variable (W : Source)
  (m k : SimplexCategory) (f : Δ k ⟶ row W m) (s : Δ m ⟶ J k)
  (x y : (row W ⦋0⦌).obj (op ⦋0⦌))
  (hx : SSet.yonedaEquiv (vertex m 0 ≫ rawGraph W m k f s) =
    JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x)
  (hy : SSet.yonedaEquiv (vertex m (Fin.last m.len) ≫ rawGraph W m k f s) =
    JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W y)

/-- The original fixed left lift space, with no endpoint-fiber replacement. -/
def leftSpace : SSet.{0} := SSet.ihomToPullbackFiber (leftSquare W m k f s x hx)

/-- The original fixed right lift space, with no endpoint-fiber replacement. -/
def rightSpace : SSet.{0} := SSet.ihomToPullbackFiber (rightSquare W m k f s y hy)

/-- The ordered product of the two independent coefficient lift spaces. -/
def space : SSet.{0} :=
  leftSpace W m k f s x hx ⨯ rightSpace W m k f s y hy

theorem leftSpace_kan
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (leftSpace W m k f s x hx).KanComplex := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  haveI : Mono (vertex k (graphIndex m k s 0)) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan
    (leftSquare W m k f s x hx)

theorem rightSpace_kan
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (rightSpace W m k f s y hy).KanComplex := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  haveI : Mono (vertex k (graphIndex m k s (Fin.last m.len))) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan
    (rightSquare W m k f s y hy)

theorem leftSpace_toPoint_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from (leftSpace W m k f s x hx)) := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  haveI : Mono (vertex k (graphIndex m k s 0)) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence (vertex k (graphIndex m k s 0)) :=
    JTInterleavedParameter.standardMap_weak _
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak
    (leftSquare W m k f s x hx)

theorem rightSpace_toPoint_weak
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence
      (SSet.stdSimplex.isTerminalObj₀.from (rightSpace W m k f s y hy)) := by
  haveI : Fibration (endpointArrow W) :=
    JTInjectiveOrderedEndpointFibration.endpointArrow_fibration W hW
  haveI : Mono (vertex k (graphIndex m k s (Fin.last m.len))) :=
    SSet.stdSimplex.isTerminalObj₀.mono_from _
  haveI : WeakEquivalence (vertex k (graphIndex m k s (Fin.last m.len))) :=
    JTInterleavedParameter.standardMap_weak _
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak
    (rightSquare W m k f s y hy)

/-- An actual left coefficient family is exactly a vertex of its fixed lift space. -/
def leftVertex (d : EdgeFamilies W m k f s x y) :
    (leftSpace W m k f s x hx).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm d.left,
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (leftSquare W m k f s x hx) d.left).mpr
      ⟨d.left_degenerate, d.left_boundary⟩⟩

/-- An actual right coefficient family is exactly a vertex of its fixed lift space. -/
def rightVertex (d : EdgeFamilies W m k f s x y) :
    (rightSpace W m k f s y hy).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm d.right,
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (rightSquare W m k f s y hy) d.right).mpr
      ⟨d.right_degenerate, d.right_boundary⟩⟩

private def firstZero (v : (space W m k f s x y hx hy).obj (op ⦋0⦌)) :
    (leftSpace W m k f s x hx).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ prod.fst)

private def secondZero (v : (space W m k f s x y hx hy).obj (op ⦋0⦌)) :
    (rightSpace W m k f s y hy).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ prod.snd)

/-- Zero simplices of the ordered product are precisely the original strict
edge families, including both boundary and degeneracy equations. -/
def zeroEquiv : (space W m k f s x y hx hy).obj (op ⦋0⦌) ≃
    EdgeFamilies W m k f s x y where
  toFun v := by
    let vl := firstZero W m k f s x y hx hy v
    let vr := secondZero W m k f s x y hx hy v
    have hl := (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (leftSquare W m k f s x hx) (SSet.ihom₀Equiv vl.1)).mp (by
        simpa only [Equiv.symm_apply_apply] using vl.2)
    have hr := (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (rightSquare W m k f s y hy) (SSet.ihom₀Equiv vr.1)).mp (by
        simpa only [Equiv.symm_apply_apply] using vr.2)
    exact ⟨SSet.ihom₀Equiv vl.1, SSet.ihom₀Equiv vr.1,
      hl.2, hr.2, hl.1, hr.1⟩
  invFun d := SSet.yonedaEquiv
    (prod.lift
      (SSet.yonedaEquiv.symm (leftVertex W m k f s x y hx d))
      (SSet.yonedaEquiv.symm (rightVertex W m k f s x y hy d)))
  left_inv v := by
    apply SSet.yonedaEquiv.symm.injective
    apply prod.hom_ext
    · simp [firstZero, leftVertex]
    · simp [secondZero, rightVertex]
  right_inv d := by
    cases d
    simp [firstZero, secondZero, leftVertex, rightVertex]

theorem zeroEquiv_left (v : (space W m k f s x y hx hy).obj (op ⦋0⦌)) :
    (zeroEquiv W m k f s x y hx hy v).left =
      SSet.ihom₀Equiv
        (((prod.fst : space W m k f s x y hx hy ⟶ leftSpace W m k f s x hx).app _ v).val) := by
  change SSet.ihom₀Equiv (firstZero W m k f s x y hx hy v).val = _
  unfold firstZero
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

theorem zeroEquiv_right (v : (space W m k f s x y hx hy).obj (op ⦋0⦌)) :
    (zeroEquiv W m k f s x y hx hy v).right =
      SSet.ihom₀Equiv
        (((prod.snd : space W m k f s x y hx hy ⟶ rightSpace W m k f s y hy).app _ v).val) := by
  change SSet.ihom₀Equiv (secondZero W m k f s x y hx hy v).val = _
  unfold secondZero
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The original chosen graph endpoint families give an actual zero simplex
of the product fixed-square lift space. -/
def chosenZero
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    (space W m k f s x y hx hy).obj (op ⦋0⦌) :=
  (zeroEquiv W m k f s x y hx hy).symm
    (chosenEdgeFamilies W hW m k f s x y hx hy)

end

end DaggerModels.PartII.JTOrdinaryGraphNormalizationSpace
