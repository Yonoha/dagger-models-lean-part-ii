import DaggerModelsPartII.JTUnitaryDiagonalPath
import DaggerModelsPartII.OrderedNecklaceVertexPoints
import DaggerModelsPartII.DiagramMappingPrecompFibration
import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! The two actual walking-unitary endpoints form a monic boundary. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerModels.OriginalWalkingIsoIntegerObstruction
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTUnitaryEndpointsFibration

open SegalLocalizers JTUnitaryDiagonalPath
open OrderedNecklaceLabelDiagram (boundary)
open OrderedNecklaceVertexPoints (boundaryMappingIso boundaryMappingIso_fst boundaryMappingIso_snd)

noncomputable section

private abbrev S := ReverseDaggerSpace.{0}

private def zeroPoint : (freeSimplex.{0} 0).toSSet.obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (freeDaggerAdjunction.{0}.unit.app (Δ[0] : SSet.{0}))

private theorem first_vertex :
    unitaryVertex.{0}.hom.app (op ⦋0⦌) zeroPoint = zeroVertex := by
  unfold zeroPoint
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv
    ((freeDaggerAdjunction.{0}.homEquiv _ _) unitaryVertex.{0}) = _
  rw [unitaryVertex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem last_vertex :
    otherVertex.hom.app (op ⦋0⦌) zeroPoint = ComposableArrows.mk₀ walkingOne.{0} := by
  unfold zeroPoint
  rw [← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv
    ((freeDaggerAdjunction.{0}.homEquiv _ _) otherVertex) = _
  rw [otherVertex, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

private theorem endpoints_disjoint (a : ReverseSimplexᵒᵖ) (q : SimplexCategoryᵒᵖ)
    (x y : ((daggerSimplex.{0} 0).obj a).obj q) :
    (unitaryCompletenessMap.{0}.app a).app q x ≠ (otherEndpoint.app a).app q y := by
  intro h
  let k := a.unop.len
  let d : ⦋0⦌ ⟶ ⦋k⦌ := SimplexCategory.const _ _ 0
  change unitaryVertex.{0}.hom.app (op ⦋k⦌) x = otherVertex.hom.app (op ⦋k⦌) y at h
  have hd := congrArg (walkingUnitaryNerve.{0}.toSSet.map d.op) h
  have h₀ := congrFun (unitaryVertex.{0}.hom.naturality d.op) x
  have h₁ := congrFun (otherVertex.hom.naturality d.op) y
  change unitaryVertex.{0}.hom.app (op ⦋0⦌)
      ((freeSimplex 0).toSSet.map d.op x) = _ at h₀
  change otherVertex.hom.app (op ⦋0⦌) ((freeSimplex 0).toSSet.map d.op y) = _ at h₁
  letI : Subsingleton ((freeSimplex.{0} 0).toSSet.obj (op ⦋0⦌)) :=
    SegalRepresentables.subsingleton_daggerSimplex_zero (op ⟨0⟩) (op ⦋0⦌)
  have he := h₀.trans (hd.trans h₁.symm)
  rw [Subsingleton.elim ((freeSimplex 0).toSSet.map d.op x) zeroPoint,
    Subsingleton.elim ((freeSimplex 0).toSSet.map d.op y) zeroPoint,
    first_vertex, last_vertex] at he
  have hne : walkingZero.{0} ≠ walkingOne.{0} := by
    intro hn
    exact Bool.false_ne_true (congrArg (fun t : walkingIso.{0} ↦ (AsSmall.down.obj t).as) hn)
  apply hne
  exact congrArg (fun t : (nerve walkingIso.{0}).obj (op ⦋0⦌) ↦ t.obj 0) he

/-- The coproduct of both original zero-vertex inclusions into the walking unitary. -/
def inclusion : boundary ⟶ walkingUnitarySpace :=
  coprod.desc unitaryCompletenessMap otherEndpoint

/-- The actual ordered boundary inclusion is monic in reversal diagrams. -/
theorem inclusion_mono : Mono inclusion := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  let E := (evaluation ReverseSimplexᵒᵖ SSet.{0}).obj a ⋙ SSet.evaluation.obj q
  let c := BinaryCofan.mk
    (E.map (coprod.inl : daggerSimplex 0 ⟶ boundary))
    (E.map (coprod.inr : daggerSimplex 0 ⟶ boundary))
  have hc : IsColimit c := mapIsColimitOfPreservesOfIsColimit E _ _ (coprodIsCoprod _ _)
  let e := hc.coconePointUniqueUpToIso (Types.binaryCoproductColimit _ _)
  have hl : E.map (coprod.inl : daggerSimplex 0 ⟶ boundary) = Sum.inl ≫ e.inv :=
    (hc.comp_coconePointUniqueUpToIso_inv (Types.binaryCoproductColimit _ _)
      ⟨WalkingPair.left⟩).symm
  have hr : E.map (coprod.inr : daggerSimplex 0 ⟶ boundary) = Sum.inr ≫ e.inv :=
    (hc.comp_coconePointUniqueUpToIso_inv (Types.binaryCoproductColimit _ _)
      ⟨WalkingPair.right⟩).symm
  have hb : Function.Surjective e.inv := e.symm.toEquiv.surjective
  have hL (x : E.obj (daggerSimplex 0)) :
      E.map inclusion (e.inv (Sum.inl x)) = E.map unitaryCompletenessMap x := by
    rw [← show E.map (coprod.inl : daggerSimplex 0 ⟶ boundary) x = e.inv (Sum.inl x) from
      congrFun hl x]
    have h := congrFun (E.map_comp (coprod.inl : daggerSimplex 0 ⟶ boundary) inclusion) x
    simpa only [inclusion, coprod.inl_desc, types_comp_apply] using h.symm
  have hR (x : E.obj (daggerSimplex 0)) :
      E.map inclusion (e.inv (Sum.inr x)) = E.map otherEndpoint x := by
    rw [← show E.map (coprod.inr : daggerSimplex 0 ⟶ boundary) x = e.inv (Sum.inr x) from
      congrFun hr x]
    have h := congrFun (E.map_comp (coprod.inr : daggerSimplex 0 ⟶ boundary) inclusion) x
    simpa only [inclusion, coprod.inr_desc, types_comp_apply] using h.symm
  change Function.Injective (E.map inclusion)
  intro x y h
  obtain ⟨x, rfl⟩ := hb x
  obtain ⟨y, rfl⟩ := hb y
  letI : Subsingleton (E.obj (daggerSimplex 0)) :=
    SegalRepresentables.subsingleton_daggerSimplex_zero a q
  cases x with
  | inl x =>
    cases y with
    | inl y => rw [Subsingleton.elim x y]
    | inr y => exact (endpoints_disjoint a q x y ((hL x).symm.trans (h.trans (hR y)))).elim
  | inr x =>
    cases y with
    | inl y => exact (endpoints_disjoint a q y x ((hL y).symm.trans (h.symm.trans (hR x)))).elim
    | inr y => rw [Subsingleton.elim x y]

/-- The original two endpoints exhaust the entire zero row of the walking unitary. -/
theorem inclusion_zero_isIso : IsIso (inclusion.app (op ⟨0⟩)) := by
  letI := inclusion_mono
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  apply (isIso_iff_bijective _).mpr
  refine ⟨(mono_iff_injective _).mp inferInstance, ?_⟩
  intro z
  change (nerve walkingIso.{0}).obj (op ⦋0⦌) at z
  obtain ⟨v, rfl⟩ := ComposableArrows.mk₀_surjective z
  have hv : v = walkingZero.{0} ∨ v = walkingOne.{0} := by
    rcases v with ⟨⟨b⟩⟩
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  let x : ((daggerSimplex.{0} 0).obj (op ⟨0⟩)).obj q := zeroPoint
  rcases hv with rfl | rfl
  · refine ⟨((coprod.inl : daggerSimplex 0 ⟶ boundary).app (op ⟨0⟩)).app q x, ?_⟩
    have h := congrFun (NatTrans.congr_app (NatTrans.congr_app
      (coprod.inl_desc unitaryCompletenessMap otherEndpoint) (op ⟨0⟩)) q) x
    exact h.trans first_vertex
  · refine ⟨((coprod.inr : daggerSimplex 0 ⟶ boundary).app (op ⟨0⟩)).app q x, ?_⟩
    have h := congrFun (NatTrans.congr_app (NatTrans.congr_app
      (coprod.inr_desc unitaryCompletenessMap otherEndpoint) (op ⟨0⟩)) q) x
    exact h.trans last_vertex

private theorem precomp_boundary (W : S) :
    diagramMappingPrecomp inclusion W ≫ (boundaryMappingIso W).hom = unitaryEndpoints W := by
  apply prod.hom_ext
  · rw [Category.assoc, boundaryMappingIso_fst, ← diagramMappingPrecomp_comp]
    simp only [inclusion, coprod.inl_desc]
    exact (prod.lift_fst (diagramMappingPrecomp unitaryCompletenessMap W)
      (diagramMappingPrecomp otherEndpoint W)).symm
  · rw [Category.assoc, boundaryMappingIso_snd, ← diagramMappingPrecomp_comp]
    simp only [inclusion, coprod.inr_desc]
    exact (prod.lift_snd (diagramMappingPrecomp unitaryCompletenessMap W)
      (diagramMappingPrecomp otherEndpoint W)).symm

/-- The strict walking-unitary endpoint arrow is an actual Kan fibration. -/
theorem unitaryEndpoints_fibration (W : S)
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    Fibration (unitaryEndpoints W) := by
  letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ
  letI := hW
  letI : Fact (InjectiveKanDiagram.GeneratorsAreAllMonos ReverseSimplexᵒᵖ) :=
    ⟨InjectiveKanDiagram.generatorsAreAllMonos ReverseSimplexᵒᵖ⟩
  letI := inclusion_mono
  letI : Fibration (diagramMappingPrecomp inclusion W) :=
    InjectiveKanDiagram.diagramMappingPrecomp_isFibration ReverseSimplexᵒᵖ inclusion W
  rw [← precomp_boundary]
  infer_instance


open ChosenHomotopyFiberComparison

/-- The actual strict walking-unitary fiber computes the chosen diagonal path
fiber, at precisely the supplied ordered pair. -/
def diagonalToStrictUnitary (W : S) [Fibration (unitaryEndpoints W)]
    (b : (Δ[0] : SSet.{0}) ⟶ Zero W ⨯ Zero W) :
    chosenFiber (diagonal W) b ⟶ pullback (unitaryEndpoints W) b :=
  comparison (diagonal W) (unitaryEndpoints W) (constantUnitary W) (𝟙 _)
    (by rw [Category.comp_id, constantUnitary_endpoints]) b b (Category.comp_id _)

theorem diagonalToStrictUnitary_weak (W : S) [Fibration (unitaryEndpoints W)]
    (hW : unitaryCompletenessCondition W) (b : (Δ[0] : SSet.{0}) ⟶ Zero W ⨯ Zero W) :
    WeakEquivalence (diagonalToStrictUnitary W b) := by
  letI := constantUnitary_weak W hW
  exact comparison_weak _ _ _ _ _ _ _ _

/-- This strict comparison agrees with the natural chosen comparison after
the canonical strict-to-chosen inclusion and Kan localization. -/
theorem diagonalToStrictUnitary_localized (W : S) [Fibration (unitaryEndpoints W)]
    (b : (Δ[0] : SSet.{0}) ⟶ Zero W ⨯ Zero W) :
    (weakEquivalences SSet.{0}).Q.map (diagonalToUnitary W b) =
      (weakEquivalences SSet.{0}).Q.map (diagonalToStrictUnitary W b ≫
        ChosenHomotopyFiberTriangle.inclusion (unitaryEndpoints W) b) :=
  ChosenHomotopyFiberFunctor.chosenMap_comparison _ _ _ _ _ _ _ _

end

end DaggerModels.PartII.JTUnitaryEndpointsFibration
