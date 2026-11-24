import DaggerModelsPartII.JTRowGraphNormalForm
import DaggerModelsPartII.JTMixedGraphVerticalArrow

/-!
# The canonical row-graph comparison lifts to the actual target comma

Choose the two endpoint families once on the canonical graph. Restrict them
to each support and extend them along the monic support inclusion. Both
resulting spans are in the original comma over the same whole native map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTRowGraphCommaComparison

open OrdinaryJTRealization JTReversalInput JTProjectiveOrderedFiberComparison
open JTRowGraphRelations JTRowGraphNormalForm JTRowGraphParameterSupport
open JTMixedGraphEndpointLifts JTMixedGraphRawRefinement
open JTMixedGraphVerticalArrow JTMixedGraphEdgeFamilyReindex

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) := realization.obj (ordinaryInput.obj W)
private abbrev J := GroupoidSimplex.parameter
private abbrev Δ (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {d : ℕ} {x y : Vertex W}

/-- The original row graph in the prescribed native bead dimension. -/
abbrev RowGraph (W : Source) (d : ℕ) :=
  Graph (ordinaryInput.obj W) ⦋d⦌

/-- The original row coefficient regarded as a simplicial map. -/
def coefficientMap (G : RowGraph W d) : Δ G.degree ⟶ row W ⦋d⦌ :=
  SSet.yonedaEquiv.symm G.coefficient

/-- The exact native map represented by the graph. -/
def nativeValue (G : RowGraph W d) : (single d).toSSet ⟶ R W :=
  (singleIso d).hom ≫ G.value

private theorem nativeValue_eq (G : RowGraph W d) :
    nativeRawGraph W d G.degree (coefficientMap G) G.parameter = nativeValue G := by
  unfold nativeRawGraph rawGraph coefficientMap nativeValue Graph.value
  erw [Equiv.apply_symm_apply]

/-- Endpoint normalization data for a prescribed graph. -/
abbrev Families (G : RowGraph W d) (x y : Vertex W) :=
  EdgeFamilies W ⦋d⦌ G.degree (coefficientMap G) G.parameter x y

variable {q : (single d).toSSet ⟶ R W}
variable (qx : q.app (op ⦋0⦌) (single d).first = rawVertex W x)
variable (qy : q.app (op ⦋0⦌) (single d).last = rawVertex W y)

private abbrev target : NecklacesOver (R W) (rawVertex W x) (rawVertex W y) :=
  ⟨single d, q, qx, qy⟩

private abbrev CommaCategory :=
  CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) (target qx qy)

/-- The actual normalized comma object for these specified families and target. -/
def commaObject (G : RowGraph W d) (hq : nativeValue G = q)
    (E : Families G x y) : CommaCategory qx qy :=
  (refinementOfGraph E ((nativeValue_eq G).trans hq) qx qy).toComma

private theorem restrictArrow_aux {k l : SimplexCategory}
    (j : k ⟶ l) (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
    (f₀ : Δ k ⟶ row W ⦋d⦌) (s₁ : Δ ⦋d⦌ ⟶ J.obj l)
    (hf : f₀ = SSet.stdSimplex.map j ≫ f) (hs : s₁ = s ≫ J.map j)
    (h₀ : nativeRawGraph W d k f₀ s = q) (h₁ : nativeRawGraph W d l f s₁ = q)
    (E : EdgeFamilies W ⦋d⦌ l f s₁ x y) :
    ∃ D : EdgeFamilies W ⦋d⦌ k f₀ s x y,
      Nonempty ((refinementOfGraph D h₀ qx qy).toComma ⟶
        (refinementOfGraph E h₁ qx qy).toComma) := by
  subst f₀
  subst s₁
  exact ⟨restrictEdgeFamilies j f s E, ⟨verticalArrow j f s E h₁ qx qy⟩⟩

private theorem extendArrow_aux {k l : SimplexCategory}
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (j : k ⟶ l) [Mono j] (f : Δ l ⟶ row W ⦋d⦌) (s : Δ ⦋d⦌ ⟶ J.obj k)
    (f₀ : Δ k ⟶ row W ⦋d⦌) (s₁ : Δ ⦋d⦌ ⟶ J.obj l)
    (hf : f₀ = SSet.stdSimplex.map j ≫ f) (hs : s₁ = s ≫ J.map j)
    (h₀ : nativeRawGraph W d k f₀ s = q) (h₁ : nativeRawGraph W d l f s₁ = q)
    (D : EdgeFamilies W ⦋d⦌ k f₀ s x y) :
    ∃ E : EdgeFamilies W ⦋d⦌ l f s₁ x y,
      Nonempty ((refinementOfGraph D h₀ qx qy).toComma ⟶
        (refinementOfGraph E h₁ qx qy).toComma) := by
  subst f₀
  subst s₁
  exact exists_verticalArrow_from j f s h₁ qx qy hW D

set_option maxHeartbeats 500000 in
/-- A specified larger normalization pulls back along any elementary
coend step to an actual arrow over the unchanged target. -/
theorem restrictArrow {G H : RowGraph W d}
    (step : Step (ordinaryInput.obj W) ⦋d⦌ G H)
    (hG : nativeValue G = q) (hH : nativeValue H = q) (E : Families H x y) :
    ∃ D : Families G x y, Nonempty (commaObject qx qy G hG D ⟶ commaObject qx qy H hH E) := by
  cases step with
  | @along k l j w s =>
    let A : RowGraph W d := ⟨k, (row W ⦋d⦌).map j.op w, s⟩
    let B : RowGraph W d := ⟨l, w, s ≫ J.map j⟩
    change nativeValue A = q at hG
    change nativeValue B = q at hH
    let f : Δ l ⟶ row W ⦋d⦌ := SSet.yonedaEquiv.symm w
    have hc : SSet.yonedaEquiv.symm ((row W ⦋d⦌).map j.op w) =
        SSet.stdSimplex.map j ≫ f :=
      (SSet.stdSimplex.map_comp_yonedaEquiv_symm (X := row W ⦋d⦌) w j).symm
    exact restrictArrow_aux (W := W) (d := d) qx qy j f s (coefficientMap A) B.parameter hc rfl
      ((nativeValue_eq A).trans hG) ((nativeValue_eq B).trans hH) E

set_option maxHeartbeats 500000 in
/-- An arbitrary normalization of the used-vertex support extends along
its injective inclusion, with an actual arrow in the original comma. -/
theorem extendSupportArrow
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G : RowGraph W d) (hG : nativeValue G = q) (hS : nativeValue (support G) = q)
    (D : Families (support G) x y) :
    ∃ E : Families G x y,
      Nonempty (commaObject qx qy (support G) hS D ⟶ commaObject qx qy G hG E) := by
  let j := inclusion G.parameter
  letI : Mono j := inclusion_mono G.parameter
  have hc : coefficientMap (support G) = SSet.stdSimplex.map j ≫ coefficientMap G :=
    (SSet.stdSimplex.map_comp_yonedaEquiv_symm (X := row W ⦋d⦌) G.coefficient j).symm
  exact extendArrow_aux (W := W) (d := d) qx qy hW j (coefficientMap G) (source G.parameter)
    (coefficientMap (support G)) G.parameter hc (source_factor G.parameter).symm
    ((nativeValue_eq (support G)).trans hS) ((nativeValue_eq G).trans hG) D

private theorem nativeValue_support (G : RowGraph W d) :
    nativeValue (support G) = nativeValue G :=
  congrArg (fun a ↦ (singleIso d).hom ≫ a) (support_step G).value_eq

private theorem nativeValue_normal (G : RowGraph W d) :
    nativeValue (normal G) = nativeValue G :=
  congrArg (fun a ↦ (singleIso d).hom ≫ a) (normal_value G)

/-- Every given canonical normalization receives a span from the support,
whose other end is a normalization of the specified graph. -/
theorem canonicalSpan
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G : RowGraph W d) (hG : nativeValue G = q) (hN : nativeValue (normal G) = q)
    (E : Families (normal G) x y) :
    ∃ (D : Families G x y) (S : Families (support G) x y),
      Nonempty (commaObject qx qy (support G) ((nativeValue_support G).trans hG) S ⟶
        commaObject qx qy G hG D) ∧
      Nonempty (commaObject qx qy (support G) ((nativeValue_support G).trans hG) S ⟶
        commaObject qx qy (normal G) hN E) := by
  let hS := (nativeValue_support G).trans hG
  obtain ⟨S, hSN⟩ := restrictArrow qx qy (support_to_normal G) hS hN E
  obtain ⟨D, hSG⟩ := extendSupportArrow qx qy hW G hG hS S
  exact ⟨D, S, hSG, hSN⟩

/-- Two raw graph representatives over one target admit compatible
normalizations connected by actual comma arrows through their common
canonical graph. -/
theorem exists_connected_normalizations
    (hW : letI := InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (G H : RowGraph W d) (hG : nativeValue G = q) (hH : nativeValue H = q) :
    ∃ (D : Families G x y) (E : Families H x y),
      Relation.EqvGen (fun A B : CommaCategory qx qy ↦ Nonempty (A ⟶ B))
        (commaObject qx qy G hG D) (commaObject qx qy H hH E) := by
  let N := normal G
  have hN : nativeValue N = q := (nativeValue_normal G).trans hG
  have hGH : G.value = H.value :=
    (cancel_epi (singleIso d).hom).mp (hG.trans hH.symm)
  have he : normal H = N := (value_eq_iff_normal_eq H G).mp hGH.symm
  have hn := (nativeValue_eq N).trans hN
  obtain ⟨hx, hy⟩ := graph_endpoints_of_native_map hn qx qy
  let E₀ : Families N x y := chosenEdgeFamilies W hW ⦋d⦌ N.degree
    (coefficientMap N) N.parameter x y hx hy
  obtain ⟨D, S, hSG, hSN⟩ := canonicalSpan qx qy hW G hG hN E₀
  have hHspan : ∀ (hh : nativeValue N = q) (F : Families N x y),
      ∃ (E : Families H x y) (T : Families (support H) x y),
        Nonempty (commaObject qx qy (support H) ((nativeValue_support H).trans hH) T ⟶
          commaObject qx qy H hH E) ∧
        Nonempty (commaObject qx qy (support H) ((nativeValue_support H).trans hH) T ⟶
          commaObject qx qy N hh F) := by
    rw [← he]
    exact canonicalSpan qx qy hW H hH
  obtain ⟨E, T, hTH, hTN⟩ := hHspan hN E₀
  refine ⟨D, E, Relation.EqvGen.trans _ (commaObject qx qy N hN E₀) _ ?_ ?_⟩
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hSG))
      (Relation.EqvGen.rel _ _ hSN)
  · exact Relation.EqvGen.trans _ _ _
      (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hTN))
      (Relation.EqvGen.rel _ _ hTH)

end

end DaggerModels.PartII.JTRowGraphCommaComparison
