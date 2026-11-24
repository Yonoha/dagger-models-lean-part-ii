import DaggerModelsPartII.JTRowGraphHorizontalSupport

/-!
# Canonical row graphs under horizontally split restriction
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial

namespace DaggerModels.PartII.JTRowGraphDegeneracyNormalization

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphNormalForm JTRowGraphResolution JTRowGraphParameterSupport

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev row (W : BiPresheaf) (d : SimplexCategory) :=
  (JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)
private abbrev Raw (W : BiPresheaf) (d : SimplexCategory) :=
  SSet.stdSimplex.{0}.obj d ⟶ realization.obj W

variable {W : BiPresheaf} {d e : SimplexCategory}

/-- The used-vertex inclusion is invertible when every parameter vertex occurs. -/
def toSupportOfSurjective (G : Graph W d)
    (hs : Function.Surjective (label G.parameter)) : G ⟶ support G := by
  let j := inclusion G.parameter
  have hj : Function.Surjective j.toOrderHom := by
    intro v
    obtain ⟨i, hi⟩ := hs v
    refine ⟨sourceLabel G.parameter i, ?_⟩
    exact (sourceLabel_inclusion G.parameter i).trans hi
  haveI : Epi j := SimplexCategory.epi_iff_surjective.mpr hj
  haveI : Mono j := inclusion_mono G.parameter
  haveI : IsIso j := isIso_of_mono_of_epi _
  refine ⟨inv j, ?_, ?_⟩
  · change (row W d).map (inv j).op
        ((row W d).map j.op G.coefficient) = G.coefficient
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, IsIso.inv_hom_id j, op_id,
      (row W d).map_id]
    rfl
  · change G.parameter ≫ J.map (inv j) = source G.parameter
    calc
      G.parameter ≫ J.map (inv j) =
          (source G.parameter ≫ J.map j) ≫ J.map (inv j) := by
        rw [source_factor]
      _ = source G.parameter := by
        rw [Category.assoc, ← J.map_comp, IsIso.hom_inv_id j,
          J.map_id, Category.comp_id]

/-- A used-supported graph maps to the canonical graph of its raw simplex. -/
def toCanonicalOfSurjective (G : Graph W d)
    (hs : Function.Surjective (label G.parameter)) : G ⟶ canonical G.value :=
  toSupportOfSurjective G hs ≫
    JTRowGraphCategory.supportToNormal G ≫
    eqToHom (JTRowGraphCategory.normal_eq_canonical G)

/-- A graph with a nondegenerate coefficient and all parameter vertices used is normal. -/
theorem normal_eq_of_reduced (G : Graph W d)
    (hc : G.coefficient ∈ (row W d).nonDegenerate G.degree.len)
    (hs : Function.Surjective (label G.parameter)) : normal G = G := by
  obtain ⟨k, w, s⟩ := G
  induction k using SimplexCategory.rec with
  | _ n =>
    let G : Graph W d := ⟨⦋n⦌, w, s⟩
    let j := inclusion s
    have hj : Function.Surjective j.toOrderHom := by
      intro v
      obtain ⟨i, hi⟩ := hs v
      refine ⟨sourceLabel s i, ?_⟩
      exact (sourceLabel_inclusion s i).trans hi
    haveI : Epi j := SimplexCategory.epi_iff_surjective.mpr hj
    unfold normal
    cases hred : reduction (support G) with
    | mk m f hf u hfac =>
      haveI : Epi f := hf
      have hG : (support G).coefficient = (row W d).map j.op w := rfl
      have hdim := (row W d).unique_nonDegenerate_dim
        (support G).coefficient j ⟨w, hc⟩ hG
        f u hfac
      change n = m at hdim
      subst m
      have hcoeff := (row W d).unique_nonDegenerate_simplex
        (support G).coefficient j ⟨w, hc⟩ hG
        f u hfac
      have hop := (row W d).unique_nonDegenerate_map
        (support G).coefficient j ⟨w, hc⟩ hG
        f u hfac
      change Graph.mk ⦋n⦌ u.val ((support G).parameter ≫ J.map f) = G
      rw [← hcoeff, ← hop]
      change Graph.mk ⦋n⦌ w (source s ≫ J.map j) = G
      rw [source_factor]

/-- A split epimorphism of horizontal ordinals preserves nondegenerate coefficients. -/
theorem restrictGraph_coefficient_nonDegenerate_of_splitEpi
    (a : d ⟶ e) (b : e ⟶ d) (h : b ≫ a = 𝟙 e) (G : Graph W e)
    (hc : G.coefficient ∈ (row W e).nonDegenerate G.degree.len) :
    (restrictGraph a G).coefficient ∈
      (row W d).nonDegenerate (restrictGraph a G).degree.len := by
  let f : row W e ⟶ row W d := (JTRealizationDiagonal.ordinaryCurry.obj W).map a.op
  let g : row W d ⟶ row W e := (JTRealizationDiagonal.ordinaryCurry.obj W).map b.op
  have hfg : f ≫ g = 𝟙 (row W e) := by
    dsimp [f, g]
    rw [← Functor.map_comp, ← op_comp, h, op_id]
    exact (JTRealizationDiagonal.ordinaryCurry.obj W).map_id (op e)
  haveI : IsSplitMono f := IsSplitMono.mk' ⟨g, hfg⟩
  haveI : Mono f := inferInstance
  obtain ⟨k, w, s⟩ := G
  induction k using SimplexCategory.rec with
  | _ n =>
    change (f.app (op ⦋n⦌)) w ∈ (row W d).nonDegenerate n
    exact (SSet.nonDegenerate_iff_of_mono f w).mpr hc

/-- Horizontal split restriction retains every parameter vertex of a reduced graph. -/
theorem restrictGraph_parameter_surjective_of_splitEpi
    (a : d ⟶ e) (b : e ⟶ d) (h : b ≫ a = 𝟙 e) (G : Graph W e)
    (hs : Function.Surjective (label G.parameter)) :
    Function.Surjective (label (restrictGraph a G).parameter) := by
  intro v
  obtain ⟨i, hi⟩ := hs v
  refine ⟨b.toOrderHom i, ?_⟩
  change label (SSet.stdSimplex.map a ≫ G.parameter) (b.toOrderHom i) = v
  rw [JTRowGraphHorizontalSupport.label_restriction]
  have hab := SimplexCategory.congr_toOrderHom_apply h i
  have hab' := congrArg (label G.parameter) hab
  change label G.parameter (a.toOrderHom (b.toOrderHom i)) = label G.parameter i at hab'
  exact hab'.trans hi

/-- Canonical graphs commute with horizontal restriction along a split epimorphism. -/
theorem canonical_restrictGraph_of_splitEpi
    (a : d ⟶ e) (b : e ⟶ d) (h : b ≫ a = 𝟙 e) (q : Raw W e) :
    canonical (SSet.stdSimplex.map a ≫ q) = restrictGraph a (canonical q) := by
  let G := restrictGraph a (canonical q)
  have hvalue : G.value = SSet.stdSimplex.map a ≫ q := by
    rw [restrictGraph_value, canonical_value]
  have hred : normal G = G := normal_eq_of_reduced G
    (restrictGraph_coefficient_nonDegenerate_of_splitEpi a b h (canonical q)
      (normal_coefficient_nonDegenerate _))
    (restrictGraph_parameter_surjective_of_splitEpi a b h (canonical q)
      (normal_parameter_surjective _))
  calc
    canonical (SSet.stdSimplex.map a ≫ q) = normal G := by
      rw [← hvalue]
      exact (normal_eq_canonical G).symm
    _ = G := hred

end

end DaggerModels.PartII.JTRowGraphDegeneracyNormalization
