import DaggerModelsPartII.JTRowGraphNormalForm
import DaggerModelsPartII.JTRealizationGraphGenerator
import OriginalFlagFlankFunctor
import NerveHomotopy

/-!
# Coefficient operators of the actual row graph presentations
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphCategory

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphParameterSupport JTRowGraphNormalForm

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev simplex (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d
private abbrev row (W : BiPresheaf) (d : SimplexCategory) :=
  (JTRealizationDiagonal.ordinaryCurry.obj W).obj (op d)

variable {W : BiPresheaf} {d : SimplexCategory}

/-- An actual coefficient operator and its exact graph and label equations. -/
@[ext]
structure Arrow (G H : Graph W d) where
  operator : G.degree ⟶ H.degree
  coefficient : (row W d).map operator.op H.coefficient = G.coefficient
  parameter : G.parameter ≫ J.map operator = H.parameter

instance : SmallCategory (Graph W d) where
  Hom := Arrow
  id G := ⟨𝟙 G.degree, by rw [op_id, (row W d).map_id]; rfl,
    by rw [J.map_id, Category.comp_id]⟩
  comp u v := ⟨u.operator ≫ v.operator, by
    rw [op_comp, Functor.map_comp, types_comp_apply, v.coefficient, u.coefficient], by
    rw [J.map_comp, ← Category.assoc, u.parameter, v.parameter]⟩
  id_comp _ := Arrow.ext (Category.id_comp _)
  comp_id _ := Arrow.ext (Category.comp_id _)
  assoc _ _ _ := Arrow.ext (Category.assoc _ _ _)

private theorem operator_ext {G H : Graph W d} {f g : G ⟶ H}
    (h : Arrow.operator f = Arrow.operator g) : f = g := Arrow.ext h

/-- Every coefficient operator is one of the existing vertical coend steps. -/
theorem step {G H : Graph W d} (f : G ⟶ H) : Step W d G H := by
  have h := Step.along f.operator H.coefficient G.parameter
  change Step W d ⟨G.degree, (row W d).map f.operator.op H.coefficient, G.parameter⟩
    ⟨H.degree, H.coefficient, G.parameter ≫ J.map f.operator⟩ at h
  rw [f.coefficient, f.parameter] at h
  exact h

/-- A map from a graph using every vertex is determined by the target
parameter. Parallel operators are still allowed for general graphs. -/
theorem hom_ext_of_label_surjective {G H : Graph W d}
    (hs : Function.Surjective (label G.parameter)) (f g : G ⟶ H) : f = g := by
  apply operator_ext
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext a
  obtain ⟨i, rfl⟩ := hs a
  have he := congrArg (fun s ↦ label s i) (f.parameter.trans g.parameter.symm)
  simpa only [label_map] using he

private theorem support_surjective (G : Graph W d) :
    Function.Surjective (label (support G).parameter) :=
  source_vertex_surjective G.parameter

/-- The induced support operator retains the exact coefficient and
parameter restrictions of the original operator. -/
def supportArrow {G H : Graph W d} (f : G ⟶ H) : support G ⟶ support H := by
  rcases G with ⟨k, w, s⟩
  rcases H with ⟨l, v, t⟩
  rcases f with ⟨j, hc, hp⟩
  change k ⟶ l at j
  change (row W d).map j.op v = w at hc
  change s ≫ J.map j = t at hp
  subst t
  refine ⟨supportMap s j, ?_, source_map s j⟩
  change (row W d).map (supportMap s j).op
      ((row W d).map (inclusion (s ≫ J.map j)).op v) =
    (row W d).map (inclusion s).op w
  have h := congrArg (fun u : supportOrdinal s ⟶ l ↦ (row W d).map u.op v)
    (supportMap_inclusion s j)
  simpa only [op_comp, Functor.map_comp, types_comp_apply, hc] using h

/-- Actual used-vertex restriction is functorial on the coefficient arrows. -/
def supportFunctor (W : BiPresheaf) (d : SimplexCategory) : Graph W d ⥤ Graph W d where
  obj := support
  map := supportArrow
  map_id G := hom_ext_of_label_surjective (support_surjective G) _ _
  map_comp {G _ _} _ _ := hom_ext_of_label_surjective (support_surjective G) _ _

/-- The support inclusion is the same original ordinal inclusion. -/
def supportInclusion (W : BiPresheaf) (d : SimplexCategory) :
    supportFunctor W d ⟶ 𝟭 (Graph W d) where
  app G := ⟨inclusion G.parameter, rfl, source_factor G.parameter⟩
  naturality {G _} _ := hom_ext_of_label_surjective (support_surjective G) _ _

/-- The Eilenberg--Zilber operator from support to the canonical graph. -/
def supportToNormal (G : Graph W d) : support G ⟶ normal G :=
  ⟨(reduction (support G)).operator, (reduction (support G)).fac.symm, rfl⟩

private abbrev Raw (W : BiPresheaf) (d : SimplexCategory) :=
  simplex d ⟶ realization.obj W

/-- The raw value functor uses the entire actual simplicial map. -/
def valueFunctor (W : BiPresheaf) (d : SimplexCategory) :
    Graph W d ⥤ Discrete (Raw W d) where
  obj G := ⟨G.value⟩
  map f := Discrete.eqToHom (step f).value_eq
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A representative of every actual raw simplex, via the original colimit. -/
theorem exists_value (q : Raw W d) : ∃ G : Graph W d, G.value = q := by
  obtain ⟨k, w, s, h⟩ := JTRealizationGraphGenerator.exists_graph_generator W d q
  exact ⟨⟨k, w, s⟩, h.symm⟩

/-- Choose the existing canonical representative of each actual raw simplex. -/
def canonical (q : Raw W d) : Graph W d :=
  normal (Classical.choose (exists_value q))

theorem canonical_value (q : Raw W d) : (canonical q).value = q :=
  (normal_value _).trans (Classical.choose_spec (exists_value q))

theorem normal_eq_canonical (G : Graph W d) : normal G = canonical G.value :=
  (value_eq_iff_normal_eq _ _).mp (Classical.choose_spec (exists_value G.value)).symm

/-- The discrete section picks the canonical row graph of each raw simplex. -/
def sectionFunctor (W : BiPresheaf) (d : SimplexCategory) :
    Discrete (Raw W d) ⥤ Graph W d :=
  Discrete.functor (fun q ↦ canonical q)

/-- The support-to-normal comparison is natural on all original arrows. -/
def supportToSection (W : BiPresheaf) (d : SimplexCategory) :
    supportFunctor W d ⟶ valueFunctor W d ⋙ sectionFunctor W d where
  app G := supportToNormal G ≫ eqToHom (normal_eq_canonical G)
  naturality {G _} _ := hom_ext_of_label_surjective (support_surjective G) _ _

/-- The actual coefficient operator nerve resolves the discrete set of
all simplices of the original raw realization in the given degree. -/
theorem valueFunctor_GW (W : BiPresheaf) (d : SimplexCategory) :
    GW (nerveMap (valueFunctor W d)) := by
  let F := valueFunctor W d
  let G := sectionFunctor W d
  have h₁ : DaggerNerveHomotopy.NatTransZigzag (F ⋙ G) (𝟭 (Graph W d)) :=
    .trans _ (supportFunctor W d) _
      (.symm _ _ (.rel _ _ ⟨supportToSection W d⟩))
      (.rel _ _ ⟨supportInclusion W d⟩)
  let h₂ : G ⋙ F ⟶ 𝟭 (Discrete (Raw W d)) :=
    { app q := Discrete.eqToHom (canonical_value q.as)
      naturality _ _ _ := Subsingleton.elim _ _ }
  exact DaggerNerveHomotopy.nerveMap_geometricW F G h₁ (.rel _ _ ⟨h₂⟩)

end

end DaggerModels.PartII.JTRowGraphCategory
