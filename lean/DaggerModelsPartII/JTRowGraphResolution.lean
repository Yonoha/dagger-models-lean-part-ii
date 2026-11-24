import DaggerModelsPartII.JTRowGraphCategory
import NativeBisimplicialDiagonalWeak

/-!
# A bisimplicial resolution of the actual raw realization by row graphs
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphResolution

open OrdinaryJTRealization JTRealizationGenerators JTRowGraphRelations JTRowGraphCategory
open DaggerNativeBisimplicialDiagonal DaggerNativeBisimplicialHorizontalMapping
open DaggerOriginalFlagFlankification (constantSSet nerveDiscreteIso)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev simplex (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d

variable {W : BiPresheaf} {d m l : SimplexCategory}

private abbrev horizontal (a : d ⟶ m) (k : SimplexCategory) : (d, k) ⟶ (m, k) := (a, 𝟙 k)
private abbrev vertical (d : SimplexCategory) {k l : SimplexCategory} (b : k ⟶ l) :
    (d, k) ⟶ (d, l) := (𝟙 d, b)

/-- Restrict the full graph in the horizontal simplex direction. -/
def restrictGraph (a : d ⟶ m) (G : Graph W m) : Graph W d where
  degree := G.degree
  coefficient := W.map (horizontal a G.degree).op G.coefficient
  parameter := SSet.stdSimplex.map a ≫ G.parameter

private def restrictArrow (a : d ⟶ m) {G H : Graph W m} (f : G ⟶ H) :
    restrictGraph a G ⟶ restrictGraph a H := by
  refine ⟨f.operator, ?_, ?_⟩
  · have sq : vertical d f.operator ≫ horizontal a H.degree =
        horizontal a G.degree ≫ vertical m f.operator := by
      ext <;> simp
    have h := congrArg (fun b : (d, G.degree) ⟶ (m, H.degree) ↦
      W.map b.op H.coefficient) sq
    have h₀ : W.map (vertical m f.operator).op H.coefficient = G.coefficient := f.coefficient
    change W.map (vertical d f.operator).op
        (W.map (horizontal a H.degree).op H.coefficient) =
      W.map (horizontal a G.degree).op G.coefficient
    simpa only [op_comp, Functor.map_comp, types_comp_apply, h₀] using h
  · change (SSet.stdSimplex.map a ≫ G.parameter) ≫ J.map f.operator =
      SSet.stdSimplex.map a ≫ H.parameter
    rw [Category.assoc, f.parameter]

/-- Horizontal restriction preserves the original vertical operators. -/
def restrict (W : BiPresheaf) (a : d ⟶ m) : Graph W m ⥤ Graph W d where
  obj := restrictGraph a
  map := restrictArrow a
  map_id _ := Arrow.ext rfl
  map_comp _ _ := Arrow.ext rfl

private theorem restrictGraph_id (G : Graph W d) : restrictGraph (𝟙 d) G = G := by
  obtain ⟨k, w, s⟩ := G
  have h : horizontal (𝟙 d) k = 𝟙 (d, k) := rfl
  simp only [restrictGraph, h, op_id, W.map_id, SSet.stdSimplex.{0}.map_id,
    Category.id_comp]
  rfl

private theorem restrictGraph_comp (a : d ⟶ m) (b : m ⟶ l) (G : Graph W l) :
    restrictGraph (a ≫ b) G = restrictGraph a (restrictGraph b G) := by
  obtain ⟨k, w, s⟩ := G
  have h : horizontal (a ≫ b) k = horizontal a k ≫ horizontal b k := by
    ext <;> simp
  simp only [restrictGraph, h, op_comp, W.map_comp, types_comp_apply,
    SSet.stdSimplex.{0}.map_comp, Category.assoc]

private theorem eqToHom_operator {G H : Graph W d} (h : G = H) :
    (eqToHom h : G ⟶ H).operator = eqToHom (congrArg Graph.degree h) := by
  cases h
  rfl

theorem restrict_id (W : BiPresheaf) (d : SimplexCategory) :
    restrict W (𝟙 d) = 𝟭 (Graph W d) := by
  refine CategoryTheory.Functor.ext restrictGraph_id ?_
  intro X Y f
  apply JTRowGraphCategory.Arrow.ext
  change f.operator =
    (eqToHom (restrictGraph_id X) : restrictGraph (𝟙 d) X ⟶ X).operator ≫
      f.operator ≫ (eqToHom (restrictGraph_id Y).symm : Y ⟶ restrictGraph (𝟙 d) Y).operator
  rw [eqToHom_operator, eqToHom_operator]
  simp

theorem restrict_comp (W : BiPresheaf) (a : d ⟶ m) (b : m ⟶ l) :
    restrict W (a ≫ b) = restrict W b ⋙ restrict W a := by
  refine CategoryTheory.Functor.ext (restrictGraph_comp a b) ?_
  intro X Y f
  apply JTRowGraphCategory.Arrow.ext
  change f.operator =
    (eqToHom (restrictGraph_comp a b X) :
      restrictGraph (a ≫ b) X ⟶ restrictGraph a (restrictGraph b X)).operator ≫
      f.operator ≫ (eqToHom (restrictGraph_comp a b Y).symm :
        restrictGraph a (restrictGraph b Y) ⟶ restrictGraph (a ≫ b) Y).operator
  rw [eqToHom_operator, eqToHom_operator]
  simp
  exact (Category.comp_id f.operator).symm

/-- Evaluating a restricted graph gives the same whole raw simplex restriction. -/
theorem restrictGraph_value (a : d ⟶ m) (G : Graph W m) :
    (restrictGraph a G).value = SSet.stdSimplex.map a ≫ G.value := by
  change lift (𝟙 (simplex d)) (SSet.stdSimplex.map a ≫ G.parameter) ≫
      generator W (d, G.degree) (W.map (horizontal a G.degree).op G.coefficient) =
    SSet.stdSimplex.map a ≫ lift (𝟙 (simplex m)) G.parameter ≫
      generator W (m, G.degree) G.coefficient
  have h : SSet.stdSimplex.map a ≫ lift (𝟙 (simplex m)) G.parameter =
      lift (SSet.stdSimplex.map a) (SSet.stdSimplex.map a ≫ G.parameter) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id]
    · simp only [Category.assoc, lift_snd]
  rw [← Category.assoc (SSet.stdSimplex.map a), h]
  exact (JTRealizationGraphGenerator.graph_generator_restriction W a _ _).symm

/-- The bisimplicial set of actual graphs and their coefficient arrows. -/
def rows (W : BiPresheaf) : BiSSet.{0} where
  obj q := nerve (Graph W q.unop)
  map j := nerveMap (restrict W j.unop)
  map_id q := by
    change nerveFunctor.map (restrict W (𝟙 q.unop)).toCatHom = _
    rw [restrict_id]
    exact nerveFunctor.map_id _
  map_comp j k := by
    change nerveFunctor.map (restrict W (k.unop ≫ j.unop)).toCatHom = _
    rw [restrict_comp]
    exact nerveFunctor.map_comp (restrict W j.unop).toCatHom (restrict W k.unop).toCatHom

/-- The horizontal simplicial direction of the actual realization, with
each vertical row constant at the raw simplices in that degree. -/
def constantRows (X : SSet.{0}) : BiSSet.{0} :=
  X ⋙ Functor.const SimplexCategoryᵒᵖ

private def rawIso (W : BiPresheaf) (d : SimplexCategory) :
    (simplex d ⟶ realization.obj W) ≅ (realization.obj W).obj (op d) :=
  Equiv.toIso SSet.yonedaEquiv

private def rowAugmentation (W : BiPresheaf) (d : SimplexCategory) :
    nerve (Graph W d) ⟶ constantSSet ((realization.obj W).obj (op d)) :=
  nerveMap (valueFunctor W d) ≫ (nerveDiscreteIso (simplex d ⟶ realization.obj W)).hom ≫
    (Functor.const SimplexCategoryᵒᵖ).map (rawIso W d).hom

/-- The coefficient nerve evaluates to the actual raw simplicial set,
commuting with every horizontal and vertical simplex operator. -/
def augmentation (W : BiPresheaf) : rows W ⟶ constantRows (realization.obj W) where
  app q := rowAugmentation W q.unop
  naturality {_ _} j := by
    apply NatTrans.ext
    funext q γ
    change SSet.yonedaEquiv ((restrictGraph j.unop (γ.obj 0)).value) =
      (realization.obj W).map j (SSet.yonedaEquiv ((γ.obj 0).value))
    rw [restrictGraph_value, SSet.yonedaEquiv_map_comp]
    rfl

theorem augmentation_row_weak (W : BiPresheaf) (q : SimplexCategoryᵒᵖ) :
    WeakEquivalence ((augmentation W).app q) := by
  haveI : WeakEquivalence (nerveMap (valueFunctor W q.unop)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (valueFunctor_GW W q.unop)
  change WeakEquivalence (nerveMap (valueFunctor W q.unop) ≫
    (nerveDiscreteIso (simplex q.unop ⟶ realization.obj W)).hom ≫
    (Functor.const SimplexCategoryᵒᵖ).map (rawIso W q.unop).hom)
  infer_instance

/-- A diagonal of vertically constant rows is the original simplicial set. -/
def constantRowsDiagonalIso (X : SSet.{0}) : diagonalFunctor.obj (constantRows X) ≅ X :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The original raw realization is Kan weakly equivalent to the diagonal
of the bisimplicial graph presentation. -/
def diagonalAugmentation (W : BiPresheaf) : diagonalFunctor.obj (rows W) ⟶ realization.obj W :=
  diagonalFunctor.map (augmentation W) ≫ (constantRowsDiagonalIso (realization.obj W)).hom

theorem diagonalAugmentation_weak (W : BiPresheaf) :
    WeakEquivalence (diagonalAugmentation W) := by
  haveI := DaggerNativeBisimplicialDiagonalWeak.diagonal_map_weak (augmentation W)
    (augmentation_row_weak W)
  unfold diagonalAugmentation
  infer_instance

end

end DaggerModels.PartII.JTRowGraphResolution
