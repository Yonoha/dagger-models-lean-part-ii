import DaggerModelsPartII.JTRealizationGenerators
import DaggerModelsPartII.JTGroupoidWeightGenerators
import NativeBisimplicialDiagonal

/-!
# The literal two-index JT realization as a diagonal of completed-simplex rows

The comparison uses the original two-index left Kan extension and the
original completed-simplex left Kan extension. Its components are calibrated
on their actual generators, retaining both simplex indices.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open DaggerNativeBisimplicialDiagonal
open scoped Prod

namespace DaggerModels.PartII.JTRealizationDiagonal

open OrdinaryJTRealization JTGroupoidWeightWeak

noncomputable section

/-- Curry the actual bisimplicial input, with its first coordinate as the
outer row and its second coordinate as a simplicial set. -/
def ordinaryCurry : BiPresheaf ⥤
    (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  ((prodOpEquiv (C := SimplexCategory)
    (D := SimplexCategory)).symm.congrLeft).inverse ⋙ Functor.curry

/-- Realize each literal row against the groupoid-completed simplex. -/
def rowwiseJ : BiPresheaf ⥤
    (SimplexCategoryᵒᵖ ⥤ SSet.{0}) :=
  ordinaryCurry ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ SSet.{0} SSet.{0}).obj
      jRealization

/-- The row at `q` has exactly the original coefficients `W(q,k)`. -/
@[simp] theorem ordinaryCurry_obj_obj_obj
    (W : BiPresheaf) (q k : SimplexCategory) :
    ((ordinaryCurry.obj W).obj (op q)).obj (op k) =
      W.obj (op (q, k)) := rfl

/-- Every input map acts on a row by its original `(q,k)` component. -/
@[simp] theorem ordinaryCurry_map_app_app
    {W V : BiPresheaf} (g : W ⟶ V)
    (q k : SimplexCategory) :
    ((ordinaryCurry.map g).app (op q)).app (op k) =
      g.app (op (q, k)) := rfl

/-- The horizontal simplicial operator on one row is the original first
component of the bisimplicial presheaf action. -/
@[simp] theorem ordinaryCurry_obj_map_app
    (W : BiPresheaf) {r q : SimplexCategory} (δ : r ⟶ q)
    (k : SimplexCategory) :
    ((ordinaryCurry.obj W).map δ.op).app (op k) =
      W.map (δ ×ₘ 𝟙 k).op := rfl

/-- The vertical simplicial operator on a row is the original second
component of the bisimplicial presheaf action. -/
@[simp] theorem ordinaryCurry_obj_obj_map
    (W : BiPresheaf) (q : SimplexCategory)
    {k l : SimplexCategory} (f : k ⟶ l) :
    ((ordinaryCurry.obj W).obj (op q)).map f.op =
      W.map (𝟙 q ×ₘ f).op := rfl

/-- The rowwise comparison map at `q` is the actual scalar J-realization
of the original row map. -/
@[simp] theorem rowwiseJ_map_app
    {W V : BiPresheaf} (g : W ⟶ V)
    (q : SimplexCategoryᵒᵖ) :
    (rowwiseJ.map g).app q =
      jRealization.map ((ordinaryCurry.map g).app q) := rfl

/-- Pointwise action of the literal product parameter on a pair of
simplex-index maps. -/
private theorem tFunctor_map_pair {p r : Index} (f : p ⟶ r)
    (q : SimplexCategoryᵒᵖ)
    (α : q.unop ⟶ p.1)
    (ξ : (GroupoidSimplex.parameter.obj p.2).obj q) :
    (tFunctor.map f).app q (ULift.up α, ξ) =
      (ULift.up (α ≫ f.1),
        (GroupoidSimplex.parameter.map f.2).app q ξ) := rfl

/-- Pointwise simplicial action of the same product parameter. -/
private theorem tFunctor_obj_map_pair (p : Index)
    {q r : SimplexCategoryᵒᵖ} (δ : q ⟶ r)
    (α : q.unop ⟶ p.1)
    (ξ : (GroupoidSimplex.parameter.obj p.2).obj q) :
    (tFunctor.obj p).map δ (ULift.up α, ξ) =
      (ULift.up (δ.unop ≫ α),
        (GroupoidSimplex.parameter.obj p.2).map δ ξ) := rfl

/-- Diagonal transport of a scalar generator first changes the row by the
literal horizontal action and then changes simplex degree. -/
private theorem diagonal_row_generator_map (W : BiPresheaf)
    {q r : SimplexCategoryᵒᵖ} (δ : q ⟶ r)
    (k : SimplexCategory)
    (w : ((ordinaryCurry.obj W).obj q).obj (op k))
    (ξ : (GroupoidSimplex.parameter.obj k).obj q) :
    ((diagonalFunctor.obj (rowwiseJ.obj W)).map δ)
        ((JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj q) k w).app q ξ) =
      (JTGroupoidWeightGenerators.generator
        ((ordinaryCurry.obj W).obj r) k
        (((ordinaryCurry.obj W).map δ).app (op k) w)).app r
          ((GroupoidSimplex.parameter.obj k).map δ ξ) := by
  let rowMap := (ordinaryCurry.obj W).map δ
  let w' := (rowMap.app (op k)) w
  have h₁ := JTGroupoidWeightGenerators.generator_naturality rowMap k w
  have h₁ξ := congrArg
    (fun t : GroupoidSimplex.parameter.obj k ⟶
        jRealization.obj ((ordinaryCurry.obj W).obj r) =>
      t.app q ξ) h₁
  have h₂ := (JTGroupoidWeightGenerators.generator
    ((ordinaryCurry.obj W).obj r) k w').naturality δ
  have h₂ξ := congrArg
    (fun f : (GroupoidSimplex.parameter.obj k).obj q →
        (jRealization.obj ((ordinaryCurry.obj W).obj r)).obj r => f ξ) h₂
  change ((jRealization.obj ((ordinaryCurry.obj W).obj r)).map δ)
      (((jRealization.map rowMap).app q)
        ((JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj q) k w).app q ξ)) = _
  have h₁ξ' :
      ((jRealization.map rowMap).app q)
          ((JTGroupoidWeightGenerators.generator
            ((ordinaryCurry.obj W).obj q) k w).app q ξ) =
        (JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj r) k w').app q ξ := by
    simpa only [NatTrans.comp_app, Function.comp_apply] using h₁ξ
  have h₂ξ' :
      ((jRealization.obj ((ordinaryCurry.obj W).obj r)).map δ)
          ((JTGroupoidWeightGenerators.generator
            ((ordinaryCurry.obj W).obj r) k w').app q ξ) =
        (JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj r) k w').app r
            ((GroupoidSimplex.parameter.obj k).map δ ξ) := by
    simpa only [Function.comp_apply] using h₂ξ.symm
  rw [h₁ξ']
  exact h₂ξ'

/-- The forward component on one literal two-index generator. At `q`, a
pair `(α, ξ)` is sent to the scalar J-generator in row `q` with coefficient
obtained by the original horizontal presheaf action along `(α, id)`. -/
private def forwardGeneratorLeg (W : BiPresheaf)
    (p : Index) (w : W.obj (op p)) :
    tFunctor.obj p ⟶ diagonalFunctor.obj (rowwiseJ.obj W) where
  app q z :=
    (JTGroupoidWeightGenerators.generator
      ((ordinaryCurry.obj W).obj q) p.2
      (W.map (z.1.down ×ₘ 𝟙 p.2).op w)).app q z.2
  naturality := by
    intro q r δ
    funext z
    let α : q.unop ⟶ p.1 := z.1.down
    let c := W.map (α ×ₘ 𝟙 p.2).op w
    let c' := W.map ((δ.unop ≫ α) ×ₘ 𝟙 p.2).op w
    have hc : (((ordinaryCurry.obj W).map δ).app (op p.2)) c = c' := by
      change W.map (δ.unop ×ₘ 𝟙 p.2).op
          (W.map (α ×ₘ 𝟙 p.2).op w) =
        W.map ((δ.unop ≫ α) ×ₘ 𝟙 p.2).op w
      change (W.map (α ×ₘ 𝟙 p.2).op ≫
        W.map (δ.unop ×ₘ 𝟙 p.2).op) w = _
      rw [← W.map_comp]
      congr 1
    have h := diagonal_row_generator_map W δ p.2 c z.2
    rw [hc] at h
    simpa [tFunctor_map, α, c, c'] using h.symm

/-- The generator leg is compatible with both simplex operators in the
original two-index coend. -/
private theorem forwardGeneratorLeg_relation (W : BiPresheaf)
    {p r : Index} (f : p ⟶ r) (w : W.obj (op r)) :
    tFunctor.map f ≫ forwardGeneratorLeg W r w =
      forwardGeneratorLeg W p (W.map f.op w) := by
  apply NatTrans.ext
  funext q
  funext z
  have h := JTGroupoidWeightGenerators.generator_relation
    ((ordinaryCurry.obj W).obj q) f.2
    (W.map ((z.1.down ≫ f.1) ×ₘ 𝟙 r.2).op w)
  have hξ := congrArg
    (fun t : GroupoidSimplex.parameter.obj p.2 ⟶
        jRealization.obj ((ordinaryCurry.obj W).obj q) =>
      t.app q z.2) h
  have hc :
      (((ordinaryCurry.obj W).obj q).map f.2.op)
          (W.map ((z.1.down ≫ f.1) ×ₘ 𝟙 r.2).op w) =
        W.map (z.1.down ×ₘ 𝟙 p.2).op (W.map f.op w) := by
    change W.map (𝟙 q.unop ×ₘ f.2).op
        (W.map ((z.1.down ≫ f.1) ×ₘ 𝟙 r.2).op w) =
      W.map (z.1.down ×ₘ 𝟙 p.2).op (W.map f.op w)
    change (W.map ((z.1.down ≫ f.1) ×ₘ 𝟙 r.2).op ≫
        W.map (𝟙 q.unop ×ₘ f.2).op) w =
      (W.map f.op ≫ W.map (z.1.down ×ₘ 𝟙 p.2).op) w
    rw [← W.map_comp, ← W.map_comp]
    congr 1
  rw [hc] at hξ
  simpa [forwardGeneratorLeg, tFunctor_map] using hξ

/-- The actual two-index LKE cocone with target the diagonal of rowwise
J-realization. -/
private def forwardCocone (W : BiPresheaf) :
    Cocone (simplexDiagram W) where
  pt := diagonalFunctor.obj (rowwiseJ.obj W)
  ι :=
    { app σ :=
        forwardGeneratorLeg W σ.left (uliftYonedaEquiv.{0} σ.hom)
      naturality := by
        intro σ τ f
        change tFunctor.map f.left ≫
          forwardGeneratorLeg W τ.left (uliftYonedaEquiv.{0} τ.hom) =
            forwardGeneratorLeg W σ.left (uliftYonedaEquiv.{0} σ.hom)
        rw [forwardGeneratorLeg_relation]
        congr 1
        rw [uliftYonedaEquiv_naturality]
        change uliftYonedaEquiv.{0}
          (uliftYoneda.map f.left ≫ τ.hom) =
            uliftYonedaEquiv.{0} σ.hom
        rw [CostructuredArrow.w f]
        rfl }

/-- Forward comparison, descended from the actual two-index pointwise
left Kan extension cocone. -/
private def forward (W : BiPresheaf) :
    realization.obj W ⟶ diagonalFunctor.obj (rowwiseJ.obj W) :=
  (simplexCoconeIsColimit W).desc (forwardCocone W)

/-- Normalization of the forward map on the original literal generator. -/
private theorem generator_forward (W : BiPresheaf)
    (p : Index) (w : W.obj (op p)) :
    JTRealizationGenerators.generator W p w ≫ forward W =
      forwardGeneratorLeg W p w := by
  rw [JTRealizationGenerators.generator_eq_cocone]
  simpa only [forward, forwardCocone, CostructuredArrow.mk_left,
    CostructuredArrow.mk_hom_eq_self, Equiv.apply_symm_apply] using
    (simplexCoconeIsColimit W).fac (forwardCocone W)
      (CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w))

/-- At a fixed outer simplex `q`, each scalar J-generator has a literal
image under the two-index generator with horizontal coordinate `id_q`. -/
private def inverseLegAt (W : BiPresheaf)
    (q : SimplexCategoryᵒᵖ)
    (k : SimplexCategory)
    (w : ((ordinaryCurry.obj W).obj q).obj (op k)) :
    (GroupoidSimplex.parameter.obj k).obj q →
      (realization.obj W).obj q :=
  fun ξ =>
    (JTRealizationGenerators.generator W (q.unop, k) w).app q
      (ULift.up (𝟙 q.unop), ξ)

/-- The inverse legs satisfy the vertical coend relation after evaluation
at `q`. -/
private theorem inverseLegAt_relation (W : BiPresheaf)
    (q : SimplexCategoryᵒᵖ)
    {k l : SimplexCategory} (f : k ⟶ l)
    (w : ((ordinaryCurry.obj W).obj q).obj (op l)) :
    (GroupoidSimplex.parameter.map f).app q ≫
        inverseLegAt W q l w =
      inverseLegAt W q k
        (((ordinaryCurry.obj W).obj q).map f.op w) := by
  funext ξ
  have h := JTRealizationGenerators.generator_relation W
    (𝟙 q.unop ×ₘ f) w
  have he := congrArg
    (fun t : tFunctor.obj (q.unop, k) ⟶ realization.obj W =>
      t.app q (ULift.up (𝟙 q.unop), ξ)) h
  simpa [inverseLegAt, tFunctor_map,
    ordinaryCurry_obj_obj_map] using he

/-- A Type-valued cocone on the actual scalar pointwise LKE diagram after
evaluation at `q`. This evaluation is essential: `id_q` does not give a
global map `J[k] ⟶ t!W`. -/
private def inverseCoconeAt (W : BiPresheaf)
    (q : SimplexCategoryᵒᵖ) :
    Cocone
      (JTGroupoidWeightGenerators.simplexDiagram
          ((ordinaryCurry.obj W).obj q) ⋙
        (evaluation _ _).obj q) where
  pt := (realization.obj W).obj q
  ι :=
    { app σ := inverseLegAt W q σ.left
        (uliftYonedaEquiv.{0} σ.hom)
      naturality := by
        intro σ τ f
        change (GroupoidSimplex.parameter.map f.left).app q ≫
          inverseLegAt W q τ.left (uliftYonedaEquiv.{0} τ.hom) =
            inverseLegAt W q σ.left (uliftYonedaEquiv.{0} σ.hom)
        rw [inverseLegAt_relation]
        congr 1
        rw [uliftYonedaEquiv_naturality]
        change uliftYonedaEquiv.{0}
          (uliftYoneda.map f.left ≫ τ.hom) =
            uliftYonedaEquiv.{0} σ.hom
        rw [CostructuredArrow.w f]
        rfl }

/-- Descent from the evaluated scalar LKE cocone at the specified simplex
degree. -/
private def inverseApp (W : BiPresheaf)
    (q : SimplexCategoryᵒᵖ) :
    ((rowwiseJ.obj W).obj q).obj q →
      (realization.obj W).obj q :=
  let E : SSet.{0} ⥤ Type := (evaluation _ _).obj q
  (isColimitOfPreserves E
    (JTGroupoidWeightGenerators.simplexCoconeIsColimit
      ((ordinaryCurry.obj W).obj q))).desc (inverseCoconeAt W q)

/-- Generator normalization of the evaluated inverse descent. -/
private theorem inverseApp_generator (W : BiPresheaf)
    (q : SimplexCategoryᵒᵖ) (k : SimplexCategory)
    (w : ((ordinaryCurry.obj W).obj q).obj (op k))
    (ξ : (GroupoidSimplex.parameter.obj k).obj q) :
    inverseApp W q
      ((JTGroupoidWeightGenerators.generator
        ((ordinaryCurry.obj W).obj q) k w).app q ξ) =
      inverseLegAt W q k w ξ := by
  let K := (ordinaryCurry.obj W).obj q
  let E : SSet.{0} ⥤ Type := (evaluation _ _).obj q
  let σ : JTGroupoidWeightGenerators.SimplexIndex K :=
    CostructuredArrow.mk (uliftYonedaEquiv.{0}.symm w)
  have hfac := (isColimitOfPreserves E
    (JTGroupoidWeightGenerators.simplexCoconeIsColimit K)).fac
      (inverseCoconeAt W q) σ
  have hξ := congrArg (fun f : (GroupoidSimplex.parameter.obj k).obj q →
      (realization.obj W).obj q => f ξ) hfac
  simpa [inverseApp, K, E, σ, inverseCoconeAt,
    JTGroupoidWeightGenerators.generator_eq_cocone] using hξ

/-- The inverse is simplicial: a horizontal operator is transported by
the original first-coordinate coend relation. -/
private theorem inverseApp_natural (W : BiPresheaf)
    {q r : SimplexCategoryᵒᵖ} (δ : q ⟶ r) :
    (fun x => inverseApp W q x) ≫
        (realization.obj W).map δ =
      ((diagonalFunctor.obj (rowwiseJ.obj W)).map δ) ≫
        (fun x => inverseApp W r x) := by
  funext x
  obtain ⟨k, w, ξ, rfl⟩ :=
    JTGroupoidWeightGenerators.exists_generator
      ((ordinaryCurry.obj W).obj q) q x
  let w' := (((ordinaryCurry.obj W).map δ).app (op k)) w
  have hj := diagonal_row_generator_map W δ k w ξ
  have hw := JTRealizationGenerators.generator_relation W
    (δ.unop ×ₘ 𝟙 k) w
  have hwξ := congrArg
    (fun t : tFunctor.obj (r.unop, k) ⟶ realization.obj W =>
      t.app r (ULift.up (𝟙 r.unop),
        (GroupoidSimplex.parameter.obj k).map δ ξ)) hw
  have hs := (JTRealizationGenerators.generator W (q.unop, k) w).naturality δ
  have hsξ := congrArg
    (fun f : (tFunctor.obj (q.unop, k)).obj q →
        (realization.obj W).obj r =>
      f (ULift.up (𝟙 q.unop), ξ)) hs
  have ht :
      (tFunctor.obj (q.unop, k)).map δ
          (ULift.up (𝟙 q.unop), ξ) =
        (ULift.up δ.unop,
          (GroupoidSimplex.parameter.obj k).map δ ξ) := by
    change
      (((SSet.stdSimplex.obj q.unop).map δ) (ULift.up (𝟙 q.unop)),
        (GroupoidSimplex.parameter.obj k).map δ ξ) = _
    congr 1
    change ULift.up (δ.unop ≫ 𝟙 q.unop) = ULift.up δ.unop
    simp
  have hsξ' :
      (realization.obj W).map δ
          ((JTRealizationGenerators.generator W (q.unop, k) w).app q
            (ULift.up (𝟙 q.unop), ξ)) =
        (JTRealizationGenerators.generator W (q.unop, k) w).app r
          (ULift.up δ.unop,
            (GroupoidSimplex.parameter.obj k).map δ ξ) := by
    have hraw := hsξ.symm
    change (realization.obj W).map δ
        ((JTRealizationGenerators.generator W (q.unop, k) w).app q
          (ULift.up (𝟙 q.unop), ξ)) =
      (JTRealizationGenerators.generator W (q.unop, k) w).app r
        ((tFunctor.obj (q.unop, k)).map δ
          (ULift.up (𝟙 q.unop), ξ)) at hraw
    simpa only [ht] using hraw
  have hwξ' :
      (JTRealizationGenerators.generator W (q.unop, k) w).app r
          (ULift.up δ.unop,
            (GroupoidSimplex.parameter.obj k).map δ ξ) =
        (JTRealizationGenerators.generator W (r.unop, k)
          (W.map (δ.unop ×ₘ 𝟙 k).op w)).app r
            (ULift.up (𝟙 r.unop),
              (GroupoidSimplex.parameter.obj k).map δ ξ) := by
    have hraw := hwξ
    change (JTRealizationGenerators.generator W (q.unop, k) w).app r
        ((tFunctor.map (δ.unop ×ₘ 𝟙 k)).app r
          (ULift.up (𝟙 r.unop),
            (GroupoidSimplex.parameter.obj k).map δ ξ)) = _ at hraw
    rw [tFunctor_map_pair] at hraw
    have hJ : GroupoidSimplex.parameter.map (𝟙 k) = 𝟙 _ :=
      GroupoidSimplex.parameter.map_id k
    rw [hJ] at hraw
    simpa only [Category.id_comp, NatTrans.id_app,
      id_eq] using hraw
  change (realization.obj W).map δ
      (inverseApp W q
        ((JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj q) k w).app q ξ)) =
    inverseApp W r
      ((diagonalFunctor.obj (rowwiseJ.obj W)).map δ
        ((JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj q) k w).app q ξ))
  rw [hj, inverseApp_generator, inverseApp_generator]
  simpa [inverseLegAt, w'] using hsξ'.trans hwξ'

/-- Inverse map assembled from the exact evaluated scalar descents. -/
private def inverse (W : BiPresheaf) :
    diagonalFunctor.obj (rowwiseJ.obj W) ⟶ realization.obj W where
  app q := inverseApp W q
  naturality := by
    intro q r δ
    exact (inverseApp_natural W δ).symm

/-- The evaluated scalar descent is a left inverse on every original
two-index generator. -/
private theorem forward_inverse (W : BiPresheaf) :
    forward W ≫ inverse W = 𝟙 (realization.obj W) := by
  apply NatTrans.ext
  funext q
  funext x
  obtain ⟨p, w, z, rfl⟩ := JTRealizationGenerators.exists_generator W q x
  have hf := generator_forward W p w
  have hfz := congrArg
    (fun t : tFunctor.obj p ⟶
        diagonalFunctor.obj (rowwiseJ.obj W) => t.app q z) hf
  have hr := JTRealizationGenerators.generator_relation W
    (z.1.down ×ₘ 𝟙 p.2) w
  have hrz := congrArg
    (fun t : tFunctor.obj (q.unop, p.2) ⟶ realization.obj W =>
      t.app q (ULift.up (𝟙 q.unop), z.2)) hr
  change inverseApp W q
      ((forward W).app q
        ((JTRealizationGenerators.generator W p w).app q z)) =
    (JTRealizationGenerators.generator W p w).app q z
  have hfz' :
      (forward W).app q
          ((JTRealizationGenerators.generator W p w).app q z) =
        (forwardGeneratorLeg W p w).app q z := by
    simpa only [NatTrans.comp_app, Function.comp_apply] using hfz
  rw [hfz']
  change inverseApp W q
      ((JTGroupoidWeightGenerators.generator
        ((ordinaryCurry.obj W).obj q) p.2
          (W.map (z.1.down ×ₘ 𝟙 p.2).op w)).app q z.2) = _
  rw [inverseApp_generator]
  have hα :
      (SSet.stdSimplex.map z.1.down).app q
          (ULift.up (𝟙 q.unop)) = z.1 := by
    cases z.1 with
    | up α =>
      change ULift.up (𝟙 q.unop ≫ α) = ULift.up α
      simp
  have hrz' :
      (JTRealizationGenerators.generator W p w).app q z =
        (JTRealizationGenerators.generator W (q.unop, p.2)
          (W.map (z.1.down ×ₘ 𝟙 p.2).op w)).app q
            (ULift.up (𝟙 q.unop), z.2) := by
    have hraw := hrz
    change (JTRealizationGenerators.generator W p w).app q
        ((tFunctor.map (z.1.down ×ₘ 𝟙 p.2)).app q
          (ULift.up (𝟙 q.unop), z.2)) = _ at hraw
    rw [tFunctor_map_pair] at hraw
    have hJ : GroupoidSimplex.parameter.map (𝟙 p.2) = 𝟙 _ :=
      GroupoidSimplex.parameter.map_id p.2
    rw [hJ] at hraw
    have hz : ULift.up z.1.down = z.1 := by cases z.1; rfl
    simpa only [Category.id_comp, NatTrans.id_app,
      id_eq, hz] using hraw
  simpa [inverseLegAt, forwardGeneratorLeg] using hrz'.symm

/-- The evaluated scalar descent is a right inverse on every rowwise
scalar generator, at every diagonal degree. -/
private theorem inverse_forward (W : BiPresheaf) :
    inverse W ≫ forward W =
      𝟙 (diagonalFunctor.obj (rowwiseJ.obj W)) := by
  apply NatTrans.ext
  funext q
  funext x
  obtain ⟨k, w, ξ, hx⟩ :=
    JTGroupoidWeightGenerators.exists_generator
      ((ordinaryCurry.obj W).obj q) q x
  rw [← hx]
  have hf := generator_forward W (q.unop, k) w
  have hfξ := congrArg
    (fun t : tFunctor.obj (q.unop, k) ⟶
        diagonalFunctor.obj (rowwiseJ.obj W) =>
      t.app q (ULift.up (𝟙 q.unop), ξ)) hf
  change (forward W).app q
      (inverseApp W q
        ((JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj W).obj q) k w).app q ξ)) =
    (JTGroupoidWeightGenerators.generator
      ((ordinaryCurry.obj W).obj q) k w).app q ξ
  rw [inverseApp_generator]
  change (forward W).app q
      ((JTRealizationGenerators.generator W (q.unop, k) w).app q
        (ULift.up (𝟙 q.unop), ξ)) = _
  have hfξ' :
      (forward W).app q
          ((JTRealizationGenerators.generator W (q.unop, k) w).app q
            (ULift.up (𝟙 q.unop), ξ)) =
        (forwardGeneratorLeg W (q.unop, k) w).app q
          (ULift.up (𝟙 q.unop), ξ) := by
    simpa only [NatTrans.comp_app, Function.comp_apply] using hfξ
  rw [hfξ']
  have hid : (𝟙 q.unop ×ₘ 𝟙 k) = 𝟙 (q.unop, k) := by simp
  change (JTGroupoidWeightGenerators.generator
      ((ordinaryCurry.obj W).obj q) k
        (W.map (𝟙 q.unop ×ₘ 𝟙 k).op w)).app q ξ = _
  simp only [hid, op_id, FunctorToTypes.map_id_apply]

/-- Naturality of one forward generator leg in the input presheaf. -/
private theorem forwardGeneratorLeg_naturality
    {W V : BiPresheaf} (g : W ⟶ V)
    (p : Index) (w : W.obj (op p)) :
    forwardGeneratorLeg W p w ≫
        diagonalFunctor.map (rowwiseJ.map g) =
      forwardGeneratorLeg V p (g.app (op p) w) := by
  apply NatTrans.ext
  funext q
  funext z
  let α : q.unop ⟶ p.1 := z.1.down
  let f : (q.unop, p.2) ⟶ p := α ×ₘ 𝟙 p.2
  have hc : (g.app (op (q.unop, p.2)))
      (W.map f.op w) = V.map f.op (g.app (op p) w) := by
    have h := g.naturality f.op
    exact congrFun h w
  have h := JTGroupoidWeightGenerators.generator_naturality
    ((ordinaryCurry.map g).app q) p.2 (W.map f.op w)
  have hξ := congrArg
    (fun t : GroupoidSimplex.parameter.obj p.2 ⟶
        jRealization.obj ((ordinaryCurry.obj V).obj q) =>
      t.app q z.2) h
  have hξ' :
      ((jRealization.map ((ordinaryCurry.map g).app q)).app q)
          ((JTGroupoidWeightGenerators.generator
            ((ordinaryCurry.obj W).obj q) p.2 (W.map f.op w)).app q z.2) =
        (JTGroupoidWeightGenerators.generator
          ((ordinaryCurry.obj V).obj q) p.2
            (g.app (op (q.unop, p.2)) (W.map f.op w))).app q z.2 := by
    simpa only [NatTrans.comp_app, Function.comp_apply,
      ordinaryCurry_map_app_app] using hξ
  rw [hc] at hξ'
  simpa [forwardGeneratorLeg,
    DaggerNativeBisimplicialDiagonal.diagonal_map_app,
    rowwiseJ_map_app, f, α] using hξ'

/-- The forward map is natural in arbitrary two-index presheaf maps;
the second component of the input is retained. -/
private theorem forward_natural {W V : BiPresheaf} (g : W ⟶ V) :
    realization.map g ≫ forward V =
      forward W ≫ diagonalFunctor.map (rowwiseJ.map g) := by
  apply NatTrans.ext
  funext q
  funext x
  obtain ⟨p, w, z, rfl⟩ := JTRealizationGenerators.exists_generator W q x
  have hs := JTRealizationGenerators.generator_naturality g p w
  have hfW := generator_forward W p w
  have hfV := generator_forward V p (g.app (op p) w)
  have hn := forwardGeneratorLeg_naturality g p w
  have hmor :
      JTRealizationGenerators.generator W p w ≫
          (realization.map g ≫ forward V) =
        JTRealizationGenerators.generator W p w ≫
          (forward W ≫ diagonalFunctor.map (rowwiseJ.map g)) := by
    calc
      _ = (JTRealizationGenerators.generator W p w ≫
          realization.map g) ≫ forward V := (Category.assoc _ _ _).symm
      _ = JTRealizationGenerators.generator V p
          (g.app (op p) w) ≫ forward V := by rw [hs]
      _ = forwardGeneratorLeg V p (g.app (op p) w) := hfV
      _ = forwardGeneratorLeg W p w ≫
          diagonalFunctor.map (rowwiseJ.map g) := hn.symm
      _ = (JTRealizationGenerators.generator W p w ≫ forward W) ≫
          diagonalFunctor.map (rowwiseJ.map g) := by rw [hfW]
      _ = _ := Category.assoc _ _ _
  have hmorξ := congrArg
    (fun t : tFunctor.obj p ⟶
        diagonalFunctor.obj (rowwiseJ.obj V) => t.app q z) hmor
  simpa only [NatTrans.comp_app, Function.comp_apply] using hmorξ

/-- The literal two-index realization is naturally the diagonal of
rowwise completed-simplex realization, calibrated by both generator
formulas above. -/
def realizationDiagonalIso : realization ≅ rowwiseJ ⋙ diagonalFunctor :=
  NatIso.ofComponents
    (fun W =>
      { hom := forward W
        inv := inverse W
        hom_inv_id := forward_inverse W
        inv_hom_id := inverse_forward W })
    (by
      intro W V g
      exact forward_natural g)

end

end DaggerModels.PartII.JTRealizationDiagonal
