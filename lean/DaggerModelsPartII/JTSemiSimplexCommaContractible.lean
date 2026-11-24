import TopCatModelCategory.SemiSimplexCategory
import DaggerModelsPartII.JTRowGraphFiber
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSemiSimplexCommaContractible

noncomputable section

private abbrev I (n : SimplexCategory) :=
  CostructuredArrow SemiSimplexCategory.toSimplexCategory n

/-- Append the last vertex of the target to an arbitrary simplex operator. -/
def extendSimplex {m : ℕ} {n : SimplexCategory} (f : ⦋m⦌ ⟶ n) :
    ⦋m + 1⦌ ⟶ n :=
  SimplexCategory.Hom.mk ⟨Fin.snoc f.toOrderHom (Fin.last n.len), by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      have hj : j = Fin.last _ := le_antisymm (Fin.le_last _) hij
      subst j
      rfl
    | cast i =>
      induction j using Fin.lastCases with
      | last => simpa only [Fin.snoc_castSucc, Fin.snoc_last, SimplexCategory.const] using
          (Fin.le_last (f.toOrderHom i))
      | cast j =>
        simpa only [Fin.snoc_castSucc] using f.toOrderHom.monotone
          (Fin.castSucc_le_castSucc_iff.mp hij)⟩

/-- Append a new last vertex to both sides of an injective operator. -/
def extendEmbedding {m k : ℕ} (j : ⦋m⦌ₛ ⟶ ⦋k⦌ₛ) :
    ⦋m + 1⦌ₛ ⟶ ⦋k + 1⦌ₛ :=
  OrderEmbedding.ofStrictMono
    (Fin.snoc (fun i ↦ ((SemiSimplexCategory.homEquiv j) i).castSucc)
      (Fin.last (k + 1))) (by
      intro i l hil
      induction i using Fin.lastCases with
      | last =>
        exact False.elim ((not_lt_of_ge (Fin.le_last _)) hil)
      | cast i =>
        induction l using Fin.lastCases with
        | last =>
          simpa only [Fin.snoc_castSucc, Fin.snoc_last, SimplexCategory.const] using
            (Fin.castSucc_lt_last ((SemiSimplexCategory.homEquiv j) i))
        | cast l =>
          simpa only [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff] using
            ((SemiSimplexCategory.homEquiv j).strictMono
              (Fin.castSucc_lt_castSucc_iff.mp hil)))

/-- The old simplex is the face omitting the new last vertex. -/
def includeInitial (m : ℕ) : ⦋m⦌ₛ ⟶ ⦋m + 1⦌ₛ :=
  Fin.castSuccOrderEmb

/-- Select the new last vertex of the enlarged simplex. -/
def includeLast (m : ℕ) : ⦋0⦌ₛ ⟶ ⦋m + 1⦌ₛ :=
  OrderEmbedding.ofStrictMono (fun _ ↦ Fin.last (m + 1)) (by
    intro i j hij
    change Fin 1 at i j
    have h : i = j := Subsingleton.elim i j
    subst j
    exact (lt_irrefl i hij).elim)

/-- Extending an identity gives the enlarged identity. -/
theorem extendEmbedding_id (m : ℕ) :
    extendEmbedding (𝟙 ⦋m⦌ₛ) = 𝟙 ⦋m + 1⦌ₛ := by
  apply SemiSimplexCategory.hom_ext
  ext i
  induction i using Fin.lastCases with
  | last => simp [extendEmbedding, SemiSimplexCategory.homEquiv, SemiSimplexCategory.smallCategory]
  | cast i =>
    simp [extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

/-- Extending injective operators commutes with their composition. -/
theorem extendEmbedding_comp {m k l : ℕ}
    (j : ⦋m⦌ₛ ⟶ ⦋k⦌ₛ) (h : ⦋k⦌ₛ ⟶ ⦋l⦌ₛ) :
    extendEmbedding (j ≫ h) = extendEmbedding j ≫ extendEmbedding h := by
  apply SemiSimplexCategory.hom_ext
  ext i
  induction i using Fin.lastCases with
  | last => simp [extendEmbedding, SemiSimplexCategory.homEquiv, SemiSimplexCategory.smallCategory]
  | cast i =>
    simp [extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

/-- The appended target operator commutes with each extended source operator. -/
theorem extendSimplex_natural {m k : ℕ} {n : SimplexCategory}
    (j : ⦋m⦌ₛ ⟶ ⦋k⦌ₛ) (f : ⦋k⦌ ⟶ n) :
    SemiSimplexCategory.toSimplexCategory.map (extendEmbedding j) ≫
      extendSimplex f = extendSimplex
        (SemiSimplexCategory.toSimplexCategory.map j ≫ f) := by
  apply SimplexCategory.Hom.ext'
  ext i
  induction i using Fin.lastCases with
  | last =>
    simp [extendEmbedding, extendSimplex, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.toSimplexCategory, SemiSimplexCategory.smallCategory]
  | cast i =>
    simp [extendEmbedding, extendSimplex, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.toSimplexCategory, SemiSimplexCategory.smallCategory]

/-- Restriction to the old face recovers the original target operator. -/
theorem extendSimplex_initial {m : ℕ} {n : SimplexCategory}
    (f : ⦋m⦌ ⟶ n) :
    SemiSimplexCategory.toSimplexCategory.map (includeInitial m) ≫
      extendSimplex f = f := by
  apply SimplexCategory.Hom.ext'
  ext i
  simp [includeInitial, extendSimplex, SemiSimplexCategory.toSimplexCategory,
    SemiSimplexCategory.homEquiv, SemiSimplexCategory.smallCategory,
    Fin.snoc_castSucc]

/-- Restriction to the new vertex recovers the last vertex of the target. -/
theorem extendSimplex_last {m : ℕ} {n : SimplexCategory}
    (f : ⦋m⦌ ⟶ n) :
    SemiSimplexCategory.toSimplexCategory.map (includeLast m) ≫
      extendSimplex f =
      SimplexCategory.const ⦋0⦌ n (Fin.last n.len) := by
  apply SimplexCategory.Hom.ext'
  ext i
  simp [includeLast, extendSimplex, SemiSimplexCategory.toSimplexCategory,
    SemiSimplexCategory.homEquiv, SemiSimplexCategory.smallCategory,
    Fin.snoc_last, SimplexCategory.const]

private def center (n : SimplexCategory) : I n :=
  CostructuredArrow.mk (SimplexCategory.const ⦋0⦌ n (Fin.last n.len))

private def extendFunctor (n : SimplexCategory) : I n ⥤ I n where
  obj c := CostructuredArrow.mk (extendSimplex c.hom)
  map {c d} u := CostructuredArrow.homMk (extendEmbedding u.left) (by
    change SemiSimplexCategory.toSimplexCategory.map (extendEmbedding u.left) ≫
      extendSimplex d.hom = extendSimplex c.hom
    rw [extendSimplex_natural, CostructuredArrow.w u])
  map_id c := CostructuredArrow.hom_ext _ _ (extendEmbedding_id c.left.len)
  map_comp u v := CostructuredArrow.hom_ext _ _
    (extendEmbedding_comp u.left v.left)

private def initialNat (n : SimplexCategory) : 𝟭 (I n) ⟶ extendFunctor n where
  app c := CostructuredArrow.homMk (includeInitial c.left.len)
    (extendSimplex_initial c.hom)
  naturality {c d} u := by
    apply CostructuredArrow.hom_ext
    change u.left ≫ includeInitial d.left.len =
      includeInitial c.left.len ≫ extendEmbedding u.left
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [includeInitial, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

private def lastNat (n : SimplexCategory) :
    (Functor.const (I n)).obj (center n) ⟶ extendFunctor n where
  app c := CostructuredArrow.homMk (includeLast c.left.len)
    (by
      change SemiSimplexCategory.toSimplexCategory.map (includeLast c.left.len) ≫
        extendSimplex c.hom = SimplexCategory.const ⦋0⦌ n (Fin.last n.len)
      exact extendSimplex_last c.hom)
  naturality {c d} u := by
    apply CostructuredArrow.hom_ext
    change includeLast d.left.len =
      includeLast c.left.len ≫ extendEmbedding u.left
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [includeLast, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

/-- The comma category of nonempty injective simplices under `n` has
weakly contractible nerve. The contraction adjoins the last vertex. -/
theorem point_GW (n : SimplexCategory) :
    GW (pointMap (nerve
      (CostructuredArrow SemiSimplexCategory.toSimplexCategory n))) := by
  let F : I n ⥤ Discrete PUnit.{1} := (Functor.const _).obj ⟨PUnit.unit⟩
  let G : Discrete PUnit.{1} ⥤ I n := (Functor.const _).obj (center n)
  let hR : F ⋙ G ⟶ extendFunctor n :=
    { app c := (lastNat n).app c
      naturality _ _ u := (lastNat n).naturality u }
  let hG : G ⋙ F ⟶ 𝟭 (Discrete PUnit.{1}) :=
    { app P := eqToHom (Subsingleton.elim _ P)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have hC : DaggerNerveHomotopy.NatTransZigzag (F ⋙ G) (𝟭 (I n)) :=
    .trans _ (extendFunctor n) _ (.rel _ _ ⟨hR⟩)
      (.symm _ _ (.rel _ _ ⟨initialNat n⟩))
  haveI : WeakEquivalence (nerveMap F) := (weakEquivalence_iff_GW _).mpr
    (DaggerNerveHomotopy.nerveMap_geometricW F G hC (.rel _ _ ⟨hG⟩))
  have he : nerveMap F ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit.{1}).hom =
      pointMap (nerve (I n)) :=
    pointIsTerminal.hom_ext _ _
  rw [← he]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTSemiSimplexCommaContractible
