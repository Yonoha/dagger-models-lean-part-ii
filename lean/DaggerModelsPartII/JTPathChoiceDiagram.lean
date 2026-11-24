import DaggerModelsPartII.JTVariableFixedLiftChoiceDiagram
import DaggerModelsPartII.JTRelativePrismChoiceSpace

/-! All higher paths between two natural sections of a fibrant simplicial diagram. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTPathChoiceDiagram

noncomputable section

private abbrev Point := (Δ[0] : SSet.{0})
private abbrev Interval := (Δ[1] : SSet.{0})
private abbrev Boundary := (SSet.boundary 1 : SSet.{0})
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {I : Type} [SmallCategory I]
variable (F : Iᵒᵖ ⥤ SSet.{0})
variable (c₀ c₁ : (Functor.const Iᵒᵖ).obj Point ⟶ F)

/-- The two natural sections specify both vertices of every boundary. -/
def endpoints (a : I) : Boundary ⟶ F.obj (op a) :=
  SSet.boundary₁.desc
    (SSet.yonedaEquiv (c₀.app (op a)))
    (SSet.yonedaEquiv (c₁.app (op a)))

theorem endpoints_zero (a : I) :
    SSet.boundary₁.ι₀ ≫ endpoints F c₀ c₁ a = c₀.app (op a) :=
  by simp only [endpoints, SSet.boundary₁.ι₀_desc, Equiv.symm_apply_apply]

theorem endpoints_one (a : I) :
    SSet.boundary₁.ι₁ ≫ endpoints F c₀ c₁ a = c₁.app (op a) :=
  by simp only [endpoints, SSet.boundary₁.ι₁_desc, Equiv.symm_apply_apply]

theorem endpoints_map {a b : I} (f : a ⟶ b) :
    endpoints F c₀ c₁ b ≫ F.map f.op = endpoints F c₀ c₁ a := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc, endpoints_zero, endpoints_zero]
    simpa only [Category.id_comp] using (c₀.naturality f.op).symm
  · rw [← Category.assoc, endpoints_one, endpoints_one]
    simpa only [Category.id_comp] using (c₁.naturality f.op).symm

/-- The unique point-valued restriction, natural in the original index. -/
def toPoint : F ⟶ (Functor.const Iᵒᵖ).obj Point where
  app a := term (F.obj a)
  naturality _ _ _ := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The generic varying-square diagram for fixed endpoint paths. -/
def data : JTVariableFixedLiftChoiceDiagram.Diagram I where
  support := (Functor.const I).obj Boundary
  domain := (Functor.const I).obj Interval
  values := F
  boundary := (Functor.const Iᵒᵖ).obj Point
  incl := {
    app := fun _ ↦ (SSet.boundary 1).ι
    naturality := by intros; simp
  }
  restriction := toPoint F
  onSupport := endpoints F c₀ c₁
  base := fun _ ↦ term Interval
  onSupport_map := by
    intro a b f
    simpa only [Category.id_comp] using endpoints_map F c₀ c₁ f
  base_map := by
    intro a b f
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  comm := by
    intro a
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- All same-degree higher paths, natural in the original index category. -/
abbrev paths := JTVariableFixedLiftChoiceDiagram.choices (data F c₀ c₁)

/-- The exact path lift square at one original object. -/
abbrev square (a : I) := JTVariableFixedLiftChoiceDiagram.square (data F c₀ c₁) a

/-- Each fixed-endpoint path space is Kan when the original value is Kan. -/
theorem paths_kan (hF : ∀ a, (F.obj a).KanComplex) (a : Iᵒᵖ) :
    ((paths F c₀ c₁).obj a).KanComplex := by
  apply JTVariableFixedLiftChoiceDiagram.choices_kan (data F c₀ c₁)
  · intro x
    change Mono (SSet.boundary.{0} 1).ι
    infer_instance
  · intro x
    change Fibration (term (F.obj (op x)))
    letI : (F.obj (op x)).KanComplex := hF (op x)
    exact (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp
      inferInstance

/-- A trivial terminal map makes every full fixed-endpoint path space
weakly contractible, without choosing any path globally. -/
theorem paths_toPoint_weak (hF : ∀ a, (F.obj a).KanComplex)
    (hw : ∀ a, WeakEquivalence (term (F.obj a))) (a : Iᵒᵖ) :
    WeakEquivalence (term ((paths F c₀ c₁).obj a)) := by
  letI : Mono ((data F c₀ c₁).incl.app a.unop) := by
    change Mono (SSet.boundary.{0} 1).ι
    infer_instance
  letI : (F.obj a).KanComplex := hF a
  letI : Fibration ((data F c₀ c₁).restriction.app (op a.unop)) := by
    change Fibration (term (F.obj a))
    exact (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp
      inferInstance
  letI : WeakEquivalence ((data F c₀ c₁).restriction.app (op a.unop)) := by
    change WeakEquivalence (term (F.obj a))
    exact hw a
  exact JTRelativePrismChoiceSpace.fixedSquare_toPoint_weak_of_right
    (square F c₀ c₁ a.unop)

/-- All higher paths are retained in the total category of simplices. -/
abbrev Cover := JTVariableFixedLiftChoiceDiagram.Cover (data F c₀ c₁)

/-- Forgetting the path retains the original index. -/
abbrev projection : Cover F c₀ c₁ ⥤ I :=
  JTVariableFixedLiftChoiceDiagram.projection (data F c₀ c₁)

/-- The entire higher path diagram weakly covers the original category. -/
theorem projection_weak (hF : ∀ a, (F.obj a).KanComplex)
    (hw : ∀ a, WeakEquivalence (term (F.obj a))) :
    WeakEquivalence (nerveMap (projection F c₀ c₁)) := by
  let D := data F c₀ c₁
  let E := (GrothendieckTotalElements.totalDiagram (paths F c₀ c₁)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff _).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (paths F c₀ c₁)) ⋙
      CategoryTheory.Prod.fst Iᵒᵖ SimplexCategoryᵒᵖ))
  apply SynchronizedSimplicialParameters.projection_weak
  intro a
  haveI := paths_toPoint_weak F c₀ c₁ hF hw a
  let q := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
    DaggerOriginalProductGadget.pointIsTerminal
  haveI : WeakEquivalence
      (DaggerOriginalProductGadget.pointMap ((paths F c₀ c₁).obj a)) := by
    rw [← DaggerOriginalProductGadget.pointIsTerminal.hom_ext
      (term ((paths F c₀ c₁).obj a) ≫ q.hom)
      (DaggerOriginalProductGadget.pointMap ((paths F c₀ c₁).obj a))]
    infer_instance
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- Every path simplex is a genuine parameterized interval in the original value. -/
def pathMap (a : I) (n : SimplexCategory)
    (v : ((paths F c₀ c₁).obj (op a)).obj (op n)) :
    Interval ⊗ SSet.stdSimplex.obj n ⟶ F.obj (op a) :=
  JTFixedLiftSpaceTimeEquiv.timeMap (square F c₀ c₁ a) n v

/-- The full endpoint boundary and terminal base are fixed in every degree. -/
theorem pathMap_conditions (a : I) (n : SimplexCategory)
    (v : ((paths F c₀ c₁).obj (op a)).obj (op n)) :
    ((SSet.boundary 1).ι ▷ SSet.stdSimplex.obj n) ≫
        pathMap F c₀ c₁ a n v =
      fst Boundary (SSet.stdSimplex.obj n) ≫ endpoints F c₀ c₁ a ∧
      pathMap F c₀ c₁ a n v ≫ term (F.obj (op a)) =
        fst Interval (SSet.stdSimplex.obj n) ≫ term Interval := by
  exact JTFixedLiftSpaceTimeEquiv.timeMap_conditions (square F c₀ c₁ a) n v

/-- Every higher path starts at the first natural section. -/
theorem pathMap_zero (a : I) (n : SimplexCategory)
    (v : ((paths F c₀ c₁).obj (op a)).obj (op n)) :
    ((SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) ▷
      SSet.stdSimplex.obj n) ≫ pathMap F c₀ c₁ a n v =
      fst Point (SSet.stdSimplex.obj n) ≫ c₀.app (op a) := by
  let N := SSet.stdSimplex.obj n
  have h := (pathMap_conditions F c₀ c₁ a n v).1
  calc
    ((SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι) ▷ N) ≫
        pathMap F c₀ c₁ a n v =
      (SSet.boundary₁.ι₀ ▷ N) ≫
        (((SSet.boundary 1).ι ▷ N) ≫ pathMap F c₀ c₁ a n v) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = (SSet.boundary₁.ι₀ ▷ N) ≫
        (fst Boundary N ≫ endpoints F c₀ c₁ a) := by rw [h]
    _ = fst Point N ≫ (SSet.boundary₁.ι₀ ≫ endpoints F c₀ c₁ a) := by
          rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc]
    _ = fst Point N ≫ c₀.app (op a) := by rw [endpoints_zero]

/-- Every higher path ends at the second natural section. -/
theorem pathMap_one (a : I) (n : SimplexCategory)
    (v : ((paths F c₀ c₁).obj (op a)).obj (op n)) :
    ((SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) ▷
      SSet.stdSimplex.obj n) ≫ pathMap F c₀ c₁ a n v =
      fst Point (SSet.stdSimplex.obj n) ≫ c₁.app (op a) := by
  let N := SSet.stdSimplex.obj n
  have h := (pathMap_conditions F c₀ c₁ a n v).1
  calc
    ((SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι) ▷ N) ≫
        pathMap F c₀ c₁ a n v =
      (SSet.boundary₁.ι₁ ▷ N) ≫
        (((SSet.boundary 1).ι ▷ N) ≫ pathMap F c₀ c₁ a n v) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = (SSet.boundary₁.ι₁ ▷ N) ≫
        (fst Boundary N ≫ endpoints F c₀ c₁ a) := by rw [h]
    _ = fst Point N ≫ (SSet.boundary₁.ι₁ ≫ endpoints F c₀ c₁ a) := by
          rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc]
    _ = fst Point N ≫ c₁.app (op a) := by rw [endpoints_one]

/-- Higher paths transport by the original target operator, with both
endpoints preserved by the natural sections. -/
theorem pathMap_map {a b : I} (f : a ⟶ b) (n : SimplexCategory)
    (v : ((paths F c₀ c₁).obj (op b)).obj (op n)) :
    pathMap F c₀ c₁ a n (((paths F c₀ c₁).map f.op).app _ v) =
      pathMap F c₀ c₁ b n v ≫ F.map f.op := by
  let D := data F c₀ c₁
  have h := JTVariableFixedLiftSpaceMap.timeMap_mapSquare
    (JTVariableFixedLiftChoiceDiagram.square D b)
    (JTVariableFixedLiftChoiceDiagram.square D a)
    (D.support.map f) (D.domain.map f)
    (D.values.map f.op) (D.boundary.map f.op)
    (D.incl.naturality f) (D.onSupport_map f)
    (D.restriction.naturality f.op).symm (D.base_map f) n v
  change pathMap F c₀ c₁ a n (((paths F c₀ c₁).map f.op).app _ v) =
    ((𝟙 Interval) ▷ SSet.stdSimplex.obj n) ≫
      pathMap F c₀ c₁ b n v ≫ F.map f.op at h
  simpa only [MonoidalCategory.id_whiskerRight, Category.id_comp] using h

/-- Restriction in the simplex degree is restriction of the full path parameter. -/
theorem pathMap_time (a : I) {m n : SimplexCategory} (α : m ⟶ n)
    (v : ((paths F c₀ c₁).obj (op a)).obj (op n)) :
    pathMap F c₀ c₁ a m (((paths F c₀ c₁).obj (op a)).map α.op v) =
      (Interval ◁ SSet.stdSimplex.map α) ≫ pathMap F c₀ c₁ a n v :=
  JTFixedLiftSpaceTimeEquiv.timeMap_map (square F c₀ c₁ a) α v

/-- Original-index and simplex-degree operators act simultaneously on each path. -/
theorem pathMap_mixed {a b : I} (f : a ⟶ b) {m n : SimplexCategory}
    (α : m ⟶ n) (v : ((paths F c₀ c₁).obj (op b)).obj (op n)) :
    pathMap F c₀ c₁ a m
        (((paths F c₀ c₁).map f.op).app (op m)
          (((paths F c₀ c₁).obj (op b)).map α.op v)) =
      (Interval ◁ SSet.stdSimplex.map α) ≫
        pathMap F c₀ c₁ b n v ≫ F.map f.op := by
  rw [pathMap_map, pathMap_time, Category.assoc]

end

end DaggerModels.PartII.JTPathChoiceDiagram
