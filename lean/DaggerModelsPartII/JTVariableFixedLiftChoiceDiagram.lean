import DaggerModelsPartII.JTVariableFixedLiftSpaceMap
import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Natural full choice spaces when both the coefficient and the native label vary. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory MonoidalClosed
open HomotopicalAlgebra DaggerModels CartesianMonoidalCategory DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTVariableFixedLiftChoiceDiagram

noncomputable section

private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- Source/support diagrams are covariant, whereas native mapping-label targets
are contravariant. Every stationary and base map retains this exact variance. -/
structure Diagram (I : Type) [SmallCategory I] where
  support : I ⥤ SSet.{0}
  domain : I ⥤ SSet.{0}
  values : Iᵒᵖ ⥤ SSet.{0}
  boundary : Iᵒᵖ ⥤ SSet.{0}
  incl : support ⟶ domain
  restriction : values ⟶ boundary
  onSupport : ∀ a, support.obj a ⟶ values.obj (op a)
  base : ∀ a, domain.obj a ⟶ boundary.obj (op a)
  onSupport_map : ∀ {a b} (f : a ⟶ b),
    support.map f ≫ onSupport b ≫ values.map f.op = onSupport a
  base_map : ∀ {a b} (f : a ⟶ b),
    domain.map f ≫ base b ≫ boundary.map f.op = base a
  comm : ∀ a, onSupport a ≫ restriction.app (op a) = incl.app a ≫ base a

variable {I : Type} [SmallCategory I] (D : Diagram I)

/-- The exact relative square for one member of the diagram. -/
def square (a : I) : CommSq (D.onSupport a) (D.incl.app a)
    (D.restriction.app (op a)) (D.base a) := ⟨D.comm a⟩

/-- The all-dimensional fixed-square fiber at one object. -/
abbrev fiber (a : I) := SSet.ihomToPullbackFiber (square D a)

/-- The full original domain and native operators act simultaneously on choices. -/
def restrict {a b : I} (f : a ⟶ b) : (fiber D b : SSet.{0}) ⟶ fiber D a :=
  JTVariableFixedLiftSpaceMap.mapSquare (square D b) (square D a)
    (D.support.map f) (D.domain.map f) (D.values.map f.op) (D.boundary.map f.op)
    (D.incl.naturality f) (D.onSupport_map f) (D.restriction.naturality f.op).symm
    (D.base_map f)

/-- The ambient internal-Hom formula is retained literally. -/
theorem restrict_ι {a b : I} (f : a ⟶ b) :
    restrict D f ≫ (fiber D a).ι = (fiber D b).ι ≫
      (MonoidalClosed.pre (D.domain.map f)).app (D.values.obj (op b)) ≫
        (ihom (D.domain.obj a)).map (D.values.map f.op) :=
  JTVariableFixedLiftSpaceMap.mapSquare_ι _ _ _ _ _ _ _ _ _ _


/-- The existing internal-Hom bifunctor supplies the strict ambient laws. -/
abbrev ambientDiagram : Iᵒᵖ ⥤ SSet.{0} :=
  (D.domain.op.prod' D.values) ⋙
    Functor.uncurry.obj (MonoidalClosed.internalHom (C := SSet.{0}))

@[reassoc]
theorem restrict_ambient {a b : I} (f : a ⟶ b) :
    restrict D f ≫ (fiber D a).ι =
      (fiber D b).ι ≫ (ambientDiagram D).map f.op := restrict_ι D f

private theorem restrict_id (a : I) : restrict D (𝟙 a) = 𝟙 _ := by
  apply (cancel_mono (fiber D a).ι).mp
  rw [restrict_ambient, op_id, (ambientDiagram D).map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

private theorem restrict_comp {a b c : I} (f : a ⟶ b) (g : b ⟶ c) :
    restrict D (f ≫ g) = restrict D g ≫ restrict D f := by
  apply (cancel_mono (fiber D a).ι).mp
  rw [restrict_ambient, op_comp, (ambientDiagram D).map_comp]
  rw [Category.assoc, restrict_ambient]
  simpa only [Category.assoc] using congrArg
    (fun q ↦ q ≫ (ambientDiagram D).map f.op) (restrict_ambient D g).symm

/-- Every simplex of every exact relative lift, natural in all specified operators. -/
def choices : Iᵒᵖ ⥤ SSet.{0} where
  obj a := fiber D a.unop
  map f := restrict D f.unop
  map_id a := restrict_id D a.unop
  map_comp f g := restrict_comp D g.unop f.unop

/-- Its inclusion in the original varying internal-Hom diagram is natural. -/
def inclusion : choices D ⟶ ambientDiagram D where
  app a := (fiber D a.unop).ι
  naturality _ _ f := restrict_ambient D f.unop

/-- Every full choice fiber is Kan under the original monic support and fibration. -/
theorem choices_kan (hi : ∀ a, Mono (D.incl.app a))
    (hp : ∀ a, Fibration (D.restriction.app (op a))) (a : Iᵒᵖ) :
    ((choices D).obj a).KanComplex := by
  haveI := hi a.unop
  haveI := hp a.unop
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan (square D a.unop)

/-- A Kan weak support inclusion makes the whole relative choice fiber weakly contractible. -/
theorem choices_toPoint_weak (hi : ∀ a, Mono (D.incl.app a))
    (hw : ∀ a, WeakEquivalence (D.incl.app a))
    (hp : ∀ a, Fibration (D.restriction.app (op a))) (a : Iᵒᵖ) :
    WeakEquivalence (term ((choices D).obj a)) := by
  haveI := hi a.unop
  haveI := hw a.unop
  haveI := hp a.unop
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak (square D a.unop)

/-- All higher choices are retained in the total category of simplices. -/
abbrev Cover := (GrothendieckTotalElements.totalDiagram (choices D)).Elementsᵒᵖ

/-- Projection retains the ORIGINAL index category, not a replacement target. -/
abbrev projection : Cover D ⥤ I :=
  (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (choices D)) ⋙
    CategoryTheory.Prod.fst Iᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The full choice diagram is a weak cover, with no globally selected lift. -/
theorem projection_weak (hi : ∀ a, Mono (D.incl.app a))
    (hw : ∀ a, WeakEquivalence (D.incl.app a))
    (hp : ∀ a, Fibration (D.restriction.app (op a))) :
    WeakEquivalence (nerveMap (projection D)) := by
  let E := (GrothendieckTotalElements.totalDiagram (choices D)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff _).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (choices D)) ⋙
      CategoryTheory.Prod.fst Iᵒᵖ SimplexCategoryᵒᵖ))
  apply SynchronizedSimplicialParameters.projection_weak
  intro a
  haveI := choices_toPoint_weak D hi hw hp a
  let q := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
    DaggerOriginalProductGadget.pointIsTerminal
  haveI : WeakEquivalence (DaggerOriginalProductGadget.pointMap ((choices D).obj a)) := by
    rw [← DaggerOriginalProductGadget.pointIsTerminal.hom_ext
      (term ((choices D).obj a) ≫ q.hom)
      (DaggerOriginalProductGadget.pointMap ((choices D).obj a))]
    infer_instance
  exact (weakEquivalence_iff_GW _).mp inferInstance

end
end DaggerModels.PartII.JTVariableFixedLiftChoiceDiagram
