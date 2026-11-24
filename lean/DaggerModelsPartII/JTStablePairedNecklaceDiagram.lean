import DaggerModelsPartII.JTStablePairedNormalization
import DaggerModelsPartII.JTStableNecklaceQuotient
import DaggerModelsPartII.JTTargetCommaExactEvaluation

/-!
# Simultaneous necklace normalization of finite diagrams in the original fixed-target comma

The replacement is an actual diagram in the original paired presentation.
Its comparison preserves the decorated base and both legs of each paired map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTStablePairedNecklaceDiagram

open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)
open JTStablePairedNormalization (normalizedAt endpointQuotients stableDiagram
  stableQuotient stableEvaluation stableQuotient_evaluation)
open JTGraphFactoredPresentation (TargetComma)

noncomputable section

private def compareAssembled {I J : Type} [SmallCategory I] [SmallCategory J]
    (F : J ⥤ Under JTXiEndpointCollapse.boundary)
    (S : I ⥤ BoundaryNecklaceComma.Presentation F) (code : I ⥤ NecklaceCode)
    (m : code ⋙ necklaceUnder ⟶ (S ⋙ Grothendieck.forget (fiberDiagram F)) ⋙ F)
    (q : S ⋙ sourceCode F ⟶ code)
    (h : ∀ p, necklaceUnder.map (q.app p) ≫ m.app p = (S.obj p).fiber.hom) :
    S ⟶ JTTargetCommaPullback.assemble F
      (S ⋙ Grothendieck.forget (fiberDiagram F)) code m where
  app p := ⟨𝟙 _, CostructuredArrow.homMk (q.app p) (by
    change necklaceUnder.map (q.app p) ≫ m.app p = _ ≫ F.map (𝟙 _)
    rw [h, F.map_id, Category.comp_id])⟩
  naturality {p p'} f := by
    apply JTTargetCommaPullback.operator_ext
    · change (S.map f).base ≫ 𝟙 _ = 𝟙 _ ≫ (S.map f).base
      rw [Category.comp_id, Category.id_comp]
    · let C := sourceCode F
      change C.map (_ ≫ _) = C.map (_ ≫ _)
      rw [Functor.map_comp, Functor.map_comp]
      exact q.naturality f

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] [∀ p : I, Finite (JTStableEndpointQuotient.Ends p)]
variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev E := JTTargetCommaPullback.diagram W x y Q
private abbrev G := JTTargetCommaPullback.Presentation W x y Q

variable (S : I ⥤ G W x y Q)

private abbrev labels := S ⋙ Grothendieck.forget (fiberDiagram (E W x y Q))
private abbrev codes := S ⋙ sourceCode (E W x y Q)
private abbrev outputs (p : I) := (normalizedAt W x y Q (S.obj p)).left

private def codeQuotients (p : I) : (codes W x y Q S).obj p ⟶ outputs W x y Q S p :=
  JTTargetCommaPullback.nativeArrow (endpointQuotients W x y Q S p)

/-- Actual necklace codes for the simultaneous image, with every original arrow. -/
def normalizedCodes : I ⥤ NecklaceCode :=
  JTStableNecklaceQuotient.normalizedDiagram (codes W x y Q S) (outputs W x y Q S)
    (codeQuotients W x y Q S)

/-- The coded diagram represents exactly the stable image under the boundary. -/
def representative : normalizedCodes W x y Q S ⋙ necklaceUnder ≅ stableDiagram W x y Q S :=
  JTStableNecklaceQuotient.diagramIso (codes W x y Q S) (outputs W x y Q S)
    (codeQuotients W x y Q S)

/-- The canonical quotient is natural in the actual necklace operators. -/
def codeQuotient : codes W x y Q S ⟶ normalizedCodes W x y Q S :=
  JTStableNecklaceQuotient.normalizedQuotient (codes W x y Q S) (outputs W x y Q S)
    (codeQuotients W x y Q S)

theorem codeQuotient_representative :
    Functor.whiskerRight (codeQuotient W x y Q S) necklaceUnder ≫
      (representative W x y Q S).hom = stableQuotient W x y Q S :=
  JTStableNecklaceQuotient.normalizedQuotient_iso (codes W x y Q S)
    (outputs W x y Q S) (codeQuotients W x y Q S)

private def pairedMap :
    normalizedCodes W x y Q S ⋙ necklaceUnder ⟶ labels W x y Q S ⋙ E W x y Q := by
  let a := Functor.associator S (Grothendieck.forget (fiberDiagram (E W x y Q))) (E W x y Q)
  exact (representative W x y Q S).hom ≫ stableEvaluation W x y Q S ≫ a.inv

/-- Assemble the normalized codes into the original fixed-target presentation. -/
def normalized : I ⥤ G W x y Q :=
  JTTargetCommaPullback.assemble (E W x y Q) (labels W x y Q S)
    (normalizedCodes W x y Q S) (pairedMap W x y Q S)

private theorem pairedMap_factor (p : I) :
    necklaceUnder.map ((codeQuotient W x y Q S).app p) ≫ (pairedMap W x y Q S).app p =
      (S.obj p).fiber.hom := by
  have h₁ := congrArg (fun a ↦ a.app p) (codeQuotient_representative W x y Q S)
  have h₂ := congrArg (fun a ↦ a.app p) (stableQuotient_evaluation W x y Q S)
  change necklaceUnder.map ((codeQuotient W x y Q S).app p) ≫
    (representative W x y Q S).hom.app p = (stableQuotient W x y Q S).app p at h₁
  change (stableQuotient W x y Q S).app p ≫ (stableEvaluation W x y Q S).app p =
    (S.obj p).fiber.hom at h₂
  change necklaceUnder.map ((codeQuotient W x y Q S).app p) ≫
    ((representative W x y Q S).hom.app p ≫ (stableEvaluation W x y Q S).app p ≫ 𝟙 _) = _
  rw [Category.comp_id, ← Category.assoc, h₁, h₂]

/-- The original diagram compares naturally to its normalized replacement over
the same decorated parameters, retaining the complete paired evaluation. -/
def comparison : S ⟶ normalized W x y Q S :=
  compareAssembled (E W x y Q) S (normalizedCodes W x y Q S) (pairedMap W x y Q S)
    (codeQuotient W x y Q S) (pairedMap_factor W x y Q S)

/-- Including every original internal necklace in the stable presentation
preserves the weak nerve type of the finite indexing category. -/
theorem forget_weak : WeakEquivalence
    (nerveMap (Grothendieck.forget (fiberDiagram (stableDiagram W x y Q S)))) := by
  apply JTStableNecklaceQuotient.forget_weak_of_necklace_iso
  intro p
  exact ⟨(normalizedCodes W x y Q S).obj p, ⟨(representative W x y Q S).app p⟩⟩

/-- The normalized evaluation is an actual diagram in the original fixed-target comma. -/
def normalizedEvaluation (T : I ⥤ TargetComma Q) : I ⥤ TargetComma Q :=
  normalized W x y Q (T ⋙ JTTargetCommaPullback.toPullback W x y Q) ⋙
    JTTargetCommaExactEvaluation.fromPresentation W x y Q

/-- The original fixed-target diagram and its normalization have naturally comparable evaluations. -/
def evaluationComparison (T : I ⥤ TargetComma Q) : T ⟶ normalizedEvaluation W x y Q T := by
  let c := JTTargetCommaPullback.equivalence W x y Q
  let e := JTTargetCommaExactEvaluation.fromPresentation W x y Q
  let i : c.inverse ⟶ e := (JTTargetCommaExactEvaluation.inverseIso W x y Q).hom
  let h := c.unitIso.hom ≫ Functor.whiskerLeft c.functor i
  exact Functor.whiskerLeft T h ≫
    Functor.whiskerRight (comparison W x y Q (T ⋙ c.functor)) e

end

end DaggerModels.PartII.JTStablePairedNecklaceDiagram
