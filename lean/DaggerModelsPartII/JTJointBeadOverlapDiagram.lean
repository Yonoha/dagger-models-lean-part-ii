import DaggerModelsPartII.JTJointBeadOverlapRestriction
import DaggerModelsPartII.JTFullPrismSupportedDiagram
import DaggerModelsPartII.JTConstantOrderedLabelDiagram
import DaggerModelsPartII.JTEndpointSimplexSlice

/-! The full timed overlap bead diagram over the literal joint point. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTJointBeadOverlapDiagram

open JTParametrizedTargetFamilies (Family codes evaluate)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient fullBeadParameter)
open JTPointTargetEvaluationCone (pointTarget)
open JTFullPrismSupportedDiagram (prisms)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (base : B ⥤ A) (D : B ⥤ SimplexCategory)
variable (h₀ : ∀ {a b : B} (f : a ⟶ b), (D.map f).toOrderHom 0 = 0)
variable (h₁ : ∀ {a b : B} (f : a ⟶ b),
  (D.map f).toOrderHom (Fin.last (D.obj a).len) = Fin.last (D.obj b).len)
variable (r : ∀ b : B, (NecklaceCode.single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j

variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (NecklaceCode.singleIso (D.obj a).len).inv ≫
    native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (NecklaceCode.singleIso (D.obj b).len).inv ≫
    native F j base D r b)

/-- The chosen horizontal operators preserve both endpoints. -/
def endpointDiagram : B ⥤ JTEndpointSimplexSlice.EndpointSimplex where
  obj b := ⟨D.obj b⟩
  map f := ⟨D.map f, ⟨h₀ f, h₁ f⟩⟩
  map_id b := by apply Subtype.ext; exact D.map_id b
  map_comp f g := by apply Subtype.ext; exact D.map_comp f g

/-- The genuine native single-bead diagram of the chosen horizontal simplices. -/
abbrev natives : B ⥤ NecklaceCode :=
  endpointDiagram D h₀ h₁ ⋙ JTEndpointSimplexSlice.bead

/-- The original coefficient ordinal, reindexed along the actual base diagram. -/
abbrev oldDegrees (L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y)
    (base : B ⥤ A) : B ⥤ SimplexCategory :=
  base ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- The actual full timed parameter before restricting to its used coefficient support. -/
def originalParameter : prisms D (base ⋙ time) ⟶ oldDegrees L base ⋙ J where
  app b := fullBeadParameter F (base.obj b) (D.obj b).len
    (native F j base D r b)
  naturality a b f := by
    let u : ⦋(D.obj a).len⦌ ⟶ ⦋(D.obj b).len⦌ :=
      eqToHom (D.obj a).mk_len ≫ D.map f ≫ eqToHom (D.obj b).mk_len.symm
    have hu : std.map u = std.map (D.map f) := by
      simp only [u, SimplexCategory.mk_len, eqToHom_refl, Category.id_comp,
        Category.comp_id]
    have hh : (NecklaceCode.singleIso (D.obj a).len).inv ≫
        native F j base D r a ≫ ((codes L).map (base.map f)).map =
      std.map u ≫ (NecklaceCode.singleIso (D.obj b).len).inv ≫
        native F j base D r b := by
      rw [hu]
      exact hr f
    have hp := JTParametrizedBeadGraph.fullBeadParameter_map
      (i := native F j base D r a) (i' := native F j base D r b) F (base.map f) u
      (by simpa only [Category.assoc] using hh)
    simpa only [hu] using hp

/-- All degrees used anywhere on each full bead prism form a natural diagram. -/
abbrev degrees : B ⥤ SimplexCategory :=
  JTFullPrismSupportedDiagram.support (originalParameter F j base D r hr)

/-- The supported full prism parameter is natural in both horizontal and time directions. -/
abbrev parameter : prisms D (base ⋙ time) ⟶ degrees F j base D r hr ⋙ J :=
  JTFullPrismSupportedDiagram.parameter (originalParameter F j base D r hr)

/-- At every object, the diagram uses the original bead's full timed support. -/
theorem degrees_obj (b : B) :
    (degrees F j base D r hr).obj b =
      JTJointBeadOverlapRestriction.usedDegree F (base.obj b) (D.obj b).len j (r b) :=
  rfl

/-- The diagram parameter is the original supported full-time bead parameter. -/
theorem parameter_app (b : B) :
    (parameter F j base D r hr).app b =
      JTJointBeadOverlapRestriction.timedParameter F (base.obj b) (D.obj b).len j (r b) :=
  rfl

/-- The constant ordered labels with the actual supported coefficient degrees. -/
abbrev labels : B ⥤ DecoratedNecklaceHomDiagram.Index W
    (jointCoefficient (Q := Q) j) (jointCoefficient (Q := Q) j) :=
  JTConstantOrderedLabelDiagram.diagram W (jointCoefficient (Q := Q) j)
    (natives D h₀ h₁) (degrees F j base D r hr)

/-- Interpret the supported parameter on the literal native single bead. -/
def nativeParameter (b : B) :
    ((natives D h₀ h₁).obj b).toSSet ⊗ J.obj (time.obj (base.obj b)) ⟶
      J.obj ((degrees F j base D r hr).obj b) :=
  ((NecklaceCode.singleIso (D.obj b).len).hom ⊗ₘ 𝟙 _) ≫
    (parameter F j base D r hr).app b

private theorem nativeIso_natural {a b : B} (f : a ⟶ b) :
    ((natives D h₀ h₁).map f).map ≫
      (NecklaceCode.singleIso (D.obj b).len).hom =
    (NecklaceCode.singleIso (D.obj a).len).hom ≫ std.map (D.map f) := by
  change ((NecklaceCode.singleIso (D.obj a).len).hom ≫ std.map (D.map f) ≫
    (NecklaceCode.singleIso (D.obj b).len).inv) ≫
      (NecklaceCode.singleIso (D.obj b).len).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem nativeParameter_natural {a b : B} (f : a ⟶ b) :
    (((natives D h₀ h₁).map f).map ⊗ₘ J.map (time.map (base.map f))) ≫
      nativeParameter F j base D h₀ h₁ r hr b =
    nativeParameter F j base D h₀ h₁ r hr a ≫
      J.map ((degrees F j base D r hr).map f) := by
  have hp := (parameter F j base D r hr).naturality f
  change (std.map (D.map f) ⊗ₘ J.map (time.map (base.map f))) ≫
    (parameter F j base D r hr).app b =
    (parameter F j base D r hr).app a ≫
      J.map ((degrees F j base D r hr).map f) at hp
  have hn := nativeIso_natural D h₀ h₁ f
  have ht :
      (((natives D h₀ h₁).map f).map ⊗ₘ J.map (time.map (base.map f))) ≫
        ((NecklaceCode.singleIso (D.obj b).len).hom ⊗ₘ 𝟙 _) =
      ((NecklaceCode.singleIso (D.obj a).len).hom ⊗ₘ 𝟙 _) ≫
        (std.map (D.map f) ⊗ₘ J.map (time.map (base.map f))) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom,
      Category.comp_id, Category.id_comp, hn]
  unfold nativeParameter
  rw [← Category.assoc, ht, Category.assoc, hp, Category.assoc]

/-- The original point-target Family for the whole overlap bead diagram. -/
def family : Family (pointTarget W (jointCoefficient (Q := Q) j))
    (labels F j base D h₀ h₁ r hr) (base ⋙ time) where
  collapse := JTOrderedLabelJointInsertion.toPointNatural (natives D h₀ h₁)
  parameter := nativeParameter F j base D h₀ h₁ r hr
  parameter_map {a b} f := by
    rw [JTConstantOrderedLabelDiagram.projection_map]
    exact nativeParameter_natural F j base D h₀ h₁ r hr f
  raw b := JTJointTraceObstruction.constant_raw_overPoint W
    (jointCoefficient (Q := Q) j) ((natives D h₀ h₁).obj b)
    ((degrees F j base D r hr).obj b) (time.obj (base.obj b))
    (nativeParameter F j base D h₀ h₁ r hr b)

/-- The whole evaluation has a natural cone at the genuine joint point. -/
def evaluation_toPoint : evaluate (family F j base D h₀ h₁ r hr) ⟶
    (Functor.const _).obj
      (JTPointTargetEvaluationCone.center W (jointCoefficient (Q := Q) j)) :=
  JTPointTargetEvaluationCone.evaluation_toPoint W (jointCoefficient (Q := Q) j)
    (family F j base D h₀ h₁ r hr)
    (JTConstantOrderedLabelDiagram.toPoint W (jointCoefficient (Q := Q) j)
      (natives D h₀ h₁) (degrees F j base D r hr))

/-- The whole fixed-point evaluation factors through a contractible comma slice. -/
theorem exists_contractible_factor :
    ∃ (C : Cat.{0, 0})
      (u : JTParametrizedTargetFamilies.Presentation
        (L := labels F j base D h₀ h₁ r hr) (time := base ⋙ time) ⥤ C)
      (v : C ⥤ JTGraphFactoredPresentation.TargetComma
        (pointTarget W (jointCoefficient (Q := Q) j))),
      GW (pointMap (nerve C)) ∧
        evaluate (family F j base D h₀ h₁ r hr) = u ⋙ v :=
  JTPointTargetEvaluationCone.exists_contractible_factor W
    (jointCoefficient (Q := Q) j) (family F j base D h₀ h₁ r hr)
    (JTConstantOrderedLabelDiagram.toPoint W (jointCoefficient (Q := Q) j)
      (natives D h₀ h₁) (degrees F j base D r hr))

end
end DaggerModels.PartII.JTJointBeadOverlapDiagram
