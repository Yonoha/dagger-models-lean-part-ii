import DaggerModelsPartII.JTJointBeadNormalizationSupport
import DaggerModelsPartII.JTSupportedCoefficientPathCover

/-! Full relative coefficient paths for the actual normalized overlap-bead chains. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointBeadContractionChoices

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
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
variable (r : ∀ b : B, (single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (singleIso (D.obj b).len).inv ≫ native F j base D r b)

private abbrev I := JTJointBeadNormalizationDiagram.Index F j base D h₀ h₁ r hr
private abbrev ordered := JTJointBeadNormalizationDiagram.labels F j base D h₀ h₁ r hr
private abbrev S := JTJointBeadNormalizationSupport.support F j base D h₀ h₁ r hr
private abbrev u := JTJointBeadNormalizationSupport.incl F j base D h₀ h₁ r hr
private abbrev z := jointCoefficient (Q := Q) j

/-- The ordered normalized label has exactly the glued three-piece coefficient. -/
theorem old_eq_three_piece (p : I F j base D h₀ h₁ r hr) :
    JTSupportedOrderedCoefficientChoices.old W (z j)
        (ordered F j base D h₀ h₁ r hr) p =
      JTComposedPrismLabels.coefficient
        (JTThreePieceLabelOperators.coefficients
          (JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p)) := by
  change SSet.yonedaEquiv.symm
    (JTRealizedLabelEndpoints.orderedLabel W (z j) (z j) _ _
      (JTComposedPrismLabels.orderedPoint
        (JTThreePieceLabelOperators.coefficients
          (JTJointBeadNormalizationDiagram.data F j base D h₀ h₁ r hr p)))) = _
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact Equiv.symm_apply_apply SSet.yonedaEquiv _

/-- The normalized ordered coefficient is literally constant on its complete
natural inverse-image support. -/
theorem old_onSupport (p : I F j base D h₀ h₁ r hr) :
    std.map ((u F j base D h₀ h₁ r hr).app p) ≫
      JTSupportedOrderedCoefficientChoices.old W (z j)
        (ordered F j base D h₀ h₁ r hr) p =
      JTSupportedOrderedCoefficientChoices.supportedConstant W (z j)
        (ordered F j base D h₀ h₁ r hr)
        (S F j base D h₀ h₁ r hr) p := by
  rw [old_eq_three_piece]
  exact JTJointBeadNormalizationSupport.coefficient_onSupport F j base D h₀ h₁ r hr p

/-- Padding by the two correction edges makes every actual normalized code positive. -/
theorem code_pos (p : I F j base D h₀ h₁ r hr) :
    0 < ((codes (ordered F j base D h₀ h₁ r hr)).obj p).len := by
  change 0 < 1 + ((D.obj
    ((JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr).obj p)).len + 1)
  omega

/-- All higher same-degree contractions of the actual normalized label. -/
abbrev spaces := JTSupportedCoefficientPathCover.spaces W (z j)
  (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
  (u F j base D h₀ h₁ r hr)
  (old_onSupport F j base D h₀ h₁ r hr)

/-- The category of all normalized coefficient path simplices. -/
abbrev Cover := JTSupportedCoefficientPathCover.Cover W (z j)
  (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
  (u F j base D h₀ h₁ r hr)
  (old_onSupport F j base D h₀ h₁ r hr)

/-- Forget the contraction while retaining the exact normalized bead chain. -/
abbrev projection : Cover F j base D h₀ h₁ r hr ⥤ I F j base D h₀ h₁ r hr :=
  JTSupportedCoefficientPathCover.projection W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr)

/-- The simplex degree of the full contraction choice. -/
abbrev choiceTime : Cover F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  JTSupportedCoefficientPathCover.choiceTime W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr)

/-- The unchanged coefficient degree on the complete contraction cover. -/
abbrev coefficient : Cover F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  JTSupportedCoefficientPathCover.coefficient W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr)

/-- The entire actual normalized coefficient contracts in its original degree,
with both outer native endpoints and the complete support fixed. -/
abbrev pathCoefficient (p : I F j base D h₀ h₁ r hr) (n : SimplexCategory)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op p)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) p n v

/-- The actual full inverse-image support remains constant at every path simplex. -/
abbrev pathCoefficient_support (p : I F j base D h₀ h₁ r hr) (n : SimplexCategory)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op p)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient_support W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) p n v

/-- Both original outer native endpoints stay fixed at every path simplex. -/
abbrev pathCoefficient_boundary (p : I F j base D h₀ h₁ r hr) (n : SimplexCategory)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op p)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient_boundary W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) p n v

/-- The first endpoint is the entire old normalized coefficient. -/
abbrev pathCoefficient_zero_old (p : I F j base D h₀ h₁ r hr) (n : SimplexCategory)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op p)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient_zero_old W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) p n v

/-- The second endpoint is the literal joint coefficient at the same degree. -/
abbrev pathCoefficient_one_constant (p : I F j base D h₀ h₁ r hr)
    (n : SimplexCategory)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op p)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient_one_constant W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) p n v

/-- Chain arrows and arbitrary higher path-time operators commute with the
whole original-degree coefficient prism. -/
abbrev pathCoefficient_mixed {p q : I F j base D h₀ h₁ r hr} (f : p ⟶ q)
    {m n : SimplexCategory} (α : m ⟶ n)
    (v : ((spaces F j base D h₀ h₁ r hr).obj (op q)).obj (op n)) :=
  JTSupportedCoefficientPathCover.pathCoefficient_mixed W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr) f α v

/-- The contraction choice category is a nerve weak cover of every normalized chain. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j base D h₀ h₁ r hr)) :=
  JTSupportedCoefficientPathCover.projection_weak W (z j)
    (ordered F j base D h₀ h₁ r hr) (S F j base D h₀ h₁ r hr)
    (u F j base D h₀ h₁ r hr)
    (old_onSupport F j base D h₀ h₁ r hr)
    (JTJointBeadNormalizationSupport.incl_mono F j base D h₀ h₁ r hr)
    hW (code_pos F j base D h₀ h₁ r hr)

/-- Forget all coefficient paths and normalized chains, retaining each original
specified overlap-bead chart and every chart arrow. -/
abbrev toCharts : Cover F j base D h₀ h₁ r hr ⥤ B :=
  projection F j base D h₀ h₁ r hr ⋙
    JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr

/-- The complete coefficient contraction cover is weak over the original
specified bead charts. -/
theorem toCharts_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toCharts F j base D h₀ h₁ r hr)) := by
  haveI : WeakEquivalence (nerveMap (projection F j base D h₀ h₁ r hr)) :=
    projection_weak F j base D h₀ h₁ r hr hW
  haveI : WeakEquivalence (nerveMap
      (JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr)) :=
    JTJointBeadNormalizationDiagram.toCharts_weak F j base D h₀ h₁ r hr hW
  change WeakEquivalence (nerveMap (projection F j base D h₀ h₁ r hr) ≫
    nerveMap (JTJointBeadNormalizationDiagram.toCharts F j base D h₀ h₁ r hr))
  infer_instance

end
end DaggerModels.PartII.JTJointBeadContractionChoices
