import DaggerModelsPartII.JTOrderedLabelPaddingPrismLabels
import DaggerModelsPartII.JTOrderedLabelPaddingSliceComparison
import DaggerModelsPartII.JTOrderedLabelCoefficientPadding

/-! A chosen time slice compares the original label with its higher prism label. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismSliceArrow

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source)
variable (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev E := (JTOrderedLabelPaddingPrismDiagram.mixed W b L).Elementsᵒᵖ
private abbrev P := OrderedLabelElements.projection W b
private abbrev J := JTOrderedLabelPaddingPrismLabels.labelIndex W b L

/-- Forget the chosen realization and retain its original label index. -/
def originalBase : E W b L ⥤ A where
  obj p := p.unop.1.1.unop
  map f := f.unop.val.1.unop
  map_id _ := rfl
  map_comp _ _ := rfl

private abbrev k (p : E W b L) :=
  OrderedLabelElements.degree W b (L.obj ((originalBase W b L).obj p))
private abbrev n (p : E W b L) :=
  SemiSimplexCategory.toSimplexCategory.obj p.unop.1.2.unop
private abbrev oldTag (p : E W b L) :=
  (P W b).obj (L.obj ((originalBase W b L).obj p))
private abbrev degreeMap {p q : E W b L} (f : p ⟶ q) :=
  ((P W b).map (L.map ((originalBase W b L).map f))).2
private abbrev timeMap {p q : E W b L} (f : p ⟶ q) :=
  SemiSimplexCategory.toSimplexCategory.map f.unop.val.2.unop
private abbrev coeff (p : E W b L) (t : Fin ((n W b L p).len + 1)) :
    k W b L p ⟶ ((JTOrderedLabelPaddingPrismLabels.tag W b L).obj p).2 :=
  JTOrderedLabelCoefficientPadding.embedding (k W b L p) ≫
    JTCommonCoefficientParameter.slice (JTOrderedLabelPaddingPrism.blocks (k W b L p))
      (n W b L p) t

private theorem coeff_natural {p q : E W b L} (f : p ⟶ q)
    (t : Fin ((n W b L p).len + 1)) (t' : Fin ((n W b L q).len + 1))
    (ht : (timeMap W b L f).toOrderHom t = t') :
    coeff W b L p t ≫ ((JTOrderedLabelPaddingPrismLabels.tag W b L).map f).2 =
      degreeMap W b L f ≫ coeff W b L q t' := by
  let v := degreeMap W b L f
  let j := timeMap W b L f
  have hj : Function.Injective j.toOrderHom :=
    (SemiSimplexCategory.homEquiv f.unop.val.2.unop).injective
  calc
    _ = JTOrderedLabelCoefficientPadding.embedding (k W b L p) ≫
        (JTCommonCoefficientParameter.slice (JTOrderedLabelPaddingPrism.blocks (k W b L p))
          (n W b L p) t ≫ JTCommonCoefficientParameter.map
            (JTPaddedTimeOperators.map v) (JTOrderedLabelPaddingPrism.map_blocks v) j hj) := by
      rw [Category.assoc]
      rfl
    _ = JTOrderedLabelCoefficientPadding.embedding (k W b L p) ≫
        (JTPaddedTimeOperators.map v ≫
          JTCommonCoefficientParameter.slice (JTOrderedLabelPaddingPrism.blocks (k W b L q))
            (n W b L q) (j.toOrderHom t)) := by
      rw [JTCommonCoefficientParameter.slice_map]
      rfl
    _ = v ≫ coeff W b L q t' := by
      rw [ht, ← Category.assoc, ← JTOrderedLabelCoefficientPadding.embedding_natural]
      rfl

private theorem component_label (p : E W b L) (t : Fin ((n W b L p).len + 1)) :
    (OrderedLabelElements.labelPresheaf W b).map
      ((show oldTag W b L p ⟶ (JTOrderedLabelPaddingPrismLabels.tag W b L).obj p
        from (𝟙 _, coeff W b L p t)).op)
      (SSet.yonedaEquiv p.unop.2.2.val) =
        OrderedLabelElements.label W b (L.obj ((originalBase W b L).obj p)) := by
  let s := p.unop.2.2
  have h := JTOrderedLabelPaddingSliceComparison.slice_interior_fixed s t
  apply SSet.yonedaEquiv.symm.injective
  let O := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b
  let T := OrderedLabelElements.necklace W b (L.obj ((originalBase W b L).obj p))
  change SSet.yonedaEquiv.symm
      ((O.obj (op T)).map (coeff W b L p t).op
        (((O.map (𝟙 T).op).app (op ((JTOrderedLabelPaddingPrismLabels.tag W b L).obj p).2))
          (SSet.yonedaEquiv s.val))) =
        SSet.yonedaEquiv.symm
          (OrderedLabelElements.label W b (L.obj ((originalBase W b L).obj p)))
  simp [O.map_id]
  rw [SSet.yonedaEquiv_symm_map, SSet.yonedaEquiv_symm_map,
    Equiv.symm_apply_apply]
  simpa only [JTOrderedLabelPaddingSpace.embedding] using h

/-- A diagram of chosen realizations with a time vertex preserved by every arrow. -/
structure TimeSection {B : Type} [SmallCategory B] (H : B ⥤ E W b L) where
  vertex : ∀ u, Fin ((n W b L (H.obj u)).len + 1)
  natural : ∀ {u v : B} (f : u ⟶ v),
    (timeMap W b L (H.map f)).toOrderHom (vertex u) = vertex v

variable {B : Type} [SmallCategory B] (H : B ⥤ E W b L)
variable (t : TimeSection W b L H)

private def component (u : B) :
    (H ⋙ originalBase W b L ⋙ L).obj u ⟶ (H ⋙ J W b L).obj u :=
  Quiver.Hom.op ⟨((show oldTag W b L (H.obj u) ⟶
      (JTOrderedLabelPaddingPrismLabels.tag W b L).obj (H.obj u)
      from (𝟙 _, coeff W b L (H.obj u) (t.vertex u))).op),
    component_label W b L (H.obj u) (t.vertex u)⟩

/-- The original ordered label compares naturally with the label realized on
its chosen preserved time slice. -/
def comparison : H ⋙ originalBase W b L ⋙ L ⟶ H ⋙ J W b L where
  app := component W b L H t
  naturality {u v} f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    apply congrArg Quiver.Hom.op
    apply Prod.ext
    · change ((P W b).map (L.map ((originalBase W b L).map (H.map f)))).1 ≫ 𝟙 _ =
        𝟙 _ ≫ ((JTOrderedLabelPaddingPrismLabels.tag W b L).map (H.map f)).1
      simp
      rfl
    · change degreeMap W b L (H.map f) ≫ coeff W b L (H.obj v) (t.vertex v) =
        coeff W b L (H.obj u) (t.vertex u) ≫
          ((JTOrderedLabelPaddingPrismLabels.tag W b L).map (H.map f)).2
      exact (coeff_natural W b L (H.map f) (t.vertex u) (t.vertex v)
        (t.natural f)).symm

/-- The component uses the identity native map and the displayed slice map. -/
theorem projection_component (u : B) :
    (P W b).map ((comparison W b L H t).app u) =
      (𝟙 _, coeff W b L (H.obj u) (t.vertex u)) := rfl

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismSliceArrow
