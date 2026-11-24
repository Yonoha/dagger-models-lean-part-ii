import DaggerModelsPartII.JTOrderedLabelPaddingPrismDiagram

/-! Decorated ordered labels carried by the chosen higher prism realizations. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismLabels

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

variable {A : Type} [SmallCategory A]
variable (W : Source)
variable (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev E := (JTOrderedLabelPaddingPrismDiagram.mixed W b L).Elementsᵒᵖ
private abbrev P := OrderedLabelElements.projection W b
private abbrev enlarged := JTOrderedLabelPaddingPrismDiagram.enlarged W b L
private abbrev original (p : E W b L) := L.obj p.unop.1.1.unop
private abbrev coords (p : E W b L) : A × SemiSimplexCategory :=
  (p.unop.1.1.unop, p.unop.1.2.unop)
private abbrev operator {p q : E W b L} (f : p ⟶ q) :
    coords W b L p ⟶ coords W b L q :=
  (f.unop.val.1.unop, f.unop.val.2.unop)

/-- The native necklace and actual common ordinal of each chosen realization. -/
def tag : E W b L ⥤ NecklaceCode × SimplexCategory where
  obj p := (((P W b).obj (original W b L p)).1,
    (enlarged W b L).obj (coords W b L p))
  map f := (((P W b).map (L.map (operator W b L f).1)).1,
    (enlarged W b L).map (operator W b L f))
  map_id p := by
    simp [operator]
  map_comp f g := by
    apply Prod.ext
    · simp [operator, Functor.map_comp]
    · change (enlarged W b L).map (operator W b L f ≫ operator W b L g) =
        (enlarged W b L).map (operator W b L f) ≫
          (enlarged W b L).map (operator W b L g)
      exact (enlarged W b L).map_comp _ _

private theorem label_natural {p q : E W b L} (f : p ⟶ q) :
    (OrderedLabelElements.labelPresheaf W b).map ((tag W b L).map f).op
      (SSet.yonedaEquiv q.unop.2.2.val) =
        SSet.yonedaEquiv p.unop.2.2.val := by
  have h := congrArg (fun z ↦ z.2.val) f.unop.property
  change ((JTOrderedLabelPaddingPrismDiagram.mixed W b L).map f.unop.val
      q.unop.2).2.val = p.unop.2.2.val at h
  rw [JTOrderedLabelPaddingPrismDiagram.mixed_map_val] at h
  apply SSet.yonedaEquiv.symm.injective
  change SSet.yonedaEquiv.symm
      (((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).obj
        (op ((tag W b L).obj p).1)).map ((tag W b L).map f).2.op
        (((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b).map
          ((tag W b L).map f).1.op).app (op ((tag W b L).obj q).2)
          (SSet.yonedaEquiv q.unop.2.2.val))) =
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv p.unop.2.2.val)
  rw [SSet.yonedaEquiv_symm_map, ← SSet.yonedaEquiv_symm_comp,
    Equiv.symm_apply_apply]
  simpa only [Equiv.symm_apply_apply] using h

/-- Each chosen higher prism realization gives its actual decorated ordered
label, natural in every original coefficient and injective time operator. -/
def labelIndex : E W b L ⥤ OrderedLabelElements.Index W b where
  obj p := op ⟨op ((tag W b L).obj p), SSet.yonedaEquiv p.unop.2.2.val⟩
  map f := Quiver.Hom.op ⟨((tag W b L).map f).op, label_natural W b L f⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((tag W b L).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((tag W b L).map_comp f g)

/-- The exact native necklace and common ordinal are recovered without a cast. -/
theorem projection_obj (p : E W b L) :
    (P W b).obj ((labelIndex W b L).obj p) = (tag W b L).obj p := rfl

/-- Both projected operators are exactly those of the source family. -/
theorem projection_map {p q : E W b L} (f : p ⟶ q) :
    (P W b).map ((labelIndex W b L).map f) = (tag W b L).map f := rfl

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismLabels
