import DaggerModelsPartII.JTOrderedLabelPaddingPrismChains

/-! A common decorated label for the two coefficient maps of each moving chain. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismChains

noncomputable section

variable {A : Type} [SmallCategory A] (W : SegalLocalizers.ReverseDaggerSpace.{0})
variable (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev P := OrderedLabelElements.projection W b
private abbrev Y := OrderedLabelElements.labelPresheaf W b
private abbrev oldTag := oldLabels W b L ⋙ P W b
private abbrev newTag := realizedLabels W b L ⋙ P W b

private abbrev commonTag :=
  ((oldTag W b L ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory).prod'
    (ordinals W b L))

private def oldOperator : commonTag W b L ⟶ oldTag W b L where
  app p := (𝟙 _, (toOriginal W b L).app p)
  naturality _ _ f :=
    Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((toOriginal W b L).naturality f)

private def newOperator : commonTag W b L ⟶ newTag W b L where
  app p := (𝟙 _, (toRealized W b L).app p)
  naturality _ _ f :=
    Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((toRealized W b L).naturality f)

private def commonLabel (p : Index W b L) :
    (Y W b).obj (op ((commonTag W b L).obj p)) :=
  (Y W b).map ((oldOperator W b L).app p).op
    (OrderedLabelElements.label W b ((oldLabels W b L).obj p))

private theorem common_natural {p q : Index W b L} (f : p ⟶ q) :
    (Y W b).map ((commonTag W b L).map f).op (commonLabel W b L q) =
      commonLabel W b L p := by
  unfold commonLabel
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, (oldOperator W b L).naturality f]
  rw [op_comp, FunctorToTypes.map_comp_apply]
  exact congrArg ((Y W b).map ((oldOperator W b L).app p).op)
    ((oldLabels W b L).map f).unop.property

/-- The simplex obtained by restricting the original label to the entire ordered chain. -/
def chainLabels : Index W b L ⥤ OrderedLabelElements.Index W b where
  obj p := op ⟨op ((commonTag W b L).obj p), commonLabel W b L p⟩
  map f := Quiver.Hom.op ⟨((commonTag W b L).map f).op, common_natural W b L f⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((commonTag W b L).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((commonTag W b L).map_comp f g)

/-- The common label maps to the original one through the quotient of chain coefficients. -/
def chainToOriginal : chainLabels W b L ⟶ oldLabels W b L where
  app p := Quiver.Hom.op ⟨((oldOperator W b L).app p).op, rfl⟩
  naturality _ _ f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((oldOperator W b L).naturality f)

/-- The same common label maps to the realized one through the inclusion of the chain. -/
def chainToRealized : chainLabels W b L ⟶ realizedLabels W b L where
  app p := Quiver.Hom.op ⟨((newOperator W b L).app p).op, by
    let O := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b
    let T := ((commonTag W b L).obj p).1
    let i := (realizedLabels W b L).obj p
    let j := (oldLabels W b L).obj p
    let α := (toOriginal W b L).app p
    let β := (toRealized W b L).app p
    change (O.obj (op T)).map β.op
        (((O.map (𝟙 T).op).app (op (OrderedLabelElements.degree W b i)))
          (OrderedLabelElements.label W b i)) =
      (O.obj (op T)).map α.op
        (((O.map (𝟙 T).op).app (op (OrderedLabelElements.degree W b j)))
          (OrderedLabelElements.label W b j))
    rw [op_id, O.map_id]
    simpa only [NatTrans.id_app, types_id_apply] using (labels_restrict W b L p).symm⟩
  naturality _ _ f := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((newOperator W b L).naturality f)

theorem chainToOriginal_projection (p : Index W b L) :
    (P W b).map ((chainToOriginal W b L).app p) = (𝟙 _, (toOriginal W b L).app p) := rfl

theorem chainToRealized_projection (p : Index W b L) :
    (P W b).map ((chainToRealized W b L).app p) = (𝟙 _, (toRealized W b L).app p) := rfl

end
end DaggerModels.PartII.JTOrderedLabelPaddingPrismChains
