import DaggerModelsPartII.JTMarkedFiniteParametrizedTargetFamilies
import DaggerModelsPartII.JTPaddedTimeOperators

/-! Add stable outside coefficient vertices while retaining the actual labels and operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelCoefficientPadding

open JTPaddedTimeOperators (pad inside extend extend_inside)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTMarkedParametrizedTargetFamilyJoin (Mark degree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)

section Ordinal

/-- The middle face in the ordinal with two added outside vertices. -/
def embedding (k : SimplexCategory) : k ⟶ pad k := SimplexCategory.Hom.mk (inside k)

theorem embedding_natural {k l : SimplexCategory} (f : k ⟶ l) :
    f ≫ embedding l = embedding k ≫ JTPaddedTimeOperators.map f := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext i
  exact (JTPaddedTimeOperators.map_inside f i).symm

/-- The inclusion of the middle face is split at each ordinal. -/
def retraction (k : SimplexCategory) : pad k ⟶ k := extend OrderHom.id

theorem embedding_retraction (k : SimplexCategory) : embedding k ≫ retraction k = 𝟙 k := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext i
  exact extend_inside (n := k) (m := k) OrderHom.id i

end Ordinal

variable {A : Type} [SmallCategory A]
variable {W : Source} {x y : Vertex W}

private abbrev B := boundaryPoint W x y
private abbrev I := OrderedLabelElements.Index W (B (W := W) (x := x) (y := y))
private abbrev pr := OrderedLabelElements.projection W (B (W := W) (x := x) (y := y))
private abbrev presheaf := OrderedLabelElements.labelPresheaf W (B (W := W) (x := x) (y := y))

variable (L : A ⥤ I (W := W) (x := x) (y := y))

private abbrev originalTag := L ⋙ pr (W := W) (x := x) (y := y)
private abbrev paddedTag :=
  originalTag L ⋙ (𝟭 NecklaceCode).prod JTPaddedTimeOperators.functor

private def inclusion : originalTag L ⟶ paddedTag L where
  app p := (𝟙 _, embedding ((originalTag L).obj p).2)
  naturality {p q} f := by
    let a := (originalTag L).map f
    exact Prod.ext ((Category.comp_id a.1).trans (Category.id_comp a.1).symm)
      (embedding_natural a.2)

private abbrev old := (originalTag L).op ⋙ presheaf (W := W) (x := x) (y := y)
private abbrev padded := (paddedTag L).op ⋙ presheaf (W := W) (x := x) (y := y)
private abbrev restrict : padded L ⟶ old L :=
  Functor.whiskerRight (NatTrans.op (inclusion L)) (presheaf (W := W) (x := x) (y := y))

private abbrev z (p : Aᵒᵖ) : (old L).obj p := (L.obj p.unop).unop.snd

private theorem z_natural {p q : Aᵒᵖ} (f : p ⟶ q) :
    (old L).map f (z L p) = z L q := (L.map f.unop).unop.property

/-- All literal extensions of each ordered label, with restriction on every original operator. -/
def choices : Aᵒᵖ ⥤ Type where
  obj p := {u : (padded L).obj p // (restrict L).app p u = z L p}
  map f u := ⟨(padded L).map f u.1,
    (congrFun ((restrict L).naturality f) u.1).trans
      ((congrArg ((old L).map f) u.2).trans (z_natural L f))⟩
  map_id p := by
    funext u
    apply Subtype.ext
    exact FunctorToTypes.map_id_apply (padded L) u.1
  map_comp f g := by
    funext u
    apply Subtype.ext
    exact FunctorToTypes.map_comp_apply (padded L) f g u.1

/-- These choices are exactly the ordinal-face extensions of the old ordered simplex. -/
def choicesEquiv (p : A) :
    (choices L).obj (op p) ≃
      {u : ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)).obj
          (op ((originalTag L).obj p).1)).obj (op (pad ((originalTag L).obj p).2)) //
        ((OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)).obj
          (op ((originalTag L).obj p).1)).map (embedding ((originalTag L).obj p).2).op u =
          OrderedLabelElements.label W (boundaryPoint W x y) (L.obj p)} := by
  let O := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W (boundaryPoint W x y)
  let k := ((originalTag L).obj p).2
  let T := ((originalTag L).obj p).1
  have h (u : (padded L).obj (op p)) :
      (restrict L).app (op p) u = (O.obj (op T)).map (embedding k).op u := by
    change (O.obj (op T)).map (embedding k).op
        ((O.map (𝟙 T).op).app (op (pad k)) u) = _
    rw [op_id, O.map_id]
    rfl
  exact {
    toFun := fun u ↦ ⟨u.val, (h u.val).symm.trans u.property⟩
    invFun := fun u ↦ ⟨u.val, (h u.val).trans u.property⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl
  }

abbrev Extensions := (choices L).Elementsᵒᵖ

/-- Remember all original operators and forget just the padded label. -/
abbrev base : Extensions L ⥤ A := (CategoryOfElements.π (choices L)).leftOp

/-- The actual padded ordered labels with their original native codes. -/
def labels : Extensions L ⥤ I (W := W) (x := x) (y := y) where
  obj p := op ⟨op ((paddedTag L).obj ((base L).obj p)), p.unop.snd.1⟩
  map {p q} f := Quiver.Hom.op ⟨(((base L ⋙ paddedTag L).map f).op),
    congrArg Subtype.val f.unop.property⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((base L ⋙ paddedTag L).map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op ((base L ⋙ paddedTag L).map_comp f g)

private def comparisonApp (p : Extensions L) :
    (base L ⋙ L).obj p ⟶ (labels L).obj p :=
  Quiver.Hom.op ⟨((inclusion L).app ((base L).obj p)).op, p.unop.snd.2⟩

/-- The middle face maps the original labels to the chosen compatible extensions. -/
def comparison : base L ⋙ L ⟶ labels L where
  app := comparisonApp L
  naturality {p q} f := by
    let f₀ := (base L).map f
    let P := pr (W := W) (x := x) (y := y)
    let a := comparisonApp L p
    let b := comparisonApp L q
    have h : P.map (L.map f₀ ≫ b) = P.map (a ≫ (labels L).map f) := by
      rw [P.map_comp, P.map_comp]
      exact (inclusion L).naturality f₀
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op h

/-- A padded ordered label exists at every original object. -/
theorem choices_nonempty (p : A) : Nonempty ((choices L).obj (op p)) := by
  let a : (paddedTag L).obj p ⟶ (originalTag L).obj p :=
    (𝟙 _, retraction ((originalTag L).obj p).2)
  let P := presheaf (W := W) (x := x) (y := y)
  refine ⟨⟨P.map a.op (z L (op p)), ?_⟩⟩
  change P.map ((inclusion L).app p).op (P.map a.op (z L (op p))) = _
  rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have h : (inclusion L).app p ≫ a = 𝟙 ((originalTag L).obj p) :=
    Prod.ext (Category.comp_id _) (embedding_retraction _)
  rw [h, op_id, FunctorToTypes.map_id_apply]


section Terminal

variable {C : Type} [SmallCategory C] (H : C ⥤ A)
variable {c : C} (hc : IsTerminal c)
variable (u : (choices L).obj (op (H.obj c)))

private def terminalObj (p : C) : Extensions L :=
  op ⟨op (H.obj p), (choices L).map (H.map (hc.from p)).op u⟩

/-- A single extension at a terminal object lifts the whole original diagram
to compatible padded labels. In particular this lifts every simplex of the nerve. -/
def liftFromTerminal : C ⥤ Extensions L where
  obj := terminalObj L H hc u
  map {p q} f := Quiver.Hom.op ⟨(H.map f).op, by
    change (choices L).map (H.map f).op ((choices L).map (H.map (hc.from q)).op u) =
      (choices L).map (H.map (hc.from p)).op u
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, ← H.map_comp,
      hc.hom_ext (f ≫ hc.from q) (hc.from p)]⟩
  map_id p := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op (H.map_id p)
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    exact congrArg Quiver.Hom.op (H.map_comp f g)

theorem liftFromTerminal_base : liftFromTerminal L H hc u ⋙ base L = H := rfl

end Terminal


/-- The first added coefficient is transported by all original arrows. -/
def lower : Mark (labels L) where
  vertex _ := 0
  naturality {_ _} f :=
    JTPaddedTimeOperators.map_first ((originalTag L).map ((base L).map f)).2

/-- The last added coefficient is transported by all original arrows. -/
def upper : Mark (labels L) where
  vertex p := Fin.last ((degree (labels L)).obj p).len
  naturality {_ _} f :=
    JTPaddedTimeOperators.map_last ((originalTag L).map ((base L).map f)).2

end
end DaggerModels.PartII.JTOrderedLabelCoefficientPadding
