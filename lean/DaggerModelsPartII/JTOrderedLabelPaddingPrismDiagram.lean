import DaggerModelsPartII.JTOrderedLabelPaddingPrism
import DaggerModelsPartII.JTOrderedLabelPaddingSemiIndex

/-! Assemble the ordered padded prism realizations over every original mixed operator. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTOrderedLabelPaddingPrismDiagram

open JTOrderedLabelPaddingPrism (blocks map_blocks Realizations timeMap_restriction)
open SemiSimplexCategory (toSimplexCategory)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev toSemiPresheaf : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj toSimplexCategory.op

variable {A : Type} [SmallCategory A]
variable (W : Source) (b : (Δ[0] : SSet.{0}) ⟶ OrderedNecklaceLabelDiagram.boundaryLabels W)
variable (L : A ⥤ OrderedLabelElements.Index W b)

private abbrev ordered := OrderedNecklaceLabelDiagram.orderedNecklaceLabels W b
private abbrev P := OrderedLabelElements.projection W b
private abbrev degrees := L ⋙ P W b ⋙ CategoryTheory.Prod.snd NecklaceCode SimplexCategory
private abbrev S := Aᵒᵖ × SemiSimplexCategoryᵒᵖ
private abbrev oldLabel (p : S (A := A)) := L.obj p.1.unop
private abbrev k (p : S (A := A)) := OrderedLabelElements.degree W b (oldLabel W b L p)
private abbrev n (p : S (A := A)) := toSimplexCategory.obj p.2.unop

/-- The padded coefficient maps into the fixed three-block ordinal. -/
def blockCoefficients : A ⥤ Over ⦋2⦌ where
  obj p := Over.mk (blocks ((degrees W b L).obj p))
  map f := Over.homMk (JTPaddedTimeOperators.map ((degrees W b L).map f)) (map_blocks _)
  map_id p := by
    apply Over.OverMorphism.ext
    change JTPaddedTimeOperators.functor.map ((degrees W b L).map (𝟙 p)) = 𝟙 _
    rw [(degrees W b L).map_id, JTPaddedTimeOperators.functor.map_id]
  map_comp f g := by
    apply Over.OverMorphism.ext
    change JTPaddedTimeOperators.functor.map ((degrees W b L).map (f ≫ g)) =
      JTPaddedTimeOperators.functor.map ((degrees W b L).map f) ≫
        JTPaddedTimeOperators.functor.map ((degrees W b L).map g)
    rw [(degrees W b L).map_comp, JTPaddedTimeOperators.functor.map_comp]

/-- The actual ordered realization ordinal for every label and time degree. -/
abbrev enlarged :=
  ((blockCoefficients W b L).prod (𝟭 SemiSimplexCategory)) ⋙
    JTCommonCoefficientParameter.parameter ⦋2⦌

/-- The exact simplicial extension spaces, with injective time operators. -/
abbrev original := JTOrderedLabelPaddingDiagram.along W b L ⋙ toSemiPresheaf

private abbrev U := Functor.uncurry.obj (original W b L)

/-- A simplex of the extension space together with one exact ordered realization. -/
abbrev Choice (p : S (A := A)) :=
  Σ v : (U W b L).obj p, Realizations (Y := (ordered W b).obj
    (op (OrderedLabelElements.necklace W b (oldLabel W b L p)))) (k := k W b L p)
      (n := n p) (a := OrderedLabelElements.label W b (oldLabel W b L p)) v

private theorem choice_ext {p : S (A := A)} {z z' : Choice W b L p}
    (h : z.1 = z'.1) (hs : z.2.val = z'.2.val) : z = z' := by
  rcases z with ⟨v, s⟩
  rcases z' with ⟨v', s'⟩
  cases h
  cases Subtype.ext hs
  rfl

private abbrev oldMap {p q : S (A := A)} (f : p ⟶ q) := L.map f.1.unop
private abbrev native :=
  (L ⋙ P W b ⋙ CategoryTheory.Prod.fst NecklaceCode SimplexCategory).op ⋙ ordered W b
private abbrev nativeMap {p q : S (A := A)} (f : p ⟶ q) := (native W b L).map f.1
private abbrev carrier := enlarged W b L ⋙ SSet.stdSimplex.{0}
private abbrev mixedMap {p q : S (A := A)} (f : p ⟶ q) :
    (q.1.unop, q.2.unop) ⟶ (p.1.unop, p.2.unop) := (f.1.unop, f.2.unop)

private def restrict {p q : S (A := A)} (f : p ⟶ q) (z : Choice W b L p) :
    Choice W b L q :=
  ⟨(U W b L).map f z.1, JTOrderedLabelPaddingPrism.restrict
    ((P W b).map (oldMap W b L f)).2
    (toSimplexCategory.map f.2.unop)
    (SemiSimplexCategory.homEquiv f.2.unop).injective (nativeMap W b L f)
    ((U W b L).map f z.1) z.1 (timeMap_restriction W b (oldMap W b L f)
      (toSimplexCategory.map f.2.unop) z.1) z.2⟩

private theorem restrict_val {p q : S (A := A)} (f : p ⟶ q) (z : Choice W b L p) :
    (restrict W b L f z).2.val =
      SSet.stdSimplex.map ((enlarged W b L).map (mixedMap f)) ≫ z.2.val ≫
        nativeMap W b L f := rfl

private theorem restrict_id (p : S (A := A)) (z : Choice W b L p) :
    restrict W b L (𝟙 p) z = z := by
  apply choice_ext W b L
  · exact FunctorToTypes.map_id_apply (U W b L) z.1
  · rw [restrict_val]
    change (carrier W b L).map (𝟙 (p.1.unop, p.2.unop)) ≫
      z.2.val ≫ (native W b L).map (𝟙 p.1) = z.2.val
    rw [(carrier W b L).map_id, (native W b L).map_id]
    exact (Category.id_comp _).trans (Category.comp_id _)

set_option maxHeartbeats 800000 in
private theorem restrict_comp {p q r : S (A := A)} (f : p ⟶ q) (g : q ⟶ r)
    (z : Choice W b L p) : restrict W b L (f ≫ g) z =
      restrict W b L g (restrict W b L f z) := by
  apply choice_ext W b L
  · exact FunctorToTypes.map_comp_apply (U W b L) f g z.1
  · rw [restrict_val, restrict_val, restrict_val]
    change (carrier W b L).map (mixedMap g ≫ mixedMap f) ≫
        z.2.val ≫ (native W b L).map (f.1 ≫ g.1) =
      (carrier W b L).map (mixedMap g) ≫
        ((carrier W b L).map (mixedMap f) ≫ z.2.val ≫ (native W b L).map f.1) ≫
          (native W b L).map g.1
    rw [(carrier W b L).map_comp, (native W b L).map_comp]
    simp only [Category.assoc]

/-- All chosen ordered realizations, natural jointly in the original label and time. -/
def mixed : S (A := A) ⥤ Type where
  obj p := Choice W b L p
  map f := restrict W b L f
  map_id p := funext (restrict_id W b L p)
  map_comp f g := funext (restrict_comp W b L f g)

/-- On the literal chosen label, restriction uses both of the original operators. -/
theorem mixed_map_val {p q : S (A := A)} (f : p ⟶ q) (z : Choice W b L p) :
    ((mixed W b L).map f z).2.val =
      SSet.stdSimplex.map ((enlarged W b L).map
        (show (q.1.unop, q.2.unop) ⟶ (p.1.unop, p.2.unop) from (f.1.unop, f.2.unop))) ≫
        z.2.val ≫ (ordered W b).map ((P W b).map (L.map f.1.unop)).1.op :=
  restrict_val W b L f z

/-- Forget the ordered realization while retaining the original extension simplex. -/
def mixedForget : mixed W b L ⟶ U W b L where
  app _ := Sigma.fst
  naturality _ _ _ := rfl

/-- The same diagram organized over the original labels. -/
abbrev choices := Functor.curryObj (mixed W b L)

/-- The forgetful transformation of the semisimplicial fibers. -/
def forget : choices W b L ⟶ original W b L :=
  Functor.curry.map (mixedForget W b L) ≫ (Functor.currying.unitIso.app (original W b L)).inv

end

end DaggerModels.PartII.JTOrderedLabelPaddingPrismDiagram
