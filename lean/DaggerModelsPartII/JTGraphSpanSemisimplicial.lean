import DaggerModelsPartII.HomSpanRestriction
import DaggerModelsPartII.JTSemiSimplexElementsWeak

/-! A weak cover of the original span index with genuine injective phase operators. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphSpanSemisimplicial

open HomSpanRestriction (Spans smaller)
open JTSemiSimplexElementsWeak (elementForget elementForget_weakEquivalence)

noncomputable section

private abbrev semi (X : SSet.{0}) := SemiSimplexCategory.toSimplexCategory.op ⋙ X

/-- Factorizations of actual injective operators in the simplicial subset. -/
abbrev Index (X : SSet.{0}) := Spans (semi X).Elementsᵒᵖ

/-- Retain the very same factorizations in the full simplex category. -/
abbrev intoFull (X : SSet.{0}) : Index X ⥤ Spans X.Elementsᵒᵖ :=
  HomSpanRestriction.map (elementForget X)

/-- The smaller simplex of a span gives its literal phase functor. -/
abbrev phase (X : SSet.{0}) : Index X ⥤ SemiSimplexCategory :=
  smaller _ ⋙ (CategoryOfElements.π (semi X)).leftOp

/-- On nerves the exact cover by injective-operator spans is weak. -/
theorem intoFull_weak (X : SSet.{0}) : WeakEquivalence (nerveMap (intoFull X)) := by
  let f := intoFull X
  let p := smaller ((semi X).Elementsᵒᵖ)
  let q := smaller X.Elementsᵒᵖ
  let g := elementForget X
  letI : WeakEquivalence (nerveMap p) := HomSpanRestriction.smaller_weak _
  letI : WeakEquivalence (nerveMap q) := HomSpanRestriction.smaller_weak _
  letI : WeakEquivalence (nerveMap g) := elementForget_weakEquivalence X
  have e : nerveMap f ≫ nerveMap q = nerveMap p ≫ nerveMap g :=
    congrArg nerveMap (HomSpanRestriction.smaller_natural g)
  apply (weakEquivalence_postcomp_iff _ (nerveMap q)).mp
  rw [e]
  infer_instance

/-- The phase map agrees exactly with the original full span time operator. -/
theorem phase_time (X : SSet.{0}) :
    phase X ⋙ SemiSimplexCategory.toSimplexCategory =
      intoFull X ⋙ smaller X.Elementsᵒᵖ ⋙ (CategoryOfElements.π X).leftOp := rfl

variable {C : Type} [SmallCategory C] (A : (nerve C).Subcomplex)

private abbrev original := HomSpanRestriction.map ((CategoryOfElements.map A.ι).op)

/-- An injective span of the subcomplex is an actual span of the original nerve. -/
abbrev intoOriginal : Index A.toSSet ⥤ JTGraphCylinderSimplexSpan.SpanIndex C :=
  intoFull A.toSSet ⋙ original A

/-- The original smaller time simplex is exactly the included phase. -/
theorem phase_original :
    phase A.toSSet ⋙ SemiSimplexCategory.toSimplexCategory =
      intoOriginal A ⋙ JTGraphCylinderSimplexSpan.smaller C ⋙
        JTGraphCylinderSimplexSpan.degree C := rfl

variable (L : C ⥤ NecklaceCode)

private abbrev full := original A ⋙ JTGraphCylinderSimplexSpan.fibers C L

/-- The injective span cover retains all original internal necklaces. -/
abbrev cover : Grothendieck (intoFull A.toSSet ⋙ full A L) ⥤ Grothendieck (full A L) :=
  Grothendieck.pre (full A L) (intoFull A.toSSet)

/-- Restricting to the exact injective phase operators preserves the weak
type of the whole cylinder resolution over the subcomplex. -/
theorem cover_weak : WeakEquivalence (nerveMap (cover A L)) := by
  let f := cover A L
  let p := Grothendieck.forget (intoFull A.toSSet ⋙ full A L)
  let q := Grothendieck.forget (full A L)
  let g := intoFull A.toSSet
  let i := JTGraphCylinderSimplexSpan.index C L
  letI : WeakEquivalence (nerveMap p) := GrothendieckContractibleFibers.projection_weak _
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at ((i.obj ((intoOriginal A).obj a))).1
      ((i.obj ((intoOriginal A).obj a))).2)
  letI : WeakEquivalence (nerveMap q) := GrothendieckContractibleFibers.projection_weak _
    (fun a ↦ JTHomotopyTargetComma.fiber_point_GW_at ((i.obj ((original A).obj a))).1
      ((i.obj ((original A).obj a))).2)
  letI : WeakEquivalence (nerveMap g) := intoFull_weak A.toSSet
  have e : nerveMap f ≫ nerveMap q = nerveMap p ≫ nerveMap g :=
    congrArg nerveMap (show f ⋙ q = p ⋙ g by rfl)
  apply (weakEquivalence_postcomp_iff _ (nerveMap q)).mp
  rw [e]
  infer_instance

end

end DaggerModels.PartII.JTGraphSpanSemisimplicial
