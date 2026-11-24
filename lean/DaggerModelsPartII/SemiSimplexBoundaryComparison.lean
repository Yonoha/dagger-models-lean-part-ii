import DaggerModelsPartII.SemiSimplexBoundaryLifting
import DaggerModelsPartII.JTSemiSimplexElementsWeak

/-!
# Boundary lifting and weak comparison of simplex categories

The comparison remembers the full simplex operators in the target. Append
the last target vertex and lift the complete compatible source boundary.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SemiSimplexBoundaryLifting

noncomputable section

private theorem elements_eqToHom_val {C : Type} [SmallCategory C]
    {F : C ⥤ Type} {a b : F.Elements} (h : a = b) :
    (eqToHom h : a ⟶ b).val = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

private abbrev inclusion := SemiSimplexCategory.toSimplexCategory
private abbrev restriction (X : SSet.{0}) := inclusion.op ⋙ X

/-- Every proper face remains proper after a further injective restriction. -/
private theorem proper_comp {l m n : SemiSimplexCategory}
    (a : l ⟶ m) (h : m.len < n.len) : l.len < n.len :=
  (SimplexCategory.len_le_of_mono (inclusion.map a)).trans_lt h

open JTSemiSimplexCommaContractible
  (extendSimplex extendEmbedding includeInitial includeLast extendEmbedding_id
    extendEmbedding_comp extendSimplex_natural extendSimplex_initial extendSimplex_last)

/-- There are no proper nonempty faces of a zero simplex. -/
def emptyBoundary (E : SemiSimplexCategoryᵒᵖ ⥤ Type) : Boundary E ⦋0⦌ₛ where
  face := fun _ h ↦ by simp at h
  naturality := by
    intro l m a j h
    simp at h

/-- The degree-zero instance of compatible boundary lifting gives a
vertex over every original target vertex. -/
theorem zeroLift {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (y : X.obj (op ⦋0⦌)) :
    ∃ e : E.obj (op ⦋0⦌ₛ), α.app (op ⦋0⦌ₛ) e = y := by
  obtain ⟨e, he, _⟩ := hα ⦋0⦌ₛ y (emptyBoundary E) (by
    intro m j h
    simp at h)
  exact ⟨e, he⟩

/-- The vertex used as the cone point is the last vertex of the original
target simplex. -/
def lastTargetOperator {X : SSet.{0}} (t : X.Elementsᵒᵖ) :
    ⦋0⦌ ⟶ t.unop.fst.unop :=
  SimplexCategory.const ⦋0⦌ t.unop.fst.unop (Fin.last t.unop.fst.unop.len)

/-- A relative boundary filler supplies the chosen source vertex over the
actual last vertex of the target simplex. -/
def centerLift {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) : E.obj (op ⦋0⦌ₛ) :=
  Classical.choose (zeroLift hα (X.map (lastTargetOperator t).op t.unop.snd))

theorem centerLift_property {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) :
    α.app (op ⦋0⦌ₛ) (centerLift hα t) =
      X.map (lastTargetOperator t).op t.unop.snd :=
  Classical.choose_spec (zeroLift hα (X.map (lastTargetOperator t).op t.unop.snd))

/-- The original full-simplex Elements comparison induced by a map with
only injective source operators. Target operators remain arbitrary. -/
def toFullElements {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) :
    E.Elementsᵒᵖ ⥤ X.Elementsᵒᵖ :=
  (NatTrans.mapElements α).op ⋙ JTSemiSimplexElementsWeak.elementForget X

/-- The exact forward comma used by Quillen A for this comparison. -/
abbrev ForwardComma {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) (t : X.Elementsᵒᵖ) :=
  CostructuredArrow (toFullElements α) t

/-- A cone point over the last vertex of the unchanged target element. -/
def center {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) : ForwardComma α t := by
  let s : E.Elements := ⟨op ⦋0⦌ₛ, centerLift hα t⟩
  let h : (toFullElements α).obj (op s) ⟶ t :=
    Quiver.Hom.op (⟨(lastTargetOperator t).op, by
      change X.map (lastTargetOperator t).op t.unop.snd =
        α.app (op ⦋0⦌ₛ) (centerLift hα t)
      exact (centerLift_property hα t).symm⟩ :
      t.unop ⟶ ((toFullElements α).obj (op s)).unop)
  exact CostructuredArrow.mk h

/-- An object of the forward comma has an arbitrary target simplex
operator, including repetitions of the last vertex. -/
def ForwardComma.targetOperator {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) :
    inclusion.obj c.left.unop.fst.unop ⟶ t.unop.fst.unop :=
  c.hom.unop.val.unop

/-- The comma equation is the unchanged target restriction equation. -/
theorem ForwardComma.targetEquation {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) :
    α.app c.left.unop.fst c.left.unop.snd =
      X.map (c.targetOperator).op t.unop.snd :=
  c.hom.unop.property.symm

/-- A face of an appended simplex which omits the new last vertex factors
through the original simplex. -/
def faceOmittingLast {k m : ℕ} (a : ⦋k⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last k) ≠ Fin.last (m + 1)) :
    ⦋k⦌ₛ ⟶ ⦋m⦌ₛ := by
  let ha : ∀ i : Fin (k + 1),
      (SemiSimplexCategory.homEquiv a) i ≠ Fin.last (m + 1) := by
    intro i
    have hi : (SemiSimplexCategory.homEquiv a) i ≤
        (SemiSimplexCategory.homEquiv a) (Fin.last k) :=
      (SemiSimplexCategory.homEquiv a).monotone (Fin.le_last i)
    exact ne_of_lt (lt_of_le_of_lt hi (Fin.lt_last_iff_ne_last.mpr h))
  exact OrderEmbedding.ofStrictMono
    (fun i ↦ Fin.castPred ((SemiSimplexCategory.homEquiv a) i) (ha i))
    (Fin.strictMono_castPred_comp ha (SemiSimplexCategory.homEquiv a).strictMono)

theorem faceOmittingLast_factor {k m : ℕ}
    (a : ⦋k⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last k) ≠ Fin.last (m + 1)) :
    faceOmittingLast a h ≫ includeInitial m = a := by
  apply SemiSimplexCategory.hom_ext
  ext i
  simp [faceOmittingLast, includeInitial, SemiSimplexCategory.homEquiv,
    SemiSimplexCategory.smallCategory, Fin.castSucc_castPred]

theorem faceOmittingLast_comp {l k m : ℕ}
    (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ) (a : ⦋k⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last k) ≠ Fin.last (m + 1))
    (hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last l) ≠
      Fin.last (m + 1)) :
    faceOmittingLast (i ≫ a) hai = i ≫ faceOmittingLast a ha := by
  apply SemiSimplexCategory.hom_ext
  ext x
  simp [faceOmittingLast, SemiSimplexCategory.homEquiv,
    SemiSimplexCategory.smallCategory]

/-- A positive-dimensional face containing the new last vertex is an
appended face of the original simplex. -/
def faceContainingLast {k m : ℕ} (a : ⦋k + 1⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last (k + 1)) =
      Fin.last (m + 1)) : ⦋k⦌ₛ ⟶ ⦋m⦌ₛ := by
  let ha : ∀ i : Fin (k + 1),
      (SemiSimplexCategory.homEquiv a) i.castSucc ≠ Fin.last (m + 1) := by
    intro i
    have hi := (SemiSimplexCategory.homEquiv a).strictMono (Fin.castSucc_lt_last i)
    rw [h] at hi
    exact ne_of_lt hi
  exact OrderEmbedding.ofStrictMono
    (fun i ↦ Fin.castPred ((SemiSimplexCategory.homEquiv a) i.castSucc) (ha i))
    (Fin.strictMono_castPred_comp ha
      ((SemiSimplexCategory.homEquiv a).strictMono.comp Fin.strictMono_castSucc))

theorem faceContainingLast_factor {k m : ℕ}
    (a : ⦋k + 1⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last (k + 1)) =
      Fin.last (m + 1)) :
    extendEmbedding (faceContainingLast a h) = a := by
  apply SemiSimplexCategory.hom_ext
  ext i
  induction i using Fin.lastCases with
  | last =>
    simpa [extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory] using congrArg Fin.val h.symm
  | cast i =>
    simp [faceContainingLast, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory, Fin.castSucc_castPred]

theorem faceContainingLast_comp {l k m : ℕ}
    (i : ⦋l + 1⦌ₛ ⟶ ⦋k + 1⦌ₛ)
    (a : ⦋k + 1⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (hi : (SemiSimplexCategory.homEquiv i) (Fin.last (l + 1)) =
      Fin.last (k + 1))
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last (k + 1)) =
      Fin.last (m + 1))
    (hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last (l + 1)) =
      Fin.last (m + 1)) :
    faceContainingLast (i ≫ a) hai =
      faceContainingLast i hi ≫ faceContainingLast a ha := by
  apply SemiSimplexCategory.hom_ext
  ext x
  simp [faceContainingLast, SemiSimplexCategory.homEquiv,
    SemiSimplexCategory.smallCategory]

theorem faceOmittingLast_comp_containing {l k m : ℕ}
    (i : ⦋l⦌ₛ ⟶ ⦋k + 1⦌ₛ)
    (a : ⦋k + 1⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (hi : (SemiSimplexCategory.homEquiv i) (Fin.last l) ≠
      Fin.last (k + 1))
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last (k + 1)) =
      Fin.last (m + 1))
    (hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last l) ≠
      Fin.last (m + 1)) :
    faceOmittingLast (i ≫ a) hai =
      faceOmittingLast i hi ≫ faceContainingLast a ha := by
  apply (cancel_mono (includeInitial m)).mp
  calc
    faceOmittingLast (i ≫ a) hai ≫ includeInitial m = i ≫ a :=
      faceOmittingLast_factor (i ≫ a) hai
    _ = (faceOmittingLast i hi ≫ faceContainingLast a ha) ≫ includeInitial m := by
      calc
        i ≫ a = (faceOmittingLast i hi ≫ includeInitial k) ≫ a :=
          congrArg (fun b ↦ b ≫ a) (faceOmittingLast_factor i hi).symm
        _ = (faceOmittingLast i hi ≫ includeInitial k) ≫
            extendEmbedding (faceContainingLast a ha) :=
          congrArg (fun b ↦ (faceOmittingLast i hi ≫ includeInitial k) ≫ b)
            (faceContainingLast_factor a ha).symm
        _ = (faceOmittingLast i hi ≫ faceContainingLast a ha) ≫
            includeInitial m := by
          apply SemiSimplexCategory.hom_ext
          ext x
          simp [includeInitial, extendEmbedding, SemiSimplexCategory.homEquiv,
            SemiSimplexCategory.smallCategory]

/-- A zero-dimensional face at the new last vertex is exactly `includeLast`. -/
theorem zeroFaceContainingLast {m : ℕ} (a : ⦋0⦌ₛ ⟶ ⦋m + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last 0) =
      Fin.last (m + 1)) : a = includeLast m := by
  apply SemiSimplexCategory.hom_ext
  ext i
  change Fin 1 at i
  have hi : i = Fin.last 0 := Subsingleton.elim _ _
  subst i
  simpa [includeLast, SemiSimplexCategory.homEquiv] using congrArg Fin.val h

theorem extendEmbedding_initial {m k : ℕ}
    (a : ⦋m⦌ₛ ⟶ ⦋k⦌ₛ) :
    includeInitial m ≫ extendEmbedding a = a ≫ includeInitial k := by
  apply SemiSimplexCategory.hom_ext
  ext i
  simp [includeInitial, extendEmbedding, SemiSimplexCategory.homEquiv,
    SemiSimplexCategory.smallCategory]

theorem extendEmbedding_last {m k : ℕ}
    (a : ⦋m⦌ₛ ⟶ ⦋k⦌ₛ) :
    includeLast m ≫ extendEmbedding a = includeLast k := by
  apply SemiSimplexCategory.hom_ext
  ext i
  simp [includeLast, extendEmbedding, SemiSimplexCategory.homEquiv,
    SemiSimplexCategory.smallCategory]

/-- The injective source operator underlying a forward-comma arrow. -/
def ForwardComma.sourceOperator {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d) :
    c.left.unop.fst.unop ⟶ d.left.unop.fst.unop :=
  f.left.unop.val.unop

private theorem ForwardComma.sourceOperator_id
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) :
    ForwardComma.sourceOperator (𝟙 c) = 𝟙 c.left.unop.fst.unop := rfl

private theorem ForwardComma.sourceOperator_comp
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c d e : ForwardComma α t} (f : c ⟶ d) (g : d ⟶ e) :
    ForwardComma.sourceOperator (f ≫ g) =
      ForwardComma.sourceOperator f ≫ ForwardComma.sourceOperator g := rfl

/-- The ordinary target operators of a comma arrow form a strict triangle.
This keeps the noninjective target component rather than replacing it. -/
theorem ForwardComma.targetOperator_natural
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d) :
    inclusion.map (ForwardComma.sourceOperator f) ≫ d.targetOperator = c.targetOperator := by
  have hw := CostructuredArrow.w f
  have h := congrArg
    (fun z : (toFullElements α).obj c.left ⟶ t ↦ z.unop.val.unop) hw
  exact h

/-- Restrict a comma object along an injective source face. The target
operator remains its actual composite, even if it is noninjective. -/
def ForwardComma.faceObject
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) : ForwardComma α t := by
  let s : E.Elements := ⟨op ⦋k⦌ₛ, E.map a.op c.left.unop.snd⟩
  let h : (toFullElements α).obj (op s) ⟶ t :=
    Quiver.Hom.op (⟨(inclusion.map a ≫ c.targetOperator).op, by
      change X.map (inclusion.map a ≫ c.targetOperator).op t.unop.snd =
        α.app (op ⦋k⦌ₛ) (E.map a.op c.left.unop.snd)
      have hnat := congrFun (α.naturality a.op) c.left.unop.snd
      change α.app (op ⦋k⦌ₛ) (E.map a.op c.left.unop.snd) =
        X.map (inclusion.map a).op
          (α.app c.left.unop.fst c.left.unop.snd) at hnat
      rw [hnat, c.targetEquation, ← FunctorToTypes.map_comp_apply, ← op_comp]
      ⟩ :
      t.unop ⟶ ((toFullElements α).obj (op s)).unop)
  exact CostructuredArrow.mk h

/-- The restriction object maps to the original comma object by its
injective source face. -/
def ForwardComma.faceArrow
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) : c.faceObject a ⟶ c := by
  let u : (c.faceObject a).left ⟶ c.left :=
    Quiver.Hom.op (⟨a.op, by
      change E.map a.op c.left.unop.snd = E.map a.op c.left.unop.snd
      rfl⟩ : c.left.unop ⟶ (c.faceObject a).left.unop)
  refine CostructuredArrow.homMk u ?_
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  change c.targetOperator.op ≫ (inclusion.map a).op =
    (inclusion.map a ≫ c.targetOperator).op
  rfl

@[simp] theorem ForwardComma.faceArrow_sourceOperator
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) :
    ForwardComma.sourceOperator (c.faceArrow a) = a := rfl

@[simp] theorem ForwardComma.faceObject_targetOperator
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) :
    (c.faceObject a).targetOperator = inclusion.map a ≫ c.targetOperator := rfl

/-- Iterated injective source restriction equals restriction along the
composite, including the exact target comma arrow. -/
theorem ForwardComma.faceObject_comp
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {l k : ℕ}
    (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) :
    (c.faceObject a).faceObject i = c.faceObject (i ≫ a) := by
  have hleft0 : ((c.faceObject a).faceObject i).left.unop =
      (c.faceObject (i ≫ a)).left.unop := by
    refine Functor.Elements.ext _ _ rfl ?_
    simp only [eqToHom_refl, E.map_id]
    change E.map i.op (E.map a.op c.left.unop.snd) =
      E.map (i ≫ a).op c.left.unop.snd
    rw [← FunctorToTypes.map_comp_apply, ← op_comp]
  have hleft : ((c.faceObject a).faceObject i).left =
      (c.faceObject (i ≫ a)).left := congrArg op hleft0
  apply CostructuredArrow.obj_ext _ _ hleft
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  simp only [eqToHom_map, unop_comp, eqToHom_unop,
    CategoryOfElements.comp_val, elements_eqToHom_val]
  change ((inclusion.map i ≫ (inclusion.map a ≫ c.targetOperator)).op) =
    (inclusion.map (i ≫ a) ≫ c.targetOperator).op
  rw [Functor.map_comp, Category.assoc]

/-- The lower face of a restricted comma object maps to the larger face,
after the exact iterated-face object equality. -/
def ForwardComma.faceSubArrow
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {l k : ℕ}
    (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) :
    c.faceObject (i ≫ a) ⟶ c.faceObject a :=
  eqToHom (c.faceObject_comp i a).symm ≫ (c.faceObject a).faceArrow i

@[simp] theorem ForwardComma.faceSubArrow_sourceOperator
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {l k : ℕ}
    (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ c.left.unop.fst.unop) :
    ForwardComma.sourceOperator (c.faceSubArrow i a) = i := by
  simp [ForwardComma.faceSubArrow, ForwardComma.sourceOperator_comp,
    ForwardComma.faceArrow_sourceOperator]
  simp [ForwardComma.sourceOperator, eqToHom_unop, elements_eqToHom_val]
  change (𝟙 ⦋l⦌ₛ) ≫ i = i
  simp

/-- An arbitrary comma arrow determines its source object as the exact
injective-face restriction of its target object. -/
theorem ForwardComma.faceObject_source
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {a c : ForwardComma α t} (f : a ⟶ c) :
    c.faceObject (ForwardComma.sourceOperator f) = a := by
  have hleft0 : (c.faceObject (ForwardComma.sourceOperator f)).left.unop =
      a.left.unop := by
    refine Functor.Elements.ext _ _ rfl ?_
    simp only [eqToHom_refl, E.map_id]
    change E.map (ForwardComma.sourceOperator f).op c.left.unop.snd =
      a.left.unop.snd
    exact f.left.unop.property
  have hleft : (c.faceObject (ForwardComma.sourceOperator f)).left =
      a.left := congrArg op hleft0
  apply CostructuredArrow.obj_ext _ _ hleft
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  simp only [eqToHom_map, unop_comp, eqToHom_unop,
    CategoryOfElements.comp_val, elements_eqToHom_val]
  simp only [eqToHom_refl, Category.comp_id]
  change a.targetOperator.op =
    (inclusion.map (ForwardComma.sourceOperator f) ≫ c.targetOperator).op
  exact congrArg Quiver.Hom.op (ForwardComma.targetOperator_natural f).symm

/-- The target operator after appending one repeated last target vertex. -/
def ForwardComma.appendTargetOperator
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) :
    ⦋c.left.unop.fst.unop.len + 1⦌ ⟶ t.unop.fst.unop :=
  extendSimplex c.targetOperator

/-- Appending commutes with the actual injective comma operators. -/
theorem ForwardComma.appendTargetOperator_natural
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d) :
    inclusion.map (extendEmbedding (ForwardComma.sourceOperator f)) ≫
        d.appendTargetOperator = c.appendTargetOperator := by
  rw [appendTargetOperator, appendTargetOperator, extendSimplex_natural,
    ForwardComma.targetOperator_natural f]

/-- A lift over the exact target simplex after repeating its last vertex.
The fiber equation is on the entire simplex, not only on its endpoints. -/
def AppendedLift {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) :=
  {e : E.obj (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) //
    α.app (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) e =
      X.map c.appendTargetOperator.op t.unop.snd}

/-- Restrict an appended lift along the same exact injective comma operator. -/
def AppendedLift.restrict {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d)
    (z : AppendedLift α d) : AppendedLift α c := by
  let a := extendEmbedding (ForwardComma.sourceOperator f)
  refine ⟨E.map a.op z.val, ?_⟩
  have hnat := congrFun (α.naturality a.op) z.val
  change α.app (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) (E.map a.op z.val) =
      X.map (inclusion.map a).op
        (α.app (op ⦋d.left.unop.fst.unop.len + 1⦌ₛ) z.val) at hnat
  rw [hnat, z.property, ← FunctorToTypes.map_comp_apply]
  exact congrArg (fun j ↦ X.map j.op t.unop.snd)
    (ForwardComma.appendTargetOperator_natural f)

/-- The old face of an appended lift has the same exact target simplex as
the original comma object. Its equality in `E` is a boundary prescription. -/
theorem AppendedLift.initial_face_target
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) (z : AppendedLift α c) :
    α.app c.left.unop.fst (E.map (includeInitial c.left.unop.fst.unop.len).op z.val) =
      α.app c.left.unop.fst c.left.unop.snd := by
  have hnat := congrFun (α.naturality (includeInitial c.left.unop.fst.unop.len).op)
    z.val
  change α.app c.left.unop.fst
      (E.map (includeInitial c.left.unop.fst.unop.len).op z.val) =
      X.map (inclusion.map (includeInitial c.left.unop.fst.unop.len)).op
        (α.app (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) z.val) at hnat
  rw [hnat, z.property, ← FunctorToTypes.map_comp_apply, ← op_comp]
  change X.map
    (inclusion.map (includeInitial c.left.unop.fst.unop.len) ≫
      extendSimplex c.targetOperator).op t.unop.snd = _
  rw [extendSimplex_initial, ← c.targetEquation]

/-- The new last face of an appended lift lies over the fixed last target
vertex. Its equality with `centerLift` is the second boundary prescription. -/
theorem AppendedLift.last_face_target
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (hα : HasBoundaryLifting α) (c : ForwardComma α t) (z : AppendedLift α c) :
    α.app (op ⦋0⦌ₛ) (E.map (includeLast c.left.unop.fst.unop.len).op z.val) =
      α.app (op ⦋0⦌ₛ) (centerLift hα t) := by
  have hnat := congrFun (α.naturality (includeLast c.left.unop.fst.unop.len).op)
    z.val
  change α.app (op ⦋0⦌ₛ)
      (E.map (includeLast c.left.unop.fst.unop.len).op z.val) =
      X.map (inclusion.map (includeLast c.left.unop.fst.unop.len)).op
        (α.app (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) z.val) at hnat
  rw [hnat, z.property, ← FunctorToTypes.map_comp_apply, ← op_comp]
  change X.map
    (inclusion.map (includeLast c.left.unop.fst.unop.len) ≫
      extendSimplex c.targetOperator).op t.unop.snd = _
  rw [extendSimplex_last]
  exact (centerLift_property hα t).symm

/-- An appended lift with the two source-level face equations required by
the cone. These equations are stronger than their automatic target images. -/
structure GoodAppendedLift {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) where
  lift : AppendedLift α c
  initial : E.map (includeInitial c.left.unop.fst.unop.len).op lift.val =
    c.left.unop.snd
  last : E.map (includeLast c.left.unop.fst.unop.len).op lift.val =
    centerLift hα t

/-- Good appended lifts restrict to good appended lifts along every comma
arrow; both distinguished face equations are preserved. -/
def GoodAppendedLift.restrict
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d)
    (z : GoodAppendedLift hα d) : GoodAppendedLift hα c where
  lift := AppendedLift.restrict α f z.lift
  initial := by
    let a := ForwardComma.sourceOperator f
    have hface := f.left.unop.property
    change E.map a.op d.left.unop.snd = c.left.unop.snd at hface
    change E.map (includeInitial c.left.unop.fst.unop.len).op
      (E.map (extendEmbedding a).op z.lift.val) = c.left.unop.snd
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, extendEmbedding_initial,
      op_comp, FunctorToTypes.map_comp_apply, z.initial, hface]
  last := by
    let a := ForwardComma.sourceOperator f
    change E.map (includeLast c.left.unop.fst.unop.len).op
      (E.map (extendEmbedding a).op z.lift.val) = centerLift hα t
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, extendEmbedding_last]
    exact z.last

@[ext] theorem GoodAppendedLift.ext
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    {c : ForwardComma α t} {z w : GoodAppendedLift hα c}
    (h : z.lift.val = w.lift.val) : z = w := by
  cases z with
  | mk z zi zl =>
    cases w with
    | mk w wi wl =>
      have hz : z = w := Subtype.ext h
      subst w
      rfl

/-- The recursively chosen cone lifts form a presheaf on the exact forward
comma; the initial and last source-face equations survive restriction. -/
def goodAppendedLiftDiagram
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) :
    (ForwardComma α t)ᵒᵖ ⥤ Type where
  obj c := GoodAppendedLift hα c.unop
  map f := GoodAppendedLift.restrict f.unop
  map_id c := by
    funext z
    apply GoodAppendedLift.ext
    change E.map (extendEmbedding (ForwardComma.sourceOperator (𝟙 c.unop))).op
        z.lift.val = z.lift.val
    rw [ForwardComma.sourceOperator_id, extendEmbedding_id, op_id, E.map_id]
    rfl
  map_comp f g := by
    funext z
    apply GoodAppendedLift.ext
    change E.map (extendEmbedding (ForwardComma.sourceOperator (g.unop ≫ f.unop))).op
        z.lift.val =
      E.map (extendEmbedding (ForwardComma.sourceOperator g.unop)).op
        (E.map (extendEmbedding (ForwardComma.sourceOperator f.unop)).op z.lift.val)
    rw [ForwardComma.sourceOperator_comp, extendEmbedding_comp, op_comp,
      E.map_comp]
    rfl

/-- An injective operator between equal-dimensional finite ordinals is the
identity, expressed after identifying the two semisimplex objects. -/
private theorem semiHom_eq_id_of_len_eq
    {a b : SemiSimplexCategory} (f : a ⟶ b) (h : a.len = b.len) :
    f = eqToHom (SemiSimplexCategory.ext h) := by
  cases a with
  | mk m =>
    cases b with
    | mk n =>
      dsimp at h
      subst n
      change f = 𝟙 ⦋m⦌ₛ
      apply SemiSimplexCategory.hom_ext
      ext i
      have hlow := (SemiSimplexCategory.homEquiv f).strictMono.id_le i
      have hhigh := (SemiSimplexCategory.homEquiv f).strictMono.dual.id_le
        (OrderDual.toDual i)
      exact le_antisymm hhigh hlow

private theorem ForwardComma.eq_of_degree_eq
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c d : ForwardComma α t} (f : c ⟶ d)
    (h : c.left.unop.fst.unop.len = d.left.unop.fst.unop.len) : c = d := by
  let hsemi : c.left.unop.fst.unop = d.left.unop.fst.unop :=
    SemiSimplexCategory.ext h
  let hbase : c.left.unop.fst = d.left.unop.fst := congrArg op hsemi
  have hsource : ForwardComma.sourceOperator f = eqToHom hsemi :=
    semiHom_eq_id_of_len_eq (ForwardComma.sourceOperator f) h
  have hval : E.map (eqToHom hbase) c.left.unop.snd = d.left.unop.snd := by
    have hp := f.left.unop.property
    change E.map (ForwardComma.sourceOperator f).op d.left.unop.snd =
      c.left.unop.snd at hp
    rw [hsource] at hp
    calc
      E.map (eqToHom hbase) c.left.unop.snd =
          E.map (eqToHom hbase)
            (E.map (eqToHom hsemi).op d.left.unop.snd) := by rw [hp]
      _ = d.left.unop.snd := by
        rw [← FunctorToTypes.map_comp_apply]
        simp [eqToHom_op]
  have hleft0 : c.left.unop = d.left.unop :=
    Functor.Elements.ext _ _ hbase hval
  have hleft : c.left = d.left := congrArg op hleft0
  have hfleft : f.left = eqToHom hleft := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext E
    rw [eqToHom_unop]
    change (ForwardComma.sourceOperator f).op =
      (CategoryOfElements.π E).map (eqToHom (congrArg unop hleft.symm))
    rw [hsource]
    rw [eqToHom_map, eqToHom_op]
  apply CostructuredArrow.obj_ext _ _ hleft
  have hw := CostructuredArrow.w f
  rw [hfleft] at hw
  exact hw

private theorem ForwardComma.endomorphism_eq_id
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    {c : ForwardComma α t} (f : c ⟶ c) : f = 𝟙 c := by
  apply CostructuredArrow.hom_ext
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext E
  change (ForwardComma.sourceOperator f).op = (𝟙 c.left.unop.fst.unop).op
  rw [semiHom_eq_id_of_len_eq (ForwardComma.sourceOperator f) rfl]
  rfl

private def commaDegree
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) : ℕ := c.left.unop.fst.unop.len

/-- Compatibility of all previously chosen lower-dimensional appended
lifts, measured by the source dimension of comma objects. -/
def CompatiblePrevious
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ)
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d) : Prop :=
  ∀ {a b : ForwardComma α t} (f : a ⟶ b)
    (hab : commaDegree a < commaDegree b)
    (hbc : commaDegree b < commaDegree c),
    GoodAppendedLift.restrict f (previous b hbc) =
      previous a (lt_trans hab hbc)

/-- A total step rule whose face equations are required only when its
already chosen lower-dimensional data are compatible. This is the precise
interface for the full appended-boundary gluing argument. -/
def ConeStep
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) :=
  ∀ (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d),
      {z : GoodAppendedLift hα c //
        CompatiblePrevious hα t c previous →
          ∀ {a : ForwardComma α t} (f : a ⟶ c)
            (h : commaDegree a < commaDegree c),
            GoodAppendedLift.restrict f z = previous a h}

/-- The boundary gluing lemma only has to fill compatible lower-dimensional
choices. A total recursive step will be derived without a default hypothesis. -/
def CompatibleConeFiller
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) :=
  ∀ (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d),
    CompatiblePrevious hα t c previous →
      {z : GoodAppendedLift hα c //
        ∀ {a : ForwardComma α t} (f : a ⟶ c)
          (h : commaDegree a < commaDegree c),
          GoodAppendedLift.restrict f z = previous a h}

/-- The three-case prescription for a proper face of an appended simplex:
an old face, the new vertex, or an appended lower-dimensional face. -/
private def appendedBoundaryFace
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {k : ℕ} (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : k < commaDegree c + 1) : E.obj (op ⦋k⦌ₛ) := by
  classical
  by_cases hlast : (SemiSimplexCategory.homEquiv a) (Fin.last k) =
      Fin.last (commaDegree c + 1)
  · cases k with
    | zero => exact centerLift hα t
    | succ r =>
      let b := faceContainingLast a hlast
      let d := c.faceObject b
      have hd : commaDegree d < commaDegree c := by
        change r < commaDegree c
        omega
      exact (previous d hd).lift.val
  · exact E.map (faceOmittingLast a hlast).op c.left.unop.snd

private theorem appendedBoundaryTarget_omit
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last k) ≠
      Fin.last (commaDegree c + 1)) :
    inclusion.map a ≫ c.appendTargetOperator =
      inclusion.map (faceOmittingLast a h) ≫ c.targetOperator := by
  conv_lhs => rw [← faceOmittingLast_factor a h]
  simp only [Functor.map_comp, Category.assoc]
  change inclusion.map (faceOmittingLast a h) ≫
      (inclusion.map (includeInitial (commaDegree c)) ≫
        extendSimplex c.targetOperator) = _
  rw [extendSimplex_initial]

private theorem appendedBoundaryTarget_containing
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X} {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t) {k : ℕ}
    (a : ⦋k + 1⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (h : (SemiSimplexCategory.homEquiv a) (Fin.last (k + 1)) =
      Fin.last (commaDegree c + 1)) :
    inclusion.map a ≫ c.appendTargetOperator =
      (c.faceObject (faceContainingLast a h)).appendTargetOperator := by
  calc
    inclusion.map a ≫ c.appendTargetOperator =
        inclusion.map (extendEmbedding (faceContainingLast a h)) ≫
          c.appendTargetOperator :=
      congrArg (fun b ↦ inclusion.map b ≫ c.appendTargetOperator)
        (faceContainingLast_factor a h).symm
    _ = (c.faceObject (faceContainingLast a h)).appendTargetOperator := by
      change inclusion.map (extendEmbedding (faceContainingLast a h)) ≫
        extendSimplex c.targetOperator =
        extendSimplex (inclusion.map (faceContainingLast a h) ≫ c.targetOperator)
      exact extendSimplex_natural (faceContainingLast a h) c.targetOperator

/-- Every prescribed proper face lies over the exact corresponding face of
the unchanged target simplex. -/
private theorem appendedBoundaryFace_target
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {k : ℕ} (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : k < commaDegree c + 1) :
    α.app (op ⦋k⦌ₛ) (appendedBoundaryFace hα c previous a hk) =
      X.map (inclusion.map a).op
        (X.map c.appendTargetOperator.op t.unop.snd) := by
  classical
  by_cases hlast : (SemiSimplexCategory.homEquiv a) (Fin.last k) =
      Fin.last (commaDegree c + 1)
  · cases k with
    | zero =>
      have ha := zeroFaceContainingLast a hlast
      subst a
      simp only [appendedBoundaryFace, dif_pos hlast]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      change α.app (op ⦋0⦌ₛ) (centerLift hα t) =
        X.map
          (inclusion.map (includeLast (commaDegree c)) ≫
            extendSimplex c.targetOperator).op t.unop.snd
      rw [extendSimplex_last]
      exact centerLift_property hα t
    | succ r =>
      let b := faceContainingLast a hlast
      let d := c.faceObject b
      have hd : commaDegree d < commaDegree c := by
        change r < commaDegree c
        omega
      have hz := (previous d hd).lift.property
      change α.app (op ⦋r + 1⦌ₛ) (previous d hd).lift.val =
        X.map d.appendTargetOperator.op t.unop.snd at hz
      simp only [appendedBoundaryFace, dif_pos hlast]
      rw [← FunctorToTypes.map_comp_apply, ← op_comp]
      rw [appendedBoundaryTarget_containing c a hlast]
      exact hz
  · have hnat := congrFun (α.naturality (faceOmittingLast a hlast).op)
      c.left.unop.snd
    change α.app (op ⦋k⦌ₛ)
      (E.map (faceOmittingLast a hlast).op c.left.unop.snd) =
      X.map (inclusion.map (faceOmittingLast a hlast)).op
        (α.app c.left.unop.fst c.left.unop.snd) at hnat
    simp only [appendedBoundaryFace, dif_neg hlast]
    rw [hnat, c.targetEquation, ← FunctorToTypes.map_comp_apply, ← op_comp]
    rw [← appendedBoundaryTarget_omit c a hlast]
    rw [op_comp, FunctorToTypes.map_comp_apply]

/-- Naturality of prescribed faces when the outer face omits the new last
vertex. Every further restriction remains an old face. -/
private theorem appendedBoundaryFace_natural_omit
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {l k : ℕ} (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : k < commaDegree c + 1)
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last k) ≠
      Fin.last (commaDegree c + 1)) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  have hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last l) ≠
      Fin.last (commaDegree c + 1) := by
    have hle : (SemiSimplexCategory.homEquiv a)
        ((SemiSimplexCategory.homEquiv i) (Fin.last l)) ≤
        (SemiSimplexCategory.homEquiv a) (Fin.last k) :=
      (SemiSimplexCategory.homEquiv a).monotone
        (Fin.le_last ((SemiSimplexCategory.homEquiv i) (Fin.last l)))
    exact ne_of_lt (lt_of_le_of_lt hle (Fin.lt_last_iff_ne_last.mpr ha))
  simp only [appendedBoundaryFace, dif_neg hai, dif_neg ha]
  change E.map (faceOmittingLast (i ≫ a) hai).op c.left.unop.snd =
    E.map i.op (E.map (faceOmittingLast a ha).op c.left.unop.snd)
  rw [faceOmittingLast_comp i a ha hai, op_comp,
    FunctorToTypes.map_comp_apply]

/-- Mixed intersection: an old face of a lower appended lift is the
corresponding old face of the original comma simplex. -/
private theorem appendedBoundaryFace_natural_mixed
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {l r : ℕ} (i : ⦋l⦌ₛ ⟶ ⦋r + 1⦌ₛ)
    (a : ⦋r + 1⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : r + 1 < commaDegree c + 1)
    (hi : (SemiSimplexCategory.homEquiv i) (Fin.last l) ≠ Fin.last (r + 1))
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last (r + 1)) =
      Fin.last (commaDegree c + 1)) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  have hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last l) ≠
      Fin.last (commaDegree c + 1) := by
    have hlt := (SemiSimplexCategory.homEquiv a).strictMono
      (Fin.lt_last_iff_ne_last.mpr hi)
    rw [ha] at hlt
    exact ne_of_lt hlt
  let b := faceContainingLast a ha
  let d := c.faceObject b
  have hd : commaDegree d < commaDegree c := by
    change r < commaDegree c
    omega
  have hinit := (previous d hd).initial
  change E.map (includeInitial r).op (previous d hd).lift.val =
    E.map b.op c.left.unop.snd at hinit
  simp only [appendedBoundaryFace, dif_neg hai, dif_pos ha]
  change E.map (faceOmittingLast (i ≫ a) hai).op c.left.unop.snd =
    E.map i.op (previous d hd).lift.val
  rw [faceOmittingLast_comp_containing i a hi ha hai]
  rw [op_comp, FunctorToTypes.map_comp_apply]
  calc
    E.map (faceOmittingLast i hi).op (E.map b.op c.left.unop.snd) =
        E.map (faceOmittingLast i hi).op
          (E.map (includeInitial r).op (previous d hd).lift.val) := by rw [hinit]
    _ = E.map i.op (previous d hd).lift.val := by
      rw [← FunctorToTypes.map_comp_apply, ← op_comp,
        faceOmittingLast_factor i hi]

/-- The intersection at the newly adjoined vertex is the same chosen
center vertex in every lower appended lift. -/
private theorem appendedBoundaryFace_natural_last
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {r : ℕ} (i : ⦋0⦌ₛ ⟶ ⦋r + 1⦌ₛ)
    (a : ⦋r + 1⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : r + 1 < commaDegree c + 1)
    (hi : (SemiSimplexCategory.homEquiv i) (Fin.last 0) = Fin.last (r + 1))
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last (r + 1)) =
      Fin.last (commaDegree c + 1)) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  have hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last 0) =
      Fin.last (commaDegree c + 1) := by
    change (SemiSimplexCategory.homEquiv a)
      ((SemiSimplexCategory.homEquiv i) (Fin.last 0)) = _
    rw [hi, ha]
  let b := faceContainingLast a ha
  let d := c.faceObject b
  have hd : commaDegree d < commaDegree c := by
    change r < commaDegree c
    omega
  simp only [Nat.add_one, appendedBoundaryFace, dif_pos hai, dif_pos ha]
  change centerLift hα t = E.map i.op (previous d hd).lift.val
  rw [zeroFaceContainingLast i hi]
  exact (previous d hd).last.symm

/-- Two positive-dimensional appended faces agree on their intersection
by the compatibility of the previously chosen lower comma lifts. -/
private theorem appendedBoundaryFace_natural_nested_strict
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    (hprevious : CompatiblePrevious hα t c previous)
    {s r : ℕ} (i : ⦋s + 1⦌ₛ ⟶ ⦋r + 1⦌ₛ)
    (a : ⦋r + 1⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : r + 1 < commaDegree c + 1) (hsr : s < r)
    (hi : (SemiSimplexCategory.homEquiv i) (Fin.last (s + 1)) =
      Fin.last (r + 1))
    (ha : (SemiSimplexCategory.homEquiv a) (Fin.last (r + 1)) =
      Fin.last (commaDegree c + 1)) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  have hai : (SemiSimplexCategory.homEquiv (i ≫ a)) (Fin.last (s + 1)) =
      Fin.last (commaDegree c + 1) := by
    change (SemiSimplexCategory.homEquiv a)
      ((SemiSimplexCategory.homEquiv i) (Fin.last (s + 1))) = _
    rw [hi, ha]
  let e := faceContainingLast i hi
  let b := faceContainingLast a ha
  let d := c.faceObject b
  let d' := c.faceObject (e ≫ b)
  have hd : commaDegree d < commaDegree c := by
    change r < commaDegree c
    omega
  have hd' : commaDegree d' < commaDegree c := by
    change s < commaDegree c
    omega
  let f : d' ⟶ d := c.faceSubArrow e b
  have hsd : commaDegree d' < commaDegree d := by
    change s < r
    exact hsr
  have hcompat := hprevious f hsd hd
  have hface : faceContainingLast (i ≫ a) hai = e ≫ b :=
    faceContainingLast_comp i a hi ha hai
  simp only [Nat.add_one, appendedBoundaryFace, dif_pos hai, dif_pos ha]
  dsimp only [Nat.casesAuxOn]
  rw [hface]
  change (previous d' hd').lift.val = E.map i.op (previous d hd).lift.val
  have hv := congrArg (fun z : GoodAppendedLift hα d' ↦ z.lift.val) hcompat
  change E.map (extendEmbedding (ForwardComma.sourceOperator f)).op
      (previous d hd).lift.val = (previous d' hd').lift.val at hv
  rw [ForwardComma.faceSubArrow_sourceOperator] at hv
  rw [faceContainingLast_factor i hi] at hv
  exact hv.symm

/-- Equal-dimensional injective restrictions are identities, so every
prescribed face respects them without a recursive compatibility condition. -/
private theorem appendedBoundaryFace_natural_equal
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {l k : ℕ} (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : k < commaDegree c + 1) (h : l = k) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  subst k
  have hi : i = 𝟙 ⦋l⦌ₛ := semiHom_eq_id_of_len_eq i rfl
  subst i
  simp

/-- All pairwise intersections of the prescribed proper faces agree. -/
private theorem appendedBoundaryFace_natural
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    (hprevious : CompatiblePrevious hα t c previous)
    {l k : ℕ} (i : ⦋l⦌ₛ ⟶ ⦋k⦌ₛ)
    (a : ⦋k⦌ₛ ⟶ ⦋commaDegree c + 1⦌ₛ)
    (hk : k < commaDegree c + 1) :
    appendedBoundaryFace hα c previous (i ≫ a) (proper_comp i hk) =
      E.map i.op (appendedBoundaryFace hα c previous a hk) := by
  have hle : l ≤ k :=
    SimplexCategory.len_le_of_mono (inclusion.map i)
  by_cases heq : l = k
  · exact appendedBoundaryFace_natural_equal hα c previous i a hk heq
  have hlt : l < k := lt_of_le_of_ne hle heq
  by_cases ha : (SemiSimplexCategory.homEquiv a) (Fin.last k) =
      Fin.last (commaDegree c + 1)
  · cases k with
    | zero => omega
    | succ r =>
      by_cases hi : (SemiSimplexCategory.homEquiv i) (Fin.last l) =
          Fin.last (r + 1)
      · cases l with
        | zero =>
          exact appendedBoundaryFace_natural_last hα c previous i a hk hi ha
        | succ s =>
          have hsr : s < r := by omega
          exact appendedBoundaryFace_natural_nested_strict hα c previous
            hprevious i a hk hsr hi ha
      · exact appendedBoundaryFace_natural_mixed hα c previous i a hk hi ha
  · exact appendedBoundaryFace_natural_omit hα c previous i a hk ha

/-- The compatible face prescription is a genuine full semisimplicial
boundary of the appended simplex. -/
private def appendedBoundary
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    (hprevious : CompatiblePrevious hα t c previous) :
    Boundary E ⦋commaDegree c + 1⦌ₛ where
  face := by
    intro m a h
    cases m with
    | mk k => exact appendedBoundaryFace hα c previous a h
  naturality := by
    intro l m i a h
    cases l with
    | mk l =>
      cases m with
      | mk k =>
        exact appendedBoundaryFace_natural hα c previous hprevious i a h

private theorem appendedBoundary_over
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    (hprevious : CompatiblePrevious hα t c previous) :
    (appendedBoundary hα c previous hprevious).Over α
      (X.map c.appendTargetOperator.op t.unop.snd) := by
  intro m a h
  cases m with
  | mk k =>
    exact appendedBoundaryFace_target hα c previous a h

private theorem appendedBoundaryFace_initial
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d) :
    appendedBoundaryFace hα c previous (includeInitial (commaDegree c))
        (Nat.lt_succ_self _) = c.left.unop.snd := by
  have hnot : (SemiSimplexCategory.homEquiv
      (includeInitial (commaDegree c))) (Fin.last (commaDegree c)) ≠
      Fin.last (commaDegree c + 1) := by
    change (Fin.last (commaDegree c)).castSucc ≠ Fin.last (commaDegree c + 1)
    exact (Fin.castSucc_lt_last _).ne
  have hid : faceOmittingLast (includeInitial (commaDegree c)) hnot =
      𝟙 ⦋commaDegree c⦌ₛ := by
    apply (cancel_mono (includeInitial (commaDegree c))).mp
    simpa using faceOmittingLast_factor (includeInitial (commaDegree c)) hnot
  simp only [appendedBoundaryFace, dif_neg hnot]
  rw [hid, op_id, E.map_id]
  rfl

private theorem appendedBoundaryFace_last
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d) :
    appendedBoundaryFace hα c previous (includeLast (commaDegree c))
        (Nat.zero_lt_succ _) = centerLift hα t := by
  have hlast : (SemiSimplexCategory.homEquiv
      (includeLast (commaDegree c))) (Fin.last 0) =
      Fin.last (commaDegree c + 1) := by
    rfl
  simp only [appendedBoundaryFace, dif_pos hlast]
  dsimp only [Nat.casesAuxOn]
  rfl

private theorem appendedBoundaryFace_append
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) {t : X.Elementsᵒᵖ}
    (c : ForwardComma α t)
    (previous : ∀ d : ForwardComma α t, commaDegree d < commaDegree c →
      GoodAppendedLift hα d)
    {r : ℕ} (a : ⦋r⦌ₛ ⟶ ⦋commaDegree c⦌ₛ)
    (hr : r < commaDegree c) :
    appendedBoundaryFace hα c previous (extendEmbedding a)
        (Nat.succ_lt_succ hr) = (previous (c.faceObject a) (by
          change r < commaDegree c
          exact hr)).lift.val := by
  have hlast : (SemiSimplexCategory.homEquiv (extendEmbedding a))
      (Fin.last (r + 1)) = Fin.last (commaDegree c + 1) := by
    simp [extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]
  simp only [appendedBoundaryFace, dif_pos hlast]
  dsimp only [Nat.casesAuxOn]
  have hfactor : faceContainingLast (extendEmbedding a) hlast = a := by
    apply SemiSimplexCategory.hom_ext
    ext x
    simp [faceContainingLast, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory, Fin.castPred_castSucc]
  rw [hfactor]

/-- Exact relative boundary lifting fills the recursively assembled
appended boundary, including both distinguished faces and every lower
injective comma arrow. -/
def compatibleConeFiller
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) :
    CompatibleConeFiller hα t := by
  intro c previous hprevious
  let b := appendedBoundary hα c previous hprevious
  let y := X.map c.appendTargetOperator.op t.unop.snd
  let witness := hα ⦋commaDegree c + 1⦌ₛ y b
    (appendedBoundary_over hα c previous hprevious)
  let e := Classical.choose witness
  have he := (Classical.choose_spec witness).1
  have hfaces : ∀ {m : SemiSimplexCategory}
      (j : m ⟶ ⦋commaDegree c + 1⦌ₛ)
      (h : m.len < ⦋commaDegree c + 1⦌ₛ.len),
      E.map j.op e = b.face j h :=
    (Classical.choose_spec witness).2
  let z : GoodAppendedLift hα c :=
    { lift := ⟨e, he⟩
      initial := by
        have h := hfaces (includeInitial (commaDegree c)) (Nat.lt_succ_self _)
        change E.map (includeInitial (commaDegree c)).op e =
          appendedBoundaryFace hα c previous (includeInitial (commaDegree c))
            (Nat.lt_succ_self _) at h
        rw [appendedBoundaryFace_initial] at h
        exact h
      last := by
        have h := hfaces (includeLast (commaDegree c)) (Nat.zero_lt_succ _)
        change E.map (includeLast (commaDegree c)).op e =
          appendedBoundaryFace hα c previous (includeLast (commaDegree c))
            (Nat.zero_lt_succ _) at h
        rw [appendedBoundaryFace_last] at h
        exact h }
  refine ⟨z, ?_⟩
  intro a f hf
  apply GoodAppendedLift.ext
  change E.map (extendEmbedding (ForwardComma.sourceOperator f)).op e =
    (previous a hf).lift.val
  have h := hfaces (extendEmbedding (ForwardComma.sourceOperator f))
    (Nat.succ_lt_succ hf)
  change E.map (extendEmbedding (ForwardComma.sourceOperator f)).op e =
    appendedBoundaryFace hα c previous
      (extendEmbedding (ForwardComma.sourceOperator f))
      (Nat.succ_lt_succ hf) at h
  rw [appendedBoundaryFace_append hα c previous (ForwardComma.sourceOperator f) hf] at h
  have hobj : c.faceObject (ForwardComma.sourceOperator f) = a :=
    ForwardComma.faceObject_source f
  have congrVal {u v : ForwardComma α t} (h : u = v)
      (hu : commaDegree u < commaDegree c) (hv : commaDegree v < commaDegree c) :
      HEq (previous u hu).lift.val (previous v hv).lift.val := by
    subst v
    rfl
  exact h.trans (eq_of_heq (congrVal hobj (by simpa only [hobj] using hf) hf))

/-- A compatible selection below a strict dimension bound. -/
private structure ConePrefix
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) (n : ℕ) where
  lift : ∀ c : ForwardComma α t, commaDegree c < n → GoodAppendedLift hα c
  natural : ∀ {a b : ForwardComma α t} (f : a ⟶ b)
    (hab : commaDegree a < commaDegree b) (hb : commaDegree b < n),
    GoodAppendedLift.restrict f (lift b hb) = lift a (lt_trans hab hb)

private def conePrefixZero
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) : ConePrefix hα t 0 where
  lift c h := False.elim (Nat.not_lt_zero _ h)
  natural := by
    intro a b f hab hb
    exact False.elim (Nat.not_lt_zero _ hb)

private def ConePrefix.topFill
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) {n : ℕ}
    (p : ConePrefix hα t n) (c : ForwardComma α t)
    (hc : commaDegree c = n) :
    {z : GoodAppendedLift hα c //
      ∀ {a : ForwardComma α t} (f : a ⟶ c)
        (h : commaDegree a < commaDegree c),
        GoodAppendedLift.restrict f z = p.lift a (by omega)} := by
  let previous : ∀ d : ForwardComma α t,
      commaDegree d < commaDegree c → GoodAppendedLift hα d :=
    fun d hd ↦ p.lift d (by omega)
  have hp : CompatiblePrevious hα t c previous := by
    intro a b f hab hbc
    exact p.natural f hab (by omega)
  exact fill c previous hp

private def ConePrefix.succ
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) {n : ℕ}
    (p : ConePrefix hα t n) : ConePrefix hα t (n + 1) where
  lift c hc := by
    classical
    exact if h : commaDegree c < n then p.lift c h
      else (p.topFill fill c (by omega)).val
  natural := by
    intro a b f hab hb
    classical
    by_cases hbn : commaDegree b < n
    · have han : commaDegree a < n := lt_trans hab hbn
      simpa [hbn, han] using p.natural f hab hbn
    · have htop : commaDegree b = n := by omega
      have han : commaDegree a < n := by omega
      simpa [hbn, han] using (p.topFill fill b htop).property f hab

private def conePrefix
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) (n : ℕ) : ConePrefix hα t n :=
  Nat.rec (conePrefixZero hα t) (fun _ p ↦ p.succ fill) n

private def coneDefault
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) (c : ForwardComma α t) :
    GoodAppendedLift hα c :=
  (conePrefix fill (commaDegree c + 1)).lift c (Nat.lt_succ_self _)

private def coneStepOfCompatibleFiller
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) : ConeStep hα t := by
  intro c previous
  classical
  by_cases hc : CompatiblePrevious hα t c previous
  · exact ⟨(fill c previous hc).val, by
      intro _ a f h
      exact (fill c previous hc).property f h⟩
  · exact ⟨coneDefault fill c, by intro h; exact False.elim (hc h)⟩

private def chosenGood
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (step : ConeStep hα t) (c : ForwardComma α t) :
    GoodAppendedLift hα c :=
  (measure commaDegree).wf.fix
    (fun c previous ↦
      (step c (fun d h ↦ previous d h)).val) c

private theorem chosenGood_eq
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (step : ConeStep hα t) (c : ForwardComma α t) :
    chosenGood step c =
      (step c (fun d _ ↦ chosenGood step d)).val := by
  let F : ∀ c : ForwardComma α t,
      (∀ d : ForwardComma α t, commaDegree d < commaDegree c →
        GoodAppendedLift hα d) → GoodAppendedLift hα c :=
    fun c previous ↦ (step c previous).val
  change (measure commaDegree).wf.fix F c =
    (step c (fun d _ ↦ (measure commaDegree).wf.fix F d)).val
  rw [WellFounded.fix_eq]
  rfl

private theorem chosenGood_natural_strict
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (step : ConeStep hα t)
    {a b : ForwardComma α t} (f : a ⟶ b)
    (h : commaDegree a < commaDegree b) :
    GoodAppendedLift.restrict f (chosenGood step b) = chosenGood step a := by
  have aux : ∀ d : ForwardComma α t,
      ∀ {c : ForwardComma α t} (g : c ⟶ d)
        (hcd : commaDegree c < commaDegree d),
        GoodAppendedLift.restrict g (chosenGood step d) = chosenGood step c := by
    intro d
    induction d using (measure commaDegree).wf.induction with
    | h d ih =>
      intro c g hcd
      rw [chosenGood_eq step d]
      apply (step d (fun e _ ↦ chosenGood step e)).property
      · intro c' d' k hcd' hdd'
        exact ih d' hdd' k hcd'
      · exact hcd
  exact aux b f h

/-- All appended-target lifts form a presheaf on the original forward comma.
Only injective source operators act on the lifts; target maps are arbitrary. -/
def appendedLiftDiagram {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} (α : E ⟶ restriction X) (t : X.Elementsᵒᵖ) :
    (ForwardComma α t)ᵒᵖ ⥤ Type where
  obj c := AppendedLift α c.unop
  map f := AppendedLift.restrict α f.unop
  map_id c := by
    funext z
    apply Subtype.ext
    change E.map (extendEmbedding (ForwardComma.sourceOperator (𝟙 c.unop))).op z.val =
      z.val
    rw [ForwardComma.sourceOperator_id, extendEmbedding_id, op_id, E.map_id]
    rfl
  map_comp f g := by
    funext z
    apply Subtype.ext
    change E.map (extendEmbedding (ForwardComma.sourceOperator (g.unop ≫ f.unop))).op
        z.val =
      E.map (extendEmbedding (ForwardComma.sourceOperator g.unop)).op
        (E.map (extendEmbedding (ForwardComma.sourceOperator f.unop)).op z.val)
    rw [ForwardComma.sourceOperator_comp, extendEmbedding_comp, op_comp,
      E.map_comp]
    rfl

/-- The exact output expected from the recursive compatible-boundary filler.
Naturality uses every injective comma arrow; the two face equalities hold in
the source, beyond their automatic target equations. -/
structure ConeChoice {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) (t : X.Elementsᵒᵖ) where
  lift : ∀ c : ForwardComma α t, AppendedLift α c
  naturality : ∀ {c d : ForwardComma α t} (f : c ⟶ d),
    AppendedLift.restrict α f (lift d) = lift c
  initial : ∀ c : ForwardComma α t,
    E.map (includeInitial c.left.unop.fst.unop.len).op (lift c).val =
      c.left.unop.snd
  last : ∀ c : ForwardComma α t,
    E.map (includeLast c.left.unop.fst.unop.len).op (lift c).val =
      centerLift hα t

/-- A degree-recursive rule with compatible proper-face equations produces
the full natural appended cone choice, including equal-degree comma arrows. -/
def coneChoiceOfStep
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (step : ConeStep hα t) : ConeChoice hα t where
  lift c := (chosenGood step c).lift
  naturality := by
    intro c d f
    have hle : commaDegree c ≤ commaDegree d :=
      SimplexCategory.len_le_of_mono (inclusion.map (ForwardComma.sourceOperator f))
    by_cases hlt : commaDegree c < commaDegree d
    · exact congrArg GoodAppendedLift.lift (chosenGood_natural_strict step f hlt)
    · have heq : commaDegree c = commaDegree d := Nat.le_antisymm hle (Nat.le_of_not_gt hlt)
      have hcd : c = d := ForwardComma.eq_of_degree_eq f heq
      subst d
      have hf : f = 𝟙 c := ForwardComma.endomorphism_eq_id f
      subst f
      have hz := congrFun ((goodAppendedLiftDiagram hα t).map_id (op c))
        (chosenGood step c)
      exact congrArg GoodAppendedLift.lift hz
  initial c := (chosenGood step c).initial
  last c := (chosenGood step c).last

/-- Compatible relative fillers alone give a cone choice. A bounded
prefix construction supplies fallback objects for the total recursion. -/
def coneChoiceOfCompatibleFiller
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (fill : CompatibleConeFiller hα t) : ConeChoice hα t :=
  coneChoiceOfStep (coneStepOfCompatibleFiller fill)

/-- An appended cone choice gives the actual forward-comma object at each
object, with the original full target simplex and arrow. -/
def ConeChoice.appendObject {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) (c : ForwardComma α t) : ForwardComma α t := by
  let s : E.Elements := ⟨op ⦋c.left.unop.fst.unop.len + 1⦌ₛ, (H.lift c).val⟩
  let h : (toFullElements α).obj (op s) ⟶ t :=
    Quiver.Hom.op (⟨c.appendTargetOperator.op, by
      change X.map c.appendTargetOperator.op t.unop.snd =
        α.app (op ⦋c.left.unop.fst.unop.len + 1⦌ₛ) (H.lift c).val
      exact (H.lift c).property.symm⟩ :
      t.unop ⟶ ((toFullElements α).obj (op s)).unop)
  exact CostructuredArrow.mk h

/-- The appended arrow uses the same injective source operator with a new
last vertex. The full target operator may still be noninjective. -/
def ConeChoice.appendArrow {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) {c d : ForwardComma α t} (f : c ⟶ d) :
    H.appendObject c ⟶ H.appendObject d := by
  let a := extendEmbedding (ForwardComma.sourceOperator f)
  let u : (H.appendObject c).left ⟶ (H.appendObject d).left :=
    Quiver.Hom.op (⟨a.op, by
      change E.map a.op (H.lift d).val = (H.lift c).val
      exact congrArg Subtype.val (H.naturality f)⟩ :
      (H.appendObject d).left.unop ⟶ (H.appendObject c).left.unop)
  refine CostructuredArrow.homMk u ?_
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  change d.appendTargetOperator.op ≫ (inclusion.map a).op =
    c.appendTargetOperator.op
  exact congrArg Quiver.Hom.op (ForwardComma.appendTargetOperator_natural f)

/-- A compatible choice of appended lifts acts functorially on the whole
forward comma, preserving the original noninjective target operators. -/
def ConeChoice.appendFunctor {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) : ForwardComma α t ⥤ ForwardComma α t where
  obj := H.appendObject
  map := H.appendArrow
  map_id c := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext E
    change (extendEmbedding (ForwardComma.sourceOperator (𝟙 c))).op =
      (𝟙 ⦋c.left.unop.fst.unop.len + 1⦌ₛ).op
    rw [ForwardComma.sourceOperator_id, extendEmbedding_id]
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext E
    change (extendEmbedding (ForwardComma.sourceOperator (f ≫ g))).op =
      (extendEmbedding (ForwardComma.sourceOperator g)).op ≫
        (extendEmbedding (ForwardComma.sourceOperator f)).op
    rw [ForwardComma.sourceOperator_comp, extendEmbedding_comp, op_comp]

/-- The old simplex includes as the initial face of its appended lift. -/
def ConeChoice.initialArrow {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) (c : ForwardComma α t) :
    c ⟶ H.appendObject c := by
  let a := includeInitial c.left.unop.fst.unop.len
  let u : c.left ⟶ (H.appendObject c).left :=
    Quiver.Hom.op (⟨a.op, by
      change E.map a.op (H.lift c).val = c.left.unop.snd
      exact H.initial c⟩ :
      (H.appendObject c).left.unop ⟶ c.left.unop)
  refine CostructuredArrow.homMk u ?_
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  change c.appendTargetOperator.op ≫ (inclusion.map a).op =
    c.targetOperator.op
  exact congrArg Quiver.Hom.op (extendSimplex_initial c.targetOperator)

/-- The selected center vertex includes as the new last face. -/
def ConeChoice.lastArrow {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) (c : ForwardComma α t) :
    center hα t ⟶ H.appendObject c := by
  let a := includeLast c.left.unop.fst.unop.len
  let u : (center hα t).left ⟶ (H.appendObject c).left :=
    Quiver.Hom.op (⟨a.op, by
      change E.map a.op (H.lift c).val = centerLift hα t
      exact H.last c⟩ :
      (H.appendObject c).left.unop ⟶ (center hα t).left.unop)
  refine CostructuredArrow.homMk u ?_
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  change c.appendTargetOperator.op ≫ (inclusion.map a).op =
    (lastTargetOperator t).op
  exact congrArg Quiver.Hom.op (extendSimplex_last c.targetOperator)

/-- The initial-face arrows are natural in every injective comma arrow. -/
def ConeChoice.initialNat {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) : 𝟭 (ForwardComma α t) ⟶ H.appendFunctor where
  app := H.initialArrow
  naturality := by
    intro c d f
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext E
    change (ForwardComma.sourceOperator f ≫ includeInitial d.left.unop.fst.unop.len).op =
      (includeInitial c.left.unop.fst.unop.len ≫
        extendEmbedding (ForwardComma.sourceOperator f)).op
    apply congrArg Quiver.Hom.op
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [includeInitial, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

/-- The last-face arrows form a natural cone from the fixed center. -/
def ConeChoice.lastNat {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) :
    (Functor.const (ForwardComma α t)).obj (center hα t) ⟶ H.appendFunctor where
  app := H.lastArrow
  naturality := by
    intro c d f
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext E
    change (includeLast d.left.unop.fst.unop.len).op =
      (includeLast c.left.unop.fst.unop.len ≫
        extendEmbedding (ForwardComma.sourceOperator f)).op
    apply congrArg Quiver.Hom.op
    apply SemiSimplexCategory.hom_ext
    ext i
    simp [includeLast, extendEmbedding, SemiSimplexCategory.homEquiv,
      SemiSimplexCategory.smallCategory]

/-- A coherent appended-lift choice contracts the exact forward comma. -/
theorem ConeChoice.comma_point_GW {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    {hα : HasBoundaryLifting α} {t : X.Elementsᵒᵖ}
    (H : ConeChoice hα t) : GW (pointMap (nerve (ForwardComma α t))) := by
  let F : ForwardComma α t ⥤ Discrete PUnit.{1} :=
    (Functor.const _).obj ⟨PUnit.unit⟩
  let G : Discrete PUnit.{1} ⥤ ForwardComma α t :=
    (Functor.const _).obj (center hα t)
  let hR : F ⋙ G ⟶ H.appendFunctor :=
    { app c := (H.lastNat).app c
      naturality _ _ u := (H.lastNat).naturality u }
  let hG : G ⋙ F ⟶ 𝟭 (Discrete PUnit.{1}) :=
    { app P := eqToHom (Subsingleton.elim _ P)
      naturality _ _ _ := Subsingleton.elim _ _ }
  have hC : DaggerNerveHomotopy.NatTransZigzag
      (F ⋙ G) (𝟭 (ForwardComma α t)) :=
    .trans _ H.appendFunctor _ (.rel _ _ ⟨hR⟩)
      (.symm _ _ (.rel _ _ ⟨H.initialNat⟩))
  haveI : WeakEquivalence (nerveMap F) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNerveHomotopy.nerveMap_geometricW F G hC (.rel _ _ ⟨hG⟩))
  have he : nerveMap F ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit.{1}).hom =
      pointMap (nerve (ForwardComma α t)) :=
    pointIsTerminal.hom_ext _ _
  rw [← he]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- The exact forward-comma cone criterion yields a weak equivalence on
the original full simplex categories of elements. -/
theorem toFullElements_weak_of_coneChoices
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α)
    (H : ∀ t : X.Elementsᵒᵖ, ConeChoice hα t) :
    GW (nerveMap (toFullElements α)) := by
  apply DaggerNerveTheoremA.nerveMap_GW
  intro t
  exact (H t).comma_point_GW

/-- Apply the forward-comma criterion to the compatible fillers of the
appended simplices. -/
theorem toFullElements_weak_of_compatibleFillers
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α)
    (fill : ∀ t : X.Elementsᵒᵖ, CompatibleConeFiller hα t) :
    GW (nerveMap (toFullElements α)) :=
  toFullElements_weak_of_coneChoices hα
    (fun t ↦ coneChoiceOfCompatibleFiller (fill t))


/-- Relative boundary lifting gives weak equivalence of the exact
semisimplicial source with the original full simplex category. -/
theorem toFullElements_weak
    {E : SemiSimplexCategoryᵒᵖ ⥤ Type}
    {X : SSet.{0}} {α : E ⟶ restriction X}
    (hα : HasBoundaryLifting α) : GW (nerveMap (toFullElements α)) :=
  toFullElements_weak_of_compatibleFillers hα (fun t ↦ compatibleConeFiller hα t)


end

end DaggerModels.PartII.SemiSimplexBoundaryLifting
