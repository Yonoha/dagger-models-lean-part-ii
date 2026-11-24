import DaggerModelsPartII.JTStrictTransport
import OriginalFlagDiscreteNerve
import NerveHomotopy
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.CategoryTheory.Limits.Presheaf

/-!
# Functorial bar rows and their augmentation

For a reversal presheaf `P`, the category `StructuredArrow d (elementIndex P)`
records elements over a full reversal-index chain and a map from `d` to its
first index. Its nerve defines a functorial reversal simplicial space.
The natural augmentation has an explicit section and contraction at each row,
giving a rowwise geometric weak equivalence and surjectivity on row vertices.

The explicit chain-coproduct presentation and identification with the
manuscript's coend realization still require separate comparison proofs.
Projective cofibrancy and the derived density comparison are not asserted here.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTProjectiveBar

noncomputable section

/-- The opposite category of elements projects to the reversal-simplex
category. An arrow is exactly a presheaf-compatible forward index map. -/
def elementIndex (P : ReverseSimplexᵒᵖ ⥤ Type) :
    P.Elementsᵒᵖ ⥤ ReverseSimplex :=
  (CategoryOfElements.π P).leftOp

/-- At outer index `d`, objects are triples `(m, x, d ⟶ m)` with
`x ∈ P_m`; morphisms are the full reversal-index maps respecting `x`. -/
abbrev barCategory (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) :=
  StructuredArrow d (elementIndex P)

/-- The literal bar simplicial set at outer index `d`. Its `r`-simplices
are the manuscript's chains with a represented `d`-simplex in the first
factor. -/
def barValue (P : ReverseSimplexᵒᵖ ⥤ Type) (d : ReverseSimplex) : SSet.{0} :=
  nerve (barCategory P d)

/-- Precomposition in the outer reversal index. -/
def barOuterMap (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e : ReverseSimplex} (f : d ⟶ e) : barValue P e ⟶ barValue P d :=
  nerveMap (StructuredArrow.map f)

private theorem structuredArrowMap_id (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    StructuredArrow.map (𝟙 d) = 𝟭 (barCategory P d) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro s
    exact StructuredArrow.map_id
  case h_map =>
    intro s t f
    apply StructuredArrow.hom_ext
    rfl

private theorem structuredArrowMap_comp (P : ReverseSimplexᵒᵖ ⥤ Type)
    {d e h : ReverseSimplex} (f : d ⟶ e) (g : e ⟶ h) :
    StructuredArrow.map (f ≫ g) =
      (StructuredArrow.map g : barCategory P h ⥤ barCategory P e) ⋙
        (StructuredArrow.map f : barCategory P e ⥤ barCategory P d) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro s
    exact StructuredArrow.map_comp
  case h_map =>
    intro s t k
    apply StructuredArrow.hom_ext
    rfl

/-- A presheaf morphism changes every terminal element of a bar chain and
keeps its complete reversal-index chain and represented first simplex. -/
def barWeightMap {P Q : ReverseSimplexᵒᵖ ⥤ Type} (α : P ⟶ Q)
    (d : ReverseSimplex) : barValue P d ⟶ barValue Q d :=
  nerveMap (StructuredArrow.pre d (CategoryOfElements.map α).op (elementIndex Q))

/-- The outer-index maps assemble into the actual reversal simplicial space.
The functor laws reduce to `StructuredArrow.map_id` and `map_comp`. -/
def barPresheaf (P : ReverseSimplexᵒᵖ ⥤ Type) :
    SegalLocalizers.ReverseDaggerSpace.{0} where
  obj d := barValue P d.unop
  map f := barOuterMap P f.unop
  map_id d := by
    change nerveMap (StructuredArrow.map (𝟙 d.unop)) = 𝟙 _
    rw [structuredArrowMap_id P d.unop]
    rfl
  map_comp f g := by
    change nerveMap (StructuredArrow.map (f ≫ g).unop) =
      nerveMap (StructuredArrow.map f.unop) ≫
        nerveMap (StructuredArrow.map g.unop)
    rw [unop_comp, structuredArrowMap_comp]
    rfl

/-- The coefficient map is natural in the outer reversal index. -/
def barPresheafMap {P Q : ReverseSimplexᵒᵖ ⥤ Type} (α : P ⟶ Q) :
    barPresheaf P ⟶ barPresheaf Q where
  app d := barWeightMap α d.unop
  naturality := by
    intro d e f
    apply NatTrans.ext
    funext q γ
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      rfl
    case h_map =>
      intro i j h
      apply StructuredArrow.hom_ext
      rfl

/-- A functorial bar construction on all reversal presheaves, before
restricting its input to dagger simplicial sets through `toPresheaf`. -/
def barFunctor :
    (ReverseSimplexᵒᵖ ⥤ Type) ⥤ SegalLocalizers.ReverseDaggerSpace.{0} where
  obj := barPresheaf
  map := barPresheafMap
  map_id P := by
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext q γ
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      rfl
    case h_map =>
      intro i j h
      apply StructuredArrow.hom_ext
      rfl
  map_comp α β := by
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext q γ
    apply CategoryTheory.Functor.ext
    case h_obj =>
      intro i
      rfl
    case h_map =>
      intro i j h
      apply StructuredArrow.hom_ext
      rfl

/-- The canonical augmentation value of a length-zero bar cell. -/
def augmentationValue (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (s : barCategory P d) : P.obj (op d) :=
  P.map s.hom.op s.right.unop.2

/-- The identity summand at `d` attached to an element of `P_d`. -/
def identityCell (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (x : P.obj (op d)) : barCategory P d :=
  StructuredArrow.mk
    (show d ⟶ (elementIndex P).obj
      (op (P.elementsMk (op d) x)) from 𝟙 d)

/-- The augmentation is surjective at every outer vertex because the
identity summand maps back to its chosen element. -/
theorem augmentationValue_identityCell (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (x : P.obj (op d)) :
    augmentationValue P d (identityCell P d x) = x := by
  change P.map (𝟙 (op d)) x = x
  rw [P.map_id]
  rfl

/-- A structured-arrow morphism preserves the represented augmentation
value. This is the category-of-elements equation and the structured-arrow
triangle, with no use of a weak-equivalence theorem. -/
private theorem augmentationValue_map (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) {s t : barCategory P d} (f : s ⟶ t) :
    augmentationValue P d s = augmentationValue P d t := by
  have hx : P.map ((elementIndex P).map f.right).op t.right.unop.2 =
      s.right.unop.2 := f.right.unop.property
  have hw : s.hom ≫ (elementIndex P).map f.right = t.hom :=
    StructuredArrow.w f
  unfold augmentationValue
  calc
    P.map s.hom.op s.right.unop.2 =
        P.map s.hom.op
          (P.map ((elementIndex P).map f.right).op t.right.unop.2) := by rw [hx]
    _ = P.map
        (((elementIndex P).map f.right).op ≫ s.hom.op) t.right.unop.2 := by
          rw [P.map_comp]
          rfl
    _ = P.map t.hom.op t.right.unop.2 := by
          rw [← op_comp, hw]

/-- The canonical augmentation functor to the discrete set of `d`-simplices. -/
def augmentationFunctor (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    barCategory P d ⥤ Discrete (P.obj (op d)) where
  obj s := Discrete.mk (augmentationValue P d s)
  map f := Discrete.eqToHom (augmentationValue_map P d f)

/-- The full augmentation at one reversal index, obtained from the nerve
of the actual augmentation functor. -/
def augmentationAt (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    barValue P d ⟶ DaggerOriginalFlagFlankification.constantSSet (P.obj (op d)) :=
  nerveMap (augmentationFunctor P d) ≫
    (DaggerOriginalFlagFlankification.nerveDiscreteIso (P.obj (op d))).hom

/-- The augmentation at `d` sends an identity cell to its original value. -/
theorem augmentationAt_identityCell (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (x : P.obj (op d)) :
    (augmentationAt P d).app (op ⦋0⦌)
      (ComposableArrows.mk₀ (identityCell P d x)) = x := by
  simpa [augmentationAt] using augmentationValue_identityCell P d x

/-- The length-zero identity summand makes the augmentation onto every
vertical-zero bidegree, including `(0,0)`. -/
theorem augmentationAt_zero_surjective (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    Function.Surjective ((augmentationAt P d).app (op ⦋0⦌)) := by
  intro x
  exact ⟨ComposableArrows.mk₀ (identityCell P d x),
    augmentationAt_identityCell P d x⟩

/-- The row augmentations are natural in the full reversal index. -/
def augmentation (P : ReverseSimplexᵒᵖ ⥤ Type) :
    barPresheaf P ⟶
      (DaggerModels.PartII.discretePresheaf ReverseSimplex).obj P where
  app d := augmentationAt P d.unop
  naturality := by
    intro d e f
    apply NatTrans.ext
    funext q γ
    have h : augmentationValue P e.unop
        ((StructuredArrow.map f.unop).obj (γ.obj 0)) =
      P.map f (augmentationValue P d.unop (γ.obj 0)) := by
      simp [augmentationValue, elementIndex, StructuredArrow.map]
    exact h

/-- The full augmentation is natural in the input dagger presheaf. -/
private theorem augmentation_naturality {P Q : ReverseSimplexᵒᵖ ⥤ Type}
    (α : P ⟶ Q) :
    barPresheafMap α ≫ augmentation Q =
      augmentation P ≫
        (DaggerModels.PartII.discretePresheaf ReverseSimplex).map α := by
  apply NatTrans.ext
  funext d
  apply NatTrans.ext
  funext q γ
  have h : augmentationValue Q d.unop
      ((StructuredArrow.pre d.unop (CategoryOfElements.map α).op
        (elementIndex Q)).obj (γ.obj 0)) =
      α.app (op d.unop) (augmentationValue P d.unop (γ.obj 0)) := by
    simp only [augmentationValue, CategoryOfElements.map,
      FunctorToTypes.naturality]
    rfl
  exact h

/-- The manuscript's bar on dagger simplicial sets, with its actual
augmentation to the constant vertical diagram. -/
def barOnDagger : DaggerSSet.{0} ⥤ SegalLocalizers.ReverseDaggerSpace.{0} :=
  DaggerSSet.toPresheaf ⋙ barFunctor

/-- The projective bar augmentation before the separate model assertion. -/
def barAugmentation : barOnDagger ⟶ ConstantVertexAdjunction.delta :=
  Functor.whiskerLeft DaggerSSet.toPresheaf
    { app := augmentation
      naturality := by
        intro P Q α
        exact augmentation_naturality α }

/-- A section of the augmentation functor, choosing the identity cell in
each component of the discrete target. -/
def sectionFunctor (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    Discrete (P.obj (op d)) ⥤ barCategory P d where
  obj x := identityCell P d x.as
  map {x y} f := eqToHom
    (congrArg (identityCell P d) (Discrete.eq_of_hom f))
  map_id x := by
    simp
  map_comp f g := by
    simp

/-- The identity cell attached to the augmentation of `s` maps canonically
to `s`; its underlying index arrow is exactly `s.hom`. -/
def centerArrow (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) (s : barCategory P d) :
    identityCell P d (augmentationValue P d s) ⟶ s := by
  refine StructuredArrow.homMk ?_ ?_
  · exact (CategoryOfElements.homMk s.right.unop
      (P.elementsMk (op d) (augmentationValue P d s)) s.hom.op rfl).op
  · simp [identityCell, elementIndex]

/-- The section followed by augmentation is strictly the identity on the
discrete target. -/
private theorem section_augmentation_id (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    sectionFunctor P d ⋙ augmentationFunctor P d =
      𝟭 (Discrete (P.obj (op d))) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro x
    apply Discrete.ext
    exact augmentationValue_identityCell P d x.as
  case h_map =>
    intro x y f
    exact Subsingleton.elim _ _

/-- The identity cells contract each augmentation fiber. -/
def contraction (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    augmentationFunctor P d ⋙ sectionFunctor P d ⟶
      𝟭 (barCategory P d) where
  app s := centerArrow P d s
  naturality := by
    intro s t f
    apply StructuredArrow.hom_ext
    letI : (elementIndex P).Faithful := by
      dsimp [elementIndex]
      infer_instance
    apply (elementIndex P).map_injective
    have elements_eqToHom {a b : P.Elements} (h : a = b) :
        (eqToHom h : a ⟶ b).val =
          eqToHom (congrArg (fun e : P.Elements ↦ e.1) h) := by
      cases h
      rfl
    simpa [centerArrow, sectionFunctor, augmentationFunctor, elementIndex,
      elements_eqToHom] using (StructuredArrow.w f).symm

/-- The row augmentation is a weak homotopy equivalence. The two explicit
functors and their natural contraction satisfy the native nerve-homotopy
criterion, and the last map is the discrete-nerve isomorphism. -/
theorem augmentationAt_GW (P : ReverseSimplexᵒᵖ ⥤ Type)
    (d : ReverseSimplex) :
    DaggerSSetGluing.GW (augmentationAt P d) := by
  let F := augmentationFunctor P d
  let G := sectionFunctor P d
  have hFG : DaggerNerveHomotopy.NatTransZigzag (F ⋙ G)
      (𝟭 (barCategory P d)) :=
    Relation.EqvGen.rel _ _ ⟨contraction P d⟩
  have hGF : DaggerNerveHomotopy.NatTransZigzag (G ⋙ F)
      (𝟭 (Discrete (P.obj (op d)))) :=
    Relation.EqvGen.rel _ _ ⟨eqToHom (section_augmentation_id P d)⟩
  have hF : DaggerSSetGluing.GW (nerveMap F) :=
    DaggerNerveHomotopy.nerveMap_geometricW F G hFG hGF
  haveI : HomotopicalAlgebra.WeakEquivalence (nerveMap F) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hF
  change DaggerSSetGluing.GW
    (nerveMap F ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso (P.obj (op d))).hom)
  exact (DaggerSSetGluing.weakEquivalence_iff_GW _).mp inferInstance

/-- The actual dagger-input augmentation is a geometric weak equivalence
at every reversal-index row. -/
theorem barAugmentation_rowwise_GW (X : DaggerSSet.{0})
    (d : ReverseSimplexᵒᵖ) :
    DaggerSSetGluing.GW (((barAugmentation.app X).app d)) :=
  augmentationAt_GW (DaggerSSet.toPresheaf.obj X) d.unop

/-- Every row vertex of the actual dagger-input augmentation has a preimage
in its identity summand, including at bidegree zero. -/
theorem barAugmentation_zero_surjective (X : DaggerSSet.{0})
    (d : ReverseSimplexᵒᵖ) :
    Function.Surjective (((barAugmentation.app X).app d).app (op ⦋0⦌)) :=
  augmentationAt_zero_surjective (DaggerSSet.toPresheaf.obj X) d.unop

end

end DaggerModels.PartII.JTProjectiveBar
