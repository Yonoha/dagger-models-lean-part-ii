import DaggerModelsPartII.JTSemiSimplexCommaContractible
import Mathlib.CategoryTheory.Elements

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSemiSimplexElementsWeak

noncomputable section

private abbrev P (X : SSet.{0}) := SemiSimplexCategory.toSimplexCategory.op ⋙ X

/-- The unrestricted simplex operator underlying a semisimplex. -/
def elementForgetUnop (X : SSet.{0}) : (P X).Elements ⥤ X.Elements where
  obj s := ⟨SemiSimplexCategory.toSimplexCategory.op.obj s.1, s.2⟩
  map f := ⟨SemiSimplexCategory.toSimplexCategory.op.map f.val, f.property⟩
  map_id s := CategoryOfElements.ext X _ _ (by simp)
  map_comp f g := CategoryOfElements.ext X _ _ (by simp)

/-- The time-direction comparison for the category of elements. -/
def elementForget (X : SSet.{0}) :
    (P X).Elementsᵒᵖ ⥤ X.Elementsᵒᵖ := (elementForgetUnop X).op

private abbrev Fiber (X : SSet.{0}) (d : X.Elementsᵒᵖ) :=
  CostructuredArrow (elementForget X) d

private abbrev Index (X : SSet.{0}) (d : X.Elementsᵒᵖ) :=
  CostructuredArrow SemiSimplexCategory.toSimplexCategory d.unop.1.unop

private def toIndex (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    Fiber X d ⥤ Index X d where
  obj c := CostructuredArrow.mk (Y := c.left.unop.1.unop) (by
    exact c.hom.unop.val.unop)
  map {c e} u := CostructuredArrow.homMk u.left.unop.val.unop (by
    have h := CostructuredArrow.w u
    simpa [elementForget, elementForgetUnop] using
      congrArg (fun z : (elementForget X).obj c.left ⟶ d ↦ z.unop.val.unop) h)
  map_id c := CostructuredArrow.hom_ext _ _ (by rfl)
  map_comp u v := CostructuredArrow.hom_ext _ _ (by rfl)

private def fromIndexObj (X : SSet.{0}) (d : X.Elementsᵒᵖ)
    (q : Index X d) : Fiber X d := by
  let s : (P X).Elements := ⟨op q.left, X.map q.hom.op d.unop.2⟩
  let h : (elementForget X).obj (op s) ⟶ d :=
    Quiver.Hom.op (⟨q.hom.op, rfl⟩ :
      d.unop ⟶ ((elementForget X).obj (op s)).unop)
  exact CostructuredArrow.mk h

private def fromIndex (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    Index X d ⥤ Fiber X d where
  obj := fromIndexObj X d
  map {q r} j := CostructuredArrow.homMk (by
    let s : (P X).Elements := ⟨op q.left, X.map q.hom.op d.unop.2⟩
    let t : (P X).Elements := ⟨op r.left, X.map r.hom.op d.unop.2⟩
    let h : t ⟶ s := by
      refine ⟨?_, ?_⟩
      · change op r.left ⟶ op q.left
        exact (j.left).op
      · change X.map (SemiSimplexCategory.toSimplexCategory.map j.left).op
          (X.map r.hom.op d.unop.2) = X.map q.hom.op d.unop.2
        have hw : r.hom.op ≫
            (SemiSimplexCategory.toSimplexCategory.map j.left).op = q.hom.op := by
          have hw₀ : SemiSimplexCategory.toSimplexCategory.map j.left ≫ r.hom =
              q.hom := CostructuredArrow.w j
          exact congrArg Quiver.Hom.op hw₀
        rw [← FunctorToTypes.map_comp_apply, hw]
    change (fromIndexObj X d q).left ⟶ (fromIndexObj X d r).left
    exact h.op) (by
      apply Quiver.Hom.unop_inj
      apply CategoryOfElements.ext X
      change r.hom.op ≫
        (SemiSimplexCategory.toSimplexCategory.map j.left).op = q.hom.op
      exact congrArg Quiver.Hom.op (CostructuredArrow.w j))
  map_id q := CostructuredArrow.hom_ext _ _ (by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext (P X)
    change 𝟙 (op q.left) = 𝟙 (op q.left)
    rfl)
  map_comp j k := CostructuredArrow.hom_ext _ _ (by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext (P X)
    simp)

private theorem to_from_obj (X : SSet.{0}) (d : X.Elementsᵒᵖ)
    (q : Index X d) :
    (toIndex X d).obj ((fromIndex X d).obj q) = q := by
  apply CostructuredArrow.obj_ext _ _ rfl
  simp [toIndex, fromIndex, fromIndexObj, elementForget, elementForgetUnop]

private theorem from_to_obj (X : SSet.{0}) (d : X.Elementsᵒᵖ)
    (c : Fiber X d) :
    (fromIndex X d).obj ((toIndex X d).obj c) = c := by
  have hl : ((fromIndex X d).obj ((toIndex X d).obj c)).left = c.left := by
    apply congrArg op
    refine Functor.Elements.ext _ _ rfl ?_
    simp [P, toIndex, elementForget, elementForgetUnop]
  apply CostructuredArrow.obj_ext _ _ hl
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  have hb : (eqToHom hl).unop.val = 𝟙 _ := by
    rw [eqToHom_unop]
    change (CategoryOfElements.π (P X)).map
      (eqToHom (congrArg unop hl.symm)) = 𝟙 _
    rw [eqToHom_map]
    exact eqToHom_refl _ _
  change c.hom.unop.val ≫
    SemiSimplexCategory.toSimplexCategory.op.map (eqToHom hl).unop.val =
      ((fromIndex X d).obj ((toIndex X d).obj c)).hom.unop.val
  rw [hb]
  simp [elementForget, elementForgetUnop, fromIndex, fromIndexObj, toIndex]

private theorem to_from (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    fromIndex X d ⋙ toIndex X d = 𝟭 (Index X d) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro q
    exact to_from_obj X d q
  · intro q r j
    apply CostructuredArrow.hom_ext
    simp [toIndex, fromIndex, fromIndexObj]

private theorem from_to (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    toIndex X d ⋙ fromIndex X d = 𝟭 (Fiber X d) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro c
    exact from_to_obj X d c
  · intro c e u
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext (P X)
    simp only [Functor.comp_map, Functor.id_map, CostructuredArrow.comp_left]
    simp [toIndex, fromIndex, fromIndexObj]
    change u.left.unop.val = (CategoryOfElements.π (P X)).map
      (eqToHom (congrArg unop (congrArg Comma.left (from_to_obj X d e))) ≫
        u.left.unop ≫
        eqToHom (congrArg unop
          (congrArg Comma.left (from_to_obj X d c)).symm))
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      eqToHom_map, eqToHom_map]
    simp

/-- The actual comma category over an element `(n,x)` is equivalent to
the category of all simplex maps into `n`, with injective operators as arrows. -/
def commaEquivalence (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    Fiber X d ≌ Index X d :=
  CategoryTheory.Equivalence.mk (toIndex X d) (fromIndex X d)
    (eqToIso (from_to X d)).symm (eqToIso (to_from X d))

/-- The comma category is weakly contractible by its exact pair of inverse
functors with the category of arbitrary simplex maps into the target ordinal.
Its arrows are injective simplex operators. -/
private theorem comma_point_GW (X : SSet.{0}) (d : X.Elementsᵒᵖ) :
    GW (pointMap (nerve (Fiber X d))) := by
  let F := toIndex X d
  let G := fromIndex X d
  have hC : DaggerNerveHomotopy.NatTransZigzag (F ⋙ G) (𝟭 (Fiber X d)) :=
    .rel _ _ ⟨eqToHom (from_to X d)⟩
  have hD : DaggerNerveHomotopy.NatTransZigzag (G ⋙ F) (𝟭 (Index X d)) :=
    .rel _ _ ⟨eqToHom (to_from X d)⟩
  have hF : WeakEquivalence (nerveMap F) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerNerveHomotopy.nerveMap_geometricW F G hC hD)
  have hI : WeakEquivalence (pointMap (nerve (Index X d))) :=
    (weakEquivalence_iff_GW _).mpr
      (DaggerModels.PartII.JTSemiSimplexCommaContractible.point_GW d.unop.1.unop)
  have he : nerveMap F ≫ pointMap (nerve (Index X d)) =
      pointMap (nerve (Fiber X d)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- Forgetting injectivity in the time category of elements induces a
Kan weak equivalence on the original nerves. -/
theorem elementForget_weak (X : SSet.{0}) : GW (nerveMap (elementForget X)) :=
  DaggerNerveTheoremA.nerveMap_GW (elementForget X) (comma_point_GW X)

theorem elementForget_weakEquivalence (X : SSet.{0}) :
    WeakEquivalence (nerveMap (elementForget X)) :=
  (weakEquivalence_iff_GW _).mpr (elementForget_weak X)

private abbrev restrictionFunctor : SSet.{0} ⥤ (SemiSimplexCategoryᵒᵖ ⥤ Type) :=
  (Functor.whiskeringLeft _ _ _).obj SemiSimplexCategory.toSimplexCategory.op

/-- The categories of elements compare naturally for the original
simplicial-set morphisms before taking opposites. -/
def elementForgetUnopNat :
    restrictionFunctor ⋙ Functor.elementsFunctor ⟶ Functor.elementsFunctor where
  app X := (elementForgetUnop X).toCatHom
  naturality {X Y} f := Cat.Hom.ext (by
    change NatTrans.mapElements
      (Functor.whiskerLeft SemiSimplexCategory.toSimplexCategory.op f) ⋙ elementForgetUnop Y =
      elementForgetUnop X ⋙ NatTrans.mapElements f
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro _ _ g
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply CategoryOfElements.ext Y
    rfl)

/-- Forgetting the restriction to injective operators on the opposite
categories of elements commutes with every original map of simplicial sets. -/
def elementForgetNat :
    restrictionFunctor ⋙ Functor.elementsFunctor ⋙ Cat.opFunctor ⟶
      Functor.elementsFunctor ⋙ Cat.opFunctor :=
  Functor.whiskerRight elementForgetUnopNat Cat.opFunctor

end
end DaggerModels.PartII.JTSemiSimplexElementsWeak
