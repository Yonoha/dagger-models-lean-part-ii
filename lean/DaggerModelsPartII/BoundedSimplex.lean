import NativeDualTheoremA
import TopCatModelCategory.SSet.NonDegenerateSimplices

/-! Bound the actual simplex operators used in finite last-vertex diagrams. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.BoundedSimplex

noncomputable section

variable (X : SSet.{0}) (n : ℕ)

/-- The full category of simplices whose dimensions are bounded by `n`. -/
def bounded : ObjectProperty X.Elementsᵒᵖ := fun P ↦ P.unop.fst.unop.len ≤ n

abbrev inclusion := (bounded X n).ι

theorem finite_objects [X.IsFinite] : Finite (bounded X n).FullSubcategory := by
  apply Finite.of_injective
    (f := fun P : (bounded X n).FullSubcategory ↦
      (⟨⟨P.obj.unop.fst.unop.len, Nat.lt_succ_of_le P.property⟩, P.obj.unop.snd⟩ :
        Σ k : Fin (n + 1), X.obj (op ⦋k.val⦌)))
  intro P Q h
  apply ObjectProperty.FullSubcategory.ext
  apply Opposite.unop_injective
  exact congrArg (fun v : Σ k : Fin (n + 1), X.obj (op ⦋k.val⦌) ↦
    (⟨op ⦋v.1.val⦌, v.2⟩ : X.Elements)) h

/-- A bounded simplex diagram has finitely many actual operators between each pair. -/
theorem finite_hom (P Q : (bounded X n).FullSubcategory) : Finite (P ⟶ Q) := by
  apply Finite.of_injective (f := fun f : P ⟶ Q ↦ f.hom.unop.val.unop)
  intro f g h
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  exact congrArg Quiver.Hom.op h

variable {X n}

private abbrev Fiber (d : X.Elementsᵒᵖ) := StructuredArrow d (inclusion X n)

private abbrev operator {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) :=
  P.hom.unop.val.unop

private def restr {P : X.Elementsᵒᵖ} {m : SimplexCategory}
    (f : m ⟶ P.unop.fst.unop) : X.Elementsᵒᵖ :=
  op ⟨op m, X.map f.op P.unop.snd⟩

private def restrArrow {P : X.Elementsᵒᵖ} {m : SimplexCategory}
    (f : m ⟶ P.unop.fst.unop) : restr f ⟶ P :=
  Quiver.Hom.op (⟨f.op, rfl⟩ : P.unop ⟶ (restr f).unop)

private def imageObj {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) : Fiber (n := n) d := by
  let j := image.ι (operator P)
  let i : (bounded X n).FullSubcategory := ⟨restr j,
    (SimplexCategory.len_le_of_mono j).trans P.right.property⟩
  refine StructuredArrow.mk (Y := i) (Quiver.Hom.op (⟨(factorThruImage (operator P)).op, ?_⟩ :
    i.obj.unop ⟶ d.unop))
  change X.map (factorThruImage (operator P)).op (X.map j.op P.right.obj.unop.snd) = d.unop.snd
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, image.fac]
  exact P.hom.unop.property

private def imageToOriginal {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) :
    imageObj P ⟶ P :=
  StructuredArrow.homMk (ObjectProperty.homMk (restrArrow (image.ι (operator P)))) (by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext X
    apply Quiver.Hom.unop_inj
    exact image.fac (operator P))

private abbrev arrowOp {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} (f : P ⟶ Q) :=
  f.right.hom.unop.val.unop

private theorem arrowOp_fac {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} (f : P ⟶ Q) :
    operator P ≫ arrowOp f = operator Q :=
  congrArg (fun g : d ⟶ Q.right.obj ↦ g.unop.val.unop) (StructuredArrow.w f)

private def imageSquare {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} (f : P ⟶ Q) :
    Arrow.mk (operator P) ⟶ Arrow.mk (operator Q) :=
  Arrow.homMk (𝟙 _) (arrowOp f) (by
    change 𝟙 _ ≫ operator Q = operator P ≫ arrowOp f
    rw [Category.id_comp, arrowOp_fac])

private def imageHom {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} (f : P ⟶ Q) :
    imageObj P ⟶ imageObj Q := by
  let k := image.map (imageSquare f)
  have hk : k ≫ image.ι (operator Q) = image.ι (operator P) ≫ arrowOp f :=
    image.map_ι (imageSquare f)
  refine StructuredArrow.homMk (ObjectProperty.homMk (Quiver.Hom.op (⟨k.op, ?_⟩ :
    (imageObj Q).right.obj.unop ⟶ (imageObj P).right.obj.unop))) ?_
  · change X.map k.op (X.map (image.ι (operator Q)).op Q.right.obj.unop.snd) =
      X.map (image.ι (operator P)).op P.right.obj.unop.snd
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, hk, op_comp, FunctorToTypes.map_comp_apply]
    exact congrArg (X.map (image.ι (operator P)).op) f.right.hom.unop.property
  · apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext X
    apply Quiver.Hom.unop_inj
    exact (image.factor_map (imageSquare f)).trans (Category.id_comp _)

private theorem hom_ext {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} {f g : P ⟶ Q}
    (h : arrowOp f = arrowOp g) : f = g := by
  apply StructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext X
  exact congrArg Quiver.Hom.op h

private theorem image_map_fac {d : X.Elementsᵒᵖ} {P Q : Fiber (n := n) d} (f : P ⟶ Q) :
    image.map (imageSquare f) ≫ image.ι (operator Q) =
      image.ι (operator P) ≫ arrowOp f := image.map_ι (imageSquare f)

private def imageFunctor (d : X.Elementsᵒᵖ) : Fiber (n := n) d ⥤ Fiber (n := n) d where
  obj := imageObj
  map := imageHom
  map_id P := by
    apply hom_ext
    apply (cancel_mono (image.ι (operator P))).mp
    change image.map (imageSquare (𝟙 P)) ≫ image.ι (operator P) = 𝟙 _ ≫ _
    rw [image_map_fac]
    change image.ι (operator P) ≫ 𝟙 _ = 𝟙 _ ≫ image.ι (operator P)
    rw [Category.comp_id, Category.id_comp]
  map_comp {P Q R} f g := by
    apply hom_ext
    apply (cancel_mono (image.ι (operator R))).mp
    change image.map (imageSquare (f ≫ g)) ≫ image.ι (operator R) =
      (image.map (imageSquare f) ≫ image.map (imageSquare g)) ≫ image.ι (operator R)
    rw [image_map_fac, Category.assoc, image_map_fac, ← Category.assoc, image_map_fac,
      Category.assoc]
    rfl

private def imageComparison (d : X.Elementsᵒᵖ) :
    imageFunctor (n := n) d ⟶ 𝟭 (Fiber (n := n) d) where
  app := imageToOriginal
  naturality {_ _} f := hom_ext (image.map_ι (imageSquare f))

private abbrev simplex (d : X.Elementsᵒᵖ) := SSet.S.equivElements.symm d.unop

private def reduced {d : X.Elementsᵒᵖ} (h : (simplex d).toN.dim ≤ n) : Fiber (n := n) d :=
  StructuredArrow.mk (Y := ⟨op (SSet.S.equivElements (simplex d).toN.toS), h⟩)
    (Quiver.Hom.op (⟨(simplex d).toNπ.op, (simplex d).map_toNπ⟩ :
      SSet.S.equivElements (simplex d).toN.toS ⟶ d.unop))

private theorem sameCore {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) :
    (simplex (imageObj P).right.obj).toN = (simplex d).toN := by
  apply SSet.S.toN_eq_iff.mpr
  rw [SSet.S.subcomplex_toN]
  exact SSet.S.subcomplex_eq_of_epi (simplex d) (simplex (imageObj P).right.obj)
    (factorThruImage (operator P)) (imageObj P).hom.unop.property

private abbrev imageToCoreOp {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) :=
  SSet.S.toNπ' (sameCore P)

private theorem imageToCore_fac {d : X.Elementsᵒᵖ} (P : Fiber (n := n) d) :
    factorThruImage (operator P) ≫ imageToCoreOp P = (simplex d).toNπ := by
  symm
  apply ((simplex d).toNπ_eq_iff _).2
  rw [op_comp, FunctorToTypes.map_comp_apply, SSet.S.map_toNπ']
  exact (imageObj P).hom.unop.property

private def imageToReduced {d : X.Elementsᵒᵖ} (h : (simplex d).toN.dim ≤ n)
    (P : Fiber (n := n) d) : imageObj P ⟶ reduced h :=
  StructuredArrow.homMk (ObjectProperty.homMk (Quiver.Hom.op
    (⟨(imageToCoreOp P).op, SSet.S.map_toNπ' (sameCore P)⟩ :
      (reduced h).right.obj.unop ⟶ (imageObj P).right.obj.unop))) (by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext X
    apply Quiver.Hom.unop_inj
    exact imageToCore_fac P)

private def reducedComparison {d : X.Elementsᵒᵖ} (h : (simplex d).toN.dim ≤ n) :
    imageFunctor (n := n) d ⟶ (Functor.const (Fiber (n := n) d)).obj (reduced h) where
  app := imageToReduced h
  naturality {P Q} f := by
    apply hom_ext
    apply (cancel_epi (factorThruImage (operator P))).mp
    change factorThruImage (operator P) ≫ (image.map (imageSquare f) ≫ imageToCoreOp Q) =
      factorThruImage (operator P) ≫ (imageToCoreOp P ≫ 𝟙 _)
    rw [Category.comp_id, ← Category.assoc]
    have hf : factorThruImage (operator P) ≫ image.map (imageSquare f) =
        factorThruImage (operator Q) :=
      (image.factor_map (imageSquare f)).trans (Category.id_comp _)
    rw [hf, imageToCore_fac, imageToCore_fac]


private theorem fiber_point {d : X.Elementsᵒᵖ} (h : (simplex d).toN.dim ≤ n) :
    GW (pointMap (nerve (Fiber (n := n) d))) := by
  let C := Fiber (n := n) d
  let F : C ⥤ Discrete PUnit.{1} := (Functor.const _).obj ⟨PUnit.unit⟩
  let G : Discrete PUnit.{1} ⥤ C := (Functor.const _).obj (reduced h)
  have hC : NatTransZigzag (F ⋙ G) (𝟭 C) :=
    .trans _ (imageFunctor d) _ (.symm _ _ (.rel _ _ ⟨reducedComparison h⟩))
      (.rel _ _ ⟨imageComparison d⟩)
  let e : G ⋙ F ⟶ 𝟭 (Discrete PUnit.{1}) :=
    { app P := eqToHom (Subsingleton.elim _ P)
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  haveI : WeakEquivalence (nerveMap F) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW F G hC (.rel _ _ ⟨e⟩))
  have he : nerveMap F ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit.{1}).hom =
      pointMap (nerve C) := pointIsTerminal.hom_ext _ _
  rw [← he]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- If the nondegenerate simplices fit inside the dimension bound, the
inclusion of the finite-degree full subcategory is a Kan weak equivalence. -/
theorem inclusion_weak (h : ∀ s : X.N, s.dim ≤ n) :
    WeakEquivalence (nerveMap (inclusion X n)) :=
  (weakEquivalence_iff_GW _).mpr
    (DaggerNativeDualTheoremA.nerveMap_GW (inclusion X n)
      (fun d ↦ fiber_point (h (simplex d).toN)))


/-- A finite simplicial set admits such a finite-object category with the
weak homotopy type of its whole simplex category. -/
theorem exists_finite_inclusion_weak [X.IsFinite] :
    ∃ n : ℕ, WeakEquivalence (nerveMap (inclusion X n)) := by
  obtain ⟨n, hn⟩ := X.hasDimensionLT_of_isFinite
  letI := hn
  exact ⟨n, inclusion_weak (fun s ↦ (X.dim_lt_of_nonDegenerate ⟨s.simplex, s.nonDegenerate⟩ n).le)⟩


end
end DaggerModels.PartII.BoundedSimplex
