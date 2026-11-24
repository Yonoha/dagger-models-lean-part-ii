import SimplexIndexLastVertexHomotopy
import DaggerModelsPartII.SimplicialResolutionFunctor
import NativeNerveOppositeIso
import NativeSimplicialOppositeKanWeak

/-!
# Vertex comparison for the actual category of elements

The opposite-Elements comparison uses the canonical Yoneda equivalence.
The first-vertex comparison is obtained by reversing whole simplices.
-/

set_option autoImplicit false
set_option warningAsError true
open CategoryTheory Simplicial Opposite HomotopicalAlgebra
open DaggerNativeSimplexIndexResolution
open DaggerNativeSimplexIndexResolutionNaturality (indexMap)
open DaggerModels.PartII.SimplexIndexLastVertexWeak (lastVertexMap)
open DaggerModels.PartII.SimplexIndexLastVertexHomotopy (lastVertexMap_weak)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.SimplexElementsFirstVertexWeak
noncomputable section

private def elementsEquiv (X : SSet.{0}) : X.Elementsᵒᵖ ≌ Index X :=
  CategoryOfElements.costructuredArrowULiftYonedaEquivalence X

/-- The canonical forward Yoneda comparison, retaining the original simplex map. -/
def elementsToLifted (X : SSet.{0}) : X.Elementsᵒᵖ ⥤ LiftedIndex X :=
  (elementsEquiv X).functor ⋙ ULiftHom.up.{0, 0, 0}

instance elementsToLifted_isEquivalence (X : SSet.{0}) :
    (elementsToLifted X).IsEquivalence := by
  letI : (elementsEquiv X).functor.IsEquivalence :=
    (elementsEquiv X).isEquivalence_functor
  letI : (ULiftHom.up.{0, 0, 0} (C := Index X)).IsEquivalence :=
    (ULiftHom.equiv (C := Index X)).isEquivalence_functor
  dsimp [elementsToLifted]
  infer_instance

/-- Evaluate a whole chain in the opposite category of elements at its last ordinal. -/
def lastVertexElements (X : SSet.{0}) : nerve X.Elementsᵒᵖ ⟶ X :=
  nerveMap (elementsToLifted X) ≫ lastVertexMap X

theorem lastVertexElements_weak (X : SSet.{0}) :
    WeakEquivalence (lastVertexElements X) := by
  have : WeakEquivalence (nerveMap (elementsToLifted X)) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have : WeakEquivalence (lastVertexMap X) := lastVertexMap_weak X
  change WeakEquivalence (nerveMap (elementsToLifted X) ≫ lastVertexMap X)
  infer_instance

/-- The Yoneda comparison commutes with postcomposition of entire simplices. -/
theorem elementsToLifted_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    (CategoryOfElements.map f).op ⋙ elementsToLifted Y =
      elementsToLifted X ⋙ indexMap f := by
  refine CategoryTheory.Functor.ext (fun s ↦ ?_) (fun s t g ↦ ?_)
  · change (CostructuredArrow.mk (uliftYonedaEquiv.symm
        (f.app _ s.unop.2)) : Index Y) =
      CostructuredArrow.mk (uliftYonedaEquiv.symm s.unop.2 ≫ f)
    apply congrArg (fun t : uliftYoneda.obj s.unop.1.unop ⟶ Y ↦
      (CostructuredArrow.mk t : Index Y))
    apply uliftYonedaEquiv.injective
    simp only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  · letI : (ULiftHom.down.{0, 0, 0} (C := Index Y)).IsEquivalence :=
      (ULiftHom.equiv (C := Index Y)).isEquivalence_inverse
    apply (ULiftHom.down.{0, 0, 0} (C := Index Y)).map_injective
    apply CostructuredArrow.ext
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map,
      CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    change g.unop.val.unop = eqToHom rfl ≫ g.unop.val.unop ≫ eqToHom rfl
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Last-ordinal evaluation commutes with every map of original simplicial sets. -/
theorem lastVertexMap_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    nerveMap (indexMap f) ≫ lastVertexMap Y = lastVertexMap X ≫ f := by
  apply NatTrans.ext
  funext q F
  rfl

/-- The opposite-Elements vertex evaluation is a natural transformation. -/
theorem lastVertexElements_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    nerveMap (CategoryOfElements.map f).op ≫ lastVertexElements Y =
      lastVertexElements X ≫ f := by
  change nerveMap (CategoryOfElements.map f).op ≫
      (nerveMap (elementsToLifted Y) ≫ lastVertexMap Y) =
    (nerveMap (elementsToLifted X) ≫ lastVertexMap X) ≫ f
  calc
    nerveMap (CategoryOfElements.map f).op ≫
        (nerveMap (elementsToLifted Y) ≫ lastVertexMap Y) =
      nerveMap ((CategoryOfElements.map f).op ⋙ elementsToLifted Y) ≫
        lastVertexMap Y := rfl
    _ = nerveMap (elementsToLifted X ⋙ indexMap f) ≫ lastVertexMap Y := by
      rw [elementsToLifted_natural f]
    _ = nerveMap (elementsToLifted X) ≫
        (nerveMap (indexMap f) ≫ lastVertexMap Y) := rfl
    _ = nerveMap (elementsToLifted X) ≫ (lastVertexMap X ≫ f) := by
      rw [lastVertexMap_natural f]
    _ = (nerveMap (elementsToLifted X) ≫ lastVertexMap X) ≫ f := by
      simp only [Category.assoc]

/-- Reversing the simplex operator gives the canonical map on actual elements. -/
def reverseElements (X : SSet.{0}) : X.Elements ⥤ X.op.Elements where
  obj s := ⟨s.1, SSet.opObjEquiv.symm s.2⟩
  map {s t} g := by
    refine ⟨(SimplexCategory.rev.map g.val.unop).op, ?_⟩
    change X.map ((SimplexCategory.rev.map
      (SimplexCategory.rev.map g.val.unop)).op) s.2 = t.2
    simpa only [SimplexCategory.rev_map_rev_map] using g.property
  map_id s := by
    apply CategoryOfElements.ext
    change (SimplexCategory.rev.map (𝟙 s.1).unop).op = 𝟙 s.1
    rw [unop_id, CategoryTheory.Functor.map_id, op_id]
    rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    change (SimplexCategory.rev.map (f.val ≫ g.val).unop).op =
      (SimplexCategory.rev.map f.val.unop).op ≫
        (SimplexCategory.rev.map g.val.unop).op
    rw [unop_comp, CategoryTheory.Functor.map_comp, op_comp]

/-- The reverse operation is an equivalence on the actual elements categories. -/
def reverseElementsEquiv (X : SSet.{0}) : X.Elements ≌ X.op.Elements where
  functor := reverseElements X
  inverse :=
    { obj := fun s ↦ ⟨s.1, SSet.opObjEquiv s.2⟩
      map := fun {s t} g ↦ by
        refine ⟨(SimplexCategory.rev.map g.val.unop).op, ?_⟩
        have h := g.property
        change X.map (SimplexCategory.rev.map g.val.unop).op s.2 = t.2 at h
        exact h
      map_id := by
        intro s
        apply CategoryOfElements.ext
        change (SimplexCategory.rev.map (𝟙 s.1).unop).op = 𝟙 s.1
        rw [unop_id, CategoryTheory.Functor.map_id, op_id]
        rfl
      map_comp := by
        intro s t u f g
        apply CategoryOfElements.ext
        change (SimplexCategory.rev.map (f.val ≫ g.val).unop).op =
          (SimplexCategory.rev.map f.val.unop).op ≫
            (SimplexCategory.rev.map g.val.unop).op
        rw [unop_comp, CategoryTheory.Functor.map_comp, op_comp] }
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro s t g
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    apply CategoryOfElements.ext
    change g.val = (SimplexCategory.rev.map
      (SimplexCategory.rev.map g.val.unop)).op
    rw [SimplexCategory.rev_map_rev_map, Quiver.Hom.op_unop])
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro s t g
    dsimp
    simp only [Category.comp_id, Category.id_comp]
    apply CategoryOfElements.ext
    change (SimplexCategory.rev.map
      (SimplexCategory.rev.map g.val.unop)).op = g.val
    rw [SimplexCategory.rev_map_rev_map, Quiver.Hom.op_unop])

/-- Reversal commutes strictly with maps of original simplicial sets. -/
theorem reverseElements_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    CategoryOfElements.map f ⋙ reverseElements Y =
      reverseElements X ⋙ CategoryOfElements.map (SSet.opFunctor.map f) := by
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro s t g
  rfl

/-- Reversing the whole nerve gives the first-vertex evaluation. -/
def firstVertexElements (X : SSet.{0}) : nerve X.Elements ⟶ X :=
  (SSet.opFunctorCompOpFunctorIso.inv.app (nerve X.Elements)) ≫
    SSet.opFunctor.map
      ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
        nerveMap (reverseElements X).op ≫ lastVertexElements X.op) ≫
    (SSet.opFunctorCompOpFunctorIso.hom.app X)

theorem firstVertexElements_weak (X : SSet.{0}) :
    WeakEquivalence (firstVertexElements X) := by
  have hReverse : WeakEquivalence (nerveMap (reverseElements X).op) := by
    letI : (reverseElements X).IsEquivalence :=
      (reverseElementsEquiv X).isEquivalence_functor
    letI : (reverseElements X).op.IsEquivalence := inferInstance
    exact DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have hLast : WeakEquivalence (lastVertexElements X.op) :=
    lastVertexElements_weak X.op
  have hOp : WeakEquivalence (SSet.opFunctor.map
      ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
        nerveMap (reverseElements X).op ≫ lastVertexElements X.op)) := by
    have : WeakEquivalence
        ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
          nerveMap (reverseElements X).op ≫ lastVertexElements X.op) := by
      letI : WeakEquivalence (nerveMap (reverseElements X).op) := hReverse
      letI : WeakEquivalence (lastVertexElements X.op) := hLast
      infer_instance
    exact DaggerNativeSimplicialOppositeKanWeak.op_weak _
  letI : WeakEquivalence (SSet.opFunctor.map
      ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
        nerveMap (reverseElements X).op ≫ lastVertexElements X.op)) := hOp
  dsimp only [firstVertexElements]
  infer_instance

private abbrev reversedLastMap (X : SSet.{0}) :
    (nerve X.Elements).op ⟶ X.op :=
  (DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
    nerveMap (reverseElements X).op ≫ lastVertexElements X.op

private theorem reverseNerve_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    nerveMap (CategoryOfElements.map f).op ≫ nerveMap (reverseElements Y).op =
      nerveMap (reverseElements X).op ≫
        nerveMap (CategoryOfElements.map (SSet.opFunctor.map f)).op := by
  calc
    nerveMap (CategoryOfElements.map f).op ≫ nerveMap (reverseElements Y).op =
        nerveMap ((CategoryOfElements.map f ⋙ reverseElements Y).op) := rfl
    _ = nerveMap ((reverseElements X ⋙
          CategoryOfElements.map (SSet.opFunctor.map f)).op) := by
      rw [reverseElements_natural f]
    _ = nerveMap (reverseElements X).op ≫
          nerveMap (CategoryOfElements.map (SSet.opFunctor.map f)).op := rfl

private theorem reversedLastMap_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    SSet.opFunctor.map (nerveMap (CategoryOfElements.map f)) ≫ reversedLastMap Y =
      reversedLastMap X ≫ SSet.opFunctor.map f := by
  have he : SSet.opFunctor.map (nerveMap (CategoryOfElements.map f)) ≫
      (DaggerNativeNerveOppositeIso.nerveOppositeIso Y.Elements).hom =
    (DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
      nerveMap (CategoryOfElements.map f).op :=
    (DaggerNativeNerveOppositeIso.nerveOppositeNatIso.hom).naturality
      (CategoryOfElements.map f).toCatHom
  have hr := reverseNerve_natural f
  have hl := lastVertexElements_natural (SSet.opFunctor.map f)
  dsimp only [reversedLastMap]
  calc
    SSet.opFunctor.map (nerveMap (CategoryOfElements.map f)) ≫
        ((DaggerNativeNerveOppositeIso.nerveOppositeIso Y.Elements).hom ≫
          nerveMap (reverseElements Y).op ≫ lastVertexElements Y.op) =
      ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
          nerveMap (CategoryOfElements.map f).op) ≫
            nerveMap (reverseElements Y).op ≫ lastVertexElements Y.op := by
        simpa only [Category.assoc] using
          congrArg (fun m ↦ m ≫ nerveMap (reverseElements Y).op ≫
            lastVertexElements Y.op) he
    _ = (DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
          (nerveMap (reverseElements X).op ≫
            nerveMap (CategoryOfElements.map (SSet.opFunctor.map f)).op) ≫
              lastVertexElements Y.op := by
        simpa only [Category.assoc] using congrArg
          (fun m ↦ (DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
            m ≫ lastVertexElements Y.op) hr
    _ = (DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
          nerveMap (reverseElements X).op ≫
            (lastVertexElements X.op ≫ SSet.opFunctor.map f) := by
        rw [Category.assoc, hl]
    _ = ((DaggerNativeNerveOppositeIso.nerveOppositeIso X.Elements).hom ≫
          nerveMap (reverseElements X).op ≫ lastVertexElements X.op) ≫
            SSet.opFunctor.map f := by simp only [Category.assoc]

/-- Naturality is literal on the actual category of elements, not chosen up to homotopy. -/
theorem firstVertexElements_natural {X Y : SSet.{0}} (f : X ⟶ Y) :
    nerveMap (CategoryOfElements.map f) ≫ firstVertexElements Y =
      firstVertexElements X ≫ f := by
  let ε := SSet.opFunctorCompOpFunctorIso.{0}
  let hX := reversedLastMap X
  let hY := reversedLastMap Y
  have hε₀ : nerveMap (CategoryOfElements.map f) ≫
      ε.inv.app (nerve Y.Elements) =
    ε.inv.app (nerve X.Elements) ≫
      SSet.opFunctor.map (SSet.opFunctor.map (nerveMap (CategoryOfElements.map f))) :=
    ε.inv.naturality (nerveMap (CategoryOfElements.map f))
  have hε₁ : SSet.opFunctor.map (SSet.opFunctor.map f) ≫ ε.hom.app Y =
      ε.hom.app X ≫ f := ε.hom.naturality f
  have hh := reversedLastMap_natural f
  change nerveMap (CategoryOfElements.map f) ≫
      (ε.inv.app (nerve Y.Elements) ≫ SSet.opFunctor.map hY ≫ ε.hom.app Y) =
    (ε.inv.app (nerve X.Elements) ≫ SSet.opFunctor.map hX ≫ ε.hom.app X) ≫ f
  calc
    nerveMap (CategoryOfElements.map f) ≫
        (ε.inv.app (nerve Y.Elements) ≫ SSet.opFunctor.map hY ≫ ε.hom.app Y) =
      (ε.inv.app (nerve X.Elements) ≫
        SSet.opFunctor.map (SSet.opFunctor.map (nerveMap
          (CategoryOfElements.map f)))) ≫
            SSet.opFunctor.map hY ≫ ε.hom.app Y := by
        simpa only [Category.assoc] using
          congrArg (fun m ↦ m ≫ SSet.opFunctor.map hY ≫ ε.hom.app Y) hε₀
    _ = ε.inv.app (nerve X.Elements) ≫
          SSet.opFunctor.map
            (SSet.opFunctor.map (nerveMap (CategoryOfElements.map f)) ≫ hY) ≫
              ε.hom.app Y := by
        simpa only [Category.assoc] using congrArg
          (fun m ↦ ε.inv.app (nerve X.Elements) ≫ m ≫ ε.hom.app Y)
          (SSet.opFunctor.map_comp
            (SSet.opFunctor.map (nerveMap (CategoryOfElements.map f))) hY).symm
    _ = ε.inv.app (nerve X.Elements) ≫
          SSet.opFunctor.map (hX ≫ SSet.opFunctor.map f) ≫ ε.hom.app Y := by
        rw [hh]
    _ = ε.inv.app (nerve X.Elements) ≫ SSet.opFunctor.map hX ≫
          (SSet.opFunctor.map (SSet.opFunctor.map f) ≫ ε.hom.app Y) := by
        rw [SSet.opFunctor.map_comp]
        simp only [Category.assoc]
    _ = (ε.inv.app (nerve X.Elements) ≫ SSet.opFunctor.map hX ≫
          ε.hom.app X) ≫ f := by rw [hε₁]; simp only [Category.assoc]

/-- The required natural weak map from the actual Elements nerve to the input. -/
def firstVertexNatural : Functor.elementsFunctor ⋙ nerveFunctor ⟶ 𝟭 (SSet.{0}) where
  app X := firstVertexElements X
  naturality {_ _} f := firstVertexElements_natural f

#print axioms elementsToLifted_isEquivalence
#print axioms lastVertexElements_weak
#print axioms lastVertexElements_natural
#print axioms reverseElementsEquiv
#print axioms firstVertexElements_weak
#print axioms firstVertexNatural

end
end DaggerModels.PartII.SimplexElementsFirstVertexWeak
