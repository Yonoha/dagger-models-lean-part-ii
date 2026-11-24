import DaggerModelsPartII.JTZeroObjects
import DaggerModelsPartII.JTActualCosimplicialFrame
import DaggerModelsPartII.JTCoendMateFormula

/-!
# The strict ordered-endpoint restriction of the original right mate

The actual objects x,y determine the constant endpoint maps through the
canonical zero-frame Hom equivalence. The original Xi and Gamma Hom objects
with those ordered endpoint equations form simplicial sets. Their comparison
is literal precomposition by the original full-index lambda and agrees with
the actual adjunction right mate on represented generators. No derived
fixed-endpoint weak equivalence is asserted by this strict construction.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels

namespace DaggerModels.PartII.JTOrderedFrameMate

open JTRelativeReedyFrame JTActualCosimplicialFrame JTZeroObjects

noncomputable section

/-- The actual reversal one-simplex index. -/
def oneIndex : ReverseSimplex := ReverseSimplex.inclusion.obj ⦋1⦌

/-- The two ordered vertices of the actual reversal one-simplex. -/
def vertex (i : Fin 2) : zeroIndex ⟶ oneIndex :=
  ReverseSimplex.inclusion.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i)

/-- Endpoint zero selects x, and endpoint one selects y. -/
def endpointObject {C : DaggerSimplicialCat.{0, 0}} (x y : C.Obj) (i : Fin 2) : C.Obj :=
  if i = 0 then x else y

@[simp] theorem endpointObject_zero {C : DaggerSimplicialCat.{0, 0}} (x y : C.Obj) :
    endpointObject x y 0 = x := by simp [endpointObject]

@[simp] theorem endpointObject_one {C : DaggerSimplicialCat.{0, 0}} (x y : C.Obj) :
    endpointObject x y 1 = y := by simp [endpointObject]

/-- A map from the actual outer-one frame with its two specified constant
endpoint maps, in their given order. -/
def OrderedHom (F : SimplexCategory ⥤ OuterDiagram) (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) (k : SimplexCategory) :=
  {f : (F.obj k).obj oneIndex ⟶ C // ∀ i : Fin 2,
    (F.obj k).map (vertex i) ≫ f =
      (a.app k).app zeroIndex ≫ objectMap C (endpointObject x y i)}

private theorem augmentation_vertical
    {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    {j k : SimplexCategory} (θ : j ⟶ k) :
    (F.map θ).app zeroIndex ≫ (a.app k).app zeroIndex =
      (a.app j).app zeroIndex := by
  have h := congrArg (fun t ↦ t.app zeroIndex) (a.naturality θ)
  have hc : (constantA.map θ).app zeroIndex = 𝟙 _ := by simp [constantA]
  simpa only [NatTrans.comp_app, hc, Category.comp_id] using h

private def precompose {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    {C : DaggerSimplicialCat.{0, 0}} {x y : C.Obj}
    {j k : SimplexCategory} (θ : j ⟶ k) (f : OrderedHom F a C x y k) :
    OrderedHom F a C x y j :=
  ⟨(F.map θ).app oneIndex ≫ f.val, by
    intro i
    calc
      (F.obj j).map (vertex i) ≫ ((F.map θ).app oneIndex ≫ f.val) =
          (F.map θ).app zeroIndex ≫ ((F.obj k).map (vertex i) ≫ f.val) := by
            rw [← Category.assoc, (F.map θ).naturality (vertex i), Category.assoc]
      _ = (F.map θ).app zeroIndex ≫
          ((a.app k).app zeroIndex ≫ objectMap C (endpointObject x y i)) := by
            rw [f.property i]
      _ = (a.app j).app zeroIndex ≫ objectMap C (endpointObject x y i) := by
            rw [← Category.assoc, augmentation_vertical a θ]⟩

/-- The actual ordered-endpoint Hom simplicial set of an augmented frame. -/
def orderedHomSSet (F : SimplexCategory ⥤ OuterDiagram) (a : F ⟶ constantA)
    (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : SSet.{0} where
  obj k := OrderedHom F a C x y k.unop
  map θ := precompose a θ.unop
  map_id k := by
    funext f
    apply Subtype.ext
    change (F.map (𝟙 k.unop)).app oneIndex ≫ f.val = f.val
    simp only [F.map_id, NatTrans.id_app, Category.id_comp]
  map_comp θ ψ := by
    funext f
    apply Subtype.ext
    change (F.map (ψ.unop ≫ θ.unop)).app oneIndex ≫ f.val =
      (F.map ψ.unop).app oneIndex ≫ ((F.map θ.unop).app oneIndex ≫ f.val)
    simp only [F.map_comp, NatTrans.comp_app, Category.assoc]

private def postcompose {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    {C D : DaggerSimplicialCat.{0, 0}} (g : C ⟶ D) {x y : C.Obj}
    {k : SimplexCategory} (f : OrderedHom F a C x y k) :
    OrderedHom F a D (g.obj x) (g.obj y) k :=
  ⟨f.val ≫ g, by
    intro i
    have ho : g.obj (endpointObject x y i) = endpointObject (g.obj x) (g.obj y) i := by
      simp only [endpointObject]
      split <;> rfl
    calc
      (F.obj k).map (vertex i) ≫ (f.val ≫ g) =
          ((a.app k).app zeroIndex ≫ objectMap C (endpointObject x y i)) ≫ g := by
            rw [← Category.assoc, f.property i]
      _ = (a.app k).app zeroIndex ≫ objectMap D (g.obj (endpointObject x y i)) := by
            rw [Category.assoc, objectMap_naturality]
      _ = (a.app k).app zeroIndex ≫ objectMap D (endpointObject (g.obj x) (g.obj y) i) := by
            rw [ho]⟩

/-- Postcomposition carries the actual ordered pair to its two actual images. -/
def orderedPostcompose {F : SimplexCategory ⥤ OuterDiagram} (a : F ⟶ constantA)
    {C D : DaggerSimplicialCat.{0, 0}} (g : C ⟶ D) (x y : C.Obj) :
    orderedHomSSet F a C x y ⟶ orderedHomSSet F a D (g.obj x) (g.obj y) where
  app _ f := postcompose a g f
  naturality {k l} θ := by
    funext f
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- Ordered Hom from the original Xi frame. -/
def XiOrdered (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : SSet.{0} :=
  orderedHomSSet XiCurried XiAugmentationCurried C x y

/-- Ordered Hom from the original Gamma frame. -/
def GammaOrdered (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) : SSet.{0} :=
  orderedHomSSet Gamma augmentation C x y

/-- The original lambda restricts to the same actual ordered endpoints. -/
def orderedMate (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj) :
    XiOrdered C x y ⟶ GammaOrdered C x y where
  app k f := ⟨(comparison.app k.unop).app oneIndex ≫ f.val, by
    intro i
    calc
      _ = (comparison.app k.unop).app zeroIndex ≫
          ((XiCurried.obj k.unop).map (vertex i) ≫ f.val) := by
            rw [← Category.assoc, (comparison.app k.unop).naturality (vertex i),
              Category.assoc]
      _ = (comparison.app k.unop).app zeroIndex ≫
          ((XiAugmentationCurried.app k.unop).app zeroIndex ≫
            objectMap C (endpointObject x y i)) := by rw [f.property i]
      _ = (augmentation.app k.unop).app zeroIndex ≫
          objectMap C (endpointObject x y i) := by
            change _ = ((comparison.app k.unop).app zeroIndex ≫
              (XiAugmentationCurried.app k.unop).app zeroIndex) ≫ _
            rw [Category.assoc]⟩
  naturality {k l} θ := by
    funext f
    apply Subtype.ext
    change (comparison.app l.unop).app oneIndex ≫
        ((XiCurried.map θ.unop).app oneIndex ≫ f.val) =
      (Gamma.map θ.unop).app oneIndex ≫
        ((comparison.app k.unop).app oneIndex ≫ f.val)
    have h := congrArg (fun t ↦ t.app oneIndex) (comparison.naturality θ.unop)
    simpa only [NatTrans.comp_app, Category.assoc] using
      (congrArg (fun t ↦ t ≫ f.val) h).symm

/-- The restricted right mate is natural in a target functor, transporting
both actual endpoints in their original order. -/
theorem orderedMate_postcompose {C D : DaggerSimplicialCat.{0, 0}}
    (g : C ⟶ D) (x y : C.Obj) :
    orderedPostcompose XiAugmentationCurried g x y ≫
        orderedMate D (g.obj x) (g.obj y) =
      orderedMate C x y ≫ orderedPostcompose augmentation g x y := by
  apply NatTrans.ext
  funext k f
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- The exact represented right-mate formula restricts to the constructed
ordered map, with the same input and output generators. -/
theorem rightMate_ordered_bidegree (C : DaggerSimplicialCat.{0, 0})
    (x y : C.Obj) (k : SimplexCategory) (f : (XiOrdered C x y).obj (op k)) :
    ((JTCoendMate.rightMate.app C).app (op oneIndex)).app (op k)
        (JTCoendMateFormula.compositeGeneratorEquiv C (oneIndex, k) f.val) =
      JTCoendMateFormula.frameGeneratorEquiv C (oneIndex, k)
        (((orderedMate C x y).app (op k) f).val) :=
  JTCoendMateFormula.rightMate_bidegree C oneIndex k f.val

/-- Before the canonical A-identification, the ordered mate is literally
identity on its underlying degree-zero Hom map. -/
theorem orderedMate_zero_val (C : DaggerSimplicialCat.{0, 0}) (x y : C.Obj)
    (f : (XiOrdered C x y).obj (op ⦋0⦌)) :
    (((orderedMate C x y).app (op ⦋0⦌)) f).val = f.val := by
  change (comparison.app ⦋0⦌).app oneIndex ≫ f.val = f.val
  rw [comparison_zero]
  exact Category.id_comp f.val

end

end DaggerModels.PartII.JTOrderedFrameMate
