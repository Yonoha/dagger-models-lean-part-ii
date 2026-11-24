import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.SynchronizedSimplicialParameters
import NativeFinitePiWeak

/-!
Simultaneous full choices at every actual original source vertex above a fixed
joint. The tuple diagram retains every original arrow and every coalescence.
The input Y is supplied: its actual incident-choice instantiation remains a
separate step. Pointwise weak contractibility gives a weak full choice cover
over the original source, without a selected cut or a weak marked projection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerChosenRigidificationNecklace
open DaggerOriginalProductGadget (pointMap pointIsTerminal)
open DaggerNativeFinitePiWeak (piObject piMap piMap_weak)
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTAllVertexChoiceProduct

open GrothendieckTotalElements (totalDiagram)

noncomputable section

section DependentProduct

variable {C : Type} [SmallCategory C] (V : C ⥤ Type) (Y : V.Elementsᵒᵖ ⥤ SSet.{0})

private def fiber (a : C) : SSet.{0} where
  obj n := ∀ v : V.obj a, (Y.obj (op ⟨a, v⟩)).obj n
  map θ q v := (Y.obj (op ⟨a, v⟩)).map θ (q v)
  map_id n := by funext q v; exact congrFun ((Y.obj (op ⟨a, v⟩)).map_id n) (q v)
  map_comp θ σ := by
    funext q v
    exact congrFun ((Y.obj (op ⟨a, v⟩)).map_comp θ σ) (q v)

private abbrev vertexArrow {a b : C} (f : a ⟶ b) (v : V.obj a) :=
  CategoryOfElements.homMk (F := V) ⟨a, v⟩ ⟨b, V.map f v⟩ f rfl

private def pull {a b : C} (f : a ⟶ b) : fiber V Y b ⟶ fiber V Y a where
  app n q v := (Y.map (vertexArrow V f v).op).app n (q (V.map f v))
  naturality n m θ := by
    funext q v
    exact congrFun ((Y.map (vertexArrow V f v).op).naturality θ) (q (V.map f v))

private theorem pull_explicit {a b : C} (f : a ⟶ b) (v : V.obj a) (w : V.obj b)
    (h : V.map f v = w) (n : SimplexCategoryᵒᵖ) (q : (fiber V Y b).obj n) :
    (Y.map (CategoryOfElements.homMk (F := V) ⟨a, v⟩ ⟨b, w⟩ f h).op).app n (q w) =
      (pull V Y f).app n q v := by
  subst w
  rfl

private theorem pull_id (a : C) : pull V Y (𝟙 a) = 𝟙 (fiber V Y a) := by
  apply NatTrans.ext
  funext n q v
  have h := pull_explicit V Y (𝟙 a) v v (FunctorToTypes.map_id_apply V v) n q
  have he : CategoryOfElements.homMk (F := V) ⟨a, v⟩ ⟨a, v⟩ (𝟙 a)
      (FunctorToTypes.map_id_apply V v) = 𝟙 (V.elementsMk a v) := Subtype.ext rfl
  rw [he, op_id, Y.map_id] at h
  exact h.symm

private theorem pull_comp {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    pull V Y (f ≫ g) = pull V Y g ≫ pull V Y f := by
  apply NatTrans.ext
  funext n q v
  have h := pull_explicit V Y (f ≫ g) v (V.map g (V.map f v))
    (FunctorToTypes.map_comp_apply V f g v) n q
  have he : vertexArrow V f v ≫ vertexArrow V g (V.map f v) =
      CategoryOfElements.homMk (F := V) ⟨a, v⟩ ⟨c, V.map g (V.map f v)⟩ (f ≫ g)
        (FunctorToTypes.map_comp_apply V f g v) := Subtype.ext rfl
  rw [← he, op_comp, Y.map_comp] at h
  exact h.symm

private def dependentProduct : Cᵒᵖ ⥤ SSet.{0} where
  obj a := fiber V Y a.unop
  map f := pull V Y f.unop
  map_id a := pull_id V Y a.unop
  map_comp f g := pull_comp V Y g.unop f.unop

private def dependentEvaluation : (CategoryOfElements.π V).op ⋙ dependentProduct V Y ⟶ Y where
  app p := { app n q := q p.unop.2, naturality := by intros; rfl }
  naturality p q f := by
    apply NatTrans.ext
    funext n t
    exact (pull_explicit V Y f.unop.val q.unop.2 p.unop.2 f.unop.property n t).symm

private def finiteIso (a : C) {n : ℕ} (e : Fin n ≃ V.obj a) :
    fiber V Y a ≅ piObject (fun i ↦ Y.obj (op ⟨a, e i⟩)) :=
  NatIso.ofComponents
    (fun d ↦ (Equiv.piCongrLeft (P := fun v ↦ (Y.obj (op ⟨a, v⟩)).obj d) e).symm.toIso)
    (by intros; rfl)

private def terminalPiIso (n : ℕ) (K : SSet.{0}) (hK : IsTerminal K) :
    piObject (fun _ : Fin n ↦ K) ≅ K where
  hom := hK.from _
  inv := { app d x i := x, naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext d x i
    let p : piObject (fun _ : Fin n ↦ K) ⟶ K :=
      { app d x := x i, naturality := by intros; rfl }
    exact congrFun (NatTrans.congr_app (hK.hom_ext (hK.from _) p) d) x
  inv_hom_id := hK.hom_ext _ _

private theorem dependentProduct_point_GW (a : C) {n : ℕ} (e : Fin n ≃ V.obj a)
    (hY : ∀ p, GW (pointMap (Y.obj p))) :
    GW (pointMap ((dependentProduct V Y).obj (op a))) := by
  let P := piMap (fun i : Fin n ↦ pointMap (Y.obj (op ⟨a, e i⟩)))
  haveI : WeakEquivalence P :=
    piMap_weak _ (fun i ↦ (weakEquivalence_iff_GW _).mpr (hY (op ⟨a, e i⟩)))
  let t := terminalPiIso n _ pointIsTerminal
  have h : (finiteIso V Y a e).hom ≫ P ≫ t.hom =
      pointMap ((dependentProduct V Y).obj (op a)) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end DependentProduct

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)
variable (Y : (JTExactlyMarkedSourceDiagram.Index F j)ᵒᵖ ⥤ SSet.{0})

/-- Simultaneous full choices at every actual source vertex above the fixed joint. -/
def tuple : Aᵒᵖ ⥤ SSet.{0} := dependentProduct (JTExactlyMarkedSourceDiagram.vertices F j) Y

/-- Every simplex is literally a tuple over all actual vertices, including empty fibers. -/
theorem tuple_obj (a : A) (n : SimplexCategoryᵒᵖ) :
    ((tuple F j Y).obj (op a)).obj n =
      (∀ v : (JTExactlyMarkedSourceDiagram.vertices F j).obj a,
        (Y.obj (op ⟨a, v⟩)).obj n) := rfl

/-- Restriction evaluates the target tuple at the exact transported vertex and then uses Y. -/
theorem tuple_map {a b : A} (f : a ⟶ b) (n : SimplexCategoryᵒᵖ)
    (q : ((tuple F j Y).obj (op b)).obj n)
    (v : (JTExactlyMarkedSourceDiagram.vertices F j).obj a) :
    (((tuple F j Y).map f.op).app n q) v =
      (Y.map (vertexArrow (JTExactlyMarkedSourceDiagram.vertices F j) f v).op).app n
        (q ((JTExactlyMarkedSourceDiagram.vertices F j).map f v)) := rfl

/-- Evaluation at the named vertex is natural in every original source and simplex operator. -/
def evaluation : (JTExactlyMarkedSourceDiagram.base F j).op ⋙ tuple F j Y ⟶ Y :=
  dependentEvaluation (JTExactlyMarkedSourceDiagram.vertices F j) Y

/-- Evaluation preserves the entire common simplex degree. -/
theorem evaluation_app (p : JTExactlyMarkedSourceDiagram.Index F j)
    (n : SimplexCategoryᵒᵖ) (q : ((tuple F j Y).obj (op p.1)).obj n) :
    ((evaluation F j Y).app (op p)).app n q = q p.2 := rfl

/-- The finite all-vertex tuple is weakly contractible when each supplied choice space is. -/
theorem tuple_point_GW (hY : ∀ p, GW (pointMap (Y.obj p))) (a : Aᵒᵖ) :
    GW (pointMap ((tuple F j Y).obj a)) := by
  classical
  letI : Fintype ((JTExactlyMarkedSourceDiagram.vertices F j).obj a.unop) := by
    change Fintype {v : Fin (((JTParametrizedTargetFamilies.codes L).obj a.unop).len + 1) //
      NecklaceCode.orderMap (F.collapse.app a.unop).map v = j.val}
    infer_instance
  exact dependentProduct_point_GW (JTExactlyMarkedSourceDiagram.vertices F j) Y a.unop
    (Fintype.equivFin _).symm hY

/-- All tuples and all common higher simplex operators over the original source. -/
abbrev Cover := (totalDiagram (tuple F j Y)).Elementsᵒᵖ

/-- Forget the tuple and its common simplex degree, retaining the original source arrow. -/
abbrev projection : Cover F j Y ⥤ A :=
  (CategoryOfElements.π (totalDiagram (tuple F j Y)) ⋙
    CategoryTheory.Prod.fst Aᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The full all-vertex choice cover is weak over the ORIGINAL source A. -/
theorem projection_weak (hY : ∀ p, GW (pointMap (Y.obj p))) :
    WeakEquivalence (nerveMap (projection F j Y)) := by
  let E := (totalDiagram (tuple F j Y)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff (projection F j Y)).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (totalDiagram (tuple F j Y)) ⋙
      CategoryTheory.Prod.fst Aᵒᵖ SimplexCategoryᵒᵖ))
  exact SynchronizedSimplicialParameters.projection_weak (tuple F j Y)
    (tuple_point_GW F j Y hY)

private def reindex {B C : Type} [SmallCategory B] [SmallCategory C]
    (G : B ⥤ C) (X : C ⥤ SSet.{0}) :
    (totalDiagram (G ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(G.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(G.map f.val.1, f.val.2), f.property⟩
  map_id p := by apply CategoryOfElements.ext; exact Prod.ext (G.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_comp f.val.1 g.val.1) rfl

/-- A full tuple together with a named actual vertex, at the same higher simplex degree. -/
abbrev MarkedCover :=
  (totalDiagram ((JTExactlyMarkedSourceDiagram.base F j).op ⋙ tuple F j Y)).Elementsᵒᵖ

/-- Forget the named vertex while keeping the complete tuple and its original source/time. -/
def toTuple : MarkedCover F j Y ⥤ Cover F j Y :=
  (reindex (JTExactlyMarkedSourceDiagram.base F j).op (tuple F j Y)).op

/-- Evaluate the full tuple at its named vertex, retaining every higher simplex. -/
def toChoice : MarkedCover F j Y ⥤ (totalDiagram Y).Elementsᵒᵖ :=
  ((Functor.uncurry.map (evaluation F j Y)).mapElements).op

private abbrev choiceProjection :=
  (CategoryOfElements.π (totalDiagram Y) ⋙
    CategoryTheory.Prod.fst (JTExactlyMarkedSourceDiagram.Index F j)ᵒᵖ
      SimplexCategoryᵒᵖ).leftOp

/-- Full evaluation and tuple restriction have the same original source and original arrow. -/
theorem toChoice_source :
    toChoice F j Y ⋙ choiceProjection F j Y ⋙ JTExactlyMarkedSourceDiagram.base F j =
      toTuple F j Y ⋙ projection F j Y := rfl

/-- Full evaluation retains the exact common higher simplex time operator. -/
theorem toChoice_time :
    toChoice F j Y ⋙ SynchronizedSimplicialParameters.time Y =
      toTuple F j Y ⋙ SynchronizedSimplicialParameters.time (tuple F j Y) := rfl

end
end DaggerModels.PartII.JTAllVertexChoiceProduct
