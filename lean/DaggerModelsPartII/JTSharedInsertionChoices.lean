import DaggerModelsPartII.JTIncidentAllVertexChoices
import DaggerModelsPartII.JTJointSubdivisionInsertion
import DaggerModelsPartII.JTJointPairChainDiagram

/-!
One actual full all-vertex tuple supplies the three cuts of an insertion.
The original source, coefficient and common choice clock agree literally.
Coalescing cuts evaluate the same tuple coordinate. One full coefficient-time
chain is shared by all three lookups. This constructs actual comparison input;
the normalized comparison in the original Q remains a separate step.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerSSetGluing DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionChoices

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row)
open JTTargetJointMarks (Joint)
open GrothendieckTotalElements (totalDiagram)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev B := JTJointSubdivisionInsertion.Index F j

/-- The unchanged original source of an actual insertion. -/
abbrev originalBase := JTJointSubdivisionInsertion.base F j

/-- The earlier actual cut of the adjacent chart. -/
abbrev earlierMark := JTJointSubdivisionInsertion.toCharts F j ⋙
  JTJointSubdivisionBeadCharts.toPairs F j ⋙ JTJointPairSourceDiagram.leftCut F j

/-- The proposed inserted cut, including insertion at either endpoint. -/
abbrev middleMark := JTJointSubdivisionInsertion.insertedCut F j

/-- The later actual cut of that same chart. -/
abbrev laterMark := JTJointSubdivisionInsertion.toCharts F j ⋙
  JTJointSubdivisionBeadCharts.toPairs F j ⋙ JTJointPairSourceDiagram.rightCut F j

theorem earlierMark_base :
    earlierMark F j ⋙ JTExactlyMarkedSourceDiagram.base F j = originalBase F j := rfl

theorem middleMark_base :
    middleMark F j ⋙ JTExactlyMarkedSourceDiagram.base F j = originalBase F j := rfl

theorem laterMark_base :
    laterMark F j ⋙ JTExactlyMarkedSourceDiagram.base F j = originalBase F j := rfl

/-- Pull back the ORIGINAL-A tuple, retaining all its actual vertex choices. -/
abbrev spaces : (B F j)ᵒᵖ ⥤ SSet.{0} :=
  (originalBase F j).op ⋙ JTIncidentAllVertexChoices.spaces F j

private def lookup {C : Type} [SmallCategory C]
    (H : C ⥤ JTExactlyMarkedSourceDiagram.Index F j) :
    (H ⋙ JTExactlyMarkedSourceDiagram.base F j).op ⋙
        JTIncidentAllVertexChoices.spaces F j ⟶
      H.op ⋙ JTActualJointChoiceCover.spaces F j :=
  Functor.whiskerLeft H.op
    (JTIncidentAllVertexChoices.evaluation F j ≫ JTIncidentBeadChoiceDiagram.restriction F j)

/-- Lookup and restrict the one tuple at its earlier vertex. -/
def earlierLookup : spaces F j ⟶ (earlierMark F j).op ⋙ JTActualJointChoiceCover.spaces F j :=
  lookup F j (earlierMark F j)

/-- Lookup the same tuple at its inserted vertex. -/
def middleLookup : spaces F j ⟶ (middleMark F j).op ⋙ JTActualJointChoiceCover.spaces F j :=
  lookup F j (middleMark F j)

/-- Lookup the same tuple at its later vertex. -/
def laterLookup : spaces F j ⟶ (laterMark F j).op ⋙ JTActualJointChoiceCover.spaces F j :=
  lookup F j (laterMark F j)

/-- All three lookups have one common full higher simplex clock. -/
abbrev Cover := (totalDiagram (spaces F j)).Elementsᵒᵖ

/-- Forget the common tuple and degree, retaining the entire insertion data. -/
abbrev projection : Cover F j ⥤ B F j :=
  (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
    CategoryTheory.Prod.fst (B F j)ᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The actual tuple fibers remain weakly contractible on every insertion. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (B F j)ᵒᵖ) : GW (pointMap ((spaces F j).obj p)) :=
  JTIncidentAllVertexChoices.spaces_point_GW F j hW ((originalBase F j).op.obj p)

/-- All common higher tuple choices form a weak cover of the actual insertion source. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) := by
  let E := (totalDiagram (spaces F j)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff (projection F j)).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
      CategoryTheory.Prod.fst (B F j)ᵒᵖ SimplexCategoryᵒᵖ))
  exact SynchronizedSimplicialParameters.projection_weak (spaces F j)
    (spaces_point_GW F j hW)

private def reindex {C D : Type} [SmallCategory C] [SmallCategory D]
    (G : C ⥤ D) (X : D ⥤ SSet.{0}) :
    (totalDiagram (G ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(G.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(G.map f.val.1, f.val.2), f.property⟩
  map_id p := by apply CategoryOfElements.ext; exact Prod.ext (G.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_comp f.val.1 g.val.1) rfl

/-- Full higher choices at the earlier cut, obtained from the one common tuple. -/
def earlier : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (earlierLookup F j)).mapElements) ⋙
    reindex (earlierMark F j).op (JTActualJointChoiceCover.spaces F j)).op

/-- Full higher choices at the inserted cut from exactly that same tuple. -/
def middle : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (middleLookup F j)).mapElements) ⋙
    reindex (middleMark F j).op (JTActualJointChoiceCover.spaces F j)).op

/-- Full higher choices at the later cut from exactly that same tuple. -/
def later : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (laterLookup F j)).mapElements) ⋙
    reindex (laterMark F j).op (JTActualJointChoiceCover.spaces F j)).op

theorem earlier_projection :
    earlier F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ earlierMark F j := rfl

theorem middle_projection :
    middle F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ middleMark F j := rfl

theorem later_projection :
    later F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ laterMark F j := rfl

/-- The same unchanged old coefficient is used at all three cut lookups. -/
abbrev coefficient : Cover F j ⥤ SimplexCategory :=
  projection F j ⋙ originalBase F j ⋙ JTJointRelativeGraphFamily.coefficient (L := L)

/-- The one common simplex clock of all three full higher choices. -/
abbrev clock : Cover F j ⥤ SimplexCategory := SynchronizedSimplicialParameters.time (spaces F j)

theorem earlier_coefficient :
    earlier F j ⋙ JTActualJointChoicePrism.coefficient F j = coefficient F j := rfl

theorem middle_coefficient :
    middle F j ⋙ JTActualJointChoicePrism.coefficient F j = coefficient F j := rfl

theorem later_coefficient :
    later F j ⋙ JTActualJointChoicePrism.coefficient F j = coefficient F j := rfl

theorem earlier_clock :
    earlier F j ⋙ JTActualJointChoicePrism.choiceTime F j = clock F j := rfl

theorem middle_clock :
    middle F j ⋙ JTActualJointChoicePrism.choiceTime F j = clock F j := rfl

theorem later_clock :
    later F j ⋙ JTActualJointChoicePrism.choiceTime F j = clock F j := rfl

private def atVertex (p : Cover F j)
    (v : (JTExactlyMarkedSourceDiagram.vertices F j).obj
      ((originalBase F j).obj ((projection F j).obj p))) :
    JTActualJointChoiceCover.Cover F j :=
  op ⟨(op ⟨(originalBase F j).obj ((projection F j).obj p), v⟩, p.unop.1.2),
    ((JTIncidentBeadChoiceDiagram.restriction F j).app
      (op ⟨(originalBase F j).obj ((projection F j).obj p), v⟩)).app p.unop.1.2
        (p.unop.2 v)⟩

/-- Coalescing the inserted and earlier cuts gives the SAME full higher choice object. -/
theorem middle_eq_earlier (p : Cover F j)
    (h : ((projection F j).obj p).2.val = ((projection F j).obj p).1.2.firstCut) :
    (middle F j).obj p = (earlier F j).obj p := by
  change atVertex F j p ((middleMark F j).obj ((projection F j).obj p)).2 =
    atVertex F j p ((earlierMark F j).obj ((projection F j).obj p)).2
  apply congrArg (atVertex F j p)
  exact Subtype.ext h

/-- Coalescing the inserted and later cuts also gives the SAME full higher choice object. -/
theorem middle_eq_later (p : Cover F j)
    (h : ((projection F j).obj p).2.val = ((projection F j).obj p).1.2.lastCut) :
    (middle F j).obj p = (later F j).obj p := by
  change atVertex F j p ((middleMark F j).obj ((projection F j).obj p)).2 =
    atVertex F j p ((laterMark F j).obj ((projection F j).obj p)).2
  apply congrArg (atVertex F j p)
  exact Subtype.ext h

/-- One full chain in the common original coefficient and choice-time prism. -/
abbrev Index := TimePrismChainDiagram.Index (coefficient F j) (clock F j)

/-- Forget only the common full chain while keeping the complete tuple. -/
abbrev base : Index F j ⥤ Cover F j := TimePrismChainDiagram.base _ _

/-- The one literal ordinal enumerating that common full chain. -/
abbrev ordinals : Index F j ⥤ SimplexCategory := TimePrismChainDiagram.ordinals _ _

/-- The common full chain projects onto its unchanged original coefficient. -/
abbrev toOriginal : ordinals F j ⟶ base F j ⋙ coefficient F j :=
  TimePrismChainDiagram.coeffProjection _ _

/-- The common full chain also has its one original higher-choice time projection. -/
abbrev toTime : ordinals F j ⟶ base F j ⋙ clock F j :=
  TimePrismChainDiagram.timeProjection _ _

theorem toOriginal_surjective (p : Index F j) :
    Function.Surjective ((toOriginal F j).app p).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective _ _ p

theorem base_weak : WeakEquivalence (nerveMap (base F j)) :=
  TimePrismChainProjection.projection_weak _ _

/-- Reuse the common chain at the earlier cut without replacing any ordinal vertex. -/
def earlierChain : Index F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  JTJointPairChainDiagram.reindex (earlier F j)
    (JTActualJointChoicePrism.coefficient F j) (JTActualJointChoicePrism.choiceTime F j)

/-- Reuse precisely the same chain at the inserted cut. -/
def middleChain : Index F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  JTJointPairChainDiagram.reindex (middle F j)
    (JTActualJointChoicePrism.coefficient F j) (JTActualJointChoicePrism.choiceTime F j)

/-- Reuse precisely the same chain at the later cut. -/
def laterChain : Index F j ⥤ JTActualJointChoiceChainGraph.Index F j :=
  JTJointPairChainDiagram.reindex (later F j)
    (JTActualJointChoicePrism.coefficient F j) (JTActualJointChoicePrism.choiceTime F j)

theorem earlierChain_base :
    earlierChain F j ⋙ JTActualJointChoiceChainGraph.base F j = base F j ⋙ earlier F j := rfl

theorem middleChain_base :
    middleChain F j ⋙ JTActualJointChoiceChainGraph.base F j = base F j ⋙ middle F j := rfl

theorem laterChain_base :
    laterChain F j ⋙ JTActualJointChoiceChainGraph.base F j = base F j ⋙ later F j := rfl

theorem earlierChain_ordinals :
    earlierChain F j ⋙ JTActualJointChoiceChainGraph.ordinals F j = ordinals F j := rfl

theorem middleChain_ordinals :
    middleChain F j ⋙ JTActualJointChoiceChainGraph.ordinals F j = ordinals F j := rfl

theorem laterChain_ordinals :
    laterChain F j ⋙ JTActualJointChoiceChainGraph.ordinals F j = ordinals F j := rfl

theorem earlierChain_toOriginal (p : Index F j) :
    (JTActualJointChoiceChainGraph.toOriginal F j).app ((earlierChain F j).obj p) =
      (toOriginal F j).app p := rfl

theorem middleChain_toOriginal (p : Index F j) :
    (JTActualJointChoiceChainGraph.toOriginal F j).app ((middleChain F j).obj p) =
      (toOriginal F j).app p := rfl

theorem laterChain_toOriginal (p : Index F j) :
    (JTActualJointChoiceChainGraph.toOriginal F j).app ((laterChain F j).obj p) =
      (toOriginal F j).app p := rfl

theorem earlierChain_toTime (p : Index F j) :
    (JTActualJointChoiceChainGraph.toTime F j).app ((earlierChain F j).obj p) =
      (toTime F j).app p := rfl

theorem middleChain_toTime (p : Index F j) :
    (JTActualJointChoiceChainGraph.toTime F j).app ((middleChain F j).obj p) =
      (toTime F j).app p := rfl

theorem laterChain_toTime (p : Index F j) :
    (JTActualJointChoiceChainGraph.toTime F j).app ((laterChain F j).obj p) =
      (toTime F j).app p := rfl

end
end DaggerModels.PartII.JTSharedInsertionChoices
