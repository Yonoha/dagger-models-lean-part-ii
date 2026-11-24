import DaggerModelsPartII.JTJointSubdivisionVertexSupport
import DaggerModelsPartII.JTActualJointChoiceCover

/-!
Full paired ending and starting choices at every actual chart vertex, supported
on its whole original bead prism. All supports, rows and source operators come
from the original family. Restriction to the existing vertex-supported choice
cover retains the same full coefficient and every higher simplex degree.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointSubdivisionVertexChoices

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)
open JTJointRelativeEdgeChoiceDiagram
open JTJointEndpointRelativeLift
open JTJointEndpointLiftSpaceRestriction
open GrothendieckTotalElements (totalDiagram)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

section Restriction

variable {I : Type} [SmallCategory I] (W : Source)
  (s t k : I ⥤ SimplexCategory) (u : s ⟶ k) (v : t ⟶ k) (β : t ⟶ s)
  (hv : β ≫ u = v)
  (f : k ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌)) (z : Vertex W)
  (hs : ∀ i, std.map (u.app i) ≫ f.app i =
    term (std.obj (s.obj i)) ≫ vertexPoint W z)
  (ht : ∀ i, std.map (v.app i) ≫ f.app i =
    term (std.obj (t.obj i)) ≫ vertexPoint W z)

private def leftRestriction (i : I) :
    liftSpace W (u.app i) (f.app i) z (hs i) ⟶
      liftSpace W (v.app i) (f.app i) z (ht i) :=
  precompSquare (square W (u.app i) (f.app i) z (hs i))
    (square W (v.app i) (f.app i) z (ht i))
    (std.map (β.app i)) (𝟙 _)
    (by
      have hi : β.app i ≫ u.app i = v.app i := NatTrans.congr_app hv i
      rw [← std.map_comp, hi, Category.comp_id])
    (identityOnFace_natural W z (β.app i)) (Category.id_comp _)

private def rightRestriction (i : I) :
    reverseLiftSpace W (u.app i) (f.app i) z (hs i) ⟶
      reverseLiftSpace W (v.app i) (f.app i) z (ht i) :=
  precompSquare (reverseSquare W (u.app i) (f.app i) z (hs i))
    (reverseSquare W (v.app i) (f.app i) z (ht i))
    (std.map (β.app i)) (𝟙 _)
    (by
      have hi : β.app i ≫ u.app i = v.app i := NatTrans.congr_app hv i
      rw [← std.map_comp, hi, Category.comp_id])
    (identityOnFace_natural W z (β.app i)) (Category.id_comp _)

private theorem leftRestriction_ι (i : I) :
    leftRestriction W s t k u v β hv f z hs ht i ≫
      (SSet.ihomToPullbackFiber (square W (v.app i) (f.app i) z (ht i))).ι =
    (SSet.ihomToPullbackFiber (square W (u.app i) (f.app i) z (hs i))).ι := by
  rw [leftRestriction, precompSquare_ι, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id]

private theorem rightRestriction_ι (i : I) :
    rightRestriction W s t k u v β hv f z hs ht i ≫
      (SSet.ihomToPullbackFiber (reverseSquare W (v.app i) (f.app i) z (ht i))).ι =
    (SSet.ihomToPullbackFiber (reverseSquare W (u.app i) (f.app i) z (hs i))).ι := by
  rw [rightRestriction, precompSquare_ι, MonoidalClosed.pre_id, NatTrans.id_app,
    Category.comp_id]

private theorem left_map_ι {i j : Iᵒᵖ} (α : i ⟶ j) :
    (leftChoices W s k u f z hs).map α ≫
      (SSet.ihomToPullbackFiber
        (square W (u.app j.unop) (f.app j.unop) z (hs j.unop))).ι =
    (SSet.ihomToPullbackFiber
      (square W (u.app i.unop) (f.app i.unop) z (hs i.unop))).ι ≫
      (MonoidalClosed.pre (std.map (k.map α.unop))).app (row W ⦋1⦌) := rfl

private theorem right_map_ι {i j : Iᵒᵖ} (α : i ⟶ j) :
    (rightChoices W s k u f z hs).map α ≫
      (SSet.ihomToPullbackFiber
        (reverseSquare W (u.app j.unop) (f.app j.unop) z (hs j.unop))).ι =
    (SSet.ihomToPullbackFiber
      (reverseSquare W (u.app i.unop) (f.app i.unop) z (hs i.unop))).ι ≫
      (MonoidalClosed.pre (std.map (k.map α.unop))).app (row W ⦋1⦌) := rfl

private def restrictLeft : leftChoices W s k u f z hs ⟶ leftChoices W t k v f z ht where
  app i := leftRestriction W s t k u v β hv f z hs ht i.unop
  naturality i j α := by
    apply (cancel_mono (SSet.ihomToPullbackFiber
      (square W (v.app j.unop) (f.app j.unop) z (ht j.unop))).ι).mp
    rw [Category.assoc, leftRestriction_ι, left_map_ι,
      Category.assoc, left_map_ι, ← Category.assoc, leftRestriction_ι]

private def restrictRight : rightChoices W s k u f z hs ⟶ rightChoices W t k v f z ht where
  app i := rightRestriction W s t k u v β hv f z hs ht i.unop
  naturality i j α := by
    apply (cancel_mono (SSet.ihomToPullbackFiber
      (reverseSquare W (v.app j.unop) (f.app j.unop) z (ht j.unop))).ι).mp
    rw [Category.assoc, rightRestriction_ι, right_map_ι,
      Category.assoc, right_map_ι, ← Category.assoc, rightRestriction_ι]

end Restriction

private def tensorNat {C : Type} [SmallCategory C]
    {P P' R R' : C ⥤ SSet.{0}} (α : P ⟶ P') (β : R ⟶ R') :
    Functor.diag C ⋙ P.prod R ⋙ MonoidalCategory.tensor SSet.{0} ⟶
      Functor.diag C ⋙ P'.prod R' ⋙ MonoidalCategory.tensor SSet.{0} where
  app p := α.app p ⊗ₘ β.app p
  naturality p q f := by
    change (P.map f ⊗ₘ R.map f) ≫ (α.app q ⊗ₘ β.app q) =
      (α.app p ⊗ₘ β.app p) ≫ (P'.map f ⊗ₘ R'.map f)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    exact congrArg₂ (fun a b ↦ a ⊗ₘ b) (α.naturality f) (β.naturality f)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private theorem support_row_transport (a : A) (n : ℕ)
    (i i' : (NecklaceCode.single n).toSSet ⟶ ((codes L).obj a).toSSet) (e : i = i')
    (f : std.obj ((JTJointRelativeGraphFamily.coefficient (L := L)).obj a) ⟶ row W ⦋0⦌)
    (h : std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F a n i) ≫ f =
      term (std.obj (JTParametrizedBeadGraph.fullBeadSupport F a n i)) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j)) :
    std.map (JTParametrizedBeadGraph.fullBeadSupportInclusion F a n i') ≫ f =
      term (std.obj (JTParametrizedBeadGraph.fullBeadSupport F a n i')) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  subst i'
  exact h

private def support_map_transport (a : A) (n : ℕ)
    (i i' : (NecklaceCode.single n).toSSet ⟶ ((codes L).obj a).toSSet) (e : i = i')
    (S : SimplexCategory)
    (v : S ⟶ (JTJointRelativeGraphFamily.coefficient (L := L)).obj a)
    (m : S ⟶ JTParametrizedBeadGraph.fullBeadSupport F a n i)
    (hm : m ≫ JTParametrizedBeadGraph.fullBeadSupportInclusion F a n i = v) :
    {m' : S ⟶ JTParametrizedBeadGraph.fullBeadSupport F a n i' //
      m' ≫ JTParametrizedBeadGraph.fullBeadSupportInclusion F a n i' = v} := by
  subst i'
  exact ⟨m, hm⟩

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev chartBase := JTJointSubdivisionBeadCharts.base F j
private abbrev D := JTJointSubdivisionBeadNormalization.degrees F j
private abbrev r := JTJointSubdivisionBeadNormalization.toJointInterval F j
private abbrev hr := @JTJointSubdivisionBeadNormalization.native_natural _ _ _ _ _ _ _ _ F j

/-- Every actual ordinal vertex of every adjacent-subdivision chart. -/
abbrev Index := JTJointSubdivisionVertexSupport.VertexIndex F j

/-- The named chart and every original arrow are retained. -/
abbrev toCharts : Index F j ⥤ JTJointSubdivisionBeadCharts.Index F j :=
  JTJointSubdivisionVertexSupport.toCharts F j

/-- The concrete original source cut determined by the named chart vertex. -/
abbrev toMarked := JTJointSubdivisionVertexSupport.toMarked F j

/-- The actual single-bead native diagram at all named chart vertices. -/
abbrev natives := toCharts F j ⋙ JTJointSubdivisionBeadCharts.singleNative F j

/-- The original source objects and arrows underlying these actual chart vertices. -/
abbrev base := toCharts F j ⋙ chartBase F j

/-- The genuine whole-bead native inclusion, natural in every original chart operator. -/
def nativeInclusions : natives F j ⋙ NecklaceCode.simplicialFunctor ⟶
    base F j ⋙ codes L ⋙ NecklaceCode.simplicialFunctor :=
  Functor.whiskerLeft (toCharts F j) (JTJointSubdivisionBeadCharts.singleInclusions F j)

/-- The original coefficient degree, unchanged by any edge or support choice. -/
abbrev oldDegrees := toMarked F j ⋙ JTExactlyMarkedSourceDiagram.degrees F j

/-- The full timed bead support, reindexed to all its actual vertices. -/
abbrev supports := toCharts F j ⋙
  JTJointBeadOverlapDiagram.degrees F j (chartBase F j) (D F j) (r F j) (hr F j)

/-- The whole bead support includes in the unchanged old coefficient ordinal. -/
def incl : supports F j ⟶ oldDegrees F j :=
  Functor.whiskerLeft (toCharts F j)
    (JTJointBeadEndpointDiagram.incl F j (chartBase F j) (D F j) (r F j) (hr F j))

/-- Every actual full bead support inclusion is monic. -/
theorem incl_mono (p : Index F j) : Mono ((incl F j).app p) :=
  JTJointBeadEndpointDiagram.incl_mono F j (chartBase F j) (D F j) (r F j) (hr F j) p.1

/-- The old vertex row is reindexed from the existing exactly marked source diagram. -/
def rows : oldDegrees F j ⋙ std ⟶ (Functor.const (Index F j)).obj (row W ⦋0⦌) :=
  Functor.whiskerLeft (toMarked F j) (JTExactlyMarkedSourceDiagram.endpointRows F j)

/-- That same actual row is stationary on the WHOLE original bead support. -/
theorem row_onSupport (p : Index F j) :
    std.map ((incl F j).app p) ≫ (rows F j).app p =
      term (std.obj ((supports F j).obj p)) ≫ vertexPoint W (z j) :=
  support_row_transport F j ((chartBase F j).obj p.1) ((D F j).obj p.1).len
    (JTJointSubdivisionBeadNormalization.inclusion F j p.1)
    (r F j p.1 ≫ JTTargetIntervalGluing.middleInclusion
      (F.collapse.app ((chartBase F j).obj p.1)) j)
    (JTJointSubdivisionBeadNormalization.toJointInterval_fac F j p.1).symm
    ((rows F j).app p) (JTJointSubdivisionVertexSupport.row_on_beadSupport F j p.1 p.2)

/-- The existing point support, with its exact original source operators. -/
abbrev vertexSupports := toMarked F j ⋙ JTExactlyMarkedSourceDiagram.supports F j

/-- The existing point support inclusion in that same original coefficient degree. -/
abbrev vertexIncl := Functor.whiskerLeft (toMarked F j) (JTExactlyMarkedSourceDiagram.incl F j)

private def vertexToWholeData (p : Index F j) :
    {m : (vertexSupports F j).obj p ⟶ (supports F j).obj p //
      m ≫ (incl F j).app p = (vertexIncl F j).app p} :=
  support_map_transport F ((chartBase F j).obj p.1) ((D F j).obj p.1).len
    (JTJointSubdivisionBeadNormalization.inclusion F j p.1)
    (r F j p.1 ≫ JTTargetIntervalGluing.middleInclusion
      (F.collapse.app ((chartBase F j).obj p.1)) j)
    (JTJointSubdivisionBeadNormalization.toJointInterval_fac F j p.1).symm
    ((vertexSupports F j).obj p) ((vertexIncl F j).app p)
    (JTJointSubdivisionVertexSupport.vertexToBead F j p.1 p.2)
    (JTJointSubdivisionVertexSupport.vertexToBead_inclusion F j p.1 p.2)

/-- The actual vertex support includes naturally in the full support of its own bead. -/
def vertexToWhole : vertexSupports F j ⟶ supports F j where
  app p := (vertexToWholeData F j p).val
  naturality p q f := by
    haveI := incl_mono F j q
    apply (cancel_mono ((incl F j).app q)).mp
    rw [Category.assoc, (vertexToWholeData F j q).property,
      Category.assoc, (incl F j).naturality f, ← Category.assoc,
      (vertexToWholeData F j p).property]
    exact (vertexIncl F j).naturality f

/-- Both support maps retain the literal same old coefficient inclusion. -/
theorem vertexToWhole_fac : vertexToWhole F j ≫ incl F j = vertexIncl F j := by
  apply NatTrans.ext
  funext p
  exact (vertexToWholeData F j p).property

/-- Full ending edges, stationary on the entire bead support at the named actual vertex. -/
abbrev endingSpaces := leftChoices W (supports F j) (oldDegrees F j) (incl F j)
  (rows F j) (z j) (row_onSupport F j)

/-- Full starting edges on the same bead support and the same old coefficient. -/
abbrev startingSpaces := rightChoices W (supports F j) (oldDegrees F j) (incl F j)
  (rows F j) (z j) (row_onSupport F j)

/-- Paired ending and starting choices share every higher simplex degree. -/
abbrev spaces := pairChoices W (supports F j) (oldDegrees F j) (incl F j)
  (rows F j) (z j) (row_onSupport F j)

/-- The existing full vertex-supported actual joint-choice spaces. -/
abbrev actualSpaces := (toMarked F j).op ⋙ JTActualJointChoiceCover.spaces F j

/-- Every full bead-supported ending edge restricts to the existing point support. -/
def restrictEnding : endingSpaces F j ⟶
    (toMarked F j).op ⋙ JTActualJointChoiceCover.endingSpaces F j :=
  restrictLeft W (supports F j) (vertexSupports F j) (oldDegrees F j)
    (incl F j) (vertexIncl F j) (vertexToWhole F j) (vertexToWhole_fac F j)
    (rows F j) (z j) (row_onSupport F j)
    (fun p ↦ JTExactlyMarkedSourceDiagram.supported_endpoint F j ((toMarked F j).obj p))

/-- Every full bead-supported starting edge has the same literal restriction. -/
def restrictStarting : startingSpaces F j ⟶
    (toMarked F j).op ⋙ JTActualJointChoiceCover.startingSpaces F j :=
  restrictRight W (supports F j) (vertexSupports F j) (oldDegrees F j)
    (incl F j) (vertexIncl F j) (vertexToWhole F j) (vertexToWhole_fac F j)
    (rows F j) (z j) (row_onSupport F j)
    (fun p ↦ JTExactlyMarkedSourceDiagram.supported_endpoint F j ((toMarked F j).obj p))

/-- Restrict the paired whole-bead choices without changing any edge's full old degree. -/
def restriction : spaces F j ⟶ actualSpaces F j :=
  tensorNat (restrictEnding F j) (restrictStarting F j)

/-- All higher whole-bead-supported paired choices form a weakly contractible space. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W)
    (p : (Index F j)ᵒᵖ) : GW (pointMap ((spaces F j).obj p)) :=
  pairChoices_point_GW W (supports F j) (oldDegrees F j) (incl F j) (rows F j)
    (z j) (row_onSupport F j) hW (incl_mono F j) p

/-- Retain every paired simplex and every original chart-and-vertex arrow. -/
abbrev Cover := (totalDiagram (spaces F j)).Elementsᵒᵖ

/-- Forget only the full higher choices and their common simplicial degree. -/
abbrev projection : Cover F j ⥤ Index F j :=
  (CategoryOfElements.π (totalDiagram (spaces F j)) ⋙
    CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- The whole-bead-supported choice cover is weak over the actual vertex source. -/
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
      CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ))
  exact pairChoices_projection_weak W (supports F j) (oldDegrees F j) (incl F j)
    (rows F j) (z j) (row_onSupport F j) hW (incl_mono F j)

private def reindex {B C : Type} [SmallCategory B] [SmallCategory C]
    (G : B ⥤ C) (X : C ⥤ SSet.{0}) :
    (totalDiagram (G ⋙ X)).Elements ⥤ (totalDiagram X).Elements where
  obj p := ⟨(G.obj p.1.1, p.1.2), p.2⟩
  map f := ⟨(G.map f.val.1, f.val.2), f.property⟩
  map_id p := by apply CategoryOfElements.ext; exact Prod.ext (G.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (G.map_comp f.val.1 g.val.1) rfl

/-- The actual restriction functor retains all paired simplices and every common time operator. -/
def toActual : Cover F j ⥤ JTActualJointChoiceCover.Cover F j :=
  (((Functor.uncurry.map (restriction F j)).mapElements) ⋙
    reindex (toMarked F j).op (JTActualJointChoiceCover.spaces F j)).op

/-- Restriction preserves the exact original cut and source arrow. -/
theorem toActual_projection :
    toActual F j ⋙ JTActualJointChoiceCover.projection F j =
      projection F j ⋙ toMarked F j := rfl

/-- Restriction retains the complete common higher-choice time coordinate. -/
theorem toActual_time :
    toActual F j ⋙ SynchronizedSimplicialParameters.time (JTActualJointChoiceCover.spaces F j) =
      SynchronizedSimplicialParameters.time (spaces F j) := rfl

end
end DaggerModels.PartII.JTJointSubdivisionVertexChoices
