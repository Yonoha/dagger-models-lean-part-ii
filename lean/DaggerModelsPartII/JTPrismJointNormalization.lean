import DaggerModelsPartII.JTParametrizedBeadGraphPrismSimplices
import DaggerModelsPartII.JTJointRelativeGraphFamily
import DaggerModelsPartII.JTRowGraphReferenceSection

/-! The row-graph diagram on the entire time-dependent inverse image of a target joint. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTPrismJointNormalization

open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedBeadGraph (products nativeGraphDiagram targetElements targetElements_native)
open JTParametrizedProductSimplices (Index degree simplex)
open JTJointRelativeParameters (withTime)
open JTJointRelativeGraphFamily (native)
open JTTargetJointMarks (Joint)
open JTTargetIntervalOverMapping (overlap)
open JTTargetIntervalGluing (middleInclusion middlePoint middlePB)
open JTSimplicialTargetRowGraphResolution

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- The full inverse image of the joint, including every time simplex. -/
abbrev overlapProducts : A ⥤ SSet.{0} :=
  withTime Q.map J time (native F) (overlap Q.code j)

set_option maxHeartbeats 900000 in
/-- The natural inclusion of the full joint prism into the whole original prism. -/
def includeWhole : overlapProducts F j ⟶ products L time where
  app i := middleInclusion (F.collapse.app i) j ▷ J.obj (time.obj i)
  naturality i i' f := by
    let a := ((codes L).map f)
    have ha : a ≫ F.collapse.app i' = F.collapse.app i :=
      (F.collapse.naturality f).trans (Category.comp_id _)
    let h := JTTargetIntervalPullback.sourceMap (F.collapse.app i) j j le_rfl a ha
    let v := J.map (time.map f)
    change ((JTDecoratedIntervalDiagram.parameterize Q.map J time
      (native F ⋙ overlap Q.code j)).map f).left ≫
      (middleInclusion (F.collapse.app i') j ▷ J.obj (time.obj i')) =
      (middleInclusion (F.collapse.app i) j ▷ J.obj (time.obj i)) ≫ (a.map ⊗ₘ v)
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    change (h ⊗ₘ v) ≫ (middleInclusion (F.collapse.app i') j ⊗ₘ 𝟙 _) =
      (middleInclusion (F.collapse.app i) j ⊗ₘ 𝟙 _) ≫ (a.map ⊗ₘ v)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun u ↦ u ⊗ₘ v)
      (JTTargetIntervalPullback.sourceMap_fac (F.collapse.app i) j j le_rfl a ha)

/-- Regard every overlap simplex as an actual original prism simplex. -/
abbrev includeIndex : Index (overlapProducts F j) ⥤ Index (products L time) :=
  Grothendieck.map (Functor.whiskerRight (includeWhole F j)
    SimplicialResolutionFunctor.elementsOpposite)

set_option maxHeartbeats 1000000 in
private theorem includeIndex_simplex (P : Index (overlapProducts F j)) :
    simplex (products L time) ((includeIndex F j).obj P) =
      simplex (overlapProducts F j) P ≫ (includeWhole F j).app P.base := by
  apply SSet.yonedaEquiv.injective
  change SSet.yonedaEquiv
    (SSet.yonedaEquiv.symm (((includeWhole F j).app P.base).app P.fiber.unop.1 P.fiber.unop.2)) =
    SSet.yonedaEquiv (SSet.yonedaEquiv.symm P.fiber.unop.2 ≫ (includeWhole F j).app P.base)
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The exact row graphs on the joint, with the original mixed operators. -/
abbrev jointGraphs : (Index (overlapProducts F j))ᵒᵖ ⥤ Resolution Q.map :=
  (includeIndex F j).op ⋙ nativeGraphDiagram F

private abbrev jointPoint : (Δ[0] : SSet.{0}) ⟶ Q.code.toSSet :=
  NecklaceCode.pointAt Q.code (ULift.up j.val)

/-- The common raw vertex from either side is the literal target joint. -/
abbrev jointRaw : (Δ[0] : SSet.{0}) ⟶ Raw W := jointPoint (Q := Q) j ≫ Q.map

private abbrev jointBase :=
  jointGraphs F j ⋙ Grothendieck.forget (diagram Q.map)

private abbrev jointFrom (P : Index (overlapProducts F j)) :=
  SSet.stdSimplex.isTerminalObj₀.from (std.obj ((degree (overlapProducts F j)).obj P))

set_option maxHeartbeats 1300000 in
/-- Every simplex of the whole joint prism maps to the literal native joint,
before applying the target's map to the raw realization. -/
theorem joint_native (P : Index (overlapProducts F j)) :
    SSet.yonedaEquiv.symm ((jointBase F j).obj (op P)).2 =
      jointFrom F j P ≫ jointPoint (Q := Q) j := by
  let T := (codes L).obj P.base
  let n := time.obj P.base
  let f : T ⟶ Q.code := F.collapse.app P.base
  let K := J.obj n
  let m := middleInclusion f j
  change SSet.yonedaEquiv.symm ((targetElements F).obj
    (op ((includeIndex F j).obj P))).2 = _
  rw [targetElements_native, includeIndex_simplex]
  change (simplex (overlapProducts F j) P ≫ (m ⊗ₘ 𝟙 K)) ≫
    fst T.toSSet K ≫ f.map = _
  have hm : m ≫ f.map = middlePoint f j ≫ jointPoint (Q := Q) j := (middlePB f j).w
  rw [Category.assoc, ← Category.assoc (m ⊗ₘ 𝟙 K), tensorHom_fst, Category.assoc, hm]
  rw [← Category.assoc (fst _ _), ← Category.assoc (simplex (overlapProducts F j) P)]
  exact congrArg (fun u ↦ u ≫ jointPoint (Q := Q) j)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext
      ((simplex (overlapProducts F j) P ≫ fst _ _) ≫ middlePoint f j) (jointFrom F j P))

/-- On every simplex of the full joint prism the actual raw graph is the
horizontal restriction of the fixed joint vertex. -/
theorem joint_value (P : Index (overlapProducts F j)) :
    value Q.map ((jointBase F j).obj (op P)) = jointFrom F j P ≫ jointRaw (Q := Q) j := by
  change SSet.yonedaEquiv.symm ((jointBase F j).obj (op P)).2 ≫ Q.map = _
  rw [joint_native F j P, Category.assoc]

set_option maxHeartbeats 900000 in
private theorem compatible : ReferenceCompatible Q.map (jointBase F j) :=
  referenceCompatible_of_point Q.map (base := jointBase F j)
    (jointRaw (Q := Q) j) (fun P ↦ joint_value F j P.unop)

/-- Use one canonical joint graph in every horizontal degree and for every time operator. -/
abbrev jointReference : (Index (overlapProducts F j))ᵒᵖ ⥤ Resolution Q.map :=
  reference Q.map (compatible F j)

set_option maxHeartbeats 1000000 in
/-- The normalized graph of a joint simplex is literally the restriction of the
one canonical graph on the target joint point. -/
theorem jointReference_obj (P : (Index (overlapProducts F j))ᵒᵖ) :
    ((jointReference F j).obj P).fiber.unop.obj =
      JTRowGraphResolution.restrictGraph
        (SimplexCategory.isTerminalZero.from ((jointBase F j).obj P).1.unop)
        (JTRowGraphCategory.canonical (jointRaw (Q := Q) j)) :=
  reference_of_point_obj Q.map (base := jointBase F j) (jointRaw (Q := Q) j)
    (fun R ↦ joint_value F j R.unop) P

private theorem supported (P : (Index (overlapProducts F j))ᵒᵖ) :
    Function.Surjective
      (JTRowGraphParameterSupport.label ((jointGraphs F j).obj P).fiber.unop.obj.parameter) :=
  JTRowGraphParameterSupport.source_vertex_surjective _

/-- All actual mixed graph operators commute with the comparison from the same
canonical reference. The comparison stays over the original native simplex. -/
def jointComparison : jointReference F j ⟶ jointGraphs F j :=
  referenceComparison Q.map (jointGraphs F j) (compatible F j) (supported F j)

set_option maxHeartbeats 900000 in
/-- The comparison leaves the actual native joint simplex unchanged. -/
theorem jointComparison_base (P : (Index (overlapProducts F j))ᵒᵖ) :
    ((jointComparison F j).app P).base = 𝟙 ((jointGraphs F j).obj P).base :=
  rfl

end

end DaggerModels.PartII.JTPrismJointNormalization
