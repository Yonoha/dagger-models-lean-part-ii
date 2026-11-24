import DaggerModelsPartII.JTJointClippedGluing
import DaggerModelsPartII.JTJointClippedSideVertices
import DaggerModelsPartII.JTJointRelativeGraphFamily

/-! Natural groupoid coefficients descend uniquely along diagrams that are bijective at vertices. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedParameters

open JTJointRelativeParameters (parameterOfNaturalVertices parameterOfNaturalVertices_coord
  parameter_ext)
open JTCodiscreteParameterPairing (coord)

noncomputable section

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev J := GroupoidSimplex.parameter

variable {I : Type} [SmallCategory I] {M N : I ⥤ SSet.{0}}
variable (a : M ⟶ N) (k : I ⥤ SimplexCategory)
variable (h : ∀ p, Function.Bijective ((a.app p).app zero))
variable (s : M ⟶ k ⋙ J)

private def vertexEquiv (p : I) :
    (M.obj p).obj zero ≃ (N.obj p).obj zero :=
  Equiv.ofBijective _ (h p)

private def assignment (p : I) (v : (N.obj p).obj zero) : Fin ((k.obj p).len + 1) :=
  coord (k.obj p) zero ((s.app p).app zero ((vertexEquiv a h p).symm v)) 0

private theorem vertexEquiv_natural {p p' : I} (f : p ⟶ p') (v : (N.obj p).obj zero) :
    (vertexEquiv a h p').symm ((N.map f).app zero v) =
      (M.map f).app zero ((vertexEquiv a h p).symm v) := by
  apply (vertexEquiv a h p').injective
  rw [Equiv.apply_symm_apply]
  let x := (vertexEquiv a h p).symm v
  have hn := congrFun (NatTrans.congr_app (a.naturality f) zero) x
  change ((a.app p').app zero) ((M.map f).app zero x) =
    (N.map f).app zero ((vertexEquiv a h p) x) at hn
  rw [Equiv.apply_symm_apply] at hn
  exact hn.symm

private theorem assignment_natural {p p' : I} (f : p ⟶ p') (v : (N.obj p).obj zero) :
    assignment a k h s p' ((N.map f).app zero v) =
      (k.map f).toOrderHom (assignment a k h s p v) := by
  let x := (vertexEquiv a h p).symm v
  have hn := congrFun (NatTrans.congr_app (s.naturality f) zero) x
  change (s.app p').app zero ((M.map f).app zero x) =
    (J.map (k.map f)).app zero ((s.app p).app zero x) at hn
  unfold assignment
  rw [vertexEquiv_natural a h f v, hn, JTCodiscreteParameterPairing.coord_map]

/-- A natural transformation into the full groupoid parameters descends along a
map inducing bijections on vertices, preserving all coefficient operators. -/
def descendVertices : N ⟶ k ⋙ J :=
  parameterOfNaturalVertices N k (assignment a k h s) (assignment_natural a k h s)

@[reassoc]
theorem precomp_descendVertices : a ≫ descendVertices a k h s = s := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro v
  change coord (k.obj p) zero
      (((parameterOfNaturalVertices N k (assignment a k h s) (assignment_natural a k h s)).app
        p).app zero ((vertexEquiv a h p) v)) 0 =
    coord (k.obj p) zero ((s.app p).app zero v) 0
  rw [parameterOfNaturalVertices_coord]
  unfold assignment
  rw [Equiv.symm_apply_apply]

include h in
/-- Agreement along the original diagram determines the descended parameter. -/
theorem precomp_vertices_injective (s₁ s₂ : N ⟶ k ⋙ J)
    (hs : a ≫ s₁ = a ≫ s₂) : s₁ = s₂ := by
  apply NatTrans.ext
  funext p
  apply parameter_ext
  intro v
  obtain ⟨u, rfl⟩ := (h p).2 v
  exact congrArg (fun z ↦ coord (k.obj p) zero z 0)
    (congrFun (NatTrans.congr_app (NatTrans.congr_app hs p) zero) u)

end

open JTJointRelativeParameters (withTime withTimeMap withTimeMap_app withTimeMap_comp)
open JTJointIntervalQuotient (overlapToWhole overlapToJoint wholeQuotient wholeCollapse
  joint jointToWhole)
open JTTargetIntervalOverMapping (whole overlap)
open JTJointClippedGluing (compare nativeGlued gluedIsoNative wedgeIso
  compare_vertex_isIso_of_sides simplicialComparison)
open JTTargetJointMarks (Joint)

noncomputable section Native

private abbrev toNative (U : NecklaceCode) (j : Joint U) :=
  compare U j ≫ (gluedIsoNative U j).hom

private abbrev originalToNative (U : NecklaceCode) (j : Joint U) :=
  wholeCollapse U j ≫ toNative U j

private abbrev jointToNative (U : NecklaceCode) (j : Joint U) :=
  jointToWhole U j ≫ toNative U j

private abbrev native (U : NecklaceCode) (j : Joint U) :=
  nativeGlued U j ⋙ Over.post NecklaceCode.simplicialFunctor

variable (U : NecklaceCode) (j : Joint U)
variable {X : SSet.{0}} (q : U.toSSet ⟶ X)
variable {I : Type} [SmallCategory I] (K : SimplexCategory ⥤ SSet.{0})
variable (time : I ⥤ SimplexCategory) (D : I ⥤ Over U) (k : I ⥤ SimplexCategory)

private theorem compare_bijective (P : Over U) :
    Function.Bijective (((compare U j).app P).left.app zero) :=
  (isIso_iff_bijective _).mp (compare_vertex_isIso_of_sides U j P
    ((isIso_iff_bijective _).mpr
      (JTJointClippedSideVertices.fromLeftQuotient_vertices_bijective U j P))
    ((isIso_iff_bijective _).mpr
      (JTJointClippedRightVertices.fromQuotient_vertices_bijective U j P)))

private theorem toNative_bijective (P : Over U) :
    Function.Bijective (((toNative U j).app P).left.app zero) := by
  let E := (evaluation SimplexCategoryᵒᵖ (Type 0)).obj zero
  haveI : IsIso ((wedgeIso U j P).hom.app zero) :=
    inferInstanceAs (IsIso (E.map (wedgeIso U j P).hom))
  have hi := (isIso_iff_bijective ((wedgeIso U j P).hom.app zero)).mp inferInstance
  exact hi.comp (compare_bijective U j P)

private theorem timed_compare_bijective (p : I) : Function.Bijective
    (((withTimeMap q K time D (toNative U j)).app p).app zero) := by
  rw [withTimeMap_app]
  constructor
  · intro a b h
    change (((toNative U j).app (D.obj p)).left.app zero a.1, a.2) =
      (((toNative U j).app (D.obj p)).left.app zero b.1, b.2) at h
    have h₁ := congrArg (fun x ↦ x.1) h
    have h₂ := congrArg (fun x ↦ x.2) h
    exact Prod.ext ((toNative_bijective U j (D.obj p)).1 h₁) h₂
  · intro b
    obtain ⟨a, ha⟩ := (toNative_bijective U j (D.obj p)).2 b.1
    exact ⟨(a, b.2), Prod.ext ha rfl⟩

variable (s : withTime q K time D (whole U) ⟶ k ⋙ J)
variable (trace : withTime q K time D (joint U j) ⟶ k ⋙ J)

/-- The full joint restriction of the parameter depends only on time,
with the indicated value on the joint point. -/
def TraceFactors : Prop :=
  withTimeMap q K time D (overlapToWhole U j) ≫ s =
    withTimeMap q K time D (overlapToJoint U j) ≫ trace

variable (hTrace : TraceFactors U j q K time D k s trace)

private abbrev quotientParameter := JTJointIntervalQuotient.descend U j q K time D s trace hTrace

/-- A parameter with the specified time-only trace on the full joint interval
descends to the wedge of the two clipped native sides. -/
def descendToNative : withTime q K time D (native U j) ⟶ k ⋙ J :=
  descendVertices (withTimeMap q K time D (toNative U j)) k
    (timed_compare_bijective U j q K time D)
    (quotientParameter U j q K time D k s trace hTrace)

@[reassoc]
theorem original_descendToNative :
    withTimeMap q K time D (originalToNative U j) ≫
      descendToNative U j q K time D k s trace hTrace = s := by
  unfold descendToNative originalToNative
  rw [withTimeMap_comp, Category.assoc, precomp_descendVertices]
  exact JTJointIntervalQuotient.descend_whole U j q K time D s trace hTrace

@[reassoc]
theorem joint_descendToNative :
    withTimeMap q K time D (jointToNative U j) ≫
      descendToNative U j q K time D k s trace hTrace = trace := by
  unfold descendToNative jointToNative
  rw [withTimeMap_comp, Category.assoc, precomp_descendVertices]
  exact JTJointIntervalQuotient.descend_joint U j q K time D s trace hTrace

/-- The full joint trace equation is exactly the condition for a unique
descended coefficient with the original diagram and the specified joint trace. -/
theorem existsUnique_descendToNative_iff :
    (∃! v : withTime q K time D (native U j) ⟶ k ⋙ J,
      withTimeMap q K time D (originalToNative U j) ≫ v = s ∧
        withTimeMap q K time D (jointToNative U j) ≫ v = trace) ↔
      TraceFactors U j q K time D k s trace := by
  have sq := JTJointIntervalQuotient.timed_isPushout U j q K time D
  constructor
  · rintro ⟨v, ⟨h₁, h₂⟩, _⟩
    unfold TraceFactors
    rw [← h₁, ← h₂, originalToNative, jointToNative,
      withTimeMap_comp q K time D (wholeCollapse U j) (toNative U j),
      withTimeMap_comp q K time D (jointToWhole U j) (toNative U j)]
    simpa only [Category.assoc] using
      congrArg (fun m ↦ m ≫ withTimeMap q K time D (toNative U j) ≫ v) sq.w
  · intro h
    let v := descendToNative U j q K time D k s trace h
    have h₁ := original_descendToNative U j q K time D k s trace h
    have h₂ := joint_descendToNative U j q K time D k s trace h
    refine ⟨v, ⟨h₁, h₂⟩, ?_⟩
    intro w hw
    apply precomp_vertices_injective (withTimeMap q K time D (toNative U j)) k
      (timed_compare_bijective U j q K time D)
    apply sq.hom_ext
    · simpa only [← withTimeMap_comp, ← Category.assoc] using hw.1.trans h₁.symm
    · simpa only [← withTimeMap_comp, ← Category.assoc] using hw.2.trans h₂.symm

end Native

noncomputable section ActualFamily

open JTParametrizedTargetFamilies (Family)
open JTJointRelativeGraphFamily (coefficient originalParameter)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {I : Type} [SmallCategory I]
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : I ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

variable (trace : withTime Q.map J time (JTJointRelativeGraphFamily.native F)
  (joint Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (h : TraceFactors Q.code j Q.map J time (JTJointRelativeGraphFamily.native F)
  (coefficient (L := L)) (originalParameter F) trace)

/-- The exact original family parameter is recovered from the descended parameter
by the endpoint-preserving comparison over its literal target. -/
theorem actualParameter_pullback :
    withTimeMap Q.map J time (JTJointRelativeGraphFamily.native F)
        (simplicialComparison Q.code j) ≫
      descendToNative Q.code j Q.map J time (JTJointRelativeGraphFamily.native F)
        (coefficient (L := L)) (originalParameter F) trace h =
      originalParameter F :=
  original_descendToNative Q.code j Q.map J time (JTJointRelativeGraphFamily.native F)
    (coefficient (L := L)) (originalParameter F) trace h

end ActualFamily
end DaggerModels.PartII.JTJointClippedParameters
