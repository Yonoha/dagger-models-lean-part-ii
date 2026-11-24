import DaggerModelsPartII.JTExactlyMarkedSourceDiagram
import DaggerModelsPartII.JTJointRelativeEdgeChoiceDiagram
import DaggerModelsPartII.JTActualJointSideChoiceTransport

/-!
# Full relative choices over the actual exactly marked source diagram

The full simplicial choice cover retains the original family, coefficient degrees,
and exact cut arrows. Its zero simplices are precisely the relative edge pairs
used by the actual left and right evaluations.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace DaggerSSetGluing
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTActualJointChoiceCover

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTExactlyMarkedSourceDiagram (Index supports degrees incl endpointRows supported_endpoint)
open JTJointRelativeEdgeChoiceDiagram
open JTActualJointSideChoiceTransport (Choices restrictChoices)
open JTProjectiveOrderedFiberComparison (row)
open JTJointEndpointRelativeLift (square reverseSquare)
open DaggerOriginalProductGadget (pointMap)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- All ending-edge simplices for every actual exactly transported cut. -/
abbrev endingSpaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  leftChoices W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j)

/-- All starting-edge simplices with the same original coefficient degrees. -/
abbrev startingSpaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  rightChoices W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j)

/-- The two choices share every simplicial degree and every exact source arrow. -/
abbrev spaces : (Index F j)ᵒᵖ ⥤ SSet.{0} :=
  pairChoices W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j)

private abbrev actualChoices (a : Index F j) := Choices F j a.1 a.2.val a.2.property

private def endingVertex {a : Index F j} (C : actualChoices F j a) :
    ((endingSpaces F j).obj (op a)).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm C.ending,
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (square W ((incl F j).app a) ((endpointRows F j).app a) (z j)
        (supported_endpoint F j a)) C.ending).mpr ⟨C.ending_face, C.ending_pair⟩⟩

private def startingVertex {a : Index F j} (C : actualChoices F j a) :
    ((startingSpaces F j).obj (op a)).obj (op ⦋0⦌) :=
  ⟨SSet.ihom₀Equiv.symm C.starting,
    (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (reverseSquare W ((incl F j).app a) ((endpointRows F j).app a) (z j)
        (supported_endpoint F j a)) C.starting).mpr ⟨C.starting_face, C.starting_pair⟩⟩

private def firstZero (a : Index F j) (v : ((spaces F j).obj (op a)).obj (op ⦋0⦌)) :
    ((endingSpaces F j).obj (op a)).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ fst _ _)

private def secondZero (a : Index F j) (v : ((spaces F j).obj (op a)).obj (op ⦋0⦌)) :
    ((startingSpaces F j).obj (op a)).obj (op ⦋0⦌) :=
  SSet.yonedaEquiv (SSet.yonedaEquiv.symm v ≫ snd _ _)

/-- Vertices of the full cover are exactly the normalized edge choices already
used by the actual left and right decorated evaluations. -/
def zeroEquiv (a : Index F j) :
    ((spaces F j).obj (op a)).obj (op ⦋0⦌) ≃ actualChoices F j a where
  toFun v := by
    let vl := firstZero F j a v
    let vr := secondZero F j a v
    have hl := (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (square W ((incl F j).app a) ((endpointRows F j).app a) (z j)
        (supported_endpoint F j a)) (SSet.ihom₀Equiv vl.val)).mp (by
          simpa only [Equiv.symm_apply_apply] using vl.property)
    have hr := (SSet.ihom₀Equiv_symm_mem_ihomToPullbackFiber_obj_zero_iff
      (reverseSquare W ((incl F j).app a) ((endpointRows F j).app a) (z j)
        (supported_endpoint F j a)) (SSet.ihom₀Equiv vr.val)).mp (by
          simpa only [Equiv.symm_apply_apply] using vr.property)
    exact ⟨SSet.ihom₀Equiv vl.val, SSet.ihom₀Equiv vr.val, hl.1, hr.1, hl.2, hr.2⟩
  invFun C := SSet.yonedaEquiv
    (lift (SSet.yonedaEquiv.symm (endingVertex F j C))
      (SSet.yonedaEquiv.symm (startingVertex F j C)))
  left_inv v := by
    apply SSet.yonedaEquiv.symm.injective
    apply CartesianMonoidalCategory.hom_ext
    · simp [firstZero, endingVertex]
    · simp [secondZero, startingVertex]
  right_inv C := by
    cases C
    simp [firstZero, secondZero, endingVertex, startingVertex]

/-- The ending edge is recovered without changing its full coefficient degree. -/
theorem zeroEquiv_ending (a : Index F j)
    (v : ((spaces F j).obj (op a)).obj (op ⦋0⦌)) :
    (zeroEquiv F j a v).ending =
      SSet.ihom₀Equiv (((fst ((endingSpaces F j).obj (op a))
        ((startingSpaces F j).obj (op a))).app _ v).val) := by
  change SSet.ihom₀Equiv (firstZero F j a v).val = _
  unfold firstZero
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- The starting edge is recovered in the same original coefficient degree. -/
theorem zeroEquiv_starting (a : Index F j)
    (v : ((spaces F j).obj (op a)).obj (op ⦋0⦌)) :
    (zeroEquiv F j a v).starting =
      SSet.ihom₀Equiv (((snd ((endingSpaces F j).obj (op a))
        ((startingSpaces F j).obj (op a))).app _ v).val) := by
  change SSet.ihom₀Equiv (secondZero F j a v).val = _
  unfold secondZero
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

private theorem choices_ext {a : Index F j} {C D : actualChoices F j a}
    (he : C.ending = D.ending) (hs : C.starting = D.starting) : C = D := by
  cases C
  cases D
  cases he
  cases hs
  rfl

/-- The full simplicial restriction on vertices is precisely the restriction
used by the existing corrected left and right evaluations. -/
theorem zeroEquiv_restrict {a b : Index F j} (f : a ⟶ b)
    (v : ((spaces F j).obj (op b)).obj (op ⦋0⦌)) :
    zeroEquiv F j a (((spaces F j).map f.op).app _ v) =
      restrictChoices F j f.val (hv := a.2.property)
        (JTExactlyMarkedSourceDiagram.cut_map F j f) (zeroEquiv F j b v) := by
  apply choices_ext F j
  · change (zeroEquiv F j a (((spaces F j).map f.op).app _ v)).ending =
      std.map ((degrees F j).map f) ≫ (zeroEquiv F j b v).ending
    rw [zeroEquiv_ending, zeroEquiv_ending]
    have h := congrFun (NatTrans.congr_app
      (tensorHom_fst ((endingSpaces F j).map f.op) ((startingSpaces F j).map f.op))
      (op ⦋0⦌)) v
    change ((fst ((endingSpaces F j).obj (op a))
      ((startingSpaces F j).obj (op a))).app _ (((spaces F j).map f.op).app _ v)) =
        (((endingSpaces F j).map f.op).app _
          ((fst ((endingSpaces F j).obj (op b))
            ((startingSpaces F j).obj (op b))).app _ v)) at h
    rw [h]
    exact leftChoices_zero W (supports F j) (degrees F j) (incl F j)
      (endpointRows F j) (z j) (supported_endpoint F j) f _
  · change (zeroEquiv F j a (((spaces F j).map f.op).app _ v)).starting =
      std.map ((degrees F j).map f) ≫ (zeroEquiv F j b v).starting
    rw [zeroEquiv_starting, zeroEquiv_starting]
    have h := congrFun (NatTrans.congr_app
      (tensorHom_snd ((endingSpaces F j).map f.op) ((startingSpaces F j).map f.op))
      (op ⦋0⦌)) v
    change ((snd ((endingSpaces F j).obj (op a))
      ((startingSpaces F j).obj (op a))).app _ (((spaces F j).map f.op).app _ v)) =
        (((startingSpaces F j).map f.op).app _
          ((snd ((endingSpaces F j).obj (op b))
            ((startingSpaces F j).obj (op b))).app _ v)) at h
    rw [h]
    exact rightChoices_zero W (supports F j) (degrees F j) (incl F j)
      (endpointRows F j) (z j) (supported_endpoint F j) f _

/-- The complete paired choice space at every actual cut is weakly contractible. -/
theorem spaces_point_GW
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) (a : (Index F j)ᵒᵖ) :
    GW (pointMap ((spaces F j).obj a)) :=
  pairChoices_point_GW W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) hW (JTExactlyMarkedSourceDiagram.incl_mono F j) a

/-- Retain every simplex of both relative choices, with all simplicial operators. -/
abbrev Cover := (GrothendieckTotalElements.totalDiagram (spaces F j)).Elementsᵒᵖ

/-- Forget the two choices and their simplicial degree, keeping the exact source cut. -/
abbrev projection : Cover F j ⥤ Index F j :=
  (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (spaces F j)) ⋙
    CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ).leftOp

/-- Adjoining all coherent relative edge choices is a weak cover of the
actual exactly marked source category, with its original variance restored. -/
theorem projection_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (projection F j)) := by
  let E := (GrothendieckTotalElements.totalDiagram (spaces F j)).Elements
  let e := (opOpEquivalence E).inverse
  haveI : WeakEquivalence (nerveMap e) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence e
  apply (TotalElementsWeakComparison.nerveMap_op_iff (projection F j)).mp
  apply (weakEquivalence_precomp_iff (nerveMap e) _).mp
  change WeakEquivalence (nerveMap (e ⋙ (projection F j).op))
  change WeakEquivalence (nerveMap
    (CategoryOfElements.π (GrothendieckTotalElements.totalDiagram (spaces F j)) ⋙
      CategoryTheory.Prod.fst (Index F j)ᵒᵖ SimplexCategoryᵒᵖ))
  exact pairChoices_projection_weak W (supports F j) (degrees F j) (incl F j)
    (endpointRows F j) (z j) (supported_endpoint F j) hW
    (JTExactlyMarkedSourceDiagram.incl_mono F j)

end
end DaggerModels.PartII.JTActualJointChoiceCover
