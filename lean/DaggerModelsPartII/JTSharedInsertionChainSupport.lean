import DaggerModelsPartII.JTSharedInsertionChoices
import DaggerModelsPartII.JTOrdinalTwoFaceUnionPullback
import DaggerModelsPartII.JTIncidentBeadSupportWeak

/-!
# Actual incident supports on the one shared insertion chain

At each of the three actual insertion marks, take the full subcomplex preimage
of the genuine incident union under the common original-coefficient projection.
All original and chain operators are retained. Weakness follows from the actual
zero-, one- or two-face description and surjectivity of that ordinal projection.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSharedInsertionChainSupport

open JTParametrizedTargetFamilies (Family)
open JTProjectiveOrderedFiberComparison (row vertexPoint)
open JTTargetJointMarks (Joint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem ordinal_face_weak {d k : SimplexCategory} (α : d ⟶ k)
    (hα : Function.Surjective α.toOrderHom) (S : Finset (Fin (k.len + 1)))
    (v : Fin (k.len + 1)) (hv : v ∈ S) :
    WeakEquivalence ((SSet.stdSimplex.face S : (std.obj k).Subcomplex).preimage
      (std.map α)).ι := by
  induction d using SimplexCategory.rec with | _ d =>
    induction k using SimplexCategory.rec with | _ k =>
      exact JTOrdinalTwoFaceUnionPullback.preimage_face_weak α hα S v hv

private theorem ordinal_union_weak {d k : SimplexCategory} (α : d ⟶ k)
    (hα : Function.Surjective α.toOrderHom) (S T : Finset (Fin (k.len + 1)))
    (v : Fin (k.len + 1)) (hvS : v ∈ S) (hvT : v ∈ T) :
    WeakEquivalence (((SSet.stdSimplex.face S : (std.obj k).Subcomplex) ⊔
      SSet.stdSimplex.face T).preimage (std.map α)).ι := by
  induction d using SimplexCategory.rec with | _ d =>
    induction k using SimplexCategory.rec with | _ k =>
      exact JTOrdinalTwoFaceUnionPullback.preimage_union_weak α hα S T v hvS hvT

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

/-- The single shared coefficient/choice-clock chain, with its full actual operators. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- Its one common chain ordinal. -/
abbrev ordinals := JTSharedInsertionChoices.ordinals F j

/-- The unchanged original object and arrow underlying this common chain. -/
abbrev originalBase := JTSharedInsertionChoices.base F j ⋙
  JTSharedInsertionChoices.projection F j ⋙ JTSharedInsertionChoices.originalBase F j

/-- The earlier, middle and later actual marks on the one common chain. -/
abbrev marks (which : Fin 3) : Index F j ⥤ JTExactlyMarkedSourceDiagram.Index F j :=
  JTSharedInsertionChoices.base F j ⋙ JTSharedInsertionChoices.projection F j ⋙
    ![JTSharedInsertionChoices.earlierMark F j, JTSharedInsertionChoices.middleMark F j,
      JTSharedInsertionChoices.laterMark F j] which

/-- The first mark is the earlier actual insertion cut. -/
theorem marks_earlier : marks F j 0 = JTSharedInsertionChoices.base F j ⋙
    JTSharedInsertionChoices.projection F j ⋙ JTSharedInsertionChoices.earlierMark F j := rfl

/-- The second mark is the proposed inserted cut. -/
theorem marks_middle : marks F j 1 = JTSharedInsertionChoices.base F j ⋙
    JTSharedInsertionChoices.projection F j ⋙ JTSharedInsertionChoices.middleMark F j := rfl

/-- The third mark is the later actual insertion cut. -/
theorem marks_later : marks F j 2 = JTSharedInsertionChoices.base F j ⋙
    JTSharedInsertionChoices.projection F j ⋙ JTSharedInsertionChoices.laterMark F j := rfl

/-- All three marks retain the same original source functor. -/
theorem marks_base (which : Fin 3) :
    marks F j which ⋙ JTExactlyMarkedSourceDiagram.base F j = originalBase F j := by
  fin_cases which <;> rfl

/-- The old coefficient simplex at each actual mark, without changing that coefficient. -/
abbrev oldDegrees (which : Fin 3) := marks F j which ⋙ JTExactlyMarkedSourceDiagram.degrees F j

/-- The SAME original-coefficient projection at each of the three marks. -/
def toOriginal (which : Fin 3) : ordinals F j ⟶ oldDegrees F j which := by
  refine Fin.cases ?_ ?_ which
  · exact JTSharedInsertionChoices.toOriginal F j
  · intro i
    refine Fin.cases ?_ ?_ i
    · exact JTSharedInsertionChoices.toOriginal F j
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact JTSharedInsertionChoices.toOriginal F j
      · intro i
        exact Fin.elim0 i

/-- This is the actual surjective projection from the common full chain. -/
theorem toOriginal_surjective (which : Fin 3) (p : Index F j) :
    Function.Surjective ((toOriginal F j which).app p).toOrderHom := by
  fin_cases which <;> exact JTSharedInsertionChoices.toOriginal_surjective F j p

/-- The old genuine incident-support diagram at the named actual insertion mark. -/
abbrev oldSupports (which : Fin 3) := marks F j which ⋙ JTIncidentBeadSupportTransport.diagram F j

/-- Its literal inclusion in the unchanged original coefficient simplex. -/
abbrev oldInclusion (which : Fin 3) :=
  Functor.whiskerLeft (marks F j which) (JTIncidentBeadSupportTransport.inclusion F j)

/-- Full inverse image of the genuine old union, without filling in a vertex hull. -/
def support (which : Fin 3) (p : Index F j) : (std.obj ((ordinals F j).obj p)).Subcomplex :=
  (JTIncidentBeadSupportData.support F j ((marks F j which).obj p)).preimage
    (std.map ((toOriginal F j which).app p))

private theorem support_condition {which : Fin 3} {p q : Index F j} (f : p ⟶ q)
    {n : SimplexCategoryᵒᵖ} (x : (std.obj ((ordinals F j).obj p)).obj n)
    (hx : x ∈ (support F j which p).obj n) :
    (std.map ((ordinals F j).map f)).app n x ∈ (support F j which q).obj n := by
  have h := (toOriginal F j which).naturality f
  have hn := congrFun (NatTrans.congr_app (congrArg std.map h) n) x
  change (std.map ((toOriginal F j which).app q)).app n
      ((std.map ((ordinals F j).map f)).app n x) =
    (std.map ((oldDegrees F j which).map f)).app n
      ((std.map ((toOriginal F j which).app p)).app n x) at hn
  change (std.map ((toOriginal F j which).app q)).app n
    ((std.map ((ordinals F j).map f)).app n x) ∈
      (JTIncidentBeadSupportData.support F j ((marks F j which).obj q)).obj n
  rw [hn]
  have hpre := (SSet.Subcomplex.image_le_iff _ _ _).mp
    (JTIncidentBeadSupportTransport.support_image F j ((marks F j which).map f))
  exact hpre n hx

/-- Restrict every actual common-chain operator to its full incident-support preimage. -/
def supportMap (which : Fin 3) {p q : Index F j} (f : p ⟶ q) :
    (support F j which p).toSSet ⟶ (support F j which q).toSSet where
  app n x := ⟨(std.map ((ordinals F j).map f)).app n x.val,
    support_condition F j f x.val x.property⟩
  naturality n m θ := by
    funext x
    apply Subtype.ext
    exact congrFun ((std.map ((ordinals F j).map f)).naturality θ) x.val

/-- The support inclusion keeps the original common-chain operator exactly. -/
theorem supportMap_fac (which : Fin 3) {p q : Index F j} (f : p ⟶ q) :
    supportMap F j which f ≫ (support F j which q).ι =
      (support F j which p).ι ≫ std.map ((ordinals F j).map f) := rfl

/-- The actual full preimage support diagram at any of the three marks. -/
def diagram (which : Fin 3) : Index F j ⥤ SSet.{0} where
  obj p := (support F j which p).toSSet
  map := supportMap F j which
  map_id p := by
    apply (cancel_mono (support F j which p).ι).mp
    rw [supportMap_fac, (ordinals F j).map_id, std.map_id,
      Category.comp_id, Category.id_comp]
  map_comp {p q r} f g := by
    apply (cancel_mono (support F j which r).ι).mp
    simp only [Category.assoc, supportMap_fac, (ordinals F j).map_comp, std.map_comp]
    conv_rhs => rw [← Category.assoc, supportMap_fac]
    exact (Category.assoc (support F j which p).ι
      (std.map ((ordinals F j).map f)) (std.map ((ordinals F j).map g))).symm

/-- The full preimage support includes naturally in the one common chain simplex. -/
def inclusion (which : Fin 3) : diagram F j which ⟶ ordinals F j ⋙ std where
  app p := (support F j which p).ι
  naturality _ _ f := supportMap_fac F j which f

/-- Restriction of the literal common projection lands in the original incident union. -/
def toOldSupport (which : Fin 3) : diagram F j which ⟶ oldSupports F j which where
  app p := {
    app n x := ⟨(std.map ((toOriginal F j which).app p)).app n x.val, x.property⟩
    naturality := by
      intro n m θ
      funext x
      apply Subtype.ext
      exact congrFun ((std.map ((toOriginal F j which).app p)).naturality θ) x.val }
  naturality p q f := by
    haveI : Mono ((oldInclusion F j which).app q) := by
      change Mono (JTIncidentBeadSupportData.support F j ((marks F j which).obj q)).ι
      infer_instance
    apply (cancel_mono ((oldInclusion F j which).app q)).mp
    have h := congrArg std.map ((toOriginal F j which).naturality f)
    simpa only [Functor.map_comp, Category.assoc] using congrArg
      (fun t ↦ (support F j which p).ι ≫ t) h

/-- The strict support square retains the original coefficient and every actual chain operator. -/
theorem natural_square (which : Fin 3) :
    toOldSupport F j which ≫ oldInclusion F j which =
      inclusion F j which ≫ Functor.whiskerRight (toOriginal F j which) std := rfl

/-- The full inverse-image support inclusion is mono, without an extra hypothesis. -/
theorem inclusion_mono (which : Fin 3) (p : Index F j) :
    Mono ((inclusion F j which).app p) := by
  change Mono (support F j which p).ι
  infer_instance

/-- Actual zero/one/two incident faces give a weak inclusion on the full shared chain. -/
theorem inclusion_weak (which : Fin 3) (p : Index F j) :
    WeakEquivalence ((inclusion F j which).app p) := by
  let q := (marks F j which).obj p
  let α := (toOriginal F j which).app p
  obtain ⟨v, hv⟩ := JTIncidentBeadSupportData.vertexSet_nonempty F j q
  change WeakEquivalence ((JTIncidentBeadSupportData.support F j q).preimage (std.map α)).ι
  rcases JTIncidentBeadCombinatorics.incident_cases
      (JTIncidentBeadSupportData.gap F j q) (JTIncidentBeadSupportData.gapCoordinate F j q) with
    h | ⟨B₀, h₀, h⟩ | ⟨B₀, B₁, _, h₀, h₁, h⟩
  · rw [JTIncidentBeadSupportWeak.support_eq_vertex_of_no_incident F j q h,
      JTIncidentBeadSupportData.vertexFace_eq_face]
    exact ordinal_face_weak α
      (toOriginal_surjective F j which p) _ v hv
  · rw [JTIncidentBeadSupportWeak.support_eq_bead_of_unique F j q B₀ h₀ h,
      JTIncidentBeadSupportData.beadFace_eq_face]
    exact ordinal_face_weak α
      (toOriginal_surjective F j which p) _ v
      (JTIncidentBeadSupportData.vertexSet_subset_beadSet F j q B₀ h₀ hv)
  · rw [JTIncidentBeadSupportWeak.support_eq_two_beads_of_cover F j q B₀ B₁ h₀ h₁ h,
      JTIncidentBeadSupportData.beadFace_eq_face, JTIncidentBeadSupportData.beadFace_eq_face]
    exact ordinal_union_weak α
      (toOriginal_surjective F j which p) _ _ v
      (JTIncidentBeadSupportData.vertexSet_subset_beadSet F j q B₀ h₀ hv)
      (JTIncidentBeadSupportData.vertexSet_subset_beadSet F j q B₁ h₁ hv)

/-- The original varying vertex row, reindexed to the actual mark on the common chain. -/
abbrev oldRows (which : Fin 3) :=
  Functor.whiskerLeft (marks F j which) (JTExactlyMarkedSourceDiagram.endpointRows F j)

/-- That same varying row pulled back along the literal original-coefficient projection. -/
def rows (which : Fin 3) : ordinals F j ⋙ std ⟶
    (Functor.const (Index F j)).obj (row W ⦋0⦌) :=
  Functor.whiskerRight (toOriginal F j which) std ≫ oldRows F j which

/-- The actual varying endpoint row is stationary on its entire full support preimage. -/
theorem row_on_support (which : Fin 3) (p : Index F j) :
    (inclusion F j which).app p ≫ (rows F j which).app p =
      term ((diagram F j which).obj p) ≫
        vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) := by
  have h := JTIncidentBeadSupportData.row_on_support F j ((marks F j which).obj p)
  have hs := NatTrans.congr_app (natural_square F j which) p
  change (toOldSupport F j which).app p ≫ (oldInclusion F j which).app p =
    (inclusion F j which).app p ≫ std.map ((toOriginal F j which).app p) at hs
  change (inclusion F j which).app p ≫
    (std.map ((toOriginal F j which).app p) ≫ (oldRows F j which).app p) = _
  change (oldInclusion F j which).app p ≫ (oldRows F j which).app p =
    term ((oldSupports F j which).obj p) ≫
      vertexPoint W (JTParametrizedBeadGraph.jointCoefficient (Q := Q) j) at h
  rw [← Category.assoc, ← hs, Category.assoc, h, ← Category.assoc]
  congr 1

end
end DaggerModels.PartII.JTSharedInsertionChainSupport
