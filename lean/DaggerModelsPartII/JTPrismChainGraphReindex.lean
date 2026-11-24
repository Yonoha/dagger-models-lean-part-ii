import DaggerModelsPartII.JTPrismChainGraphTransport
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# Reindexing full prism-chain graph covers

The existing pullback comparison for precomposition identifies the full cover
on a changed source with the changed source of the full cover. All assignment
and parameter data remain present; no ordinal section is chosen.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.JTPrismChainGraphReindex

noncomputable section

open JTCodiscreteParameterPairing (coord coord_map)

private abbrev J := GroupoidSimplex.parameter
private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev V := SSet.evaluation.{0}.obj zero
private abbrev R := evaluationRightAdjoint (Type 0) zero
private abbrev adj := evaluationAdjunctionLeft (Type 0) zero

variable {I B : Type} [SmallCategory I] [SmallCategory B]

section Assignments

variable (G : I ⥤ B) (X : B ⥤ SSet.{0}) (m : B ⥤ SimplexCategory)
variable (allowed : ∀ b, (X.obj b).obj zero → Set (Fin ((m.obj b).len + 1)))
variable (stable : ∀ {b b' : B} (f : b ⟶ b') (v : (X.obj b).obj zero),
  Set.MapsTo (m.map f).toOrderHom (allowed b v) (allowed b' ((X.map f).app zero v)))

private def assignmentIso :
    JTVertexAssignmentCover.cover (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v) ≅
      G ⋙ JTVertexAssignmentCover.cover X m allowed stable :=
  (PreservesPullback.iso ((Functor.whiskeringLeft I B SSet.{0}).obj G)
    (Functor.whiskerLeft X adj.unit)
    (Functor.whiskerRight (JTVertexAssignmentCover.forgetChoice X m allowed stable) R)).symm

private theorem assignmentIso_projection :
    (assignmentIso G X m allowed stable).hom ≫
        Functor.whiskerLeft G (JTVertexAssignmentCover.projection X m allowed stable) =
      JTVertexAssignmentCover.projection (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v) :=
  PreservesPullback.iso_inv_fst ((Functor.whiskeringLeft I B SSet.{0}).obj G)
    (Functor.whiskerLeft X adj.unit)
    (Functor.whiskerRight (JTVertexAssignmentCover.forgetChoice X m allowed stable) R)

private abbrev coskeletonProjection :=
  pullback.snd (Functor.whiskerLeft X adj.unit)
    (Functor.whiskerRight (JTVertexAssignmentCover.forgetChoice X m allowed stable) R)

private theorem assignmentIso_coskeleton :
    (assignmentIso G X m allowed stable).hom ≫
        Functor.whiskerLeft G (coskeletonProjection X m allowed stable) =
      coskeletonProjection (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v) :=
  PreservesPullback.iso_inv_snd ((Functor.whiskeringLeft I B SSet.{0}).obj G)
    (Functor.whiskerLeft X adj.unit)
    (Functor.whiskerRight (JTVertexAssignmentCover.forgetChoice X m allowed stable) R)

private theorem assignmentIso_choice :
    Functor.whiskerRight (assignmentIso G X m allowed stable).hom V ≫
        Functor.whiskerLeft G (JTVertexAssignmentCover.coveredChoice X m allowed stable) =
      JTVertexAssignmentCover.coveredChoice (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v) := by
  apply NatTrans.ext
  funext i
  have h := NatTrans.congr_app (assignmentIso_coskeleton G X m allowed stable) i
  change (assignmentIso G X m allowed stable).hom.app i ≫
      (coskeletonProjection X m allowed stable).app (G.obj i) =
    (coskeletonProjection (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
      (fun f v ↦ stable (G.map f) v)).app i at h
  change V.map ((assignmentIso G X m allowed stable).hom.app i) ≫
      (V.map ((coskeletonProjection X m allowed stable).app (G.obj i)) ≫
        adj.counit.app _) =
    V.map ((coskeletonProjection (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
      (fun f v ↦ stable (G.map f) v)).app i) ≫ adj.counit.app _
  rw [← Category.assoc, ← V.map_comp, h]
  rfl

private theorem trace_choice (b : B)
    (v : ((JTVertexAssignmentCover.cover X m allowed stable).obj b).obj zero) :
    coord (m.obj b) zero (((JTVertexAssignmentCover.trace X m allowed stable).app b).app
        zero v) 0 = ((JTVertexAssignmentCover.coveredChoice X m allowed stable).app b v).val.2 := by
  let φ := fun b (v : ((JTVertexAssignmentCover.cover X m allowed stable).obj b).obj zero) ↦
    ((JTVertexAssignmentCover.coveredChoice X m allowed stable).app b v).val.2
  have hφ : ∀ {b b' : B} (f : b ⟶ b')
      (v : ((JTVertexAssignmentCover.cover X m allowed stable).obj b).obj zero),
      φ b' (((JTVertexAssignmentCover.cover X m allowed stable).map f).app zero v) =
        (m.map f).toOrderHom (φ b v) := by
    intro b b' f v
    exact congrArg (fun u ↦ u.val.2)
      (congrFun ((JTVertexAssignmentCover.coveredChoice X m allowed stable).naturality f) v)
  exact JTJointRelativeParameters.parameterOfNaturalVertices_coord _ m φ hφ b v

private theorem assignmentIso_trace :
    (assignmentIso G X m allowed stable).hom ≫
        Functor.whiskerLeft G (JTVertexAssignmentCover.trace X m allowed stable) =
      JTVertexAssignmentCover.trace (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v) := by
  apply NatTrans.ext
  funext i
  apply JTJointRelativeParameters.parameter_ext
  intro v
  change coord (m.obj (G.obj i)) zero
      (((JTVertexAssignmentCover.trace X m allowed stable).app (G.obj i)).app zero
        (((assignmentIso G X m allowed stable).hom.app i).app zero v)) 0 =
    coord (m.obj (G.obj i)) zero
      (((JTVertexAssignmentCover.trace (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
        (fun f v ↦ stable (G.map f) v)).app i).app zero v) 0
  exact (trace_choice X m allowed stable (G.obj i)
    (((assignmentIso G X m allowed stable).hom.app i).app zero v)).trans
      ((congrArg (fun u ↦ u.val.2)
        (congrFun (NatTrans.congr_app (assignmentIso_choice G X m allowed stable) i) v)).trans
          (trace_choice (G ⋙ X) (G ⋙ m) (fun i ↦ allowed (G.obj i))
            (fun f v ↦ stable (G.map f) v) i v).symm)

end Assignments

variable (G : I ⥤ B) (X : B ⥤ SSet.{0}) {k m : B ⥤ SimplexCategory}
variable (θ : X ⟶ k ⋙ J) (α : m ⟶ k)

private def prismAllowed (b : B) (v : (X.obj b).obj zero) : Set (Fin ((m.obj b).len + 1)) :=
  {a | (α.app b).toOrderHom a = coord (k.obj b) zero ((θ.app b).app zero v) 0}

private theorem prismStable {b b' : B} (f : b ⟶ b') (v : (X.obj b).obj zero) :
    Set.MapsTo (m.map f).toOrderHom (prismAllowed X θ α b v)
      (prismAllowed X θ α b' ((X.map f).app zero v)) := by
  intro a ha
  have hα := SimplexCategory.congr_toOrderHom_apply (α.naturality f) a
  have hθ := congrFun (NatTrans.congr_app (θ.naturality f) zero) v
  change (θ.app b').app zero ((X.map f).app zero v) =
    (J.map (k.map f)).app zero ((θ.app b).app zero v) at hθ
  change (α.app b').toOrderHom ((m.map f).toOrderHom a) =
    (k.map f).toOrderHom ((α.app b).toOrderHom a) at hα
  change (α.app b).toOrderHom a = _ at ha
  change (α.app b').toOrderHom ((m.map f).toOrderHom a) =
    coord (k.obj b') zero ((θ.app b').app zero ((X.map f).app zero v)) 0
  rw [hθ, coord_map, hα, ha]

/-- The canonical reindex comparison is an isomorphism of full graph diagrams. -/
def iso :
    JTPrismChainGraphCover.cover (k := G ⋙ k) (m := G ⋙ m) (G ⋙ X)
        (Functor.whiskerLeft G θ) (Functor.whiskerLeft G α) ≅
      G ⋙ JTPrismChainGraphCover.cover X θ α :=
  assignmentIso G X m (prismAllowed X θ α) (prismStable X θ α)

/-- Compare the full cover after changing its source to the original full cover. -/
def reindex := (iso G X θ α).hom

/-- The inverse retains the same full assignment data. -/
def inverse := (iso G X θ α).inv

/-- The complete underlying projection commutes with source reindexing. -/
theorem reindex_projection :
    reindex G X θ α ≫ Functor.whiskerLeft G (JTPrismChainGraphCover.projection X θ α) =
      JTPrismChainGraphCover.projection (k := G ⋙ k) (m := G ⋙ m) (G ⋙ X)
        (Functor.whiskerLeft G θ) (Functor.whiskerLeft G α) :=
  assignmentIso_projection G X m (prismAllowed X θ α) (prismStable X θ α)

/-- The complete lifted parameter commutes with source reindexing. -/
theorem reindex_parameter :
    reindex G X θ α ≫ Functor.whiskerLeft G (JTPrismChainGraphCover.parameter X θ α) =
      JTPrismChainGraphCover.parameter (k := G ⋙ k) (m := G ⋙ m) (G ⋙ X)
        (Functor.whiskerLeft G θ) (Functor.whiskerLeft G α) :=
  assignmentIso_trace G X m (prismAllowed X θ α) (prismStable X θ α)

/-- The inverse comparison preserves the same full underlying projection. -/
theorem inverse_projection :
    inverse G X θ α ≫ JTPrismChainGraphCover.projection (k := G ⋙ k) (m := G ⋙ m)
        (G ⋙ X) (Functor.whiskerLeft G θ) (Functor.whiskerLeft G α) =
      Functor.whiskerLeft G (JTPrismChainGraphCover.projection X θ α) := by
  change (iso G X θ α).inv ≫ _ = _
  rw [Iso.inv_comp_eq]
  exact (reindex_projection G X θ α).symm

/-- The inverse comparison also preserves every simplex of the lifted parameter. -/
theorem inverse_parameter :
    inverse G X θ α ≫ JTPrismChainGraphCover.parameter (k := G ⋙ k) (m := G ⋙ m)
        (G ⋙ X) (Functor.whiskerLeft G θ) (Functor.whiskerLeft G α) =
      Functor.whiskerLeft G (JTPrismChainGraphCover.parameter X θ α) := by
  change (iso G X θ α).inv ≫ _ = _
  rw [Iso.inv_comp_eq]
  exact (reindex_parameter G X θ α).symm

end
end DaggerModels.PartII.JTPrismChainGraphReindex
