import DaggerModelsPartII.JTParametrizedBeadGraphHorizontal
import DaggerModelsPartII.JTRowGraphFaceResolution

/-! The exact horizontal face and graph of a parametrized bead in a one-bead target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTRowGraphFaceResolution (Resolution)
open scoped SSet.modelCategoryQuillen

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) {n : ℕ} (r : Q.code.toSSet ≅ (Δ[n] : SSet.{0}))

/-- The raw map of the whole one-bead target, before choosing any graph representative. -/
def targetSimplex : (Δ[n] : SSet.{0}) ⟶ R W := r.inv ≫ Q.map

variable (a : A) (d : ℕ)
variable (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)

private def horizontal : (Δ[d] : SSet.{0}) ⟶ Δ[n] :=
  (NecklaceCode.singleIso d).inv ≫ i ≫ (F.collapse.app a).map ≫ r.hom

/-- The actual operator into the target simplex is determined before taking its raw value. -/
def targetFace : Over ⦋n⦌ := Over.mk (SSet.stdSimplex.{0}.preimage (horizontal F r a d i))

theorem targetFace_map :
    SSet.stdSimplex.{0}.map (targetFace F r a d i).hom = horizontal F r a d i :=
  SSet.stdSimplex.{0}.map_preimage _

/-- The face value is exactly the restriction of the original raw target. -/
theorem targetFace_value :
    JTRowGraphFaceResolution.value (targetSimplex r) (targetFace F r a d i) =
      (NecklaceCode.singleIso d).inv ≫ beadRaw F a d i := by
  change SSet.stdSimplex.{0}.map (targetFace F r a d i).hom ≫ targetSimplex r = _
  rw [targetFace_map]
  unfold horizontal targetSimplex beadRaw
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable (v : (Δ[0] : SSet.{0}) ⟶ J.obj (time.obj a))

/-- The original graph lies over the exact slice object, including degenerate operators. -/
def targetFaceGraph : Resolution (targetSimplex r) :=
  ⟨op (targetFace F r a d i), op
    ⟨(fiberGraph F a d i v).obj, (fiberGraph F a d i v).property.trans
      (targetFace_value F r a d i).symm⟩⟩

section Mixed

variable {b : A} (f : a ⟶ b) (e : ℕ)
variable (j : (NecklaceCode.single e).toSSet ⟶ ((codes L).obj b).toSSet)
variable (u : ⦋d⦌ ⟶ ⦋e⦌)
variable (h : (NecklaceCode.singleIso d).inv ≫ i ≫ ((codes L).map f).map =
  SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j)

include h in
private theorem face_triangle :
    u ≫ (targetFace F r b e j).hom = (targetFace F r a d i).hom := by
  apply SSet.stdSimplex.{0}.map_injective
  rw [Functor.map_comp, targetFace_map, targetFace_map]
  let c := (F.collapse.app b).map ≫ r.hom
  have hc : ((codes L).map f).map ≫ (F.collapse.app b).map = (F.collapse.app a).map :=
    congrArg (fun g : (codes L).obj a ⟶ Q.code ↦ g.map)
      ((F.collapse.naturality f).trans (Category.comp_id _))
  unfold horizontal
  calc
    _ = (SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j) ≫ c := by
      simp only [Category.assoc]
      rfl
    _ = ((NecklaceCode.singleIso d).inv ≫ i ≫ ((codes L).map f).map) ≫ c :=
      congrArg (· ≫ c) h.symm
    _ = _ := by
      simp only [Category.assoc, c]
      rw [← Category.assoc ((codes L).map f).map, hc]

/-- The native triangle gives the actual commutative triangle in the horizontal slice. -/
def targetFaceArrow : targetFace F r a d i ⟶ targetFace F r b e j :=
  Over.homMk u (face_triangle F r a d i f e j u h)

/-- The mixed graph arrow is an actual arrow of the weakly contractible target resolution. -/
def targetFaceGraphArrow :
    targetFaceGraph F r b e j (v ≫ J.map (time.map f)) ⟶ targetFaceGraph F r a d i v :=
  ⟨(targetFaceArrow F r a d i f e j u h).op,
    Quiver.Hom.op ⟨mixedFiberGraphArrow a i u F v f j h⟩⟩

/-- A specified target time vertex can be used without transporting the horizontal operator. -/
def targetFaceGraphArrowOfTime (v' : (Δ[0] : SSet.{0}) ⟶ J.obj (time.obj b))
    (ht : v ≫ J.map (time.map f) = v') :
    targetFaceGraph F r b e j v' ⟶ targetFaceGraph F r a d i v where
  base := (targetFaceArrow F r a d i f e j u h).op
  fiber := by
    subst v'
    exact (targetFaceGraphArrow F r a d i v f e j u h).fiber

end Mixed

section Diagrams

variable {B : Type} [SmallCategory B]

/-- A varying horizontal simplex in the original code and a compatible time vertex. -/
structure SampleDiagram (base : B ⥤ A) (shape : B ⥤ SimplexCategory) where
  bead : ∀ b, (NecklaceCode.single (shape.obj b).len).toSSet ⟶ ((codes L).obj (base.obj b)).toSSet
  timeVertex : ∀ b, (Δ[0] : SSet.{0}) ⟶ J.obj (time.obj (base.obj b))
  bead_map : ∀ {b c} (f : b ⟶ c),
    (NecklaceCode.singleIso (shape.obj b).len).inv ≫ bead b ≫ ((codes L).map (base.map f)).map =
      SSet.stdSimplex.{0}.map (shape.map f) ≫
        (NecklaceCode.singleIso (shape.obj c).len).inv ≫ bead c
  timeVertex_map : ∀ {b c} (f : b ⟶ c),
    timeVertex b ≫ J.map (time.map (base.map f)) = timeVertex c

variable {base : B ⥤ A} {shape : B ⥤ SimplexCategory}
variable (S : SampleDiagram (L := L) (time := time) base shape)

private abbrev faceAt (b : B) := targetFace F r (base.obj b) (shape.obj b).len (S.bead b)
private abbrev faceOp {b c : B} (f : b ⟶ c) : faceAt F r S b ⟶ faceAt F r S c :=
  targetFaceArrow F r (base.obj b) (shape.obj b).len (S.bead b)
    (base.map f) (shape.obj c).len (S.bead c) (shape.map f) (S.bead_map f)

/-- The exact operators into the target form an entire horizontal diagram. -/
def targetFaces : B ⥤ Over ⦋n⦌ where
  obj := faceAt F r S
  map f := faceOp F r S f
  map_id b := Over.OverMorphism.ext (shape.map_id b)
  map_comp f g := Over.OverMorphism.ext (shape.map_comp f g)

private abbrev graphAt (b : B) := targetFaceGraph F r (base.obj b)
  (shape.obj b).len (S.bead b) (S.timeVertex b)

private def graphOp {b c : B} (f : b ⟶ c) : graphAt F r S c ⟶ graphAt F r S b :=
  targetFaceGraphArrowOfTime F r (base.obj b) (shape.obj b).len (S.bead b) (S.timeVertex b)
    (base.map f) (shape.obj c).len (S.bead c) (shape.map f) (S.bead_map f) (S.timeVertex c)
    (S.timeVertex_map f)

/-- The whole diagram of actual sampled graphs compares coherently in the weakly
contractible resolution after restricting each coefficient to its used vertices. -/
def sampledGraphDiagram : Bᵒᵖ ⥤ Resolution (targetSimplex r) where
  obj b := (JTRowGraphFaceResolution.supported _).obj (graphAt F r S b.unop)
  map f := (JTRowGraphFaceResolution.supported _).map (graphOp F r S f.unop)
  map_id b := JTRowGraphFaceResolution.supported_ext _
    (graphAt F r S b.unop) (congrArg Quiver.Hom.op ((targetFaces F r S).map_id b.unop))
  map_comp {_ _ c} f g := JTRowGraphFaceResolution.supported_ext _ (graphAt F r S c.unop)
    (congrArg Quiver.Hom.op ((targetFaces F r S).map_comp g.unop f.unop))

/-- The supported graph diagram lies over exactly the original horizontal operators. -/
theorem sampledGraphDiagram_forget :
    sampledGraphDiagram F r S ⋙ Grothendieck.forget (JTRowGraphFaceResolution.diagram _) =
      (targetFaces F r S).op := rfl

end Diagrams

end

end DaggerModels.PartII.JTParametrizedBeadGraph
