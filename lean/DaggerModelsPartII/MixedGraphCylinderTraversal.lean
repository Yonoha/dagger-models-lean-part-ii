import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTParameterContraction
import DaggerModelsPartII.NecklaceCylinderHomSpan
import ChosenNecklaceTripleWedge
import ChosenNecklaceWedgeFunctor

/-!
# Mixed horizontal and groupoid-parameter traversal

A three-bead native necklace has one middle bead of
arbitrary length `d`, including `d = 0`. Its first and last beads carry
constant parameter vertices; its middle bead carries the whole specified
map `s`. The horizontal coordinate is the literal identity on the whole
three-bead code.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.MixedGraphCylinderTraversal

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev A := single 1
private abbrev B (d : ℕ) := single d

/-- Native first, central, and last bead, with no positivity premise on `d`. -/
def code (d : ℕ) : DaggerChosenRigidificationNecklace.NecklaceCode :=
  wedge A (wedge (B d) A)

private abbrev L (d : ℕ) : A.toSSet ⟶ (code d).toSSet :=
  tripleRightT A (B d) A
private abbrev M (d : ℕ) : (B d).toSSet ⟶ (code d).toSSet :=
  tripleRightU A (B d) A
private abbrev RR (d : ℕ) : A.toSSet ⟶ (code d).toSSet :=
  tripleRightV A (B d) A

/-- A constant parameter on one complete native bead. -/
def constantParameter (C : DaggerChosenRigidificationNecklace.NecklaceCode)
    (k : SimplexCategory) (a : Fin (k.len + 1)) : C.toSSet ⟶ J.obj k :=
  SSet.stdSimplex.isTerminalObj₀.from C.toSSet ≫
    JTParameterContraction.parameterVertex k a

theorem pointAt_constantParameter
    (C : DaggerChosenRigidificationNecklace.NecklaceCode)
    (k : SimplexCategory) (a : Fin (k.len + 1))
    (v : DaggerChosenRigidificationNecklace.NecklaceCode.Vertices.{0} C) :
    pointAt C v ≫ constantParameter C k a =
      JTParameterContraction.parameterVertex k a := by
  dsimp only [constantParameter]
  rw [← Category.assoc]
  have h : pointAt C v ≫ SSet.stdSimplex.isTerminalObj₀.from C.toSSet =
      𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

/-- The graph parameter is defined by the actual triple-wedge pushout. -/
def graphParameter (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1))
    (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    (code d).toSSet ⟶ J.obj k :=
  tripleRightDesc A (B d) A
    (constantParameter A k a) s (constantParameter A k b)
    ((pointAt_constantParameter A k a (ULift.up (Fin.last A.len))).trans ha.symm)
    (hb.trans (pointAt_constantParameter A k b (ULift.up 0)).symm)

/-- Three complete restrictions of the graph parameter. -/
theorem graphParameter_left (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    L d ≫ graphParameter d k a b s ha hb = constantParameter A k a :=
  tripleRightDesc_T _ _ _ _ _ _ _ _

theorem graphParameter_middle (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    M d ≫ graphParameter d k a b s ha hb = s :=
  tripleRightDesc_U _ _ _ _ _ _ _ _

theorem graphParameter_right (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    RR d ≫ graphParameter d k a b s ha hb = constantParameter A k b :=
  tripleRightDesc_V _ _ _ _ _ _ _ _

/-- Horizontal coordinate is literally the identity on the entire code. -/
def productTraversal (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    (code d).toSSet ⟶ (code d).toSSet ⊗ J.obj k :=
  CartesianMonoidalCategory.lift (𝟙 _) (graphParameter d k a b s ha hb)

theorem productTraversal_left (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    L d ≫ productTraversal d k a b s ha hb =
      CartesianMonoidalCategory.lift (L d) (constantParameter A k a) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_fst, Category.comp_id]
  · simpa only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_snd] using graphParameter_left d k a b s ha hb

theorem productTraversal_middle (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    M d ≫ productTraversal d k a b s ha hb =
      CartesianMonoidalCategory.lift (M d) s := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_fst, Category.comp_id]
  · simpa only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_snd] using graphParameter_middle d k a b s ha hb

theorem productTraversal_right (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    RR d ≫ productTraversal d k a b s ha hb =
      CartesianMonoidalCategory.lift (RR d) (constantParameter A k b) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_fst, Category.comp_id]
  · simpa only [productTraversal, Category.assoc,
      CartesianMonoidalCategory.lift_snd] using graphParameter_right d k a b s ha hb

/-- The same graph in the checked reduced cylinder for this exact code. -/
def cylinderTraversal (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    (code d).toSSet ⟶
      (JTNecklaceEndpointCylinder.value (code d)).obj k :=
  productTraversal d k a b s ha hb ≫
    (JTNecklaceEndpointCylinder.cylinder (code d)).app k

private theorem boundary_first (d : ℕ) :
    SSet.boundary₁.ι₀ ≫ JTNecklaceEndpointCylinder.endpointInclusion (code d) =
      pointAt (code d) (ULift.up 0) := by
  change SSet.boundary₁.ι₀ ≫
    SSet.boundary₁.desc (code d).first (code d).last =
      SSet.yonedaEquiv.symm (code d).first
  exact SSet.boundary₁.ι₀_desc _ _

private theorem boundary_last (d : ℕ) :
    SSet.boundary₁.ι₁ ≫ JTNecklaceEndpointCylinder.endpointInclusion (code d) =
      pointAt (code d) (ULift.up (Fin.last (code d).len)) := by
  change SSet.boundary₁.ι₁ ≫
    SSet.boundary₁.desc (code d).first (code d).last =
      SSet.yonedaEquiv.symm (code d).last
  exact SSet.boundary₁.ι₁_desc _ _

private theorem cylinderTraversal_at_boundary (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b)
    (j : (Δ[0] : SSet.{0}) ⟶ JTXiEndpointCollapse.boundary)
    (q : (Δ[0] : SSet.{0}) ⟶ (code d).toSSet)
    (hq : j ≫ JTNecklaceEndpointCylinder.endpointInclusion (code d) = q) :
    q ≫ cylinderTraversal d k a b s ha hb =
      j ≫ (JTNecklaceEndpointCylinder.boundary (code d)).app k := by
  let v : (Δ[0] : SSet.{0}) ⟶ J.obj k :=
    q ≫ graphParameter d k a b s ha hb
  have hp : q ≫ productTraversal d k a b s ha hb =
      CartesianMonoidalCategory.lift j v ≫
        (JTNecklaceEndpointCylinder.endpointInclusion (code d) ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [productTraversal, Category.assoc,
        CartesianMonoidalCategory.lift_fst,
        CartesianMonoidalCategory.tensorHom_fst, Category.comp_id] using hq.symm
    · simp only [productTraversal, v, Category.assoc,
        CartesianMonoidalCategory.lift_snd,
        CartesianMonoidalCategory.tensorHom_snd, Category.comp_id]
  calc
    _ = (q ≫ productTraversal d k a b s ha hb) ≫
        (JTNecklaceEndpointCylinder.cylinder (code d)).app k :=
          (Category.assoc _ _ _).symm
    _ = (CartesianMonoidalCategory.lift j v ≫
          (JTNecklaceEndpointCylinder.endpointInclusion (code d) ⊗ₘ
            𝟙 (J.obj k))) ≫
          (JTNecklaceEndpointCylinder.cylinder (code d)).app k := by rw [hp]
    _ = CartesianMonoidalCategory.lift j v ≫
          CartesianMonoidalCategory.fst JTXiEndpointCollapse.boundary (J.obj k) ≫
          (JTNecklaceEndpointCylinder.boundary (code d)).app k := by
            rw [Category.assoc, (JTNecklaceEndpointCylinder.isPushout (code d) k).w]
    _ = _ := by rw [← Category.assoc, CartesianMonoidalCategory.lift_fst]

/-- Full ordered boundary map, beyond equality merely on two zero-simplices. -/
theorem cylinderTraversal_boundary (d : ℕ) (k : SimplexCategory)
    (a b : Fin (k.len + 1)) (s : (B d).toSSet ⟶ J.obj k)
    (ha : pointAt (B d) (ULift.up 0) ≫ s =
      JTParameterContraction.parameterVertex k a)
    (hb : pointAt (B d) (ULift.up (Fin.last (B d).len)) ≫ s =
      JTParameterContraction.parameterVertex k b) :
    JTNecklaceEndpointCylinder.endpointInclusion (code d) ≫
      cylinderTraversal d k a b s ha hb =
        (JTNecklaceEndpointCylinder.boundary (code d)).app k := by
  apply SSet.boundary₁.hom_ext
  · rw [← Category.assoc, boundary_first]
    exact cylinderTraversal_at_boundary d k a b s ha hb SSet.boundary₁.ι₀
      (pointAt (code d) (ULift.up 0)) (boundary_first d)
  · rw [← Category.assoc, boundary_last]
    exact cylinderTraversal_at_boundary d k a b s ha hb SSet.boundary₁.ι₁
      (pointAt (code d) (ULift.up (Fin.last (code d).len))) (boundary_last d)

/-- Collapse both outer beads to the central endpoints, keeping the full
middle bead, including its zero-length case. -/
def collapseMap (d : ℕ) : (code d).toSSet ⟶ (B d).toSSet :=
  tripleRightDesc A (B d) A
    (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫ pointAt (B d) (ULift.up 0))
    (𝟙 (B d).toSSet)
    (SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
      pointAt (B d) (ULift.up (Fin.last (B d).len)))
    (by
      rw [← Category.assoc]
      have h : pointAt A (ULift.up (Fin.last A.len)) ≫
          SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
            𝟙 (Δ[0] : SSet.{0}) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [h, Category.id_comp, Category.comp_id])
    (by
      rw [Category.comp_id, ← Category.assoc]
      have h : pointAt A (ULift.up 0) ≫
          SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
            𝟙 (Δ[0] : SSet.{0}) :=
        SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      rw [h, Category.id_comp])

theorem collapseMap_left (d : ℕ) :
    L d ≫ collapseMap d =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt (B d) (ULift.up 0) :=
  tripleRightDesc_T _ _ _ _ _ _ _ _

theorem collapseMap_middle (d : ℕ) :
    M d ≫ collapseMap d = 𝟙 (B d).toSSet :=
  tripleRightDesc_U _ _ _ _ _ _ _ _

theorem collapseMap_right (d : ℕ) :
    RR d ≫ collapseMap d =
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet ≫
        pointAt (B d) (ULift.up (Fin.last (B d).len)) :=
  tripleRightDesc_V _ _ _ _ _ _ _ _

private theorem collapseMap_first (d : ℕ) :
    pointAt (code d) (ULift.up 0) ≫ collapseMap d =
      pointAt (B d) (ULift.up 0) := by
  change pointAt (wedge A (wedge (B d) A)) (ULift.up 0) ≫ collapseMap d = _
  rw [← pointAt_first_left A (wedge (B d) A)]
  change (pointAt A (ULift.up 0) ≫ L d) ≫ collapseMap d = _
  rw [Category.assoc, collapseMap_left, ← Category.assoc]
  have h : pointAt A (ULift.up 0) ≫
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
        𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

private theorem collapseMap_last (d : ℕ) :
    pointAt (code d) (ULift.up (Fin.last (code d).len)) ≫ collapseMap d =
      pointAt (B d) (ULift.up (Fin.last (B d).len)) := by
  change pointAt (wedge A (wedge (B d) A))
    (ULift.up (Fin.last (wedge A (wedge (B d) A)).len)) ≫ collapseMap d = _
  rw [← pointAt_last_right A (wedge (B d) A),
    ← pointAt_last_right (B d) A]
  change (pointAt A (ULift.up (Fin.last A.len)) ≫ RR d) ≫ collapseMap d = _
  rw [Category.assoc, collapseMap_right, ← Category.assoc]
  have h : pointAt A (ULift.up (Fin.last A.len)) ≫
      SSet.stdSimplex.isTerminalObj₀.from A.toSSet =
        𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

/-- The collapse is an original native necklace-code morphism. -/
def collapseOuter (d : ℕ) :
    DaggerChosenRigidificationNecklace.NecklaceCode.Hom.{0} (code d) (B d) where
  map := collapseMap d
  first := first_of_point (collapseMap d) (collapseMap_first d)
  last := last_of_point (collapseMap d) (collapseMap_last d)

end

end DaggerModels.PartII.MixedGraphCylinderTraversal
