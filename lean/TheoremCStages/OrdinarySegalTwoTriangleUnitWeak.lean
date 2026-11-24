import OrdinarySegalUnitPullbackWeak
import OrdinarySegalFaceFibrations
import OrdinarySegalOrderedMappingFibres

/-!
# The literal two-triangle unit comparison

The two triangles share their middle face. Their remaining outer faces
give the exact right-hand map in Rezk's two-triangle square, and the two
vertex degeneracies give its bottom map. This file constructs the actual
strict pullback comparison. Its Kan weakness requires the joint outer-horn
restriction of the two triangles, beyond the separate face fibrations;
that fibration and the resulting pasting theorem are not asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.OrdinarySegalTwoTriangleUnitWeak

open OrdinaryCSSLocalization (Space)

noncomputable section

private abbrev row (W : Space) (n : ℕ) := W.obj (op ⦋n⦌)

private def face (W : Space) {n : ℕ} (i : Fin (n + 2)) :
    row W (n + 1) ⟶ row W n := W.map (SimplexCategory.δ i).op

private def degeneracy (W : Space) {n : ℕ} (i : Fin (n + 1)) :
    row W n ⟶ row W (n + 1) := W.map (SimplexCategory.σ i).op

private theorem map_op_comp (W : Space) {a b c : SimplexCategory}
    (f : a ⟶ b) (g : b ⟶ c) :
    W.map g.op ≫ W.map f.op = W.map (f ≫ g).op := by
  rw [op_comp, Functor.map_comp]

private theorem degeneracy_face_middle_zero (W : Space) :
    degeneracy W (0 : Fin 2) ≫ face W (1 : Fin 3) = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  calc
    degeneracy W (0 : Fin 2) ≫ face W (1 : Fin 3) =
        W.map (SimplexCategory.δ (1 : Fin 3) ≫
          SimplexCategory.σ (0 : Fin 2)).op := map_op_comp W _ _
    _ = 𝟙 (row W 1) := by rw [h, op_id, W.map_id]

private theorem degeneracy_face_middle_one (W : Space) :
    degeneracy W (1 : Fin 2) ≫ face W (1 : Fin 3) = 𝟙 (row W 1) := by
  have h : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      𝟙 ⦋1⦌ := by
    ext j
    fin_cases j <;> rfl
  calc
    degeneracy W (1 : Fin 2) ≫ face W (1 : Fin 3) =
        W.map (SimplexCategory.δ (1 : Fin 3) ≫
          SimplexCategory.σ (1 : Fin 2)).op := map_op_comp W _ _
    _ = 𝟙 (row W 1) := by rw [h, op_id, W.map_id]

private theorem degeneracy_face_outer_zero (W : Space) :
    degeneracy W (0 : Fin 2) ≫ face W (Fin.last 2) =
      face W (1 : Fin 2) ≫ degeneracy W (0 : Fin 1) := by
  have h : SimplexCategory.δ (Fin.last 2) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (1 : Fin 2) := by
    ext j
    fin_cases j <;> rfl
  calc
    degeneracy W (0 : Fin 2) ≫ face W (Fin.last 2) =
        W.map (SimplexCategory.δ (Fin.last 2) ≫
          SimplexCategory.σ (0 : Fin 2)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (1 : Fin 2)).op := by rw [h]
    _ = face W (1 : Fin 2) ≫ degeneracy W (0 : Fin 1) :=
      (map_op_comp W _ _).symm

private theorem degeneracy_face_outer_one (W : Space) :
    degeneracy W (1 : Fin 2) ≫ face W (0 : Fin 3) =
      face W (0 : Fin 2) ≫ degeneracy W (0 : Fin 1) := by
  have h : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      SimplexCategory.σ (0 : Fin 1) ≫ SimplexCategory.δ (0 : Fin 2) := by
    ext j
    fin_cases j <;> rfl
  calc
    degeneracy W (1 : Fin 2) ≫ face W (0 : Fin 3) =
        W.map (SimplexCategory.δ (0 : Fin 3) ≫
          SimplexCategory.σ (1 : Fin 2)).op := map_op_comp W _ _
    _ = W.map (SimplexCategory.σ (0 : Fin 1) ≫
          SimplexCategory.δ (0 : Fin 2)).op := by rw [h]
    _ = face W (0 : Fin 2) ≫ degeneracy W (0 : Fin 1) :=
      (map_op_comp W _ _).symm

/-- Two actual degree-two triangles with the same middle face. -/
def twoTriangles (W : Space) : SSet.{0} :=
  pullback (face W (1 : Fin 3)) (face W (1 : Fin 3))

/-- The lower triangle contributes its last outer edge; the upper triangle
contributes its first outer edge, in the literal Rezk order. -/
def outerPair (W : Space) : twoTriangles W ⟶ row W 1 ⨯ row W 1 :=
  prod.lift
    (pullback.fst _ _ ≫ face W (Fin.last 2))
    (pullback.snd _ _ ≫ face W (0 : Fin 3))

/-- The bottom map is the pair of actual degree-zero degeneracies. -/
def degeneratePair (W : Space) : row W 0 ⨯ row W 0 ⟶ row W 1 ⨯ row W 1 :=
  prod.map (degeneracy W (0 : Fin 1)) (degeneracy W (0 : Fin 1))

/-- Insert the two literal degeneracies as triangles sharing their
identity middle face. -/
def insertedTriangles (W : Space) : row W 1 ⟶ twoTriangles W :=
  pullback.lift (degeneracy W (0 : Fin 2))
    (degeneracy W (1 : Fin 2)) (by
      rw [degeneracy_face_middle_zero, degeneracy_face_middle_one])

/-- The two-triangle square commutes strictly, before any homotopy
pullback replacement. -/
theorem insertedTriangles_outerPair (W : Space) :
    insertedTriangles W ≫ outerPair W =
      OrdinarySegalOrderedMappingFibres.endpointArrow W ≫ degeneratePair W := by
  apply prod.hom_ext
  · simp only [Category.assoc, outerPair, prod.lift_fst, insertedTriangles,
      pullback.lift_fst_assoc, degeneratePair, prod.map_fst,
      OrdinarySegalOrderedMappingFibres.endpointArrow, prod.lift_fst_assoc]
    exact degeneracy_face_outer_zero W
  · simp only [Category.assoc, outerPair, prod.lift_snd, insertedTriangles,
      pullback.lift_snd_assoc, degeneratePair, prod.map_snd,
      OrdinarySegalOrderedMappingFibres.endpointArrow, prod.lift_snd_assoc]
    exact degeneracy_face_outer_one W

/-- The exact strict comparison into Rezk's two-triangle pullback. -/
def twoTriangleUnitComparison (W : Space) :
    row W 1 ⟶ pullback (outerPair W) (degeneratePair W) :=
  pullback.lift (insertedTriangles W)
    (OrdinarySegalOrderedMappingFibres.endpointArrow W)
    (insertedTriangles_outerPair W)

theorem twoTriangleUnitComparison_fst (W : Space) :
    twoTriangleUnitComparison W ≫ pullback.fst (outerPair W) (degeneratePair W) =
      insertedTriangles W := pullback.lift_fst _ _ _

theorem twoTriangleUnitComparison_snd (W : Space) :
    twoTriangleUnitComparison W ≫ pullback.snd (outerPair W) (degeneratePair W) =
      OrdinarySegalOrderedMappingFibres.endpointArrow W := pullback.lift_snd _ _ _

#print axioms insertedTriangles_outerPair
#print axioms twoTriangleUnitComparison_fst
#print axioms twoTriangleUnitComparison_snd

end

end DaggerModels.PartII.OrdinarySegalTwoTriangleUnitWeak
