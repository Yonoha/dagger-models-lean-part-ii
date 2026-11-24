import DaggerModelsPartII.JTParameterVertexKan

/-!
# Two separated blocks in one JT parameter

The extra ordinal edge separates the two closed blocks.
All endpoint identities below refer to arbitrary selected block vertices.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTParameterBlocks

noncomputable section

/-- The common ordinal has one edge between the two full parameter blocks. -/
def common (k l : SimplexCategory) : SimplexCategory :=
  ⦋k.len + l.len + 1⦌

/-- Inclusion of the first closed block. -/
def leftIn (k l : SimplexCategory) : k ⟶ common k l :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨i.val, by
        have hi := i.isLt
        change i.val < k.len + 1 at hi
        change i.val < k.len + l.len + 1 + 1
        omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      exact hij⟩

/-- Inclusion of the second closed block after the separating edge. -/
def rightIn (k l : SimplexCategory) : l ⟶ common k l :=
  SimplexCategory.Hom.mk
    ⟨fun i ↦ ⟨k.len + 1 + i.val, by
        have hi := i.isLt
        change i.val < l.len + 1 at hi
        change k.len + 1 + i.val < k.len + l.len + 1 + 1
        omega⟩, by
      intro i j hij
      change i.val ≤ j.val at hij
      change k.len + 1 + i.val ≤ k.len + 1 + j.val
      omega⟩

/-- Clamp the common ordinal to the first block. -/
def leftRet (k l : SimplexCategory) : common k l ⟶ k :=
  SimplexCategory.Hom.mk
    ⟨fun u ↦ ⟨min u.val k.len, by omega⟩, by
      intro u v huv
      change u.val ≤ v.val at huv
      change min u.val k.len ≤ min v.val k.len
      omega⟩

/-- Shift the common ordinal down to the second block, clamping its left side. -/
def rightRet (k l : SimplexCategory) : common k l ⟶ l :=
  SimplexCategory.Hom.mk
    ⟨fun u ↦ ⟨u.val - (k.len + 1), by
        have hu := u.isLt
        change u.val < k.len + l.len + 1 + 1 at hu
        omega⟩, by
      intro u v huv
      change u.val ≤ v.val at huv
      change u.val - (k.len + 1) ≤ v.val - (k.len + 1)
      omega⟩

/-- Restriction after extension is strictly the identity on the first block. -/
theorem left_split (k l : SimplexCategory) :
    leftIn k l ≫ leftRet k l = 𝟙 k := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change min i.val k.len = i.val
  have hi := i.isLt
  change i.val < k.len + 1 at hi
  omega

/-- Restriction after extension is strictly the identity on the second block. -/
theorem right_split (k l : SimplexCategory) :
    rightIn k l ≫ rightRet k l = 𝟙 l := by
  apply SimplexCategory.Hom.ext'
  apply OrderHom.ext
  funext i
  apply Fin.ext
  change k.len + 1 + i.val - (k.len + 1) = i.val
  omega

/-- An arbitrary vertex in the left block, viewed in the common ordinal. -/
def leftPoint (k l : SimplexCategory) (i : Fin (k.len + 1)) :
    Fin ((common k l).len + 1) :=
  (leftIn k l).toOrderHom i

/-- An arbitrary vertex in the right block, viewed in the common ordinal. -/
def rightPoint (k l : SimplexCategory) (j : Fin (l.len + 1)) :
    Fin ((common k l).len + 1) :=
  (rightIn k l).toOrderHom j

theorem leftPoint_lt_rightPoint (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    leftPoint k l i < rightPoint k l j := by
  change i.val < k.len + 1 + j.val
  have hi := i.isLt
  change i.val < k.len + 1 at hi
  omega

/-- The actual one-edge seam from the selected left vertex to the selected
right vertex, including zero-dimensional blocks. -/
def seam (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    ⦋1⦌ ⟶ common k l :=
  SimplexCategory.mkOfLe (leftPoint k l i) (rightPoint k l j)
    (le_of_lt (leftPoint_lt_rightPoint k l i j))

/-- The seam's initial ordinal endpoint is the selected left block vertex. -/
theorem seam_left_endpoint (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 ≫ seam k l i j =
      SimplexCategory.const ⦋0⦌ k i ≫ leftIn k l := by
  rw [SimplexCategory.const_comp, SimplexCategory.const_comp]
  rfl

/-- The seam's terminal ordinal endpoint is the selected right block vertex. -/
theorem seam_right_endpoint (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫ seam k l i j =
      SimplexCategory.const ⦋0⦌ l j ≫ rightIn k l := by
  rw [SimplexCategory.const_comp, SimplexCategory.const_comp]
  rfl

/-- The actual groupoid parameter sends an ordinal vertex to the same
selected vertex after every simplex operator. -/
theorem parameterVertex_map {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 1)) :
    JTParameterContraction.parameterVertex a i ≫
        GroupoidSimplex.parameter.map f =
      JTParameterContraction.parameterVertex b (f.toOrderHom i) := by
  let vertexArrow : ⦋0⦌ ⟶ a := SimplexCategory.const ⦋0⦌ a i
  calc
    JTParameterContraction.parameterVertex a i ≫ GroupoidSimplex.parameter.map f =
        (JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
          GroupoidSimplex.parameter.map vertexArrow) ≫
          GroupoidSimplex.parameter.map f := by
            rw [← JTCylinderCEComparison.simplexUnit.naturality vertexArrow]
            exact congrArg (fun h ↦ h ≫ GroupoidSimplex.parameter.map f)
              (JTParameterVertexKan.simplexUnit_vertex a i).symm
    _ = JTCylinderCEComparison.simplexUnit.app ⦋0⦌ ≫
          GroupoidSimplex.parameter.map (vertexArrow ≫ f) := by
            rw [GroupoidSimplex.parameter.map_comp, Category.assoc]
    _ = JTParameterContraction.parameterVertex b (f.toOrderHom i) := by
          rw [show vertexArrow ≫ f =
            SimplexCategory.const ⦋0⦌ b (f.toOrderHom i) from
              SimplexCategory.const_comp ⦋0⦌ f i]
          rw [← JTCylinderCEComparison.simplexUnit.naturality
            (SimplexCategory.const ⦋0⦌ b (f.toOrderHom i))]
          exact JTParameterVertexKan.simplexUnit_vertex b (f.toOrderHom i)

/-- Vertex equation for the first full block in the actual JT parameter. -/
theorem leftIn_parameter_vertex (k l : SimplexCategory)
    (i : Fin (k.len + 1)) :
    JTParameterContraction.parameterVertex k i ≫
        GroupoidSimplex.parameter.map (leftIn k l) =
      JTParameterContraction.parameterVertex (common k l) (leftPoint k l i) :=
  parameterVertex_map (leftIn k l) i

/-- Vertex equation for the second full block in the actual JT parameter. -/
theorem rightIn_parameter_vertex (k l : SimplexCategory)
    (j : Fin (l.len + 1)) :
    JTParameterContraction.parameterVertex l j ≫
        GroupoidSimplex.parameter.map (rightIn k l) =
      JTParameterContraction.parameterVertex (common k l) (rightPoint k l j) :=
  parameterVertex_map (rightIn k l) j

/-- The whole actual JT seam has the selected left parameter vertex. -/
theorem seam_left_parameter_endpoint (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    JTParameterContraction.parameterVertex ⦋1⦌ 0 ≫
        GroupoidSimplex.parameter.map (seam k l i j) =
      JTParameterContraction.parameterVertex k i ≫
        GroupoidSimplex.parameter.map (leftIn k l) := by
  rw [parameterVertex_map, parameterVertex_map]
  have h := seam_left_endpoint k l i j
  apply congrArg (JTParameterContraction.parameterVertex (common k l))
  simpa only [SimplexCategory.const_comp, SimplexCategory.const_apply] using
    SimplexCategory.congr_toOrderHom_apply h (0 : Fin 1)

/-- The whole actual JT seam has the selected right parameter vertex. -/
theorem seam_right_parameter_endpoint (k l : SimplexCategory)
    (i : Fin (k.len + 1)) (j : Fin (l.len + 1)) :
    JTParameterContraction.parameterVertex ⦋1⦌ 1 ≫
        GroupoidSimplex.parameter.map (seam k l i j) =
      JTParameterContraction.parameterVertex l j ≫
        GroupoidSimplex.parameter.map (rightIn k l) := by
  rw [parameterVertex_map, parameterVertex_map]
  have h := seam_right_endpoint k l i j
  apply congrArg (JTParameterContraction.parameterVertex (common k l))
  simpa only [SimplexCategory.const_comp, SimplexCategory.const_apply] using
    SimplexCategory.congr_toOrderHom_apply h (0 : Fin 1)

end

end DaggerModels.PartII.JTParameterBlocks
