import ActualOriginalNecklaceInclusionWeak
import ChosenNecklaceTripleWedge
import ChosenNecklaceSingleBead
import NativeOriginalWeakMonoPushout

/-!
# The literal two-block simplex quotient

The source simplex is kept separate from the three-bead necklace.  The
two-block quotient is formed by successively collapsing its initial and
terminal blocks; the necklace pushout is a second object to be compared
with that literal quotient.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCylinderBlockQuotient

noncomputable section

variable (a b : ℕ)

/-- The initial block, crossing edge, and terminal block as a three-bead
subcomplex of the original simplex. -/
def code : NecklaceCode :=
  wedge (single a) (wedge (single 1) (single b))

def simplex : SSet.{0} := Δ[(code a b).len]

/-- The block-height map, zero on the first full simplex and one on
the terminal full simplex. -/
def heightHom : ⦋(code a b).len⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.mkHom
    ⟨fun i ↦ if i.val ≤ a then 0 else 1, by
      intro i j hij
      change (if i.val ≤ a then (0 : Fin 2) else 1) ≤
        (if j.val ≤ a then (0 : Fin 2) else 1)
      change i.val ≤ j.val at hij
      by_cases hi : i.val ≤ a
      · by_cases hj : j.val ≤ a <;> simp [hi, hj]
      · have hj : ¬ j.val ≤ a := by omega
        simp [hi, hj]⟩

def height : simplex a b ⟶ (Δ[1] : SSet.{0}) :=
  SSet.stdSimplex.map (heightHom a b)

def firstBlock : (Δ[a] : SSet.{0}) ⟶ simplex a b :=
  (singleIso.{0} a).inv ≫
    tripleRightT (single a) (single 1) (single b) ≫
      (code a b).inclusion

def crossingEdge : (Δ[1] : SSet.{0}) ⟶ simplex a b :=
  (singleIso.{0} 1).inv ≫
    tripleRightU (single a) (single 1) (single b) ≫
      (code a b).inclusion

def lastBlock : (Δ[b] : SSet.{0}) ⟶ simplex a b :=
  (singleIso.{0} b).inv ≫
    tripleRightV (single a) (single 1) (single b) ≫
      (code a b).inclusion

/-- The three original ordinal injections into the same ambient simplex. -/
def firstHom : ⦋a⦌ ⟶ ⦋(code a b).len⦌ :=
  SimplexCategory.Hom.mk
    (wedgeLeft (single a) (wedge (single 1) (single b))).toOrderHom

def crossingHom : ⦋1⦌ ⟶ ⦋(code a b).len⦌ :=
  SimplexCategory.Hom.mk
    ((wedgeRight (single a) (wedge (single 1) (single b))).toOrderHom.comp
      (wedgeLeft (single 1) (single b)).toOrderHom)

def lastHom : ⦋b⦌ ⟶ ⦋(code a b).len⦌ :=
  SimplexCategory.Hom.mk
    ((wedgeRight (single a) (wedge (single 1) (single b))).toOrderHom.comp
      (wedgeRight (single 1) (single b)).toOrderHom)

theorem firstBlock_eq_map :
    firstBlock a b = SSet.stdSimplex.map (firstHom a b) := by
  let T := single a
  let U := wedge (single 1) (single b)
  change (singleIso.{0} a).inv ≫
    ((wedgeιLeft T U) ≫ (wedge T U).inclusion) = _
  rw [wedgeιLeft_inclusion]
  change (singleIso.{0} a).inv ≫
    ((single a).inclusion ≫ SSet.stdSimplex.map (firstHom a b)) = _
  rw [← singleIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

theorem crossingEdge_eq_map :
    crossingEdge a b = SSet.stdSimplex.map (crossingHom a b) := by
  let T := single a
  let U := single 1
  let V := single b
  change (singleIso.{0} 1).inv ≫
    ((wedgeιLeft U V ≫ wedgeιRight T (wedge U V)) ≫
      (wedge T (wedge U V)).inclusion) = _
  rw [Category.assoc, wedgeιRight_inclusion,
    ← Category.assoc (wedgeιLeft U V) (wedge U V).inclusion
      (SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight T (wedge U V)).toOrderHom :
          ⦋(wedge U V).len⦌ ⟶ ⦋(wedge T (wedge U V)).len⦌)),
    wedgeιLeft_inclusion]
  change (singleIso.{0} 1).inv ≫
    ((single 1).inclusion ≫
      SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeLeft U V).toOrderHom :
          ⦋U.len⦌ ⟶ ⦋(wedge U V).len⦌)) ≫
      SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight T (wedge U V)).toOrderHom :
          ⦋(wedge U V).len⦌ ⟶ ⦋(wedge T (wedge U V)).len⦌) = _
  simp only [← singleIso_hom, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, ← SSet.stdSimplex.map_comp]
  rfl

theorem lastBlock_eq_map :
    lastBlock a b = SSet.stdSimplex.map (lastHom a b) := by
  let T := single a
  let U := single 1
  let V := single b
  change (singleIso.{0} b).inv ≫
    ((wedgeιRight U V ≫ wedgeιRight T (wedge U V)) ≫
      (wedge T (wedge U V)).inclusion) = _
  rw [Category.assoc, wedgeιRight_inclusion,
    ← Category.assoc (wedgeιRight U V) (wedge U V).inclusion
      (SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight T (wedge U V)).toOrderHom :
          ⦋(wedge U V).len⦌ ⟶ ⦋(wedge T (wedge U V)).len⦌)),
    wedgeιRight_inclusion]
  change (singleIso.{0} b).inv ≫
    ((single b).inclusion ≫
      SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight U V).toOrderHom :
          ⦋V.len⦌ ⟶ ⦋(wedge U V).len⦌)) ≫
      SSet.stdSimplex.map
        (SimplexCategory.Hom.mk (wedgeRight T (wedge U V)).toOrderHom :
          ⦋(wedge U V).len⦌ ⟶ ⦋(wedge T (wedge U V)).len⦌) = _
  simp only [← singleIso_hom, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, ← SSet.stdSimplex.map_comp]
  rfl

theorem firstBlock_necklace :
    (singleIso.{0} a).hom ≫ firstBlock a b =
      tripleRightT (single a) (single 1) (single b) ≫
        (code a b).inclusion := by
  simp only [firstBlock, Iso.hom_inv_id_assoc]

theorem crossingEdge_necklace :
    (singleIso.{0} 1).hom ≫ crossingEdge a b =
      tripleRightU (single a) (single 1) (single b) ≫
        (code a b).inclusion := by
  simp only [crossingEdge, Iso.hom_inv_id_assoc]

theorem lastBlock_necklace :
    (singleIso.{0} b).hom ≫ lastBlock a b =
      tripleRightV (single a) (single 1) (single b) ≫
        (code a b).inclusion := by
  simp only [lastBlock, Iso.hom_inv_id_assoc]

theorem crossingHom_apply (i : Fin 2) :
    (crossingHom a b).toOrderHom i =
      ⟨a + i.val, by
        have hi := i.isLt
        change i.val < 2 at hi
        change a + i.val < (code a b).len + 1
        dsimp [code, wedge, single]
        omega⟩ := by
  apply Fin.ext
  rfl

theorem firstHom_apply (i : Fin (a + 1)) :
    (firstHom a b).toOrderHom i =
      ⟨i.val, by
        have hi := i.isLt
        change i.val < a + 1 at hi
        change i.val < (code a b).len + 1
        dsimp [code, wedge, single]
        omega⟩ := by
  apply Fin.ext
  rfl

theorem lastHom_apply (i : Fin (b + 1)) :
    (lastHom a b).toOrderHom i =
      ⟨a + 1 + i.val, by
        have hi := i.isLt
        change i.val < b + 1 at hi
        change a + 1 + i.val < (code a b).len + 1
        dsimp [code, wedge, single]
        omega⟩ := by
  apply Fin.ext
  dsimp [lastHom, wedgeRight, code, wedge, single]
  omega

theorem firstHom_heightHom :
    firstHom a b ≫ heightHom a b =
      SimplexCategory.const ⦋a⦌ ⦋1⦌ 0 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.const_apply]
  dsimp only [heightHom, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk]
  change (if ((firstHom a b).toOrderHom i).val ≤ a then
    (0 : Fin 2) else 1).val = 0
  rw [firstHom_apply]
  have hi : i.val ≤ a := Nat.le_of_lt_succ i.isLt
  simp [hi]

theorem crossingHom_heightHom :
    crossingHom a b ≫ heightHom a b = 𝟙 ⦋1⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.id_toOrderHom]
  dsimp only [heightHom, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk]
  change (if ((crossingHom a b).toOrderHom i).val ≤ a then
    (0 : Fin 2) else 1).val = i.val
  rw [crossingHom_apply]
  fin_cases i <;> simp

theorem lastHom_heightHom :
    lastHom a b ≫ heightHom a b =
      SimplexCategory.const ⦋b⦌ ⦋1⦌ 1 := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe,
    Function.comp_apply, SimplexCategory.const_apply]
  dsimp only [heightHom, SimplexCategory.mkHom,
    SimplexCategory.Hom.toOrderHom_mk]
  change (if ((lastHom a b).toOrderHom i).val ≤ a then
    (0 : Fin 2) else 1).val = 1
  rw [lastHom_apply]
  have hi : ¬ a + 1 + i.val ≤ a := by omega
  simp [hi]

theorem firstBlock_height :
    firstBlock a b ≫ height a b =
      SSet.stdSimplex.map (SimplexCategory.const ⦋a⦌ ⦋1⦌ 0) := by
  rw [firstBlock_eq_map, height, ← SSet.stdSimplex.map_comp,
    firstHom_heightHom]

theorem crossingEdge_height :
    crossingEdge a b ≫ height a b = 𝟙 (Δ[1] : SSet.{0}) := by
  rw [crossingEdge_eq_map, height, ← SSet.stdSimplex.map_comp,
    crossingHom_heightHom]
  exact SSet.stdSimplex.map_id ⦋1⦌

theorem lastBlock_height :
    lastBlock a b ≫ height a b =
      SSet.stdSimplex.map (SimplexCategory.const ⦋b⦌ ⦋1⦌ 1) := by
  rw [lastBlock_eq_map, height, ← SSet.stdSimplex.map_comp,
    lastHom_heightHom]

def edgeZero : (Δ[0] : SSet.{0}) ⟶ Δ[1] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)

def edgeOne : (Δ[0] : SSet.{0}) ⟶ Δ[1] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)

def lastOfFirst : (Δ[0] : SSet.{0}) ⟶ Δ[a] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋a⦌ (Fin.last a))

def firstOfLast : (Δ[0] : SSet.{0}) ⟶ Δ[b] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)

theorem edgeZero_crossing :
    edgeZero ≫ crossingEdge a b = lastOfFirst a ≫ firstBlock a b := by
  rw [edgeZero, lastOfFirst, crossingEdge_eq_map, firstBlock_eq_map,
    ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  fin_cases i
  simp only [SimplexCategory.const_comp, SimplexCategory.const_apply,
    crossingHom_apply, firstHom_apply]
  simp [Fin.val_last]

theorem edgeOne_crossing :
    edgeOne ≫ crossingEdge a b = firstOfLast b ≫ lastBlock a b := by
  rw [edgeOne, firstOfLast, crossingEdge_eq_map, lastBlock_eq_map,
    ← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  apply congrArg SSet.stdSimplex.map
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  apply Fin.ext
  fin_cases i
  simp only [SimplexCategory.const_comp, SimplexCategory.const_apply,
    crossingHom_apply, lastHom_apply]
  simp

theorem firstBlock_height_point :
    firstBlock a b ≫ height a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫ edgeZero := by
  rw [firstBlock_height, edgeZero]
  have hc : SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0}) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋a⦌ ⦋0⦌ 0) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hc, ← SSet.stdSimplex.map_comp]
  congr 1

theorem lastBlock_height_point :
    lastBlock a b ≫ height a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫ edgeOne := by
  rw [lastBlock_height, edgeOne]
  have hc : SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0}) =
      SSet.stdSimplex.map (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hc, ← SSet.stdSimplex.map_comp]
  congr 1

/-- The literal first collapse, before quotienting the terminal block. -/
def firstQuotient : SSet.{0} :=
  pushout (firstBlock a b) (SSet.stdSimplex.isTerminalObj₀.from _)

def simplexToFirst : simplex a b ⟶ firstQuotient a b :=
  pushout.inl (firstBlock a b) (SSet.stdSimplex.isTerminalObj₀.from _)

def firstPoint : (Δ[0] : SSet.{0}) ⟶ firstQuotient a b :=
  pushout.inr (firstBlock a b) (SSet.stdSimplex.isTerminalObj₀.from _)

def firstProjection : firstQuotient a b ⟶ (Δ[1] : SSet.{0}) :=
  pushout.desc (height a b) edgeZero (firstBlock_height_point a b)

theorem simplexToFirst_projection :
    simplexToFirst a b ≫ firstProjection a b = height a b :=
  pushout.inl_desc _ _ _

theorem firstPoint_projection :
    firstPoint a b ≫ firstProjection a b = edgeZero :=
  pushout.inr_desc _ _ _

/-- The literal quotient which collapses the two disjoint full blocks
to distinct vertices.  This is independent of the necklace pushout. -/
def blockQuotient : SSet.{0} :=
  pushout (lastBlock a b ≫ simplexToFirst a b)
    (SSet.stdSimplex.isTerminalObj₀.from _)

def simplexToBlock : simplex a b ⟶ blockQuotient a b :=
  simplexToFirst a b ≫
    pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from _)

def firstVertex : (Δ[0] : SSet.{0}) ⟶ blockQuotient a b :=
  firstPoint a b ≫
    pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from _)

def lastVertex : (Δ[0] : SSet.{0}) ⟶ blockQuotient a b :=
  pushout.inr (lastBlock a b ≫ simplexToFirst a b)
    (SSet.stdSimplex.isTerminalObj₀.from _)

def blockProjection : blockQuotient a b ⟶ (Δ[1] : SSet.{0}) :=
  pushout.desc (firstProjection a b) edgeOne (by
    calc
      (lastBlock a b ≫ simplexToFirst a b) ≫ firstProjection a b =
          lastBlock a b ≫ height a b := by
            rw [Category.assoc, simplexToFirst_projection]
      _ = (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
            edgeOne := lastBlock_height_point a b)

theorem simplexToBlock_projection :
    simplexToBlock a b ≫ blockProjection a b = height a b := by
  have h : pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
      blockProjection a b = firstProjection a b :=
    pushout.inl_desc _ _ _
  calc
    simplexToBlock a b ≫ blockProjection a b =
        simplexToFirst a b ≫
          (pushout.inl (lastBlock a b ≫ simplexToFirst a b)
            (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            blockProjection a b) := Category.assoc _ _ _
    _ = simplexToFirst a b ≫ firstProjection a b := by rw [h]
    _ = height a b := simplexToFirst_projection a b

theorem firstVertex_projection :
    firstVertex a b ≫ blockProjection a b = edgeZero := by
  have h : pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
      blockProjection a b = firstProjection a b :=
    pushout.inl_desc _ _ _
  calc
    firstVertex a b ≫ blockProjection a b =
        firstPoint a b ≫
          (pushout.inl (lastBlock a b ≫ simplexToFirst a b)
            (SSet.stdSimplex.isTerminalObj₀.from _) ≫
            blockProjection a b) := Category.assoc _ _ _
    _ = firstPoint a b ≫ firstProjection a b := by rw [h]
    _ = edgeZero := firstPoint_projection a b

theorem lastVertex_projection :
    lastVertex a b ≫ blockProjection a b = edgeOne :=
  pushout.inr_desc _ _ _

def edgeToBlock : (Δ[1] : SSet.{0}) ⟶ blockQuotient a b :=
  crossingEdge a b ≫ simplexToBlock a b

theorem edgeToBlock_projection :
    edgeToBlock a b ≫ blockProjection a b = 𝟙 (Δ[1] : SSet.{0}) := by
  rw [edgeToBlock, Category.assoc, simplexToBlock_projection,
    crossingEdge_height]

theorem firstCollapse :
    firstBlock a b ≫ simplexToBlock a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫
        firstVertex a b := by
  have h : firstBlock a b ≫ simplexToFirst a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫
        firstPoint a b := pushout.condition
  calc
    firstBlock a b ≫ simplexToBlock a b =
        (firstBlock a b ≫ simplexToFirst a b) ≫
          pushout.inl (lastBlock a b ≫ simplexToFirst a b)
            (SSet.stdSimplex.isTerminalObj₀.from _) := by
          simp only [simplexToBlock, Category.assoc]
    _ = ((SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫
          firstPoint a b) ≫
          pushout.inl (lastBlock a b ≫ simplexToFirst a b)
            (SSet.stdSimplex.isTerminalObj₀.from _) := by rw [h]
    _ = (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫
          firstVertex a b := by
          simp only [firstVertex, Category.assoc]

theorem lastCollapse :
    lastBlock a b ≫ simplexToBlock a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
        lastVertex a b := by
  have h : (lastBlock a b ≫ simplexToFirst a b) ≫
        pushout.inl (lastBlock a b ≫ simplexToFirst a b)
          (SSet.stdSimplex.isTerminalObj₀.from _) =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
        lastVertex a b := pushout.condition
  simpa only [simplexToBlock, Category.assoc] using h

theorem edgeZero_toBlock :
    edgeZero ≫ edgeToBlock a b = firstVertex a b := by
  have ht : lastOfFirst a ≫
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) =
      𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [edgeToBlock, ← Category.assoc, edgeZero_crossing,
    Category.assoc, firstCollapse, ← Category.assoc, ht, Category.id_comp]

theorem edgeOne_toBlock :
    edgeOne ≫ edgeToBlock a b = lastVertex a b := by
  have ht : firstOfLast b ≫
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) =
      𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [edgeToBlock, ← Category.assoc, edgeOne_crossing,
    Category.assoc, lastCollapse, ← Category.assoc, ht, Category.id_comp]

theorem firstBlock_relation :
    firstBlock a b ≫ simplexToBlock a b =
      (firstBlock a b ≫ height a b) ≫ edgeToBlock a b := by
  rw [firstCollapse, firstBlock_height_point, Category.assoc,
    edgeZero_toBlock]

theorem crossingEdge_relation :
    crossingEdge a b ≫ simplexToBlock a b =
      (crossingEdge a b ≫ height a b) ≫ edgeToBlock a b := by
  rw [crossingEdge_height, Category.id_comp]
  rfl

theorem lastBlock_relation :
    lastBlock a b ≫ simplexToBlock a b =
      (lastBlock a b ≫ height a b) ≫ edgeToBlock a b := by
  rw [lastCollapse, lastBlock_height_point, Category.assoc,
    edgeOne_toBlock]

/-- The auxiliary pushout of the actual three-bead inclusion.  It is
not used as the definition of the literal quotient. -/
def necklaceToEdge : (code a b).toSSet ⟶ (Δ[1] : SSet.{0}) :=
  (code a b).inclusion ≫ height a b

def necklaceQuotient : SSet.{0} :=
  pushout (code a b).inclusion (necklaceToEdge a b)

def simplexToNecklaceQuotient : simplex a b ⟶ necklaceQuotient a b :=
  pushout.inl (code a b).inclusion (necklaceToEdge a b)

def edgeToNecklaceQuotient : (Δ[1] : SSet.{0}) ⟶
    necklaceQuotient a b :=
  pushout.inr (code a b).inclusion (necklaceToEdge a b)

theorem necklace_relation :
    (code a b).inclusion ≫ simplexToNecklaceQuotient a b =
      necklaceToEdge a b ≫ edgeToNecklaceQuotient a b :=
  pushout.condition

theorem necklace_relation_block :
    (code a b).inclusion ≫ simplexToBlock a b =
      necklaceToEdge a b ≫ edgeToBlock a b := by
  change (code a b).inclusion ≫ simplexToBlock a b =
    ((code a b).inclusion ≫ height a b) ≫ edgeToBlock a b
  apply tripleRight_hom_ext (T := single a) (U := single 1)
    (V := single b)
  · have h := congrArg (fun f ↦ (singleIso.{0} a).hom ≫ f)
      (firstBlock_relation a b)
    simp only [← Category.assoc, firstBlock_necklace] at h
    simpa only [Category.assoc] using h
  · have h := congrArg (fun f ↦ (singleIso.{0} 1).hom ≫ f)
      (crossingEdge_relation a b)
    simp only [← Category.assoc, crossingEdge_necklace] at h
    simpa only [Category.assoc] using h
  · have h := congrArg (fun f ↦ (singleIso.{0} b).hom ≫ f)
      (lastBlock_relation a b)
    simp only [← Category.assoc, lastBlock_necklace] at h
    simpa only [Category.assoc] using h

def necklaceToBlock : necklaceQuotient a b ⟶ blockQuotient a b :=
  pushout.desc (simplexToBlock a b) (edgeToBlock a b)
    (necklace_relation_block a b)

theorem simplexToNecklace_toBlock :
    simplexToNecklaceQuotient a b ≫ necklaceToBlock a b =
      simplexToBlock a b :=
  pushout.inl_desc _ _ _

theorem edgeToNecklace_toBlock :
    edgeToNecklaceQuotient a b ≫ necklaceToBlock a b =
      edgeToBlock a b :=
  pushout.inr_desc _ _ _

theorem firstBlock_necklace_relation :
    firstBlock a b ≫ simplexToNecklaceQuotient a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[a] : SSet.{0})) ≫
        edgeZero ≫ edgeToNecklaceQuotient a b := by
  have h0 : firstBlock a b ≫ simplexToNecklaceQuotient a b =
      (firstBlock a b ≫ height a b) ≫
        edgeToNecklaceQuotient a b := by
    apply (cancel_epi (singleIso.{0} a).hom).mp
    have h := congrArg
      (fun f ↦ tripleRightT (single a) (single 1) (single b) ≫ f)
      (necklace_relation a b)
    simp only [necklaceToEdge, ← Category.assoc, ← firstBlock_necklace] at h
    simpa only [Category.assoc] using h
  rw [h0, firstBlock_height_point, Category.assoc]

theorem lastBlock_necklace_relation :
    lastBlock a b ≫ simplexToNecklaceQuotient a b =
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
        edgeOne ≫ edgeToNecklaceQuotient a b := by
  have h0 : lastBlock a b ≫ simplexToNecklaceQuotient a b =
      (lastBlock a b ≫ height a b) ≫
        edgeToNecklaceQuotient a b := by
    apply (cancel_epi (singleIso.{0} b).hom).mp
    have h := congrArg
      (fun f ↦ tripleRightV (single a) (single 1) (single b) ≫ f)
      (necklace_relation a b)
    simp only [necklaceToEdge, ← Category.assoc, ← lastBlock_necklace] at h
    simpa only [Category.assoc] using h
  rw [h0, lastBlock_height_point, Category.assoc]

def firstToNecklace : firstQuotient a b ⟶ necklaceQuotient a b :=
  pushout.desc (simplexToNecklaceQuotient a b)
    (edgeZero ≫ edgeToNecklaceQuotient a b)
    (firstBlock_necklace_relation a b)

theorem simplexToFirst_toNecklace :
    simplexToFirst a b ≫ firstToNecklace a b =
      simplexToNecklaceQuotient a b :=
  pushout.inl_desc _ _ _

theorem firstPoint_toNecklace :
    firstPoint a b ≫ firstToNecklace a b =
      edgeZero ≫ edgeToNecklaceQuotient a b :=
  pushout.inr_desc _ _ _

def blockToNecklace : blockQuotient a b ⟶ necklaceQuotient a b :=
  pushout.desc (firstToNecklace a b)
    (edgeOne ≫ edgeToNecklaceQuotient a b) (by
      calc
        (lastBlock a b ≫ simplexToFirst a b) ≫ firstToNecklace a b =
            lastBlock a b ≫ simplexToNecklaceQuotient a b := by
              rw [Category.assoc, simplexToFirst_toNecklace]
        _ = (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
              edgeOne ≫ edgeToNecklaceQuotient a b :=
                lastBlock_necklace_relation a b)

theorem simplexToBlock_toNecklace :
    simplexToBlock a b ≫ blockToNecklace a b =
      simplexToNecklaceQuotient a b := by
  have h : pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
      blockToNecklace a b = firstToNecklace a b :=
    pushout.inl_desc _ _ _
  change simplexToFirst a b ≫
    (pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from _) ≫ blockToNecklace a b) =
      simplexToNecklaceQuotient a b
  rw [h, simplexToFirst_toNecklace]

theorem firstVertex_toNecklace :
    firstVertex a b ≫ blockToNecklace a b =
      edgeZero ≫ edgeToNecklaceQuotient a b := by
  have h : pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[b] : SSet.{0})) ≫
      blockToNecklace a b = firstToNecklace a b :=
    pushout.inl_desc _ _ _
  change firstPoint a b ≫
    (pushout.inl (lastBlock a b ≫ simplexToFirst a b)
      (SSet.stdSimplex.isTerminalObj₀.from _) ≫ blockToNecklace a b) =
      edgeZero ≫ edgeToNecklaceQuotient a b
  rw [h, firstPoint_toNecklace]

theorem lastVertex_toNecklace :
    lastVertex a b ≫ blockToNecklace a b =
      edgeOne ≫ edgeToNecklaceQuotient a b :=
  pushout.inr_desc _ _ _

theorem crossingEdge_necklace_relation :
    crossingEdge a b ≫ simplexToNecklaceQuotient a b =
      edgeToNecklaceQuotient a b := by
  have h0 : crossingEdge a b ≫ simplexToNecklaceQuotient a b =
      (crossingEdge a b ≫ height a b) ≫
        edgeToNecklaceQuotient a b := by
    apply (cancel_epi (singleIso.{0} 1).hom).mp
    have h := congrArg
      (fun f ↦ tripleRightU (single a) (single 1) (single b) ≫ f)
      (necklace_relation a b)
    simp only [necklaceToEdge, ← Category.assoc, ← crossingEdge_necklace] at h
    simpa only [Category.assoc] using h
  simpa only [crossingEdge_height, Category.id_comp] using h0

theorem edgeToBlock_toNecklace :
    edgeToBlock a b ≫ blockToNecklace a b =
      edgeToNecklaceQuotient a b := by
  rw [edgeToBlock, Category.assoc, simplexToBlock_toNecklace,
    crossingEdge_necklace_relation]

theorem necklaceToBlock_toNecklace :
    necklaceToBlock a b ≫ blockToNecklace a b =
      𝟙 (necklaceQuotient a b) := by
  apply pushout.hom_ext
  · change simplexToNecklaceQuotient a b ≫
        (necklaceToBlock a b ≫ blockToNecklace a b) =
        simplexToNecklaceQuotient a b ≫ 𝟙 _
    rw [← Category.assoc, simplexToNecklace_toBlock,
      simplexToBlock_toNecklace, Category.comp_id]
  · change edgeToNecklaceQuotient a b ≫
        (necklaceToBlock a b ≫ blockToNecklace a b) =
        edgeToNecklaceQuotient a b ≫ 𝟙 _
    rw [← Category.assoc, edgeToNecklace_toBlock,
      edgeToBlock_toNecklace, Category.comp_id]

theorem blockToNecklace_toBlock :
    blockToNecklace a b ≫ necklaceToBlock a b =
      𝟙 (blockQuotient a b) := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · change simplexToBlock a b ≫
          (blockToNecklace a b ≫ necklaceToBlock a b) =
          simplexToBlock a b ≫ 𝟙 _
      calc
        simplexToBlock a b ≫
            (blockToNecklace a b ≫ necklaceToBlock a b) =
            (simplexToBlock a b ≫ blockToNecklace a b) ≫
              necklaceToBlock a b := (Category.assoc _ _ _).symm
        _ = simplexToNecklaceQuotient a b ≫ necklaceToBlock a b :=
          congrArg (· ≫ necklaceToBlock a b)
            (simplexToBlock_toNecklace a b)
        _ = simplexToBlock a b := simplexToNecklace_toBlock a b
        _ = simplexToBlock a b ≫ 𝟙 _ := (Category.comp_id _).symm
    · change firstVertex a b ≫
          (blockToNecklace a b ≫ necklaceToBlock a b) =
          firstVertex a b ≫ 𝟙 _
      calc
        firstVertex a b ≫
            (blockToNecklace a b ≫ necklaceToBlock a b) =
            (firstVertex a b ≫ blockToNecklace a b) ≫
              necklaceToBlock a b := (Category.assoc _ _ _).symm
        _ = (edgeZero ≫ edgeToNecklaceQuotient a b) ≫
              necklaceToBlock a b :=
          congrArg (· ≫ necklaceToBlock a b)
            (firstVertex_toNecklace a b)
        _ = edgeZero ≫
              (edgeToNecklaceQuotient a b ≫ necklaceToBlock a b) :=
          Category.assoc _ _ _
        _ = edgeZero ≫ edgeToBlock a b := by
          rw [edgeToNecklace_toBlock]
        _ = firstVertex a b := edgeZero_toBlock a b
        _ = firstVertex a b ≫ 𝟙 _ := (Category.comp_id _).symm
  · change lastVertex a b ≫
        (blockToNecklace a b ≫ necklaceToBlock a b) =
        lastVertex a b ≫ 𝟙 _
    calc
      lastVertex a b ≫
          (blockToNecklace a b ≫ necklaceToBlock a b) =
          (lastVertex a b ≫ blockToNecklace a b) ≫
            necklaceToBlock a b := (Category.assoc _ _ _).symm
      _ = (edgeOne ≫ edgeToNecklaceQuotient a b) ≫
            necklaceToBlock a b :=
        congrArg (· ≫ necklaceToBlock a b)
          (lastVertex_toNecklace a b)
      _ = edgeOne ≫
            (edgeToNecklaceQuotient a b ≫ necklaceToBlock a b) :=
        Category.assoc _ _ _
      _ = edgeOne ≫ edgeToBlock a b := by
        rw [edgeToNecklace_toBlock]
      _ = lastVertex a b := edgeOne_toBlock a b
      _ = lastVertex a b ≫ 𝟙 _ := (Category.comp_id _).symm

/-- The literal two-collapse quotient is canonically the three-bead
necklace pushout, with all simplex and crossing-edge legs fixed. -/
def blockNecklaceIso : blockQuotient a b ≅ necklaceQuotient a b where
  hom := blockToNecklace a b
  inv := necklaceToBlock a b
  hom_inv_id := blockToNecklace_toBlock a b
  inv_hom_id := necklaceToBlock_toNecklace a b

theorem edgeToNecklace_weak :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (edgeToNecklaceQuotient a b) := by
  let h : IsPushout (code a b).inclusion (necklaceToEdge a b)
      (simplexToNecklaceQuotient a b)
      (edgeToNecklaceQuotient a b) := IsPushout.of_hasPushout _ _
  exact DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout h
    (DaggerActualOriginalNecklaceInclusionWeak.original_inclusion_weak
      (code a b))

theorem edgeToBlock_weak :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (edgeToBlock a b) := by
  haveI : IsIso (necklaceToBlock a b) := by
    change IsIso (blockNecklaceIso a b).inv
    infer_instance
  have hi : DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (necklaceToBlock a b) :=
    MorphismProperty.of_isIso _ _
  have h := DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.comp_mem
    (edgeToNecklaceQuotient a b) (necklaceToBlock a b)
    (edgeToNecklace_weak a b) hi
  rw [edgeToNecklace_toBlock] at h
  exact h

/-- The projection of the independently formed literal two-collapse
quotient is weak in the original Joyal class, including both zero-length
end-bead cases. -/
theorem blockProjection_weak :
    DaggerNativeJoyalMappingTest.weakCategoricalEquivalences
      (blockProjection a b) := by
  exact DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.of_precomp
    (edgeToBlock a b) (blockProjection a b) (edgeToBlock_weak a b)
    ((edgeToBlock_projection a b).symm ▸
      DaggerNativeJoyalMappingTest.weakCategoricalEquivalences.id_mem
        (Δ[1] : SSet.{0}))

end

end DaggerModels.PartII.JTCylinderBlockQuotient
