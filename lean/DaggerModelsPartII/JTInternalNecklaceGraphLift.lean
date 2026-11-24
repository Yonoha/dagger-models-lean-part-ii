import DaggerModelsPartII.JTNecklaceCylinderConnector
import DaggerModelsPartII.NecklaceCylinderAugmentation
import DaggerModelsPartII.JTGraphBinaryTraversal
import OriginalFlagSourceAssemblyIso

/-!
# An internal native necklace admits a graph lift after a native collapse

Lift each bead in the actual reduced cylinder. A connector at a joint
repairs a discrepancy between its two parameter lifts and is constant
in the reduced cylinder. The assembly uses the original source prefix.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTInternalNecklaceGraphLift

open JTNecklaceEndpointCylinder JTNecklaceCylinderSimplexLift
open DaggerOriginalFlagFlankification

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev C (T : NecklaceCode) (k : SimplexCategory) := (value T).obj k
private abbrev cyl (T : NecklaceCode) (k : SimplexCategory) := (cylinder T).app k
private abbrev aug := NecklaceCylinderAugmentation.augmentation

variable {T : NecklaceCode} {k : SimplexCategory}

/-- The complete graph with horizontal map induced by the actual
augmentation of the given traversal. -/
def graph {X : SSet.{0}} (u : X ⟶ C T k) (s : X ⟶ J.obj k) : X ⟶ C T k :=
  lift (u ≫ aug T k) s ≫ cyl T k

theorem graph_comp {X Y : SSet.{0}} (f : X ⟶ Y) (u : Y ⟶ C T k) (s : Y ⟶ J.obj k) :
    f ≫ graph u s = graph (f ≫ u) (f ≫ s) := by
  unfold graph
  rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.assoc f u]

/-- Retain the complete original traversal after collapsing only the
added parts of its native graph lift. -/
structure Lift {a b : (C T k).obj (op ⦋0⦌)} (P : NecklacesOver (C T k) a b) where
  code : NecklaceCode
  collapse : code ⟶ P.code
  parameter : code.toSSet ⟶ J.obj k
  comm : graph (collapse.map ≫ P.map) parameter = collapse.map ≫ P.map

/-- A traversal on a simplicial set isomorphic to a simplex lifts with its original domain. -/
theorem exists_parameter_on_simplex {X : SSet.{0}} {d : ℕ}
    (e : X ≅ (Δ[d] : SSet.{0})) (u : X ⟶ C T k) :
    ∃ s : X ⟶ J.obj k, graph u s = u := by
  let m := e.inv ≫ u
  obtain ⟨z, hz⟩ := simplex_lift T k d (SSet.yonedaEquiv m)
  let Z := e.hom ≫ SSet.yonedaEquiv.symm z
  have h₀ : SSet.yonedaEquiv.symm z ≫ cyl T k = m := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz
  have h₁ : Z ≫ cyl T k = u := by
    dsimp only [Z, m] at *
    rw [Category.assoc, h₀, Iso.hom_inv_id_assoc]
  have h₂ : Z ≫ fst (T.toSSet) (J.obj k) = u ≫ aug T k := by
    rw [← NecklaceCylinderAugmentation.augmentation_cylinder, ← Category.assoc, h₁]
  have h₃ : lift (u ≫ aug T k) (Z ≫ snd T.toSSet (J.obj k)) = Z := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst, h₂]
    · rw [lift_snd]
  refine ⟨Z ≫ snd T.toSSet (J.obj k), ?_⟩
  rw [graph, h₃, h₁]

/-- Every original single-bead traversal lifts on the same native code. -/
theorem single_lift (d : ℕ) {a b : (C T k).obj (op ⦋0⦌)} (P : NecklacesOver (C T k) a b)
    (hP : P.code = single d) : Nonempty (Lift P) := by
  obtain ⟨U, u, hu₀, hu₁⟩ := P
  change U = single d at hP
  subst U
  obtain ⟨s, hs⟩ := exists_parameter_on_simplex (singleIso d) u
  refine ⟨⟨single d, 𝟙 _, s, ?_⟩⟩
  change graph (𝟙 _ ≫ u) s = 𝟙 _ ≫ u
  simpa only [Category.id_comp] using hs

variable {a b c : (C T k).obj (op ⦋0⦌)}
variable {P : NecklacesOver (C T k) a b} {Q : NecklacesOver (C T k) b c}
variable (D : Lift P) (E : Lift Q)

private abbrev A := single 1
private abbrev G := wedge D.code (wedge A E.code)
private abbrev L := tripleRightT.{0} D.code A E.code
private abbrev M := tripleRightU.{0} D.code A E.code
private abbrev U := tripleRightV.{0} D.code A E.code

private abbrev firstPoint (T : NecklaceCode) := pointAt T (ULift.up 0)
private abbrev lastPoint (T : NecklaceCode) := pointAt T (ULift.up (Fin.last T.len))
private abbrev terminalFrom := SSet.stdSimplex.isTerminalObj₀.from A.toSSet

private def collapse : G D E ⟶ (NecklacesOver.wedge P Q).code :=
  JTGraphBinaryTraversal.collapse D.code E.code ≫ wedgeMap D.collapse E.collapse

private def joinedMap : (G D E).toSSet ⟶ C T k :=
  (collapse D E).map ≫ (NecklacesOver.wedge P Q).map

private def joint : (Δ[0] : SSet.{0}) ⟶ C T k :=
  lastPoint P.code ≫ P.map

private theorem joinedMap_left :
    L D E ≫ joinedMap D E = D.collapse.map ≫ P.map := by
  unfold joinedMap
  change L D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map = _
  rw [← Category.assoc (L D E), ← Category.assoc (L D E),
    JTGraphBinaryTraversal.collapse_left, wedgeMap_left, Category.assoc,
    NecklacesOver.wedge_left]

private theorem joinedMap_right :
    U D E ≫ joinedMap D E = E.collapse.map ≫ Q.map := by
  unfold joinedMap
  change U D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map = _
  rw [← Category.assoc (U D E), ← Category.assoc (U D E),
    JTGraphBinaryTraversal.collapse_right, wedgeMap_right, Category.assoc,
    NecklacesOver.wedge_right]

private theorem joinedMap_middle :
    M D E ≫ joinedMap D E = terminalFrom ≫ joint (P := P) := by
  unfold joinedMap
  change M D E ≫ ((JTGraphBinaryTraversal.collapse D.code E.code).map ≫
      (wedgeMap D.collapse E.collapse).map) ≫ (NecklacesOver.wedge P Q).map = _
  rw [← Category.assoc (M D E), ← Category.assoc (M D E),
    JTGraphBinaryTraversal.collapse_middle, JTGraphBinaryTraversal.joint]
  simp only [Category.assoc]
  rw [← Category.assoc (wedgeιLeft D.code E.code), wedgeMap_left, Category.assoc,
    NecklacesOver.wedge_left, ← Category.assoc (lastPoint D.code), pointAt_last_comp]
  rfl

private theorem left_joint :
    graph (joint (P := P)) (lastPoint D.code ≫ D.parameter) = joint (P := P) := by
  have h := congrArg (fun z ↦ lastPoint D.code ≫ z) D.comm
  dsimp only at h
  rw [graph_comp, ← Category.assoc (lastPoint D.code), pointAt_last_comp] at h
  exact h

private theorem right_joint :
    graph (joint (P := P)) (firstPoint E.code ≫ E.parameter) = joint (P := P) := by
  have h := congrArg (fun z ↦ firstPoint E.code ≫ z) E.comm
  dsimp only at h
  rw [graph_comp, ← Category.assoc (firstPoint E.code), pointAt_first_comp,
    ← NecklacesOver.wedge_compat P Q] at h
  exact h

/-- The full finite wedge lift, inserting a connector only in the
parameter direction at the joint. The connector collapses in the
original reduced cylinder. -/
def wedgeLift : Lift (NecklacesOver.wedge P Q) := by
  let u := lastPoint D.code ≫ D.parameter
  let v := firstPoint E.code ≫ E.parameter
  have h := (left_joint D).trans (right_joint (P := P) E).symm
  let hc := JTNecklaceCylinderConnector.exists_connector T k (joint (P := P) ≫ aug T k)
    u v h
  let s := Classical.choose hc
  have hs := Classical.choose_spec hc
  let p := tripleRightDesc D.code A E.code D.parameter s E.parameter hs.1.symm hs.2.1
  refine ⟨G D E, collapse D E, p, ?_⟩
  change graph (joinedMap D E) p = joinedMap D E
  apply tripleRight_hom_ext (T := D.code) (U := A) (V := E.code)
  · rw [graph_comp, joinedMap_left]
    change graph _ (tripleRightT D.code A E.code ≫ p) = _
    dsimp only [p]
    rw [tripleRightDesc_T]
    exact D.comm
  · rw [graph_comp, joinedMap_middle]
    change graph _ (tripleRightU D.code A E.code ≫ p) = _
    dsimp only [p]
    rw [tripleRightDesc_U, graph, Category.assoc]
    exact hs.2.2.trans (congrArg (fun q ↦ terminalFrom ≫ q) (left_joint D))
  · rw [graph_comp, joinedMap_right]
    change graph _ (tripleRightV D.code A E.code ≫ p) = _
    dsimp only [p]
    rw [tripleRightDesc_V]
    exact E.comm

private theorem prefix_lift {a b : (C T k).obj (op ⦋0⦌)}
    (P : NecklacesOver (C T k) a b) (n : ℕ) (hn : n ≤ beadCount P.code) :
    Nonempty (Lift (orderedPrefix P n hn).source) := by
  induction n with
  | zero =>
    exact single_lift 0 _ (code_zero_eq_point (single 0) rfl).symm
  | succ n ih =>
    let i : Fin (beadCount P.code) := ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
    let c := jointBead P.code i
    obtain ⟨D⟩ := ih (Nat.le_of_succ_le hn)
    obtain ⟨E⟩ := single_lift c.length (sourceBeadOver P c) rfl
    exact ⟨wedgeLift D E⟩

/-- Every internal finite native necklace in the original cylinder has
a graph lift after a native code map, retaining its whole cylinder map. -/
theorem nonempty_lift {a b : (C T k).obj (op ⦋0⦌)}
    (P : NecklacesOver (C T k) a b) : Nonempty (Lift P) := by
  obtain ⟨D⟩ := prefix_lift P (beadCount P.code) le_rfl
  let f := (sourceAssemblyIso P).hom
  refine ⟨⟨D.code, D.collapse ≫ f.hom, D.parameter, ?_⟩⟩
  change graph ((D.collapse.map ≫ f.hom.map) ≫ P.map) D.parameter =
    (D.collapse.map ≫ f.hom.map) ≫ P.map
  rw [Category.assoc, f.w]
  exact D.comm

end

end DaggerModels.PartII.JTInternalNecklaceGraphLift
