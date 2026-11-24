import DaggerModelsPartII.JTBinaryPrismParameter
import DaggerModelsPartII.JTBinaryPrismLabelOperators

/-! The joined ordered label retains both native side operators. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismNativeLabels

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open TripleBeadEndpointLabel (labels wedgeMappingPullback)
open JTOrderedLabelBinaryGlue
open JTBinaryPrismParameter (sideMap sideMap_left sideMap_middle sideMap_right)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev F := discreteFree.{0}
private abbrev A := single 1

variable {W : Source} {x z y : Vertex W}

private abbrev restrictLabel (W : Source) (x y : Vertex W) {S T : NecklaceCode}
    (f : S ⟶ T) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :=
  ((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app (op k) a

private abbrev pre (W : Source) {S T : SSet.{0}} (f : S ⟶ T) :=
  diagramMappingPrecomp (F.map f) W

private theorem pre_comp (W : Source) {S T U : SSet.{0}} (f : S ⟶ T) (g : T ⟶ U) :
    pre W (f ≫ g) = pre W g ≫ pre W f := by
  dsimp only [pre]
  rw [F.map_comp, diagramMappingPrecomp_comp]

private theorem coefficient_native {S T : NecklaceCode} (f : S ⟶ T) (k : SimplexCategory)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y S k (restrictLabel W x y f k u) =
      coefficient W x y T k u ≫ pre W f.map := by
  let G := orderedNecklaceLabels W (boundaryPoint W x y)
  let pS := pullback.fst ((necklaceBoundaryRestriction W).app (op S)) (boundaryPoint W x y)
  let pT := pullback.fst ((necklaceBoundaryRestriction W).app (op T)) (boundaryPoint W x y)
  have h : G.map f.op ≫ pS = pT ≫ pre W f.map := by
    simp only [G, pS, pT, orderedNecklaceLabels, orderedLabelDiagram,
      pullback.map, pullback.lift_fst]
    rfl
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [coefficient, Equiv.apply_symm_apply, JTRealizedLabelEndpoints.orderedLabel]
  exact congrFun (NatTrans.congr_app h (op k)) u

private theorem coefficient_injective (W : Source) (x y : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) : Function.Injective (coefficient W x y T k) := by
  intro u v h
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · let π := pullback.fst ((necklaceBoundaryRestriction W).app (op T)) (boundaryPoint W x y)
    exact (SSet.yonedaEquiv_symm_comp u π).trans (h.trans (SSet.yonedaEquiv_symm_comp v π).symm)
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable {L R L' R' : NecklaceCode} {k : SimplexCategory}
variable (f : L ⟶ L') (g : R ⟶ R') (a : Inputs W L' R' k x z y)

/-- Restrict both original side labels along their native operators. -/
def restrictInputs : Inputs W L R k x z y where
  left := restrictLabel W x z f k a.left
  right := restrictLabel W z y g k a.right

private theorem triple_label_ext {X : SSet.{0}} {u v : X ⟶ labels W (code L R)}
    (hl : u ≫ pre W (tripleRightT L A R) = v ≫ pre W (tripleRightT L A R))
    (hm : u ≫ pre W (tripleRightU L A R) = v ≫ pre W (tripleRightU L A R))
    (hr : u ≫ pre W (tripleRightV L A R) = v ≫ pre W (tripleRightV L A R)) : u = v := by
  apply (wedgeMappingPullback W L (wedge A R)).hom_ext
  · exact hl
  · apply (wedgeMappingPullback W A R).hom_ext
    · simpa only [Category.assoc, ← pre_comp, tripleRightU] using hm
    · simpa only [Category.assoc, ← pre_comp, tripleRightV] using hr

/-- The actual ordered label of the joined comparison restricts along
the two native side maps, with the inserted connector unchanged. -/
theorem orderedTriplePoint_native :
    restrictLabel W x y (sideMap f g) k (orderedTriplePoint a) =
      orderedTriplePoint (restrictInputs f g a) := by
  apply coefficient_injective W x y (code L R) k
  rw [coefficient_native]
  apply triple_label_ext
  · rw [Category.assoc, ← pre_comp, sideMap_left, pre_comp, ← Category.assoc]
    calc
      _ = leftCoefficient a ≫ pre W f.map :=
        congrArg (fun h ↦ h ≫ pre W f.map) (orderedTriplePoint_left a)
      _ = leftCoefficient (restrictInputs f g a) := (coefficient_native f k a.left).symm
      _ = _ := (orderedTriplePoint_left (restrictInputs f g a)).symm
  · rw [Category.assoc, ← pre_comp, sideMap_middle]
    exact (orderedTriplePoint_middle a).trans
      (orderedTriplePoint_middle (restrictInputs f g a)).symm
  · rw [Category.assoc, ← pre_comp, sideMap_right, pre_comp, ← Category.assoc]
    calc
      _ = rightCoefficient a ≫ pre W g.map :=
        congrArg (fun h ↦ h ≫ pre W g.map) (orderedTriplePoint_right a)
      _ = rightCoefficient (restrictInputs f g a) := (coefficient_native g k a.right).symm
      _ = _ := (orderedTriplePoint_right (restrictInputs f g a)).symm


open JTBinaryPrismRealization (blockInputs)
open JTParameterBlocks (common leftRet rightRet)

variable {l : SimplexCategory}
variable (u : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op L')).obj (op k))
variable (v : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op R')).obj (op l))

private theorem blockInputs_native :
    restrictInputs f g (blockInputs u v) =
      blockInputs (restrictLabel W x z f k u) (restrictLabel W z y g l v) := by
  refine congrArg₂ (Inputs.mk (W := W) (T := L) (U := R) (k := common k l)
    (x := x) (z := z) (y := y)) ?_ ?_
  · exact congrFun (((orderedNecklaceLabels W (boundaryPoint W x z)).map f.op).naturality
      (leftRet k l).op) u
  · exact congrFun (((orderedNecklaceLabels W (boundaryPoint W z y)).map g.op).naturality
      (rightRet k l).op) v

/-- The coefficient blocks commute with restriction in the two native axes. -/
theorem blockLabel_native :
    restrictLabel W x y (sideMap f g) (common k l) (orderedTriplePoint (blockInputs u v)) =
      orderedTriplePoint (blockInputs (restrictLabel W x z f k u) (restrictLabel W z y g l v)) := by
  rw [orderedTriplePoint_native, blockInputs_native]


open OrderedLabelElements (projection)

section Mixed

variable {k₀ l₀ : SimplexCategory} (α : k₀ ⟶ k) (β : l₀ ⟶ l)
variable (hα : α.toOrderHom (Fin.last k₀.len) = Fin.last k.len) (hβ : β.toOrderHom 0 = 0)

private abbrev outerLabels := orderedNecklaceLabels W (boundaryPoint W x y)
private abbrev sourceLeft :=
  ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op L)).map α.op
    (restrictLabel W x z f k u)
private abbrev sourceRight :=
  ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op R)).map β.op
    (restrictLabel W z y g l v)
private abbrev block := JTParameterBlockOperators.map α β

private abbrev indexOf {T U : NecklaceCode} {i j : SimplexCategory}
    (a : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op i))
    (b : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op j)) :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (code T U) (common i j)
    (orderedTriplePoint (blockInputs a b))

/-- The category of original decorated labels receives the actual native
and coefficient operators in a single arrow. -/
def labelArrow :
    indexOf (sourceLeft f u α) (sourceRight g v β) ⟶ indexOf u v := by
  let A := (indexOf u v).unop
  let B := (indexOf (sourceLeft f u α) (sourceRight g v β)).unop
  let m : (code L R, common k₀ l₀) ⟶ (code L' R', common k l) :=
    (sideMap f g, block α β)
  refine (CategoryOfElements.homMk A B m.op ?_).op
  change ((outerLabels (W := W) (x := x) (y := y)).obj (op (code L R))).map (block α β).op
      (restrictLabel W x y (sideMap f g) (common k l) (orderedTriplePoint (blockInputs u v))) =
    orderedTriplePoint (blockInputs (sourceLeft f u α) (sourceRight g v β))
  rw [blockLabel_native f g u v]
  exact JTBinaryPrismLabelOperators.label_map _ _ α β hα hβ

/-- Both underlying operators of this arrow are the original specified operators. -/
theorem labelArrow_projection :
    (projection W (boundaryPoint W x y)).map (labelArrow f g u v α β hα hβ) =
      (sideMap f g, block α β) := rfl

end Mixed

end

end DaggerModels.PartII.JTBinaryPrismNativeLabels
