import DaggerModelsPartII.JTOrderedLabelBinaryGlue
import DaggerModelsPartII.OrderedLabelElements

/-!
# Binary wedge of actual ordered necklace labels

Two ordered labels at a common simplex degree, with the same literal middle
zero-row vertex, determine an ordered label on their native binary wedge.
The construction retains the complete coefficient and both native legs.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTOrderedLabelWedge

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open TripleBeadEndpointLabel ReversalDiscreteFreeColimits

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev K (k : SimplexCategory) : SSet.{0} := SSet.stdSimplex.obj k
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)

/-- Two original ordered labels with a shared literal middle vertex. -/
structure Inputs (W : Source) (T U : NCode) (k : SimplexCategory)
    (x z y : Vertex W) where
  left : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k)
  right : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op k)

variable {W : Source} {T U : NCode} {k : SimplexCategory}
variable {x z y : Vertex W}

def leftCoefficient (a : Inputs W T U k x z y) : K k ⟶ labels W T :=
  JTOrderedLabelBinaryGlue.coefficient W x z T k a.left

def rightCoefficient (a : Inputs W T U k x z y) : K k ⟶ labels W U :=
  JTOrderedLabelBinaryGlue.coefficient W z y U k a.right

private theorem joint (a : Inputs W T U k x z y) :
    leftCoefficient a ≫ lastRestriction W T =
      rightCoefficient a ≫ firstRestriction W U := by
  rw [leftCoefficient, JTOrderedLabelBinaryGlue.coefficient_last]
  rw [rightCoefficient, JTOrderedLabelBinaryGlue.coefficient_first]

/-- The complete joined coefficient on the actual native wedge. -/
def joinedLabel (a : Inputs W T U k x z y) : K k ⟶ labels W (wedge T U) :=
  glue W T U k (leftCoefficient a) (rightCoefficient a) (joint a)

theorem joinedLabel_left (a : Inputs W T U k x z y) :
    joinedLabel a ≫ diagramMappingPrecomp (F.map (wedgeιLeft T U)) W =
      leftCoefficient a :=
  glue_left W T U k (leftCoefficient a) (rightCoefficient a) (joint a)

theorem joinedLabel_right (a : Inputs W T U k x z y) :
    joinedLabel a ≫ diagramMappingPrecomp (F.map (wedgeιRight T U)) W =
      rightCoefficient a :=
  glue_right W T U k (leftCoefficient a) (rightCoefficient a) (joint a)

private theorem boundary_first (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      firstRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inl W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inl_desc, firstRestriction]
  rfl

private theorem boundary_last (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      lastRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inr W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inr_desc, lastRestriction]
  rfl

/-- The two complete endpoint equations determine the ordered boundary. -/
theorem joinedLabel_boundary (a : Inputs W T U k x z y) :
    joinedLabel a ≫ (necklaceBoundaryRestriction W).app (op (wedge T U)) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ boundaryPoint W x y := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst]
    rw [boundary_first]
    rw [show joinedLabel a ≫ firstRestriction W (wedge T U) =
      leftCoefficient a ≫ firstRestriction W T from
      glue_first W T U k (leftCoefficient a) (rightCoefficient a) (joint a)]
    rw [leftCoefficient, JTOrderedLabelBinaryGlue.coefficient_first,
      boundaryPoint_first]
  · simp only [Category.assoc, boundaryMappingIso_snd]
    rw [boundary_last]
    rw [show joinedLabel a ≫ lastRestriction W (wedge T U) =
      rightCoefficient a ≫ lastRestriction W U from
      glue_last W T U k (leftCoefficient a) (rightCoefficient a) (joint a)]
    rw [rightCoefficient, JTOrderedLabelBinaryGlue.coefficient_last,
      boundaryPoint_last]

/-- The ordered simplex in the original ordered boundary pullback. -/
def joinedPoint (a : Inputs W T U k x z y) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (wedge T U))).obj
      (op k) :=
  SSet.yonedaEquiv (pullback.lift (joinedLabel a)
    (SSet.stdSimplex.isTerminalObj₀.from (K k)) (joinedLabel_boundary a))

theorem joinedPoint_coefficient (a : Inputs W T U k x z y) :
    JTRealizedLabelEndpoints.orderedLabel W x y (wedge T U) k (joinedPoint a) =
      SSet.yonedaEquiv (joinedLabel a) := by
  dsimp only [JTRealizedLabelEndpoints.orderedLabel, joinedPoint]
  erw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
  rfl

theorem joinedPoint_left (a : Inputs W T U k x z y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge T U) k (joinedPoint a) ≫
      diagramMappingPrecomp (F.map (wedgeιLeft T U)) W = leftCoefficient a := by
  rw [JTOrderedLabelBinaryGlue.coefficient, joinedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact joinedLabel_left a

theorem joinedPoint_right (a : Inputs W T U k x z y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge T U) k (joinedPoint a) ≫
      diagramMappingPrecomp (F.map (wedgeιRight T U)) W = rightCoefficient a := by
  rw [JTOrderedLabelBinaryGlue.coefficient, joinedPoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact joinedLabel_right a

/-- The coefficient in the mapping space is the first projection of an ordered label. -/
theorem coefficient_projection (W : Source) (x y : Vertex W)
    (T : NCode) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    JTOrderedLabelBinaryGlue.coefficient W x y T k a =
      SSet.yonedaEquiv.symm a ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y) := by
  apply SSet.yonedaEquiv.injective
  simp only [JTOrderedLabelBinaryGlue.coefficient, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, JTRealizedLabelEndpoints.orderedLabel]

/-- A coefficient determines its ordered point because the second ordered
pullback projection is the unique map to the terminal simplex. -/
theorem coefficient_injective (W : Source) (x y : Vertex W) (T : NCode)
    (k : SimplexCategory) :
    Function.Injective (JTOrderedLabelBinaryGlue.coefficient W x y T k) := by
  intro a b h
  apply SSet.yonedaEquiv.symm.injective
  apply pullback.hom_ext
  · rw [← coefficient_projection W x y T k a,
      ← coefficient_projection W x y T k b]
    exact h
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem coefficient_native_ordinal (W : Source) (x y : Vertex W)
    {S T : NCode} (f : S ⟶ T) {k l : SimplexCategory} (r : k ⟶ l)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    JTOrderedLabelBinaryGlue.coefficient W x y S k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map r.op
          (((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app (op l) a)) =
      SSet.stdSimplex.map r ≫
        JTOrderedLabelBinaryGlue.coefficient W x y T l a ≫
          diagramMappingPrecomp (F.map f.map) W := by
  let G := orderedNecklaceLabels W (boundaryPoint W x y)
  let pS := pullback.fst ((necklaceBoundaryRestriction W).app (op S))
    (boundaryPoint W x y)
  let pT := pullback.fst ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)
  have hp : G.map f.op ≫ pS = pT ≫ diagramMappingPrecomp (F.map f.map) W := by
    simp only [G, pS, pT, orderedNecklaceLabels, orderedLabelDiagram,
      pullback.map, pullback.lift_fst]
    rfl
  have hn := congrFun (NatTrans.congr_app hp (op l)) a
  change pS.app (op l) ((G.map f.op).app (op l) a) =
    (diagramMappingPrecomp (F.map f.map) W).app (op l) (pT.app (op l) a) at hn
  rw [coefficient_projection, coefficient_projection,
    SSet.yonedaEquiv_symm_map, Category.assoc]
  rw [SSet.yonedaEquiv_symm_comp, hn, ← SSet.yonedaEquiv_symm_comp,
    ← SSet.yonedaEquiv_symm_comp]
  rfl

/-- An ordered index arrow is determined by a coefficient equation together
with its specified native and ordinal operators. -/
def indexHomOfCoefficient {S T : NCode} {i j : SimplexCategory}
    (f : S ⟶ T) (r : i ⟶ j)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op i))
    (b : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op j))
    (h : JTOrderedLabelBinaryGlue.coefficient W x y S i a =
      SSet.stdSimplex.map r ≫ JTOrderedLabelBinaryGlue.coefficient W x y T j b ≫
        diagramMappingPrecomp (F.map f.map) W) :
    OrderedLabelElements.mk W (boundaryPoint W x y) S i a ⟶
      OrderedLabelElements.mk W (boundaryPoint W x y) T j b := by
  let P := OrderedLabelElements.labelPresheaf W (boundaryPoint W x y)
  refine (CategoryOfElements.homMk
    (P.elementsMk (op (T, j)) b) (P.elementsMk (op (S, i)) a)
    ((show (S, i) ⟶ (T, j) from (f, r)).op) ?_).op
  exact coefficient_injective W x y S i
    ((coefficient_native_ordinal W x y f r b).trans h.symm)

theorem indexHomOfCoefficient_projection {S T : NCode} {i j : SimplexCategory}
    (f : S ⟶ T) (r : i ⟶ j)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op i))
    (b : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op j))
    (h : JTOrderedLabelBinaryGlue.coefficient W x y S i a =
      SSet.stdSimplex.map r ≫ JTOrderedLabelBinaryGlue.coefficient W x y T j b ≫
        diagramMappingPrecomp (F.map f.map) W) :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map
      (indexHomOfCoefficient f r a b h) = (f, r) := rfl

/-- The original decorated index carrying the joined ordered label. -/
def joinedIndex (a : Inputs W T U k x z y) :
    OrderedLabelElements.Index W (boundaryPoint W x y) :=
  OrderedLabelElements.mk W (boundaryPoint W x y) (wedge T U) k (joinedPoint a)

private theorem joinedPoint_full_coefficient (a : Inputs W T U k x z y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge T U) k (joinedPoint a) =
      joinedLabel a := by
  rw [JTOrderedLabelBinaryGlue.coefficient, joinedPoint_coefficient]
  exact Equiv.symm_apply_apply _ _

/-- An actual ordered-label arrow restricts its coefficient by both projected operators. -/
theorem coefficient_of_indexHom {S T : NCode} {i j : SimplexCategory}
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).obj (op i))
    (b : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op j))
    (f : S ⟶ T) (r : i ⟶ j)
    (u : OrderedLabelElements.mk W (boundaryPoint W x y) S i a ⟶
      OrderedLabelElements.mk W (boundaryPoint W x y) T j b)
    (hu : (OrderedLabelElements.projection W (boundaryPoint W x y)).map u = (f, r)) :
    JTOrderedLabelBinaryGlue.coefficient W x y S i a =
      SSet.stdSimplex.map r ≫ JTOrderedLabelBinaryGlue.coefficient W x y T j b ≫
        diagramMappingPrecomp (F.map f.map) W := by
  have hlabel := OrderedLabelElements.label_map W (boundaryPoint W x y) u
  rw [hu] at hlabel
  change ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op S)).map r.op
      (((orderedNecklaceLabels W (boundaryPoint W x y)).map f.op).app (op j) b) = a
    at hlabel
  rw [← hlabel]
  exact coefficient_native_ordinal W x y f r b

private theorem wedge_precomp (W : Source) {S S' T T' : NCode}
    (f : S ⟶ S') (g : T ⟶ T') :
    diagramMappingPrecomp (F.map (wedgeMap f g).map) W ≫
      diagramMappingPrecomp (F.map (wedgeιLeft S T)) W =
        diagramMappingPrecomp (F.map (wedgeιLeft S' T')) W ≫
          diagramMappingPrecomp (F.map f.map) W := by
  rw [← diagramMappingPrecomp_comp, ← F.map_comp, wedgeMap_left,
    F.map_comp, diagramMappingPrecomp_comp]

private theorem wedge_precomp_right (W : Source) {S S' T T' : NCode}
    (f : S ⟶ S') (g : T ⟶ T') :
    diagramMappingPrecomp (F.map (wedgeMap f g).map) W ≫
      diagramMappingPrecomp (F.map (wedgeιRight S T)) W =
        diagramMappingPrecomp (F.map (wedgeιRight S' T')) W ≫
          diagramMappingPrecomp (F.map g.map) W := by
  rw [← diagramMappingPrecomp_comp, ← F.map_comp, wedgeMap_right,
    F.map_comp, diagramMappingPrecomp_comp]

variable {T' U' : NCode} {l : SimplexCategory}

/-- Pair two original decorated arrows with the same ordinal operator.
The native operator is the literal `wedgeMap` of the two original operators. -/
def joinedIndexHom (a : Inputs W T U k x z y) (b : Inputs W T' U' l x z y)
    (f : T ⟶ T') (g : U ⟶ U') (r : k ⟶ l)
    (left : OrderedLabelElements.mk W (boundaryPoint W x z) T k a.left ⟶
      OrderedLabelElements.mk W (boundaryPoint W x z) T' l b.left)
    (right : OrderedLabelElements.mk W (boundaryPoint W z y) U k a.right ⟶
      OrderedLabelElements.mk W (boundaryPoint W z y) U' l b.right)
    (hl : (OrderedLabelElements.projection W (boundaryPoint W x z)).map left =
      (f, r))
    (hr : (OrderedLabelElements.projection W (boundaryPoint W z y)).map right =
      (g, r)) : joinedIndex a ⟶ joinedIndex b := by
  have hleft := coefficient_of_indexHom a.left b.left f r left hl
  have hright := coefficient_of_indexHom a.right b.right g r right hr
  have hjoined : joinedLabel a = SSet.stdSimplex.map r ≫ joinedLabel b ≫
      diagramMappingPrecomp (F.map (wedgeMap f g).map) W := by
    apply (wedgeMappingPullback W T U).hom_ext
    · calc
        joinedLabel a ≫ diagramMappingPrecomp (F.map (wedgeιLeft T U)) W =
            leftCoefficient a := joinedLabel_left a
        _ = SSet.stdSimplex.map r ≫ leftCoefficient b ≫
            diagramMappingPrecomp (F.map f.map) W := hleft
        _ = SSet.stdSimplex.map r ≫ joinedLabel b ≫
            diagramMappingPrecomp (F.map (wedgeMap f g).map) W ≫
              diagramMappingPrecomp (F.map (wedgeιLeft T U)) W := by
          rw [← joinedLabel_left b]
          simp only [Category.assoc]
          rw [wedge_precomp W f g]
    · calc
        joinedLabel a ≫ diagramMappingPrecomp (F.map (wedgeιRight T U)) W =
            rightCoefficient a := joinedLabel_right a
        _ = SSet.stdSimplex.map r ≫ rightCoefficient b ≫
            diagramMappingPrecomp (F.map g.map) W := hright
        _ = SSet.stdSimplex.map r ≫ joinedLabel b ≫
            diagramMappingPrecomp (F.map (wedgeMap f g).map) W ≫
              diagramMappingPrecomp (F.map (wedgeιRight T U)) W := by
          rw [← joinedLabel_right b]
          simp only [Category.assoc]
          rw [wedge_precomp_right W f g]
  exact indexHomOfCoefficient (wedgeMap f g) r (joinedPoint a) (joinedPoint b)
    ((joinedPoint_full_coefficient a).trans
      (hjoined.trans (by rw [joinedPoint_full_coefficient b])))

theorem joinedIndexHom_projection (a : Inputs W T U k x z y)
    (b : Inputs W T' U' l x z y) (f : T ⟶ T') (g : U ⟶ U') (r : k ⟶ l)
    (left : OrderedLabelElements.mk W (boundaryPoint W x z) T k a.left ⟶
      OrderedLabelElements.mk W (boundaryPoint W x z) T' l b.left)
    (right : OrderedLabelElements.mk W (boundaryPoint W z y) U k a.right ⟶
      OrderedLabelElements.mk W (boundaryPoint W z y) U' l b.right)
    (hl : (OrderedLabelElements.projection W (boundaryPoint W x z)).map left =
      (f, r))
    (hr : (OrderedLabelElements.projection W (boundaryPoint W z y)).map right =
      (g, r)) :
    (OrderedLabelElements.projection W (boundaryPoint W x y)).map
      (joinedIndexHom a b f g r left right hl hr) = (wedgeMap f g, r) := rfl

end

end DaggerModels.PartII.JTOrderedLabelWedge
