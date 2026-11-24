import DaggerModelsPartII.JTGraphRefinement
import DaggerModelsPartII.TripleBeadEndpointLabel
import DaggerModelsPartII.OrderedLabelElements

/-!
# Ordered finite-necklace binary composition with an identity bead

Two actual ordered necklace simplices at the same parameter degree are joined
through the actual single identity bead. The three coefficient restrictions
are equalities of entire `Δ[k]` families. This is a point-set construction;
no finality or weak equivalence is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTOrderedLabelBinaryGlue

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open TripleBeadEndpointLabel ReversalDiscreteFreeColimits

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev NCode := DaggerChosenRigidificationNecklace.NecklaceCode
private abbrev K (k : SimplexCategory) : SSet.{0} := SSet.stdSimplex.obj k
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)

/-- The actual native code of the three parts. -/
def code (T U : NCode) : NCode := wedge T (wedge (single 1) U)

/-- The full coefficient of an actual ordered simplex. -/
def coefficient (W : Source) (x y : Vertex W) (T : NCode)
    (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    K k ⟶ labels W T :=
  SSet.yonedaEquiv.symm (JTRealizedLabelEndpoints.orderedLabel W x y T k a)

private theorem coefficient_eq_projection (W : Source) (x y : Vertex W)
    (T : NCode) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y T k a =
      SSet.yonedaEquiv.symm a ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y) := by
  apply SSet.yonedaEquiv.injective
  simp only [coefficient, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply, JTRealizedLabelEndpoints.orderedLabel]

/-- The whole boundary equation follows from the actual ordered pullback. -/
theorem coefficient_boundary (W : Source) (x y : Vertex W)
    (T : NCode) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y T k a ≫ (necklaceBoundaryRestriction W).app (op T) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ boundaryPoint W x y := by
  rw [coefficient_eq_projection]
  have h : pullback.fst ((necklaceBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) ≫ (necklaceBoundaryRestriction W).app (op T) =
      pullback.snd ((necklaceBoundaryRestriction W).app (op T))
        (boundaryPoint W x y) ≫ boundaryPoint W x y := pullback.condition
  calc
    (SSet.yonedaEquiv.symm a ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y)) ≫
        (necklaceBoundaryRestriction W).app (op T) =
      (SSet.yonedaEquiv.symm a ≫
        pullback.snd ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W x y)) ≫ boundaryPoint W x y := by
            simp only [Category.assoc, h]
    _ = SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ boundaryPoint W x y := by
      congr 1
      exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem firstRestriction_boundary (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      firstRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inl W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inl_desc, firstRestriction]
  rfl

private theorem lastRestriction_boundary (W : Source) (T : NCode) :
    (necklaceBoundaryRestriction W).app (op T) ≫
      diagramMappingPrecomp
        (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W =
      lastRestriction W T := by
  change diagramMappingPrecomp (boundaryNecklace T) W ≫
    diagramMappingPrecomp coprod.inr W = _
  rw [← diagramMappingPrecomp_comp]
  simp only [boundaryNecklace, coprod.inr_desc, lastRestriction]
  rfl

/-- The first ordered endpoint is fixed on the entire parameter. -/
theorem coefficient_first (W : Source) (x y : Vertex W)
    (T : NCode) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y T k a ≫ firstRestriction W T =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ zeroPoint W x := by
  rw [← firstRestriction_boundary, ← Category.assoc, coefficient_boundary,
    Category.assoc, boundaryPoint_first]

/-- The last ordered endpoint is fixed on the entire parameter. -/
theorem coefficient_last (W : Source) (x y : Vertex W)
    (T : NCode) (k : SimplexCategory)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y T k a ≫ lastRestriction W T =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ zeroPoint W y := by
  rw [← lastRestriction_boundary, ← Category.assoc, coefficient_boundary,
    Category.assoc, boundaryPoint_last]

/-- Input ordered points and their three complete native coefficients. -/
structure Inputs (W : Source) (T U : NCode) (k : SimplexCategory)
    (x z y : Vertex W) where
  left : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k)
  right : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op k)

variable {W : Source} {T U : NCode} {k : SimplexCategory}
variable {x z y : Vertex W}

private theorem parameter_exchange {A B : Source} (f : A ⟶ B)
    {L M : SSet.{0}} (g : L ⟶ M) :
    (diagramTensor A).map g ≫
        Functor.whiskerRight f (tensorRight M) =
      Functor.whiskerRight f (tensorRight L) ≫
        (diagramTensor B).map g := by
  apply NatTrans.ext
  funext c
  exact whisker_exchange (f.app c) g

/-- A constant identity coefficient restricts to the original zero label
along every map from the point into the identity bead. -/
private theorem identityCoefficient_restrict (W : Source) (z : Vertex W)
    (k : SimplexCategory) (p : (Δ[0] : SSet.{0}) ⟶ (single 1).toSSet) :
    (diagramMappingPrecomp (F.map p) W).app (op k)
        (JTGraphRefinement.identityCoefficient W z k) =
      (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map
        (SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0)) ≫
        zeroLabel W z := by
  let q : (single 1).toSSet ⟶ (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.from (single 1).toSSet
  let g : K k ⟶ (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0)
  have hp : p ≫ q = 𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  change Functor.whiskerRight (F.map p) (tensorRight (K k)) ≫
      (diagramTensor (F.obj (single 1).toSSet)).map g ≫
        JTIdentityRowRealization.identityEdgeLabel W z = _
  rw [JTIdentityRowRealization.identityEdgeLabel_eq_zeroLabel]
  calc
    _ = (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map g ≫
          Functor.whiskerRight (F.map p) (tensorRight (Δ[0] : SSet.{0})) ≫
            Functor.whiskerRight (F.map q) (tensorRight (Δ[0] : SSet.{0})) ≫
              zeroLabel W z := by
      rw [← Category.assoc (Functor.whiskerRight (F.map p) (tensorRight (K k))),
        ← parameter_exchange (F.map p) g]
      simp only [Category.assoc]
      rfl
    _ = (diagramTensor (F.obj (Δ[0] : SSet.{0}))).map g ≫
          zeroLabel W z := by
      rw [← Category.assoc (Functor.whiskerRight (F.map p) (tensorRight (Δ[0] : SSet.{0}))),
        ← Functor.whiskerRight_comp, ← F.map_comp, hp, F.map_id]
      erw [Functor.whiskerRight_id, Category.id_comp]

private theorem identityCoefficient_endpoint (W : Source) (z : Vertex W)
    (k : SimplexCategory) (p : (Δ[0] : SSet.{0}) ⟶ (single 1).toSSet) :
    SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k) ≫
        diagramMappingPrecomp (F.map p) W =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ zeroPoint W z := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rw [SSet.yonedaEquiv_comp, zeroPoint]
  rw [identityCoefficient_restrict]
  have hg : SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [hg]
  rfl

/-- The complete identity coefficient has the specified first endpoint. -/
theorem identityCoefficient_first (W : Source) (z : Vertex W)
    (k : SimplexCategory) :
    SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k) ≫
        firstRestriction W (single 1) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ zeroPoint W z :=
  identityCoefficient_endpoint W z k (pointAt (single 1) (ULift.up 0))

/-- The complete identity coefficient has the specified last endpoint. -/
theorem identityCoefficient_last (W : Source) (z : Vertex W)
    (k : SimplexCategory) :
    SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k) ≫
        lastRestriction W (single 1) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ zeroPoint W z :=
  identityCoefficient_endpoint W z k
    (pointAt (single 1) (ULift.up (Fin.last 1)))

def leftCoefficient (a : Inputs W T U k x z y) : K k ⟶ labels W T :=
  coefficient W x z T k a.left

def middleCoefficient (_a : Inputs W T U k x z y) :
    K k ⟶ labels W (single 1) :=
  SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k)

def rightCoefficient (a : Inputs W T U k x z y) : K k ⟶ labels W U :=
  coefficient W z y U k a.right

private theorem leftJoint (a : Inputs W T U k x z y) :
    leftCoefficient a ≫ lastRestriction W T =
      middleCoefficient a ≫ firstRestriction W (single 1) := by
  rw [leftCoefficient, coefficient_last]
  exact (identityCoefficient_first W z k).symm

private theorem rightJoint (a : Inputs W T U k x z y) :
    middleCoefficient a ≫ lastRestriction W (single 1) =
      rightCoefficient a ≫ firstRestriction W U := by
  rw [rightCoefficient, coefficient_first]
  exact identityCoefficient_last W z k

def innerLabel (a : Inputs W T U k x z y) :
    K k ⟶ labels W (wedge (single 1) U) :=
  glue W (single 1) U k (middleCoefficient a) (rightCoefficient a) (rightJoint a)

private theorem outerJoint (a : Inputs W T U k x z y) :
    leftCoefficient a ≫ lastRestriction W T =
      innerLabel a ≫ firstRestriction W (wedge (single 1) U) := by
  calc
    _ = middleCoefficient a ≫ firstRestriction W (single 1) := leftJoint a
    _ = _ := (glue_first W (single 1) U k
      (middleCoefficient a) (rightCoefficient a) (rightJoint a)).symm

def tripleLabel (a : Inputs W T U k x z y) : K k ⟶ labels W (code T U) :=
  glue W T (wedge (single 1) U) k (leftCoefficient a) (innerLabel a) (outerJoint a)

theorem tripleLabel_left (a : Inputs W T U k x z y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightT T (single 1) U)) W = leftCoefficient a :=
  glue_left W T (wedge (single 1) U) k
    (leftCoefficient a) (innerLabel a) (outerJoint a)

theorem tripleLabel_middle (a : Inputs W T U k x z y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightU T (single 1) U)) W = middleCoefficient a := by
  have hp : diagramMappingPrecomp (F.map (tripleRightU T (single 1) U)) W =
      diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W ≫
        diagramMappingPrecomp (F.map (wedgeιLeft (single 1) U)) W := by
    dsimp only [tripleRightU]
    rw [Functor.map_comp, diagramMappingPrecomp_comp]
  rw [hp, ← Category.assoc]
  rw [show tripleLabel a ≫
      diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W =
        innerLabel a from glue_right W _ _ k
      (leftCoefficient a) (innerLabel a) (outerJoint a)]
  exact glue_left W (single 1) U k
    (middleCoefficient a) (rightCoefficient a) (rightJoint a)

theorem tripleLabel_right (a : Inputs W T U k x z y) :
    tripleLabel a ≫ diagramMappingPrecomp
      (F.map (tripleRightV T (single 1) U)) W = rightCoefficient a := by
  have hp : diagramMappingPrecomp (F.map (tripleRightV T (single 1) U)) W =
      diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W ≫
        diagramMappingPrecomp (F.map (wedgeιRight (single 1) U)) W := by
    dsimp only [tripleRightV]
    rw [Functor.map_comp, diagramMappingPrecomp_comp]
  rw [hp, ← Category.assoc]
  rw [show tripleLabel a ≫
      diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W =
        innerLabel a from glue_right W _ _ k
      (leftCoefficient a) (innerLabel a) (outerJoint a)]
  exact glue_right W (single 1) U k
    (middleCoefficient a) (rightCoefficient a) (rightJoint a)

theorem tripleLabel_boundary (a : Inputs W T U k x z y) :
    tripleLabel a ≫ (necklaceBoundaryRestriction W).app (op (code T U)) =
      SSet.stdSimplex.isTerminalObj₀.from (K k) ≫ boundaryPoint W x y := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst]
    rw [firstRestriction_boundary]
    rw [show tripleLabel a ≫ firstRestriction W (code T U) =
      leftCoefficient a ≫ firstRestriction W T from
      glue_first W T (wedge (single 1) U) k
        (leftCoefficient a) (innerLabel a) (outerJoint a)]
    rw [leftCoefficient, coefficient_first, boundaryPoint_first]
  · simp only [Category.assoc, boundaryMappingIso_snd]
    rw [lastRestriction_boundary]
    rw [show tripleLabel a ≫ lastRestriction W (code T U) =
      rightCoefficient a ≫ lastRestriction W U by
        calc
          _ = innerLabel a ≫ lastRestriction W (wedge (single 1) U) :=
            glue_last W T (wedge (single 1) U) k
              (leftCoefficient a) (innerLabel a) (outerJoint a)
          _ = _ := glue_last W (single 1) U k
            (middleCoefficient a) (rightCoefficient a) (rightJoint a)]
    rw [rightCoefficient, coefficient_last, boundaryPoint_last]

/-- The actual ordered point on the three-part native necklace. -/
def orderedTriplePoint (a : Inputs W T U k x z y) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code T U))).obj
      (op k) :=
  SSet.yonedaEquiv (pullback.lift (tripleLabel a)
    (SSet.stdSimplex.isTerminalObj₀.from (K k)) (tripleLabel_boundary a))

theorem orderedTriplePoint_coefficient (a : Inputs W T U k x z y) :
    JTRealizedLabelEndpoints.orderedLabel W x y (code T U) k
      (orderedTriplePoint a) = SSet.yonedaEquiv (tripleLabel a) := by
  dsimp only [JTRealizedLabelEndpoints.orderedLabel, orderedTriplePoint]
  erw [← SSet.yonedaEquiv_comp, pullback.lift_fst]
  rfl

/-- The full left coefficient is recovered along the actual first bead map. -/
theorem orderedTriplePoint_left (a : Inputs W T U k x z y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code T U) k
          (orderedTriplePoint a)) ≫
      diagramMappingPrecomp (F.map (tripleRightT T (single 1) U)) W =
        leftCoefficient a := by
  rw [orderedTriplePoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_left a

/-- The full identity coefficient is recovered along the actual middle map. -/
theorem orderedTriplePoint_middle (a : Inputs W T U k x z y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code T U) k
          (orderedTriplePoint a)) ≫
      diagramMappingPrecomp (F.map (tripleRightU T (single 1) U)) W =
        middleCoefficient a := by
  rw [orderedTriplePoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_middle a

/-- The full right coefficient is recovered along the actual last bead map. -/
theorem orderedTriplePoint_right (a : Inputs W T U k x z y) :
    SSet.yonedaEquiv.symm
        (JTRealizedLabelEndpoints.orderedLabel W x y (code T U) k
          (orderedTriplePoint a)) ≫
      diagramMappingPrecomp (F.map (tripleRightV T (single 1) U)) W =
        rightCoefficient a := by
  rw [orderedTriplePoint_coefficient]
  erw [Equiv.symm_apply_apply]
  exact tripleLabel_right a


/-- Restrict the two whole ordered simplices along the same coefficient operator. -/
def reindex {l : SimplexCategory} (r : l ⟶ k) (a : Inputs W T U k x z y) :
    Inputs W T U l x z y where
  left := ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).map r.op a.left
  right := ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).map r.op a.right

private theorem coefficient_map (W : Source) (x y : Vertex W) (T : NCode)
    {l k : SimplexCategory} (r : l ⟶ k)
    (a : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op k)) :
    coefficient W x y T l
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map r.op a) =
      SSet.stdSimplex.map r ≫ coefficient W x y T k a := by
  rw [coefficient_eq_projection, coefficient_eq_projection, SSet.yonedaEquiv_symm_map,
    Category.assoc]

private theorem middleCoefficient_map {l : SimplexCategory} (r : l ⟶ k)
    (a : Inputs W T U k x z y) :
    middleCoefficient (reindex r a) = SSet.stdSimplex.map r ≫ middleCoefficient a := by
  have h : ((labels W (single 1)).map r.op (JTGraphRefinement.identityCoefficient W z k)) =
      JTGraphRefinement.identityCoefficient W z l := by
    change (diagramTensor (F.obj (single 1).toSSet)).map (SSet.stdSimplex.map r) ≫
        ((diagramTensor (F.obj (single 1).toSSet)).map
          (SSet.stdSimplex.map (SimplexCategory.const k ⦋0⦌ 0)) ≫
            JTIdentityRowRealization.identityEdgeLabel W z) =
      (diagramTensor (F.obj (single 1).toSSet)).map
        (SSet.stdSimplex.map (SimplexCategory.const l ⦋0⦌ 0)) ≫
          JTIdentityRowRealization.identityEdgeLabel W z
    rw [← Category.assoc, ← Functor.map_comp, ← SSet.stdSimplex.map_comp]
    rfl
  change SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z l) =
    SSet.stdSimplex.map r ≫ SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k)
  rw [← SSet.yonedaEquiv_symm_map]
  exact congrArg SSet.yonedaEquiv.symm h.symm

private theorem innerLabel_map {l : SimplexCategory} (r : l ⟶ k)
    (a : Inputs W T U k x z y) :
    innerLabel (reindex r a) = SSet.stdSimplex.map r ≫ innerLabel a := by
  apply (wedgeMappingPullback W (single 1) U).hom_ext
  · rw [Category.assoc]
    change _ ≫ diagramMappingPrecomp (F.map (wedgeιLeft (single 1) U)) W = _
    rw [innerLabel, innerLabel, glue_left, glue_left]
    exact middleCoefficient_map r a
  · rw [Category.assoc]
    change _ ≫ diagramMappingPrecomp (F.map (wedgeιRight (single 1) U)) W = _
    rw [innerLabel, innerLabel, glue_right, glue_right]
    exact coefficient_map W z y U r a.right

private theorem tripleLabel_map {l : SimplexCategory} (r : l ⟶ k)
    (a : Inputs W T U k x z y) :
    tripleLabel (reindex r a) = SSet.stdSimplex.map r ≫ tripleLabel a := by
  apply (wedgeMappingPullback W T (wedge (single 1) U)).hom_ext
  · change _ ≫ diagramMappingPrecomp (F.map (wedgeιLeft T (wedge (single 1) U))) W =
      (SSet.stdSimplex.map r ≫ tripleLabel a) ≫
        diagramMappingPrecomp (F.map (wedgeιLeft T (wedge (single 1) U))) W
    rw [Category.assoc, tripleLabel, tripleLabel, glue_left, glue_left]
    exact coefficient_map W x z T r a.left
  · change _ ≫ diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W =
      (SSet.stdSimplex.map r ≫ tripleLabel a) ≫
        diagramMappingPrecomp (F.map (wedgeιRight T (wedge (single 1) U))) W
    rw [Category.assoc, tripleLabel, tripleLabel, glue_right, glue_right]
    exact innerLabel_map r a

/-- Gluing commutes with every common coefficient operator, including
the complete identity coefficient of the connector. -/
theorem orderedTriplePoint_map {l : SimplexCategory} (r : l ⟶ k)
    (a : Inputs W T U k x z y) :
    ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op (code T U))).map
        r.op (orderedTriplePoint a) =
      orderedTriplePoint (reindex r a) := by
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_map]
  simp only [orderedTriplePoint, Equiv.symm_apply_apply]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    exact (tripleLabel_map r a).symm
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end

end DaggerModels.PartII.JTOrderedLabelBinaryGlue
