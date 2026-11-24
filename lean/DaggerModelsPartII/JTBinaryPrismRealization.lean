import DaggerModelsPartII.JTGraphBinaryRefinement

/-!
# The complete raw equation for a binary prism

The left and right prisms use the split parameter blocks of the actual
binary ordered label. Its identity connector can carry an arbitrary
groupoid parameter map while its raw realization stays at the joint.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismRealization

open JTProjectiveOrderedFiberComparison ReversalDiscreteFreeColimits
open JTNecklaceLabelRealization JTRealizedLabelEndpoints
open JTOrderedLabelBinaryGlue OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open JTParameterBlocks

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev F := discreteFree.{0}
private abbrev A := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev L (T U : NecklaceCode) := tripleRightT.{0} T A U
private abbrev M (T U : NecklaceCode) := tripleRightU.{0} T A U
private abbrev R (T U : NecklaceCode) := tripleRightV.{0} T A U

/-- Evaluate a graph with arbitrary time parameter, keeping the full
horizontal coordinate. -/
def realizeProduct {X I : SSet.{0}} (W : Source) (k : SimplexCategory)
    (s : X ⊗ I ⟶ J.obj k) (a : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    X ⊗ I ⟶ Raw W :=
  lift (fst X I) s ≫ realizedLabel X W k a

/-- The raw product comparison is natural in the entire time simplicial set. -/
theorem realizeProduct_reindexTime {X I I' : SSet.{0}} (W : Source) (k : SimplexCategory)
    (v : I' ⟶ I) (s : X ⊗ I ⟶ J.obj k)
    (a : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    (X ◁ v) ≫ realizeProduct W k s a =
      realizeProduct W k ((X ◁ v) ≫ s) a := by
  have h : (X ◁ v) ≫ lift (fst X I) s = lift (fst X I') ((X ◁ v) ≫ s) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst]
    · simp only [Category.assoc, lift_snd]
  unfold realizeProduct
  rw [← Category.assoc, h]

private theorem realizeProduct_precomp {X Y I : SSet.{0}} (W : Source)
    (k : SimplexCategory) (i : X ⟶ Y) (s : Y ⊗ I ⟶ J.obj k)
    (a : (diagramMappingSpace (F.obj Y) W).obj (op k)) :
    (i ⊗ₘ 𝟙 I) ≫ realizeProduct W k s a =
      realizeProduct W k ((i ⊗ₘ 𝟙 I) ≫ s)
        (Functor.whiskerRight (F.map i) (tensorRight (SSet.stdSimplex.obj k)) ≫ a) := by
  have h : (i ⊗ₘ 𝟙 I) ≫ lift (fst Y I) s =
      lift (fst X I) ((i ⊗ₘ 𝟙 I) ≫ s) ≫ (i ⊗ₘ 𝟙 (J.obj k)) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, lift_fst_assoc]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, Category.comp_id]
  unfold realizeProduct
  rw [← Category.assoc, h, Category.assoc, realizedLabel_natural_X]

private theorem realizeProduct_split {X I : SSet.{0}} (W : Source) {k l : SimplexCategory}
    (i : k ⟶ l) (r : l ⟶ k) (hir : i ≫ r = 𝟙 k) (s : X ⊗ I ⟶ J.obj k)
    (a : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    realizeProduct W l (s ≫ J.map i)
        ((diagramTensor (F.obj X)).map (SSet.stdSimplex.map r) ≫ a) =
      realizeProduct W k s a := by
  have h : lift (fst X I) (s ≫ J.map i) = lift (fst X I) s ≫ (𝟙 X ⊗ₘ J.map i) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · simp only [Category.assoc, lift_snd, tensorHom_snd, lift_snd_assoc]
  unfold realizeProduct
  rw [h, Category.assoc, realizedLabel_natural_k, ← Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp, hir]
  have hId : (diagramTensor (F.obj X)).map (SSet.stdSimplex.{0}.map (𝟙 k)) ≫ a = a := by
    rw [SSet.stdSimplex.{0}.map_id, (diagramTensor (F.obj X)).map_id, Category.id_comp]
  erw [hId]

private theorem orderedLabel_reindex {W : Source} {x y : Vertex W}
    {T : NecklaceCode} {k l : SimplexCategory} (r : k ⟶ l)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    orderedLabel W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map r.op u) =
      (diagramTensor (F.obj T.toSSet)).map (SSet.stdSimplex.map r) ≫
        orderedLabel W x y T l u :=
  congrFun ((pullback.fst ((necklaceBoundaryRestriction W).app (op T))
    (boundaryPoint W x y)).naturality r.op) u

/-- Reindexing an ordered coefficient and applying the same operator to
the full parameter give the same raw comparison. -/
theorem realizeOrderedProduct_reindex {W : Source} {x y : Vertex W}
    {T : NecklaceCode} {k l : SimplexCategory} {I : SSet.{0}} (r : k ⟶ l)
    (p : T.toSSet ⊗ I ⟶ J.obj k)
    (u : ((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).obj (op l)) :
    realizeProduct W l (p ≫ J.map r) (orderedLabel W x y T l u) =
      realizeProduct W k p (orderedLabel W x y T k
        (((orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)).map r.op u)) := by
  have h : lift (fst T.toSSet I) (p ≫ J.map r) =
      lift (fst T.toSSet I) p ≫ (𝟙 T.toSSet ⊗ₘ J.map r) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, tensorHom_fst, Category.comp_id]
    · simp only [lift_snd, Category.assoc, tensorHom_snd, lift_snd_assoc]
  unfold realizeProduct
  rw [h, Category.assoc, realizedLabel_natural_k, ← orderedLabel_reindex]

/-- The original left and right labels, transported to the shared
ordinal by the two block retractions. -/
def blockInputs {W : Source} {x z y : Vertex W}
    {T U : NecklaceCode} {k l : SimplexCategory}
    (a : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k))
    (b : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op l)) :
    Inputs W T U (common k l) x z y where
  left := ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).map
    (leftRet k l).op a
  right := ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).map
    (rightRet k l).op b

private theorem tripleTensor_hom_ext (T U : NecklaceCode) {I Y : SSet.{0}}
    {f g : (code T U).toSSet ⊗ I ⟶ Y}
    (hl : (L T U ⊗ₘ 𝟙 I) ≫ f = (L T U ⊗ₘ 𝟙 I) ≫ g)
    (hm : (M T U ⊗ₘ 𝟙 I) ≫ f = (M T U ⊗ₘ 𝟙 I) ≫ g)
    (hr : (R T U ⊗ₘ 𝟙 I) ≫ f = (R T U ⊗ₘ 𝟙 I) ≫ g) : f = g := by
  apply ((wedgeIsPushout T (wedge A U)).map (tensorRight I)).hom_ext
  · exact hl
  · apply ((wedgeIsPushout A U).map (tensorRight I)).hom_ext
    · change (wedgeιLeft A U ⊗ₘ 𝟙 I) ≫ (wedgeιRight T (wedge A U) ⊗ₘ 𝟙 I) ≫ f =
        (wedgeιLeft A U ⊗ₘ 𝟙 I) ≫ (wedgeιRight T (wedge A U) ⊗ₘ 𝟙 I) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hm
    · change (wedgeιRight A U ⊗ₘ 𝟙 I) ≫ (wedgeιRight T (wedge A U) ⊗ₘ 𝟙 I) ≫ f =
        (wedgeιRight A U ⊗ₘ 𝟙 I) ≫ (wedgeιRight T (wedge A U) ⊗ₘ 𝟙 I) ≫ g
      simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      exact hr

section SharedCoefficient

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {m : SimplexCategory} {I : SSet.{0}}
variable (d : Inputs W T U m x z y) (p : (code T U).toSSet ⊗ I ⟶ J.obj m)

/-- Evaluate two inputs on an arbitrary shared ordinal, with their actual
identity connector. -/
def realizeInputs : (code T U).toSSet ⊗ I ⟶ Raw W :=
  realizeProduct W m p (orderedLabel W x y (code T U) m (orderedTriplePoint d))

theorem realizeInputs_left :
    (L T U ⊗ₘ 𝟙 I) ≫ realizeInputs d p =
      realizeProduct W m ((L T U ⊗ₘ 𝟙 I) ≫ p) (orderedLabel W x z T m d.left) := by
  unfold realizeInputs
  rw [realizeProduct_precomp]
  have h := congrArg SSet.yonedaEquiv (orderedTriplePoint_left d)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, leftCoefficient, coefficient] at h
  erw [Equiv.apply_symm_apply] at h
  change Functor.whiskerRight (F.map (L T U)) (tensorRight (SSet.stdSimplex.obj m)) ≫
    orderedLabel W x y (code T U) m (orderedTriplePoint d) =
    orderedLabel W x z T m d.left at h
  rw [h]

theorem realizeInputs_right :
    (R T U ⊗ₘ 𝟙 I) ≫ realizeInputs d p =
      realizeProduct W m ((R T U ⊗ₘ 𝟙 I) ≫ p) (orderedLabel W z y U m d.right) := by
  unfold realizeInputs
  rw [realizeProduct_precomp]
  have h := congrArg SSet.yonedaEquiv (orderedTriplePoint_right d)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, rightCoefficient, coefficient] at h
  erw [Equiv.apply_symm_apply] at h
  change Functor.whiskerRight (F.map (R T U)) (tensorRight (SSet.stdSimplex.obj m)) ≫
    orderedLabel W x y (code T U) m (orderedTriplePoint d) =
    orderedLabel W z y U m d.right at h
  rw [h]

theorem realizeInputs_middle :
    (M T U ⊗ₘ 𝟙 I) ≫ realizeInputs d p =
      term (A.toSSet ⊗ I) ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
  unfold realizeInputs
  rw [realizeProduct_precomp]
  have h := congrArg SSet.yonedaEquiv (orderedTriplePoint_middle d)
  simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, middleCoefficient] at h
  change Functor.whiskerRight (F.map (M T U)) (tensorRight (SSet.stdSimplex.obj m)) ≫
    orderedLabel W x y (code T U) m (orderedTriplePoint d) =
    JTGraphRefinement.identityCoefficient W z m at h
  rw [h, realizeProduct, JTGraphRefinement.realizedIdentityCoefficient, ← Category.assoc]
  congr 1

end SharedCoefficient

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode}
variable {k l : SimplexCategory} {I : SSet.{0}}
variable (a : ((orderedNecklaceLabels W (boundaryPoint W x z)).obj (op T)).obj (op k))
variable (b : ((orderedNecklaceLabels W (boundaryPoint W z y)).obj (op U)).obj (op l))
variable (p : (code T U).toSSet ⊗ I ⟶ J.obj (common k l))

/-- Realize the product graph using the actual joined ordered label. -/
def raw : (code T U).toSSet ⊗ I ⟶ Raw W :=
  realizeInputs (blockInputs a b) p

/-- The left product graph realizes to the original left comparison. -/
theorem raw_left (s : T.toSSet ⊗ I ⟶ J.obj k)
    (hp : (L T U ⊗ₘ 𝟙 I) ≫ p = s ≫ J.map (leftIn k l)) :
    (L T U ⊗ₘ 𝟙 I) ≫ raw a b p =
      realizeProduct W k s (orderedLabel W x z T k a) := by
  rw [raw, realizeInputs_left, hp]
  dsimp only [blockInputs]
  rw [orderedLabel_reindex, realizeProduct_split W _ _ (left_split k l)]

/-- The right product graph realizes to the original right comparison. -/
theorem raw_right (t : U.toSSet ⊗ I ⟶ J.obj l)
    (hp : (R T U ⊗ₘ 𝟙 I) ≫ p = t ≫ J.map (rightIn k l)) :
    (R T U ⊗ₘ 𝟙 I) ≫ raw a b p =
      realizeProduct W l t (orderedLabel W z y U l b) := by
  rw [raw, realizeInputs_right, hp]
  dsimp only [blockInputs]
  rw [orderedLabel_reindex, realizeProduct_split W _ _ (right_split k l)]

/-- The whole connector realizes to the actual raw joint, for any
parameter map on the connector. -/
theorem raw_middle :
    (M T U ⊗ₘ 𝟙 I) ≫ raw a b p =
      term (A.toSSet ⊗ I) ≫ SSet.yonedaEquiv.symm (rawVertex W z) :=
  realizeInputs_middle (blockInputs a b) p

private theorem tensor_fst_assoc {X Y I Z : SSet.{0}} (i : X ⟶ Y) (f : Y ⟶ Z) :
    (i ⊗ₘ 𝟙 I) ≫ fst Y I ≫ f = fst X I ≫ i ≫ f := by
  rw [← Category.assoc, tensorHom_fst, Category.assoc]

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}

/-- Collapse the connector and apply the same two original target maps. -/
def collapse (c : T ⟶ P.code) (e : U ⟶ Q.code) : code T U ⟶ (NecklacesOver.wedge P Q).code :=
  JTGraphBinaryTraversal.collapse T U ≫ wedgeMap c e

theorem collapse_left_map (c : T ⟶ P.code) (e : U ⟶ Q.code) :
    L T U ≫ (collapse c e).map = c.map ≫ wedgeιLeft P.code Q.code := by
  change L T U ≫ (JTGraphBinaryTraversal.collapse T U).map ≫ (wedgeMap c e).map = _
  rw [← Category.assoc, JTGraphBinaryTraversal.collapse_left, wedgeMap_left]

theorem collapse_right_map (c : T ⟶ P.code) (e : U ⟶ Q.code) :
    R T U ≫ (collapse c e).map = e.map ≫ wedgeιRight P.code Q.code := by
  change R T U ≫ (JTGraphBinaryTraversal.collapse T U).map ≫ (wedgeMap c e).map = _
  rw [← Category.assoc, JTGraphBinaryTraversal.collapse_right, wedgeMap_right]

/-- The connector collapses to the literal joint of the target wedge. -/
theorem collapse_middle_map (c : T ⟶ P.code) (e : U ⟶ Q.code) :
    M T U ≫ (collapse c e).map = term A.toSSet ≫ JTGraphBinaryTraversal.joint P.code Q.code := by
  change M T U ≫ (JTGraphBinaryTraversal.collapse T U).map ≫ (wedgeMap c e).map = _
  rw [← Category.assoc, JTGraphBinaryTraversal.collapse_middle, JTGraphBinaryTraversal.joint,
    JTGraphBinaryTraversal.joint]
  simp only [Category.assoc]
  rw [wedgeMap_left]
  have h : pointAt T (ULift.up (Fin.last T.len)) ≫ c.map =
      pointAt P.code (ULift.up (Fin.last P.code.len)) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, pointAt_vertex, pointAt_vertex]
    exact c.last
  rw [← Category.assoc (pointAt T _) c.map, h]
  rfl

/-- Two comparisons on an arbitrary shared ordinal realize over the
original native wedge once both raw side equations hold. -/
theorem realizeInputs_over_wedge {m : SimplexCategory} (d : Inputs W T U m x z y)
    (q : (code T U).toSSet ⊗ I ⟶ J.obj m) (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (hs : realizeProduct W m ((L T U ⊗ₘ 𝟙 I) ≫ q) (orderedLabel W x z T m d.left) =
      fst T.toSSet I ≫ c.map ≫ P.map)
    (ht : realizeProduct W m ((R T U ⊗ₘ 𝟙 I) ≫ q) (orderedLabel W z y U m d.right) =
      fst U.toSSet I ≫ e.map ≫ Q.map) :
    realizeInputs d q = fst (code T U).toSSet I ≫ (collapse c e).map ≫
      (NecklacesOver.wedge P Q).map := by
  let r := (collapse c e).map ≫ (NecklacesOver.wedge P Q).map
  have hL : L T U ≫ r = c.map ≫ P.map := by
    dsimp only [r]
    rw [← Category.assoc, collapse_left_map, Category.assoc, NecklacesOver.wedge_left]
  have hR : R T U ≫ r = e.map ≫ Q.map := by
    dsimp only [r]
    rw [← Category.assoc, collapse_right_map, Category.assoc, NecklacesOver.wedge_right]
  have hP : pointAt P.code (ULift.up (Fin.last P.code.len)) ≫ P.map =
      SSet.yonedaEquiv.symm (rawVertex W z) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, pointAt_vertex, Equiv.apply_symm_apply]
    exact P.last
  have hM : M T U ≫ r = term A.toSSet ≫ SSet.yonedaEquiv.symm (rawVertex W z) := by
    dsimp only [r]
    rw [← Category.assoc, collapse_middle_map, JTGraphBinaryTraversal.joint]
    simp only [Category.assoc, NecklacesOver.wedge_left, hP]
  apply tripleTensor_hom_ext T U
  · exact (realizeInputs_left d q).trans (hs.trans
      ((congrArg (fun u ↦ fst T.toSSet I ≫ u) hL.symm).trans
        (tensor_fst_assoc (I := I) (L T U) r).symm))
  · refine (realizeInputs_middle d q).trans (Eq.trans ?_ (tensor_fst_assoc (I := I) (M T U) r).symm)
    rw [hM, ← Category.assoc]
    exact congrArg (fun u ↦ u ≫ SSet.yonedaEquiv.symm (rawVertex W z))
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  · exact (realizeInputs_right d q).trans (ht.trans
      ((congrArg (fun u ↦ fst U.toSSet I ≫ u) hR.symm).trans
        (tensor_fst_assoc (I := I) (R T U) r).symm))

/-- Two strict comparisons over the original native targets give one
strict comparison over their native wedge, with the original raw map. -/
theorem raw_over_wedge (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (s : T.toSSet ⊗ I ⟶ J.obj k) (t : U.toSSet ⊗ I ⟶ J.obj l)
    (hpL : (L T U ⊗ₘ 𝟙 I) ≫ p = s ≫ J.map (leftIn k l))
    (hpR : (R T U ⊗ₘ 𝟙 I) ≫ p = t ≫ J.map (rightIn k l))
    (hs : realizeProduct W k s (orderedLabel W x z T k a) = fst T.toSSet I ≫ c.map ≫ P.map)
    (ht : realizeProduct W l t (orderedLabel W z y U l b) = fst U.toSSet I ≫ e.map ≫ Q.map) :
    raw a b p = fst (code T U).toSSet I ≫ (collapse c e).map ≫ (NecklacesOver.wedge P Q).map :=
  realizeInputs_over_wedge (blockInputs a b) p c e
    ((realizeInputs_left (blockInputs a b) p).symm.trans ((raw_left a b p s hpL).trans hs))
    ((realizeInputs_right (blockInputs a b) p).symm.trans ((raw_right a b p t hpR).trans ht))

end

end DaggerModels.PartII.JTBinaryPrismRealization
