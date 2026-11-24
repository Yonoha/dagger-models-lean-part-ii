import DaggerModelsPartII.JTOrderedLabelWedge
import DaggerModelsPartII.JTConstantOrderedLabel
import DaggerModelsPartII.JTSharedCoefficientEvaluation

/-! Inserting the entire constant middle necklace between two ordered labels. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTOrderedLabelJointInsertion

open OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints ReversalDiscreteFreeColimits
open JTOrderedLabelWedge (joinedIndex joinedPoint joinedIndexHom indexHomOfCoefficient)
open JTOrderedLabelBinaryGlue (Inputs coefficient)
open JTConstantOrderedLabel (constantLabel constantIndexHom constantCoefficient)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (wedgeMappingPullback glue_left glue_right)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := discreteFree.{0}
private abbrev I (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.Index W (boundaryPoint W x y)
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)

/-- The native point code represents the terminal simplicial set. -/
def pointIsTerminal : IsTerminal (point.toSSet : SSet.{0}) :=
  IsTerminal.ofIso SSet.stdSimplex.isTerminalObj₀
    ((eqToIso (congrArg NecklaceCode.toSSet
        (NecklaceCode.code_eq_point_of_zero (single 0) rfl))).symm ≪≫ singleIso 0).symm

/-- Collapse an arbitrary middle necklace, with both endpoints retained. -/
def toPoint (M : NecklaceCode) : M ⟶ point where
  map := pointIsTerminal.from M.toSSet
  first := first_of_point _ (pointIsTerminal.hom_ext _ _)
  last := last_of_point _ (pointIsTerminal.hom_ext _ _)

/-- The collapse of the entire middle is natural in every native operator. -/
def toPointNatural {A : Type} [SmallCategory A] (M : A ⥤ NecklaceCode) :
    M ⟶ (Functor.const A).obj point where
  app a := toPoint (M.obj a)
  naturality {_ _} _ := Hom.ext (pointIsTerminal.hom_ext _ _)

variable {W : Source} {x z y : Vertex W}
variable {T T' U U' : NecklaceCode} {k k' : SimplexCategory}

private def inner (P : NecklaceCode) (a : Inputs W T U k x z y) :
    JTOrderedLabelWedge.Inputs W P U k z z y :=
  ⟨constantLabel W z P k, a.right⟩

private def outer (P : NecklaceCode) (a : Inputs W T U k x z y) :
    JTOrderedLabelWedge.Inputs W T (wedge P U) k x z y :=
  ⟨a.left, joinedPoint (inner P a)⟩

/-- The decorated label whose middle is the full native necklace with the
shared constant coefficient and whose two side labels are unchanged. -/
abbrev index (P : NecklaceCode) (a : Inputs W T U k x z y) : I W x y :=
  joinedIndex (outer P a)

private theorem hom_ext {i i' : I W x y} {f g : i ⟶ i'}
    (h : (pr W x y).map f = (pr W x y).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

private abbrev wedgeOperator {S S' T T' : NecklaceCode}
    (f : S ⟶ S') (g : T ⟶ T') : wedge S T ⟶ wedge S' T' :=
  wedgeMap f g

private theorem wedgeOperator_id (S T : NecklaceCode) :
    wedgeOperator (𝟙 S) (𝟙 T) = 𝟙 (wedge S T) := wedgeMap_id

private theorem wedgeOperator_comp {S S' S'' T T' T'' : NecklaceCode}
    (f : S ⟶ S') (g : T ⟶ T') (f' : S' ⟶ S'') (g' : T' ⟶ T'') :
    wedgeOperator f g ≫ wedgeOperator f' g' = wedgeOperator (f ≫ f') (g ≫ g') :=
  (wedgeMap_comp f g f' g').symm

private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (free.map f) W

/-- The seam coefficient of the existing binary gluing is the actual constant
coefficient on the native identity bead. -/
theorem identityCoefficient_eq_constant (W : Source) (z : Vertex W) (k : SimplexCategory) :
    SSet.yonedaEquiv.symm (JTGraphRefinement.identityCoefficient W z k) =
      constantCoefficient W z (single 1) k := by
  let A := (single 1).toSSet
  let q := SSet.stdSimplex.isTerminalObj₀.from (A : SSet.{0})
  let g := SimplexCategory.const k ⦋0⦌ 0
  have hg : SSet.stdSimplex.{0}.map g = SSet.stdSimplex.isTerminalObj₀.from
      (SSet.stdSimplex.{0}.obj k) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  change JTGraphRefinement.identityCoefficient W z k = SSet.yonedaEquiv
    (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.{0}.obj k) ≫
      zeroPoint W z ≫ diagramMappingPrecomp (discreteFree.{0}.map q) W)
  rw [← hg, SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_comp, zeroPoint, Equiv.apply_symm_apply]
  unfold JTGraphRefinement.identityCoefficient
  rw [JTIdentityRowRealization.identityEdgeLabel_eq_zeroLabel]
  rfl


set_option maxHeartbeats 650000 in
/-- The coefficient on the entire middle is its literal constant coefficient. -/
theorem coefficient_middle (P : NecklaceCode) (a : Inputs W T U k x z y) :
    coefficient W x y (wedge T (wedge P U)) k
        (OrderedLabelElements.label W (boundaryPoint W x y) (index P a)) ≫
      pre W (tripleRightU T P U) = constantCoefficient W z P k := by
  have h : pre W (tripleRightU T P U) =
      pre W (wedgeιRight T (wedge P U)) ≫ pre W (wedgeιLeft P U) := by
    unfold pre tripleRightU
    rw [free.map_comp, diagramMappingPrecomp_comp]
  change coefficient W x y (wedge T (wedge P U)) k (joinedPoint (outer P a)) ≫
    pre W (tripleRightU T P U) = _
  rw [h, ← Category.assoc, JTOrderedLabelWedge.joinedPoint_right]
  change coefficient W z y (wedge P U) k (joinedPoint (inner P a)) ≫
    pre W (wedgeιLeft P U) = _
  rw [JTOrderedLabelWedge.joinedPoint_left]
  exact JTConstantOrderedLabel.coefficient_constantLabel W z P k

private theorem fullCoefficient {V : NecklaceCode} {w : Vertex W}
    (b : JTOrderedLabelWedge.Inputs W T V k x z w) :
    coefficient W x w (wedge T V) k (joinedPoint b) = JTOrderedLabelWedge.joinedLabel b := by
  rw [coefficient, JTOrderedLabelWedge.joinedPoint_coefficient]
  exact Equiv.symm_apply_apply _ _

set_option maxHeartbeats 600000 in
private theorem inner_identity (a : Inputs W T U k x z y) :
    JTOrderedLabelWedge.joinedLabel (inner (single 1) a) =
      JTOrderedLabelBinaryGlue.innerLabel a := by
  apply (wedgeMappingPullback W (single 1) U).hom_ext
  · change _ ≫ pre W (wedgeιLeft (single 1) U) = _ ≫ pre W (wedgeιLeft (single 1) U)
    rw [JTOrderedLabelWedge.joinedLabel_left]
    conv_rhs => rw [JTOrderedLabelBinaryGlue.innerLabel, glue_left]
    change coefficient W z z (single 1) k (constantLabel W z (single 1) k) =
      JTOrderedLabelBinaryGlue.middleCoefficient a
    rw [JTConstantOrderedLabel.coefficient_constantLabel, JTOrderedLabelBinaryGlue.middleCoefficient]
    exact (identityCoefficient_eq_constant W z k).symm
  · change _ ≫ pre W (wedgeιRight (single 1) U) = _ ≫ pre W (wedgeιRight (single 1) U)
    rw [JTOrderedLabelWedge.joinedLabel_right]
    conv_rhs => rw [JTOrderedLabelBinaryGlue.innerLabel, glue_right]
    rfl

set_option maxHeartbeats 800000 in
/-- With the ordinary identity bead as middle, the ordered index is exactly the
existing index of the three-part gluing. -/
theorem index_identity (a : Inputs W T U k x z y) :
    index (single 1) a = JTSharedCoefficientEvaluation.index a := by
  change OrderedLabelElements.mk W (boundaryPoint W x y)
      (JTOrderedLabelBinaryGlue.code T U) k (joinedPoint (outer (single 1) a)) =
    OrderedLabelElements.mk W (boundaryPoint W x y)
      (JTOrderedLabelBinaryGlue.code T U) k (JTOrderedLabelBinaryGlue.orderedTriplePoint a)
  apply congrArg (OrderedLabelElements.mk W (boundaryPoint W x y)
    (JTOrderedLabelBinaryGlue.code T U) k)
  apply JTOrderedLabelWedge.coefficient_injective W x y (JTOrderedLabelBinaryGlue.code T U) k
  have hc : coefficient W x y (JTOrderedLabelBinaryGlue.code T U) k
        (JTOrderedLabelBinaryGlue.orderedTriplePoint a) =
      JTOrderedLabelBinaryGlue.tripleLabel a := by
    rw [coefficient, JTOrderedLabelBinaryGlue.orderedTriplePoint_coefficient]
    exact Equiv.symm_apply_apply _ _
  rw [hc]
  change coefficient W x y (wedge T (wedge (single 1) U)) k
    (joinedPoint (outer (single 1) a)) = _
  rw [fullCoefficient]
  apply (wedgeMappingPullback W T (wedge (single 1) U)).hom_ext
  · change _ ≫ pre W (wedgeιLeft T (wedge (single 1) U)) =
      _ ≫ pre W (wedgeιLeft T (wedge (single 1) U))
    rw [JTOrderedLabelWedge.joinedLabel_left]
    conv_rhs => rw [JTOrderedLabelBinaryGlue.tripleLabel, glue_left]
    rfl
  · change _ ≫ pre W (wedgeιRight T (wedge (single 1) U)) =
      _ ≫ pre W (wedgeιRight T (wedge (single 1) U))
    rw [JTOrderedLabelWedge.joinedLabel_right]
    conv_rhs => rw [JTOrderedLabelBinaryGlue.tripleLabel, glue_right]
    change coefficient W z y (wedge (single 1) U) k (joinedPoint (inner (single 1) a)) = _
    rw [fullCoefficient]
    exact inner_identity a

section Maps

variable {P P' : NecklaceCode}
variable (a : Inputs W T U k x z y) (b : Inputs W T' U' k' x z y)
variable (f : T ⟶ T') (g : P ⟶ P') (h : U ⟶ U') (u : k ⟶ k')
variable (hL : coefficient W x z T k a.left =
  std.map u ≫ coefficient W x z T' k' b.left ≫ pre W f.map)
variable (hR : coefficient W z y U k a.right =
  std.map u ≫ coefficient W z y U' k' b.right ≫ pre W h.map)

set_option maxHeartbeats 650000 in
/-- All three native maps and the one common coefficient map give an actual
arrow of decorated labels. -/
def mapIndex : index P a ⟶ index P' b := by
  let l := indexHomOfCoefficient f u a.left b.left hL
  let r := indexHomOfCoefficient h u a.right b.right hR
  let m := constantIndexHom W z g u
  let p := joinedIndexHom (inner P a) (inner P' b) g h u m r rfl rfl
  exact joinedIndexHom (outer P a) (outer P' b) f (wedgeMap g h) u l p rfl rfl

set_option maxHeartbeats 650000 in
theorem mapIndex_projection :
    (pr W x y).map (mapIndex a b f g h u hL hR) = (wedgeOperator f (wedgeOperator g h), u) := by
  rfl

end Maps

private theorem restrict_id {p q : Vertex W} {T : NecklaceCode} {k : SimplexCategory}
    (a : ((orderedNecklaceLabels W (boundaryPoint W p q)).obj (op T)).obj (op k)) :
    coefficient W p q T k a =
      std.map (𝟙 k) ≫ coefficient W p q T k a ≫ pre W (𝟙 T : T ⟶ T).map := by
  change _ = std.map (𝟙 k) ≫ coefficient W p q T k a ≫
    diagramMappingPrecomp (free.map (𝟙 T.toSSet)) W
  rw [std.map_id, Category.id_comp, free.map_id, diagramMappingPrecomp_id]
  exact (Category.comp_id (coefficient W p q T k a)).symm

section Diagrams

variable {A : Type} [SmallCategory A]
variable (L R : A ⥤ NecklaceCode) (degree : A ⥤ SimplexCategory)

/-- Left and right ordered coefficients, with the same literal seam vertex and
the same changing coefficient degree. -/
structure Sides where
  labels : ∀ a, Inputs W (L.obj a) (R.obj a) (degree.obj a) x z y
  left_map : ∀ {a b : A} (f : a ⟶ b),
    coefficient W x z (L.obj a) (degree.obj a) (labels a).left =
      std.map (degree.map f) ≫
        coefficient W x z (L.obj b) (degree.obj b) (labels b).left ≫ pre W (L.map f).map
  right_map : ∀ {a b : A} (f : a ⟶ b),
    coefficient W z y (R.obj a) (degree.obj a) (labels a).right =
      std.map (degree.map f) ≫
        coefficient W z y (R.obj b) (degree.obj b) (labels b).right ≫ pre W (R.map f).map

variable {L R degree}
variable (S : Sides (W := W) (x := x) (z := z) (y := y) L R degree)
variable (M : A ⥤ NecklaceCode)

set_option maxHeartbeats 800000 in
/-- Insert the complete diagram of constant middle necklaces between the
same two decorating side diagrams. -/
def labels : A ⥤ I W x y where
  obj a := index (M.obj a) (S.labels a)
  map f := mapIndex _ _ (L.map f) (M.map f) (R.map f) (degree.map f)
    (S.left_map f) (S.right_map f)
  map_id a := by
    apply hom_ext
    rw [mapIndex_projection, L.map_id, M.map_id, R.map_id, degree.map_id, wedgeOperator_id,
      wedgeOperator_id, (pr W x y).map_id]
    rfl
  map_comp f g := by
    apply hom_ext
    rw [(pr W x y).map_comp, mapIndex_projection, mapIndex_projection, mapIndex_projection,
      L.map_comp, M.map_comp, R.map_comp, degree.map_comp]
    apply Prod.ext
    · change _ = wedgeOperator (L.map f) (wedgeOperator (M.map f) (R.map f)) ≫
        wedgeOperator (L.map g) (wedgeOperator (M.map g) (R.map g))
      rw [wedgeOperator_comp, wedgeOperator_comp]
    · rfl

/-- Read the exact original native and degree operators of an inserted diagram. -/
theorem labels_map_projection {a b : A} (f : a ⟶ b) :
    (pr W x y).map ((labels S M).map f) =
      (wedgeOperator (L.map f) (wedgeOperator (M.map f) (R.map f)), degree.map f) :=
  mapIndex_projection (S.labels a) (S.labels b) (L.map f) (M.map f) (R.map f)
    (degree.map f) (S.left_map f) (S.right_map f)

variable {M} {M' : A ⥤ NecklaceCode} (ρ : M ⟶ M')

set_option maxHeartbeats 850000 in
/-- A natural change of the whole middle interval is an actual decorated
comparison, leaving both side operators and the common coefficient fixed. -/
def middleMap : labels S M ⟶ labels S M' where
  app a := mapIndex (S.labels a) (S.labels a) (𝟙 _) (ρ.app a) (𝟙 _) (𝟙 _)
    (restrict_id _) (restrict_id _)
  naturality {a b} f := by
    apply hom_ext
    simp only [Functor.map_comp]
    change (pr W x y).map (mapIndex (S.labels a) (S.labels b) (L.map f) (M.map f)
        (R.map f) (degree.map f) (S.left_map f) (S.right_map f)) ≫
        (pr W x y).map (mapIndex (S.labels b) (S.labels b) _ _ _ _ _ _) =
      (pr W x y).map (mapIndex (S.labels a) (S.labels a) _ _ _ _ _ _) ≫
        (pr W x y).map (mapIndex (S.labels a) (S.labels b) (L.map f) (M'.map f)
          (R.map f) (degree.map f) (S.left_map f) (S.right_map f))
    simp only [mapIndex_projection]
    apply Prod.ext
    · change wedgeOperator (L.map f) (wedgeOperator (M.map f) (R.map f)) ≫
          wedgeOperator (𝟙 _) (wedgeOperator (ρ.app b) (𝟙 _)) =
        wedgeOperator (𝟙 _) (wedgeOperator (ρ.app a) (𝟙 _)) ≫
          wedgeOperator (L.map f) (wedgeOperator (M'.map f) (R.map f))
      rw [wedgeOperator_comp, wedgeOperator_comp, wedgeOperator_comp, wedgeOperator_comp]
      simp only [Category.id_comp, Category.comp_id, ρ.naturality f]
    · change degree.map f ≫ 𝟙 _ = 𝟙 _ ≫ degree.map f
      rw [Category.id_comp, Category.comp_id]

/-- Collapse the entire middle to the same actual point label. -/
abbrev collapseLabels (M : A ⥤ NecklaceCode) := middleMap S (toPointNatural M)

/-- The coefficient operator of a change of the middle is always the identity. -/
theorem middleMap_coefficient (a : A) :
    ((pr W x y).map ((middleMap S ρ).app a)).2 = 𝟙 (degree.obj a) :=
  congrArg Prod.snd (mapIndex_projection (S.labels a) (S.labels a)
    (𝟙 _) (ρ.app a) (𝟙 _) (𝟙 _) (restrict_id _) (restrict_id _))

end Diagrams

end

end DaggerModels.PartII.JTOrderedLabelJointInsertion
