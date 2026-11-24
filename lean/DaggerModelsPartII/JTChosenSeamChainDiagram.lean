import DaggerModelsPartII.JTWhiskeredSeamDiagram
import DaggerModelsPartII.JTSeamTriangleChoiceDiagram
import DaggerModelsPartII.JTActualJointChoiceChainGraph

/-! Full-chain natural seam triangles from all higher relative filler choices. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open MonoidalCategory CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTChosenSeamChainDiagram

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTEndpointNormalizationLifts (identityFamily)
open JTJointSubcomplexRelativeLift (boundaryPair reverseBoundaryPair identityOnU)
open JTRelativeSeamTriangle (rowEdge fullRowIso boundaryPrecomp)
open TripleBeadEndpointLabel (labels firstRestriction lastRestriction)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
private abbrev Domain := K ⋙ std
variable (incl : U ⟶ Domain K)
variable (f : Domain K ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : Domain K ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ endpointArrow W = boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ endpointArrow W =
  reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a =
  term (U.obj a) ≫ vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a = identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a = identityOnU W z)

private abbrev choices := JTSeamTriangleChoiceDiagram.spaces
  W z U K incl f e s he hs hfU heU hsU

/-- The total category retains every higher relative seam filler simplex. -/
abbrev Cover := JTVariableFixedLiftChoiceDiagram.Cover
  (JTSeamTriangleChoiceDiagram.diagram W z U K incl f e s he hs hfU heU hsU)

/-- Forget a higher filler but retain the original source object and arrow. -/
abbrev projection : Cover W z U K incl f e s he hs hfU heU hsU ⥤ I :=
  JTVariableFixedLiftChoiceDiagram.projection
    (JTSeamTriangleChoiceDiagram.diagram W z U K incl f e s he hs hfU heU hsU)

/-- The original coefficient degree on the full choice cover. -/
abbrev coefficient : Cover W z U K incl f e s he hs hfU heU hsU ⥤
    SimplexCategory := projection W z U K incl f e s he hs hfU heU hsU ⋙ K

/-- The entire simplex degree of a higher filler choice. -/
abbrev choiceTime : Cover W z U K incl f e s he hs hfU heU hsU ⥤
    SimplexCategory := SynchronizedSimplicialParameters.time
      (choices W z U K incl f e s he hs hfU heU hsU)

private abbrev CK := coefficient W z U K incl f e s he hs hfU heU hsU
private abbrev CN := choiceTime W z U K incl f e s he hs hfU heU hsU

/-- One full chain synchronizes old coefficient and higher choice coordinates. -/
abbrev Index := TimePrismChainDiagram.Index
  (CK W z U K incl f e s he hs hfU heU hsU)
  (CN W z U K incl f e s he hs hfU heU hsU)

/-- Forget the chain, retaining its higher filler simplex. -/
abbrev chainBase : Index W z U K incl f e s he hs hfU heU hsU ⥤
    Cover W z U K incl f e s he hs hfU heU hsU :=
  TimePrismChainDiagram.base _ _

/-- The common coefficient-choice chain ordinal. -/
abbrev ordinals : Index W z U K incl f e s he hs hfU heU hsU ⥤
    SimplexCategory := TimePrismChainDiagram.ordinals _ _

/-- The unchanged old coefficient coordinate. -/
abbrev toOld : ordinals W z U K incl f e s he hs hfU heU hsU ⟶
    chainBase W z U K incl f e s he hs hfU heU hsU ⋙
      CK W z U K incl f e s he hs hfU heU hsU :=
  TimePrismChainDiagram.coeffProjection _ _

/-- The full higher filler simplex coordinate on the same chain. -/
abbrev toChoice : ordinals W z U K incl f e s he hs hfU heU hsU ⟶
    chainBase W z U K incl f e s he hs hfU heU hsU ⋙
      CN W z U K incl f e s he hs hfU heU hsU :=
  TimePrismChainDiagram.timeProjection _ _

/-- Projection to the original seam index through the two weak covers. -/
abbrev toOriginal : Index W z U K incl f e s he hs hfU heU hsU ⥤ I :=
  chainBase W z U K incl f e s he hs hfU heU hsU ⋙
    projection W z U K incl f e s he hs hfU heU hsU

/-- The common-chain choice cover is weak over the original index. -/
theorem toOriginal_weak
    (hi : ∀ a : I, Mono (incl.app a))
    (hw : ∀ a : I, WeakEquivalence (incl.app a))
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toOriginal W z U K incl f e s he hs hfU heU hsU)) := by
  haveI : WeakEquivalence (nerveMap (chainBase W z U K incl f e s he hs hfU heU hsU)) :=
    TimePrismChainProjection.projection_weak _ _
  haveI : WeakEquivalence (nerveMap (projection W z U K incl f e s he hs hfU heU hsU)) :=
    JTSeamTriangleChoiceDiagram.projection_weak W z U K incl f e s he hs hfU heU hsU
      hi hw hW
  change WeakEquivalence (nerveMap (chainBase W z U K incl f e s he hs hfU heU hsU) ≫
    nerveMap (projection W z U K incl f e s he hs hfU heU hsU))
  infer_instance

private theorem choice_restrict {c d : Cover W z U K incl f e s he hs hfU heU hsU}
    (g : c ⟶ d) :
    c.unop.2 =
      ((choices W z U K incl f e s he hs hfU heU hsU).obj
        (op ((projection W z U K incl f e s he hs hfU heU hsU).obj c))).map
          ((CN W z U K incl f e s he hs hfU heU hsU).map g).op
        (((choices W z U K incl f e s he hs hfU heU hsU).map
          ((projection W z U K incl f e s he hs hfU heU hsU).map g).op).app
            (op ((CN W z U K incl f e s he hs hfU heU hsU).obj d)) d.unop.2) :=
  g.unop.property.symm

/-- The coefficient-choice prisms before taking common chains. -/
abbrev prisms := JTActualJointChoiceChainGraph.prism
  (CK W z U K incl f e s he hs hfU heU hsU)
  (CN W z U K incl f e s he hs hfU heU hsU)

/-- Every higher filler gives one full row-two map, natural in the original
index operator and in every simplex operator of the filler. -/
def trianglePrism : prisms W z U K incl f e s he hs hfU heU hsU ⟶
    (Functor.const (Cover W z U K incl f e s he hs hfU heU hsU)).obj (row W ⦋2⦌) where
  app c := JTSeamTriangleChoiceDiagram.timeMap W z U K incl f e s he hs hfU heU hsU
    ((projection W z U K incl f e s he hs hfU heU hsU).obj c)
    ((CN W z U K incl f e s he hs hfU heU hsU).obj c) c.unop.2
  naturality c d g := by
    let p := projection W z U K incl f e s he hs hfU heU hsU
    let N := CN W z U K incl f e s he hs hfU heU hsU
    change (std.map (K.map (p.map g)) ⊗ₘ std.map (N.map g)) ≫
        JTSeamTriangleChoiceDiagram.timeMap W z U K incl f e s he hs hfU heU hsU
          (p.obj d) (N.obj d) d.unop.2 =
      JTSeamTriangleChoiceDiagram.timeMap W z U K incl f e s he hs hfU heU hsU
        (p.obj c) (N.obj c) c.unop.2 ≫ 𝟙 _
    rw [Category.comp_id, choice_restrict W z U K incl f e s he hs hfU heU hsU g]
    rw [JTSeamTriangleChoiceDiagram.timeMap_time
      W z U K incl f e s he hs hfU heU hsU (N.map g)
      (p.obj c)
      (((choices W z U K incl f e s he hs hfU heU hsU).map (p.map g).op).app
        (op (N.obj d)) d.unop.2)]
    rw [JTSeamTriangleChoiceDiagram.timeMap_natural
      W z U K incl f e s he hs hfU heU hsU (p.map g) (N.obj d) d.unop.2]
    have ht :
        (std.obj (K.obj (p.obj c)) ◁ std.map (N.map g)) ≫
          ((Domain K).map (p.map g) ▷ std.obj (N.obj d)) =
        std.map (K.map (p.map g)) ⊗ₘ std.map (N.map g) := by
      change (𝟙 _ ⊗ₘ std.map (N.map g)) ≫
        (std.map (K.map (p.map g)) ⊗ₘ 𝟙 _) = _
      rw [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [← Category.assoc, ht]

/-- Each higher triangle choice has exactly its prescribed boundary edge,
including every choice simplex degree. -/
theorem timeMap_edge (a : I) (n : SimplexCategory)
    (v : (choices W z U K incl f e s he hs hfU heU hsU).obj (op a) |>.obj (op n))
    (j : Fin 3) :
    JTSeamTriangleChoiceDiagram.timeMap W z U K incl f e s he hs hfU heU hsU
        a n v ≫ rowEdge W j =
      fst (std.obj (K.obj a)) (std.obj n) ≫
        JTSeamTriangleChoiceDiagram.edges W K f e s a j := by
  let t := JTSeamTriangleChoiceDiagram.timeMap
    W z U K incl f e s he hs hfU heU hsU a n v
  have hface := JTRelativeSeamTriangle.fullEdgePrecomp_row W j
  have hι := JTTriangleBoundaryLabel.full_facePrecomp W j
  have hD := JTTriangleBoundaryLabel.boundaryLabel_face
    (JTSeamTriangleChoiceDiagram.boundaryData W z K f e s he hs a) j
  have hb := JTSeamTriangleChoiceDiagram.timeMap_boundary
    W z U K incl f e s he hs hfU heU hsU a n v
  calc
    t ≫ rowEdge W j =
      t ≫ (fullRowIso W).inv ≫
        JTRelativeSeamTriangle.fullEdgePrecomp W j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      rw [← hface]
    _ = t ≫ (fullRowIso W).inv ≫ boundaryPrecomp W ≫
        JTTriangleBoundaryLabel.facePrecomp W j ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      have hh := congrArg (fun q ↦
        (t ≫ (fullRowIso W).inv) ≫ q ≫
          (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) hι.symm
      simpa only [Category.assoc, boundaryPrecomp,
        JTRelativeSeamTriangle.fullEdgePrecomp] using hh
    _ = fst (std.obj (K.obj a)) (std.obj n) ≫
          JTTriangleBoundaryLabel.boundaryLabel
            (JTSeamTriangleChoiceDiagram.boundaryData W z K f e s he hs a) ≫
          JTTriangleBoundaryLabel.facePrecomp W j ≫
            (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom := by
      have hh := congrArg (fun q ↦ q ≫ JTTriangleBoundaryLabel.facePrecomp W j ≫
        (OrderedSimplexEndpointFiber.freeSimplexRowIso W 1).hom) hb
      simpa only [t, Category.assoc] using hh
    _ = fst (std.obj (K.obj a)) (std.obj n) ≫
          JTSeamTriangleChoiceDiagram.edges W K f e s a j := by
      have hh := congrArg (fun q ↦ fst (std.obj (K.obj a)) (std.obj n) ≫ q) hD
      simpa only [Category.assoc,
        JTSeamTriangleChoiceDiagram.boundaryData_edge] using hh

/-- The literal common-chain chart into the full coefficient-choice prism. -/
abbrev chainChart : ordinals W z U K incl f e s he hs hfU heU hsU ⋙ std ⟶
    chainBase W z U K incl f e s he hs hfU heU hsU ⋙
      prisms W z U K incl f e s he hs hfU heU hsU :=
  JTActualJointChoiceChainGraph.chart _ _

/-- The row-two triangle on every common full chain, without selecting a
filler from any choice fiber. -/
def triangle : ordinals W z U K incl f e s he hs hfU heU hsU ⋙ std ⟶
    (Functor.const (Index W z U K incl f e s he hs hfU heU hsU)).obj
      (row W ⦋2⦌) :=
  chainChart W z U K incl f e s he hs hfU heU hsU ≫
    Functor.whiskerLeft (chainBase W z U K incl f e s he hs hfU heU hsU)
      (trianglePrism W z U K incl f e s he hs hfU heU hsU)

/-- The unchanged varying seam row pulled back through the old coefficient. -/
def seamRow : ordinals W z U K incl f e s he hs hfU heU hsU ⋙ std ⟶
    (Functor.const (Index W z U K incl f e s he hs hfU heU hsU)).obj
      (row W ⦋0⦌) :=
  Functor.whiskerRight (toOld W z U K incl f e s he hs hfU heU hsU) std ≫
    Functor.whiskerLeft (toOriginal W z U K incl f e s he hs hfU heU hsU) f

/-- Every ordinary face of the chosen triangle is the corresponding old
boundary edge after the exact coefficient projection of its common chain. -/
theorem triangle_edge (p : Index W z U K incl f e s he hs hfU heU hsU)
    (j : Fin 3) :
    (triangle W z U K incl f e s he hs hfU heU hsU).app p ≫ rowEdge W j =
      std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p) ≫
        JTSeamTriangleChoiceDiagram.edges W K f e s
          ((toOriginal W z U K incl f e s he hs hfU heU hsU).obj p) j := by
  let c := (chainBase W z U K incl f e s he hs hfU heU hsU).obj p
  have h := timeMap_edge W z U K incl f e s he hs hfU heU hsU
    ((projection W z U K incl f e s he hs hfU heU hsU).obj c)
    ((CN W z U K incl f e s he hs hfU heU hsU).obj c) c.unop.2 j
  have hh := congrArg
    (fun q ↦ (chainChart W z U K incl f e s he hs hfU heU hsU).app p ≫ q) h
  calc
    _ = (chainChart W z U K incl f e s he hs hfU heU hsU).app p ≫
          fst _ _ ≫ JTSeamTriangleChoiceDiagram.edges W K f e s
            ((toOriginal W z U K incl f e s he hs hfU heU hsU).obj p) j := by
      simpa only [triangle, trianglePrism, Category.assoc] using hh
    _ = _ := by
      rw [← Category.assoc]
      change (lift (std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p))
        (std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)) ≫
          fst _ _) ≫ _ = _
      rw [lift_fst]

/-- The full triangle's long face is the identity at the actual varying seam
row on every common coefficient-choice chain. -/
theorem triangle_long (p : Index W z U K incl f e s he hs hfU heU hsU) :
    (triangle W z U K incl f e s he hs hfU heU hsU).app p ≫ rowEdge W 1 =
      (seamRow W z U K incl f e s he hs hfU heU hsU).app p ≫
        identityFamily W := by
  rw [triangle_edge]
  rfl

private theorem triangle_first {k : SimplexCategory}
    (τ : std.obj k ⟶ row W ⦋2⦌) (v : std.obj k ⟶ row W ⦋0⦌)
    (h : τ ≫ rowEdge W 1 = v ≫ identityFamily W) :
    (τ ≫ JTNativeRowLabel.labelFromRow W 2) ≫
        firstRestriction W (single 2) =
      (v ≫ JTNativeRowLabel.labelFromRow W 0) ≫
        firstRestriction W (single 0) := by
  let t := τ ≫ JTNativeRowLabel.labelFromRow W 2
  let q := v ≫ JTNativeRowLabel.labelFromRow W 0
  have hlong := JTSeamNativeCoefficients.triangle_long W τ
  have hid := JTSeamNativeCoefficients.identity_coefficient W v
  calc
    t ≫ firstRestriction W (single 2) =
      (t ≫ pre W JTSeamNativeCoefficients.longEdge.map) ≫
        firstRestriction W (single 1) := by
      have hp := JTWhiskeredMiddleRestriction.pre_first
        (W := W) JTSeamNativeCoefficients.longEdge
      simpa only [Category.assoc] using (congrArg (fun q ↦ t ≫ q) hp).symm
    _ = ((v ≫ identityFamily W) ≫ JTNativeRowLabel.labelFromRow W 1) ≫
        firstRestriction W (single 1) := by
      rw [hlong]
      change ((τ ≫ rowEdge W 1) ≫ JTNativeRowLabel.labelFromRow W 1) ≫ _ = _
      rw [h]
    _ = (q ≫ pre W JTSeamNativeCoefficients.collapseIdentity.map) ≫
        firstRestriction W (single 1) := by rw [hid]
    _ = q ≫ firstRestriction W (single 0) := by
      have hp := JTWhiskeredMiddleRestriction.pre_first
        (W := W) JTSeamNativeCoefficients.collapseIdentity
      simpa only [Category.assoc] using congrArg (fun v ↦ q ≫ v) hp

private theorem triangle_last {k : SimplexCategory}
    (τ : std.obj k ⟶ row W ⦋2⦌) (v : std.obj k ⟶ row W ⦋0⦌)
    (h : τ ≫ rowEdge W 1 = v ≫ identityFamily W) :
    (τ ≫ JTNativeRowLabel.labelFromRow W 2) ≫
        lastRestriction W (single 2) =
      (v ≫ JTNativeRowLabel.labelFromRow W 0) ≫
        lastRestriction W (single 0) := by
  let t := τ ≫ JTNativeRowLabel.labelFromRow W 2
  let q := v ≫ JTNativeRowLabel.labelFromRow W 0
  have hlong := JTSeamNativeCoefficients.triangle_long W τ
  have hid := JTSeamNativeCoefficients.identity_coefficient W v
  calc
    t ≫ lastRestriction W (single 2) =
      (t ≫ pre W JTSeamNativeCoefficients.longEdge.map) ≫
        lastRestriction W (single 1) := by
      have hp := JTWhiskeredMiddleRestriction.pre_last
        (W := W) JTSeamNativeCoefficients.longEdge
      simpa only [Category.assoc] using (congrArg (fun q ↦ t ≫ q) hp).symm
    _ = ((v ≫ identityFamily W) ≫ JTNativeRowLabel.labelFromRow W 1) ≫
        lastRestriction W (single 1) := by
      rw [hlong]
      change ((τ ≫ rowEdge W 1) ≫ JTNativeRowLabel.labelFromRow W 1) ≫ _ = _
      rw [h]
    _ = (q ≫ pre W JTSeamNativeCoefficients.collapseIdentity.map) ≫
        lastRestriction W (single 1) := by rw [hid]
    _ = q ≫ lastRestriction W (single 0) := by
      have hp := JTWhiskeredMiddleRestriction.pre_last
        (W := W) JTSeamNativeCoefficients.collapseIdentity
      simpa only [Category.assoc] using congrArg (fun v ↦ q ≫ v) hp

variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}

/-- The actual varying surrounding coefficients, attached at the original
seam row and fixed at the original two global endpoints. -/
structure Surroundings (P R : I ⥤ NecklaceCode) (x y : Vertex W) where
  left : ∀ a : I, std.obj (K.obj a) ⟶ labels W (P.obj a)
  right : ∀ a : I, std.obj (K.obj a) ⟶ labels W (R.obj a)
  left_join : ∀ a : I, left a ≫ lastRestriction W (P.obj a) =
    (f.app a ≫ JTNativeRowLabel.labelFromRow W 0) ≫ firstRestriction W (single 0)
  right_join : ∀ a : I,
    (f.app a ≫ JTNativeRowLabel.labelFromRow W 0) ≫ lastRestriction W (single 0) =
      right a ≫ firstRestriction W (R.obj a)
  first : ∀ a : I, left a ≫ firstRestriction W (P.obj a) =
    term (std.obj (K.obj a)) ≫ OrderedNecklaceVertexPoints.zeroPoint W x
  last : ∀ a : I, right a ≫ lastRestriction W (R.obj a) =
    term (std.obj (K.obj a)) ≫ OrderedNecklaceVertexPoints.zeroPoint W y
  left_nat : ∀ {a b : I} (g : a ⟶ b),
    left a = std.map (K.map g) ≫ left b ≫ pre W (P.map g).map
  right_nat : ∀ {a b : I} (g : a ⟶ b),
    right a = std.map (K.map g) ≫ right b ≫ pre W (R.map g).map

variable (O : Surroundings W K f P R x y)

private abbrev oldBase (p : Index W z U K incl f e s he hs hfU heU hsU) :=
  (toOriginal W z U K incl f e s he hs hfU heU hsU).obj p
private abbrev α (p : Index W z U K incl f e s he hs hfU heU hsU) :=
  (toOld W z U K incl f e s he hs hfU heU hsU).app p

/-- The complete left coefficient at the unchanged chain degree. -/
def leftCoefficient (p : Index W z U K incl f e s he hs hfU heU hsU) :
    std.obj ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p) ⟶
      labels W (P.obj (oldBase W z U K incl f e s he hs hfU heU hsU p)) :=
  std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
    O.left (oldBase W z U K incl f e s he hs hfU heU hsU p)

/-- The complete right coefficient at that same chain degree. -/
def rightCoefficient (p : Index W z U K incl f e s he hs hfU heU hsU) :
    std.obj ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p) ⟶
      labels W (R.obj (oldBase W z U K incl f e s he hs hfU heU hsU p)) :=
  std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
    O.right (oldBase W z U K incl f e s he hs hfU heU hsU p)

/-- The chosen row-two simplex fits the exact full surrounding labels. -/
def data (p : Index W z U K incl f e s he hs hfU heU hsU) :
    JTThreePieceLabelOperators.Data W
      (P.obj (oldBase W z U K incl f e s he hs hfU heU hsU p))
      (single 2)
      (R.obj (oldBase W z U K incl f e s he hs hfU heU hsU p))
      ((ordinals W z U K incl f e s he hs hfU heU hsU).obj p) x y where
  left := leftCoefficient W z U K incl f e s he hs hfU heU hsU O p
  middle := (triangle W z U K incl f e s he hs hfU heU hsU).app p ≫
    JTNativeRowLabel.labelFromRow W 2
  right := rightCoefficient W z U K incl f e s he hs hfU heU hsU O p
  left_join := by
    let a := oldBase W z U K incl f e s he hs hfU heU hsU p
    let v := (seamRow W z U K incl f e s he hs hfU heU hsU).app p
    have ht := triangle_first W
      ((triangle W z U K incl f e s he hs hfU heU hsU).app p) v
      (triangle_long W z U K incl f e s he hs hfU heU hsU p)
    calc
      _ = std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
            (O.left a ≫ lastRestriction W (P.obj a)) := by
        rfl
      _ = std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
            ((f.app a ≫ JTNativeRowLabel.labelFromRow W 0) ≫
              firstRestriction W (single 0)) := by rw [O.left_join]
      _ = (v ≫ JTNativeRowLabel.labelFromRow W 0) ≫
            firstRestriction W (single 0) := by rfl
      _ = _ := ht.symm
  right_join := by
    let a := oldBase W z U K incl f e s he hs hfU heU hsU p
    let v := (seamRow W z U K incl f e s he hs hfU heU hsU).app p
    have ht := triangle_last W
      ((triangle W z U K incl f e s he hs hfU heU hsU).app p) v
      (triangle_long W z U K incl f e s he hs hfU heU hsU p)
    calc
      _ = (v ≫ JTNativeRowLabel.labelFromRow W 0) ≫
            lastRestriction W (single 0) := ht
      _ = std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
            ((f.app a ≫ JTNativeRowLabel.labelFromRow W 0) ≫
              lastRestriction W (single 0)) := by rfl
      _ = std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫
            (O.right a ≫ firstRestriction W (R.obj a)) := by rw [O.right_join]
      _ = _ := by rfl
  first := by
    let a := oldBase W z U K incl f e s he hs hfU heU hsU p
    change (std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫ O.left a) ≫
        firstRestriction W (P.obj a) = _
    rw [Category.assoc, O.first]
    simp only [← Category.assoc]
    congr 1
  last := by
    let a := oldBase W z U K incl f e s he hs hfU heU hsU p
    change (std.map (α W z U K incl f e s he hs hfU heU hsU p) ≫ O.right a) ≫
        lastRestriction W (R.obj a) = _
    rw [Category.assoc, O.last]
    simp only [← Category.assoc]
    congr 1

private theorem leftCoefficient_natural
    {p q : Index W z U K incl f e s he hs hfU heU hsU} (g : p ⟶ q) :
    leftCoefficient W z U K incl f e s he hs hfU heU hsU O p =
      std.map ((ordinals W z U K incl f e s he hs hfU heU hsU).map g) ≫
        leftCoefficient W z U K incl f e s he hs hfU heU hsU O q ≫
          pre W (P.map ((toOriginal W z U K incl f e s he hs hfU heU hsU).map g)).map := by
  let b := toOriginal W z U K incl f e s he hs hfU heU hsU
  let n := ordinals W z U K incl f e s he hs hfU heU hsU
  let v := toOld W z U K incl f e s he hs hfU heU hsU
  have hn := v.naturality g
  change n.map g ≫ v.app q = v.app p ≫ K.map (b.map g) at hn
  change std.map (v.app p) ≫ O.left (b.obj p) =
    std.map (n.map g) ≫ (std.map (v.app q) ≫ O.left (b.obj q)) ≫
      pre W (P.map (b.map g)).map
  rw [O.left_nat (b.map g)]
  have hh := congrArg
    (fun t ↦ std.map t ≫ O.left (b.obj q) ≫ pre W (P.map (b.map g)).map) hn.symm
  simpa only [std.map_comp, Category.assoc] using hh

private theorem rightCoefficient_natural
    {p q : Index W z U K incl f e s he hs hfU heU hsU} (g : p ⟶ q) :
    rightCoefficient W z U K incl f e s he hs hfU heU hsU O p =
      std.map ((ordinals W z U K incl f e s he hs hfU heU hsU).map g) ≫
        rightCoefficient W z U K incl f e s he hs hfU heU hsU O q ≫
          pre W (R.map ((toOriginal W z U K incl f e s he hs hfU heU hsU).map g)).map := by
  let b := toOriginal W z U K incl f e s he hs hfU heU hsU
  let n := ordinals W z U K incl f e s he hs hfU heU hsU
  let v := toOld W z U K incl f e s he hs hfU heU hsU
  have hn := v.naturality g
  change n.map g ≫ v.app q = v.app p ≫ K.map (b.map g) at hn
  change std.map (v.app p) ≫ O.right (b.obj p) =
    std.map (n.map g) ≫ (std.map (v.app q) ≫ O.right (b.obj q)) ≫
      pre W (R.map (b.map g)).map
  rw [O.right_nat (b.map g)]
  have hh := congrArg
    (fun t ↦ std.map t ≫ O.right (b.obj q) ≫ pre W (R.map (b.map g)).map) hn.symm
  simpa only [std.map_comp, Category.assoc] using hh

set_option maxHeartbeats 3000000 in
/-- The entire chosen seam span forms a genuine natural three-piece family.
The triangle and seam row come from all higher choices on one full chain. -/
def seamFamily : JTWhiskeredSeamDiagram.SeamFamily
    (W := W) (x := x) (y := y)
    (toOriginal W z U K incl f e s he hs hfU heU hsU ⋙ P)
    (toOriginal W z U K incl f e s he hs hfU heU hsU ⋙ R)
    (ordinals W z U K incl f e s he hs hfU heU hsU) where
  triangle := {
    data := data W z U K incl f e s he hs hfU heU hsU O
    left_nat := by
      intro p q g
      exact leftCoefficient_natural W z U K incl f e s he hs hfU heU hsU O g
    middle_nat := by
      intro p q g
      have h := (triangle W z U K incl f e s he hs hfU heU hsU).naturality g
      have hh :
          (triangle W z U K incl f e s he hs hfU heU hsU).app p =
            std.map ((ordinals W z U K incl f e s he hs hfU heU hsU).map g) ≫
              (triangle W z U K incl f e s he hs hfU heU hsU).app q := by
        simpa only [Category.comp_id] using h.symm
      exact congrArg (fun t ↦ t ≫ JTNativeRowLabel.labelFromRow W 2) hh
    right_nat := by
      intro p q g
      exact rightCoefficient_natural W z U K incl f e s he hs hfU heU hsU O g }
  tau p := (triangle W z U K incl f e s he hs hfU heU hsU).app p
  tau_nat := by
    intro p q g
    simpa only [Category.comp_id] using
      ((triangle W z U K incl f e s he hs hfU heU hsU).naturality g).symm
  middle_eq _ := rfl
  seamRow p := (seamRow W z U K incl f e s he hs hfU heU hsU).app p
  seamRow_nat := by
    intro p q g
    simpa only [Category.comp_id] using
      ((seamRow W z U K incl f e s he hs hfU heU hsU).naturality g).symm
  long_eq p := triangle_long W z U K incl f e s he hs hfU heU hsU p

/-- The complete naturally whiskered detour-to-triangle comparison on every
higher choice and every full coefficient-choice chain. -/
def detourToTriangle := JTWhiskeredSeamDiagram.detourToTriangle
  (seamFamily W z U K incl f e s he hs hfU heU hsU O)

/-- The full long-edge-to-triangle comparison on the same common chains. -/
def longToTriangle := JTWhiskeredSeamDiagram.longToTriangle
  (seamFamily W z U K incl f e s he hs hfU heU hsU O)

/-- The natural collapse of the identity long edge at the original seam row. -/
def longToCollapsed := JTWhiskeredSeamDiagram.longToCollapsed
  (seamFamily W z U K incl f e s he hs hfU heU hsU O)

/-- The entire chosen triangle is stationary whenever a chain simplex lands
in the original FULL support face after the old coefficient projection. -/
theorem triangle_onSupport (p : Index W z U K incl f e s he hs hfU heU hsU)
    (s₀ : SimplexCategory)
    (u : s₀ ⟶ (ordinals W z U K incl f e s he hs hfU heU hsU).obj p)
    (a : std.obj s₀ ⟶
      U.obj ((toOriginal W z U K incl f e s he hs hfU heU hsU).obj p))
    (h : std.map u ≫
      std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p) =
        a ≫ incl.app ((toOriginal W z U K incl f e s he hs hfU heU hsU).obj p)) :
    std.map u ≫ (triangle W z U K incl f e s he hs hfU heU hsU).app p =
      term (std.obj s₀) ≫ vertexPoint W z ≫
        JTRelativeSeamTriangle.identityTriangle W := by
  let c := (chainBase W z U K incl f e s he hs hfU heU hsU).obj p
  let b := (toOriginal W z U K incl f e s he hs hfU heU hsU).obj p
  let n := (CN W z U K incl f e s he hs hfU heU hsU).obj c
  let v := std.map u ≫
    std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)
  let factor : std.obj s₀ ⟶ U.obj b ⊗ std.obj n := lift a v
  have hchart : std.map u ≫
      (chainChart W z U K incl f e s he hs hfU heU hsU).app p =
        factor ≫ (incl.app b ▷ std.obj n) := by
    apply CartesianMonoidalCategory.hom_ext
    · change std.map u ≫
          lift (std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p))
            (std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)) ≫
              fst _ _ = factor ≫ (incl.app b ▷ std.obj n) ≫ fst _ _
      simpa only [Category.assoc, lift_fst, tensorHom_fst, factor] using h
    · change std.map u ≫
          lift (std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p))
            (std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)) ≫
              snd _ _ = factor ≫ (incl.app b ▷ std.obj n) ≫ snd _ _
      change std.map u ≫
          lift (std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p))
            (std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)) ≫
              snd _ _ = lift a v ≫ (incl.app b ⊗ₘ 𝟙 (std.obj n)) ≫ snd _ _
      simp only [Category.assoc, lift_snd_assoc, tensorHom_snd,
        v]
      have hh := congrArg (fun q ↦ std.map u ≫ q)
        (lift_snd
          (std.map ((toOld W z U K incl f e s he hs hfU heU hsU).app p))
          (std.map ((toChoice W z U K incl f e s he hs hfU heU hsU).app p)))
      simpa only [Category.assoc, Category.comp_id] using hh
  have hsupport := JTSeamTriangleChoiceDiagram.timeMap_support
    W z U K incl f e s he hs hfU heU hsU b n c.unop.2
  calc
    std.map u ≫ (triangle W z U K incl f e s he hs hfU heU hsU).app p =
      (std.map u ≫ (chainChart W z U K incl f e s he hs hfU heU hsU).app p) ≫
        (trianglePrism W z U K incl f e s he hs hfU heU hsU).app c := by rfl
    _ = factor ≫ (incl.app b ▷ std.obj n) ≫
          JTSeamTriangleChoiceDiagram.timeMap W z U K incl f e s he hs hfU heU hsU
            b n c.unop.2 := by rw [hchart]; rfl
    _ = factor ≫ fst (U.obj b) (std.obj n) ≫
          (term (U.obj b) ≫ vertexPoint W z ≫
            JTRelativeSeamTriangle.identityTriangle W) := by
      simpa only [Category.assoc] using congrArg (fun q ↦ factor ≫ q) hsupport
    _ = _ := by
      have ht : factor ≫ fst (U.obj b) (std.obj n) ≫ term (U.obj b) =
          term (std.obj s₀) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      simpa only [Category.assoc] using
        congrArg (fun q ↦ q ≫ vertexPoint W z ≫
          JTRelativeSeamTriangle.identityTriangle W) ht

end
end DaggerModels.PartII.JTChosenSeamChainDiagram
