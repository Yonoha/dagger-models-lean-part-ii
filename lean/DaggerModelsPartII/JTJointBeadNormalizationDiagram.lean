import DaggerModelsPartII.JTJointBeadFullSupportChoices
import DaggerModelsPartII.JTThreePieceLabelOperators
import DaggerModelsPartII.JTParametrizedBeadGraphTimeMapOperators
import DaggerModelsPartII.JTNativeRowCoefficientOperators
import DaggerModelsPartII.TimePrismChainProjection

/-! Natural three-piece normalized labels on every full-support bead chain. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTJointBeadNormalizationDiagram

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row endpointArrow)
open JTTargetJointMarks (Joint)
open JTParametrizedBeadGraph (jointCoefficient)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

variable {A B : Type} [SmallCategory A] [SmallCategory B]
variable {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)
variable (base : B ⥤ A) (D : B ⥤ SimplexCategory)
variable (h₀ : ∀ {a b : B} (f : a ⟶ b), (D.map f).toOrderHom 0 = 0)
variable (h₁ : ∀ {a b : B} (f : a ⟶ b),
  (D.map f).toOrderHom (Fin.last (D.obj a).len) = Fin.last (D.obj b).len)
variable (r : ∀ b : B, (single (D.obj b).len).toSSet ⟶
  (JTTargetIntervalPullback.sourceInterval (F.collapse.app (base.obj b)) j j le_rfl).toSSet)
private abbrev native (b : B) :=
  r b ≫ JTTargetIntervalGluing.middleInclusion (F.collapse.app (base.obj b)) j
variable (hr : ∀ {a b : B} (f : a ⟶ b),
  (singleIso (D.obj a).len).inv ≫ native F j base D r a ≫
    ((codes L).map (base.map f)).map =
  std.map (D.map f) ≫ (singleIso (D.obj b).len).inv ≫ native F j base D r b)

private abbrev Choice := JTJointBeadFullSupportChoices.Cover F j base D h₀ h₁ r hr
private abbrev K := JTJointBeadFullSupportChoices.coefficient F j base D h₀ h₁ r hr
private abbrev N := JTJointBeadFullSupportChoices.choiceTime F j base D h₀ h₁ r hr

/-- The full chain category over all relative choices of both bead endpoints. -/
abbrev Index := TimePrismChainDiagram.Index (K F j base D h₀ h₁ r hr)
  (N F j base D h₀ h₁ r hr)

/-- Forget the chain while retaining the complete paired edge choice. -/
abbrev chainBase : Index F j base D h₀ h₁ r hr ⥤ Choice F j base D h₀ h₁ r hr :=
  TimePrismChainDiagram.base _ _

/-- The coefficient ordinal of the full coefficient-choice-time chain. -/
abbrev ordinals : Index F j base D h₀ h₁ r hr ⥤ SimplexCategory :=
  TimePrismChainDiagram.ordinals _ _

/-- The original old coefficient projection of each chain. -/
abbrev toOriginal : ordinals F j base D h₀ h₁ r hr ⟶
    chainBase F j base D h₀ h₁ r hr ⋙ K F j base D h₀ h₁ r hr :=
  TimePrismChainDiagram.coeffProjection _ _

/-- The higher-choice time projection of the same chain. -/
abbrev toChoice : ordinals F j base D h₀ h₁ r hr ⟶
    chainBase F j base D h₀ h₁ r hr ⋙ N F j base D h₀ h₁ r hr :=
  TimePrismChainDiagram.timeProjection _ _

/-- Every old coefficient vertex occurs in each full chain. -/
theorem toOriginal_surjective (p : Index F j base D h₀ h₁ r hr) :
    Function.Surjective ((toOriginal F j base D h₀ h₁ r hr).app p).toOrderHom :=
  TimePrismChainDiagram.coeffProjection_surjective _ _ p

/-- The chain category weakly covers the full higher-choice chart. -/
theorem chainBase_weak :
    WeakEquivalence (nerveMap (chainBase F j base D h₀ h₁ r hr)) :=
  TimePrismChainProjection.projection_weak _ _

/-- Forget both the full chain and its higher endpoint choice, retaining the
original overlap-bead chart and every chart arrow. -/
abbrev toCharts : Index F j base D h₀ h₁ r hr ⥤ B :=
  chainBase F j base D h₀ h₁ r hr ⋙
    JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr

/-- The entire normalized-label domain is a nerve weak cover of the original
bead chart category. -/
theorem toCharts_weak
    (hW : letI : ModelCategory Source :=
      InjectiveKanDiagram.modelCategory ReverseSimplexᵒᵖ; IsFibrant W) :
    WeakEquivalence (nerveMap (toCharts F j base D h₀ h₁ r hr)) := by
  haveI : WeakEquivalence (nerveMap (chainBase F j base D h₀ h₁ r hr)) :=
    chainBase_weak F j base D h₀ h₁ r hr
  haveI : WeakEquivalence (nerveMap
      (JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr)) :=
    JTJointBeadFullSupportChoices.projection_weak F j base D h₀ h₁ r hr hW
  change WeakEquivalence (nerveMap (chainBase F j base D h₀ h₁ r hr) ≫
    nerveMap (JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr))
  infer_instance

private abbrev prism := JTJointBeadFullSupportChoices.prisms F j base D h₀ h₁ r hr
private abbrev chart := JTActualJointChoiceChainGraph.chart
  (K F j base D h₀ h₁ r hr) (N F j base D h₀ h₁ r hr)

/-- Full front edge row on every coefficient-time chain. -/
def front : ordinals F j base D h₀ h₁ r hr ⋙ std ⟶
    (Functor.const (Index F j base D h₀ h₁ r hr)).obj (row W ⦋1⦌) :=
  chart F j base D h₀ h₁ r hr ≫ Functor.whiskerLeft
    (chainBase F j base D h₀ h₁ r hr)
    (JTJointBeadFullSupportChoices.front F j base D h₀ h₁ r hr)

/-- Full back edge row on those identical chains. -/
def back : ordinals F j base D h₀ h₁ r hr ⋙ std ⟶
    (Functor.const (Index F j base D h₀ h₁ r hr)).obj (row W ⦋1⦌) :=
  chart F j base D h₀ h₁ r hr ≫ Functor.whiskerLeft
    (chainBase F j base D h₀ h₁ r hr)
    (JTJointBeadFullSupportChoices.back F j base D h₀ h₁ r hr)

private abbrev source := chainBase F j base D h₀ h₁ r hr ⋙
  JTJointBeadFullSupportChoices.projection F j base D h₀ h₁ r hr
private abbrev b (p : Index F j base D h₀ h₁ r hr) :=
  (source F j base D h₀ h₁ r hr).obj p
private abbrev n (p : Index F j base D h₀ h₁ r hr) :=
  (ordinals F j base D h₀ h₁ r hr).obj p
private abbrev α (p : Index F j base D h₀ h₁ r hr) :=
  (toOriginal F j base D h₀ h₁ r hr).app p
private abbrev z := jointCoefficient (Q := Q) j
private abbrev oldRow (a : B) :=
  JTParametrizedBeadGraph.coefficient (a := base.obj a) (D.obj a).len
    (native F j base D r a)
private abbrev rowMap {a c : B} (f : a ⟶ c) :=
  (Rows W).map (D.map f).op
private abbrev u {a c : B} (f : a ⟶ c) : ⦋(D.obj a).len⦌ ⟶ ⦋(D.obj c).len⦌ :=
  eqToHom (D.obj a).mk_len ≫ D.map f ≫ eqToHom (D.obj c).mk_len.symm
private theorem u_eq {a c : B} (f : a ⟶ c) : std.map (u D f) = std.map (D.map f) := by
  simp only [u, SimplexCategory.mk_len, eqToHom_refl,
    Category.id_comp, Category.comp_id]

include hr in
/-- The original bead's whole row coefficient transports under both its
native horizontal operator and the unchanged original coefficient operator. -/
theorem oldRow_map {a c : B} (f : a ⟶ c) :
    oldRow F j base D r a =
      std.map ((JTJointBeadFullSupportChoices.oldDegrees (L := L) base).map f) ≫
        oldRow F j base D r c ≫ rowMap (W := W) D f := by
  let g := base.map f
  let u := D.map f
  let i := native F j base D r a
  let i' := native F j base D r c
  have hc := JTParametrizedBeadGraph.coefficient_map g (D.obj a).len i
  have hh := JTParametrizedBeadGraph.coefficient_horizontal
    (a := base.obj c) (i ≫ ((codes L).map g).map) i' u (hr f)
  change std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
      JTParametrizedBeadGraph.coefficient (a := base.obj c) (D.obj a).len
        (i ≫ ((codes L).map g).map) =
    JTParametrizedBeadGraph.coefficient (a := base.obj a) (D.obj a).len i at hc
  change JTParametrizedBeadGraph.coefficient (a := base.obj c) (D.obj a).len
      (i ≫ ((codes L).map g).map) =
    JTParametrizedBeadGraph.coefficient (a := base.obj c) (D.obj c).len i' ≫
      (Rows W).map u.op at hh
  change JTParametrizedBeadGraph.coefficient (a := base.obj a) (D.obj a).len i =
    std.map ((JTJointRelativeGraphFamily.coefficient (L := L)).map g) ≫
      JTParametrizedBeadGraph.coefficient (a := base.obj c) (D.obj c).len i' ≫
        (Rows W).map u.op
  rw [← hh, hc]

/-- The original native bead label, reindexed at the full chain degree. -/
def oldMiddle (p : Index F j base D h₀ h₁ r hr) :
    std.obj (n F j base D h₀ h₁ r hr p) ⟶
      TripleBeadEndpointLabel.labels W (single (D.obj (b F j base D h₀ h₁ r hr p)).len) :=
  std.map (α F j base D h₀ h₁ r hr p) ≫
    oldRow F j base D r (b F j base D h₀ h₁ r hr p) ≫
      JTNativeRowLabel.labelFromRow W (D.obj (b F j base D h₀ h₁ r hr p)).len

/-- The middle is literally the original restricted bead label at the old
coefficient degree, then pulled back to the full chain degree. -/
theorem oldMiddle_eq (p : Index F j base D h₀ h₁ r hr) :
    oldMiddle F j base D h₀ h₁ r hr p =
      std.map (α F j base D h₀ h₁ r hr p) ≫
        JTJointBeadSupportedNormalization.coefficient F
          (base.obj (b F j base D h₀ h₁ r hr p))
          (D.obj (b F j base D h₀ h₁ r hr p)).len j
          (r (b F j base D h₀ h₁ r hr p)) := by
  have h := JTParametrizedBeadGraph.coefficient_label
    (a := base.obj (b F j base D h₀ h₁ r hr p))
    (D.obj (b F j base D h₀ h₁ r hr p)).len
    (native F j base D r (b F j base D h₀ h₁ r hr p))
  have h' : oldRow F j base D r (b F j base D h₀ h₁ r hr p) ≫
      JTNativeRowLabel.labelFromRow W (D.obj (b F j base D h₀ h₁ r hr p)).len =
        JTJointBeadSupportedNormalization.coefficient F
          (base.obj (b F j base D h₀ h₁ r hr p))
          (D.obj (b F j base D h₀ h₁ r hr p)).len j
          (r (b F j base D h₀ h₁ r hr p)) := by
    apply SSet.yonedaEquiv.injective
    simpa only [JTJointBeadSupportedNormalization.coefficient,
      Equiv.apply_symm_apply] using h
  exact congrArg (fun t ↦ std.map (α F j base D h₀ h₁ r hr p) ≫ t) h'

private abbrev firstRow (p : Index F j base D h₀ h₁ r hr) :=
  std.map (α F j base D h₀ h₁ r hr p) ≫
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr).app
      (b F j base D h₀ h₁ r hr p)
private abbrev lastRow (p : Index F j base D h₀ h₁ r hr) :=
  std.map (α F j base D h₀ h₁ r hr p) ≫
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr).app
      (b F j base D h₀ h₁ r hr p)

/-- The front edge runs from the joint to the actual old first row. -/
theorem front_pair (p : Index F j base D h₀ h₁ r hr) :
    (front F j base D h₀ h₁ r hr).app p ≫ endpointArrow W =
      JTJointEndpointRelativeLift.reverseBoundaryPair W
        (firstRow F j base D h₀ h₁ r hr p) (z j) := by
  have h := JTTwoEndpointChoicePrism.front_endpoints W
    (JTJointBeadFullSupportChoices.degrees F j base D r hr)
    (JTJointBeadFullSupportChoices.oldDegrees (L := L) base)
    (JTJointBeadFullSupportChoices.incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr) (z j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)
    ((chainBase F j base D h₀ h₁ r hr).obj p)
  change ((chart F j base D h₀ h₁ r hr).app p ≫
      (JTJointBeadFullSupportChoices.front F j base D h₀ h₁ r hr).app
        ((chainBase F j base D h₀ h₁ r hr).obj p)) ≫ endpointArrow W = _
  rw [Category.assoc, h]
  change lift (std.map (α F j base D h₀ h₁ r hr p))
      (std.map ((toChoice F j base D h₀ h₁ r hr).app p)) ≫
        fst _ _ ≫ JTJointEndpointRelativeLift.reverseBoundaryPair W
          ((JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr).app
            (b F j base D h₀ h₁ r hr p)) (z j) = _
  rw [lift_fst_assoc]
  exact JTJointEndpointRelativeLift.reverseBoundaryPair_natural W (z j)
    (α F j base D h₀ h₁ r hr p) _

/-- The back edge runs from the actual old last row to the joint. -/
theorem back_pair (p : Index F j base D h₀ h₁ r hr) :
    (back F j base D h₀ h₁ r hr).app p ≫ endpointArrow W =
      JTJointEndpointRelativeLift.boundaryPair W
        (lastRow F j base D h₀ h₁ r hr p) (z j) := by
  have h := JTTwoEndpointChoicePrism.back_endpoints W
    (JTJointBeadFullSupportChoices.degrees F j base D r hr)
    (JTJointBeadFullSupportChoices.oldDegrees (L := L) base)
    (JTJointBeadFullSupportChoices.incl F j base D r hr)
    (JTJointBeadEndpointDiagram.firstRows F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr) (z j)
    (JTJointBeadEndpointDiagram.firstRows_supported F j base D h₀ r hr)
    (JTJointBeadEndpointDiagram.lastRows_supported F j base D h₁ r hr)
    ((chainBase F j base D h₀ h₁ r hr).obj p)
  change ((chart F j base D h₀ h₁ r hr).app p ≫
      (JTJointBeadFullSupportChoices.back F j base D h₀ h₁ r hr).app
        ((chainBase F j base D h₀ h₁ r hr).obj p)) ≫ endpointArrow W = _
  rw [Category.assoc, h]
  change lift (std.map (α F j base D h₀ h₁ r hr p))
      (std.map ((toChoice F j base D h₀ h₁ r hr).app p)) ≫
        fst _ _ ≫ JTJointEndpointRelativeLift.boundaryPair W
          ((JTJointBeadEndpointDiagram.lastRows F j base D h₁ r hr).app
            (b F j base D h₀ h₁ r hr p)) (z j) = _
  rw [lift_fst_assoc]
  exact JTJointEndpointRelativeLift.boundaryPair_natural W (z j)
    (α F j base D h₀ h₁ r hr p) _

/-- The old bead's first native endpoint equals its first row at every chain. -/
theorem oldMiddle_first (p : Index F j base D h₀ h₁ r hr) :
    oldMiddle F j base D h₀ h₁ r hr p ≫
      TripleBeadEndpointLabel.firstRestriction W
        (single (D.obj (b F j base D h₀ h₁ r hr p)).len) =
      firstRow F j base D h₀ h₁ r hr p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  simp only [oldMiddle, firstRow, TripleBeadEndpointLabel.firstRestriction,
    Category.assoc]
  rw [JTNativeRowLabel.labelFromRow_vertex]
  rfl

/-- The old bead's last native endpoint equals its last row at every chain. -/
theorem oldMiddle_last (p : Index F j base D h₀ h₁ r hr) :
    oldMiddle F j base D h₀ h₁ r hr p ≫
      TripleBeadEndpointLabel.lastRestriction W
        (single (D.obj (b F j base D h₀ h₁ r hr p)).len) =
      lastRow F j base D h₀ h₁ r hr p ≫
        TwoBeadEndpointLabel.jointLabelFromRow W := by
  simp only [oldMiddle, lastRow, TripleBeadEndpointLabel.lastRestriction,
    Category.assoc]
  rw [JTNativeRowLabel.labelFromRow_vertex]
  rfl

/-- The three actual native coefficients share the unchanged old chain degree. -/
def data (p : Index F j base D h₀ h₁ r hr) :
    JTThreePieceLabelOperators.Data W E
      (single (D.obj (b F j base D h₀ h₁ r hr p)).len) E
      (n F j base D h₀ h₁ r hr p) (z j) (z j) :=
  { left := (front F j base D h₀ h₁ r hr).app p ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W
    middle := oldMiddle F j base D h₀ h₁ r hr p
    right := (back F j base D h₀ h₁ r hr).app p ≫
      TwoBeadEndpointLabel.edgeLabelFromRow W
    left_join := by
      rw [JTWhiskerEdgeCoefficient.last,
        (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
          (front_pair F j base D h₀ h₁ r hr p)).2]
      exact (oldMiddle_first F j base D h₀ h₁ r hr p).symm
    right_join := by
      rw [JTWhiskerEdgeCoefficient.first,
        (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
          (back_pair F j base D h₀ h₁ r hr p)).1]
      exact oldMiddle_last F j base D h₀ h₁ r hr p
    first := by
      rw [JTWhiskerEdgeCoefficient.first,
        (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
          (front_pair F j base D h₀ h₁ r hr p)).1]
      simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]
    last := by
      rw [JTWhiskerEdgeCoefficient.last,
        (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
          (back_pair F j base D h₀ h₁ r hr p)).2]
      simp only [Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex] }

private abbrev beadDiagram := JTJointBeadOverlapDiagram.natives D h₀ h₁
private abbrev oldArrow {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :=
  (source F j base D h₀ h₁ r hr).map f
private abbrev nativeMap {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :=
  (beadDiagram D h₀ h₁).map (oldArrow F j base D h₀ h₁ r hr f)
private abbrev pre (W : Source) {S T : SSet.{0}} (g : S ⟶ T) :=
  diagramMappingPrecomp (discreteFree.map g) W

private theorem nativeMap_eq {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    (nativeMap F j base D h₀ h₁ r hr f).map =
      JTNativeRowCoefficientOperators.nativeOperator
        (u D (oldArrow F j base D h₀ h₁ r hr f)) := rfl

include hr in
private theorem oldLabel_map {a c : B} (f : a ⟶ c) :
    oldRow F j base D r a ≫ JTNativeRowLabel.labelFromRow W (D.obj a).len =
      std.map ((JTJointBeadFullSupportChoices.oldDegrees (L := L) base).map f) ≫
        (oldRow F j base D r c ≫ JTNativeRowLabel.labelFromRow W (D.obj c).len) ≫
          pre W (JTNativeRowCoefficientOperators.nativeOperator (u D f)) := by
  rw [oldRow_map F j base D r hr f]
  simp only [Category.assoc]
  have hu : (Rows W).map (D.map f).op = (Rows W).map (u D f).op := by
    congr 1
    simp only [u, SimplexCategory.mk_len, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  dsimp only [rowMap]
  rw [hu, ← JTNativeRowCoefficientOperators.labelFromRow_operator W (u D f)]

private theorem original_natural {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    α F j base D h₀ h₁ r hr p ≫
        (JTJointBeadFullSupportChoices.oldDegrees (L := L) base).map
          (oldArrow F j base D h₀ h₁ r hr f) =
      (ordinals F j base D h₀ h₁ r hr).map f ≫ α F j base D h₀ h₁ r hr q :=
  (toOriginal F j base D h₀ h₁ r hr).naturality f |>.symm

/-- The retained old middle label is natural under every chart and chain arrow. -/
theorem oldMiddle_map {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    oldMiddle F j base D h₀ h₁ r hr p =
      std.map ((ordinals F j base D h₀ h₁ r hr).map f) ≫
        oldMiddle F j base D h₀ h₁ r hr q ≫
          pre W (nativeMap F j base D h₀ h₁ r hr f).map := by
  have hm := oldLabel_map F j base D r hr (oldArrow F j base D h₀ h₁ r hr f)
  rw [← nativeMap_eq F j base D h₀ h₁ r hr f] at hm
  unfold oldMiddle
  rw [hm]
  have hα := congrArg std.map (original_natural F j base D h₀ h₁ r hr f)
  simpa only [std.map_comp, Category.assoc] using
    congrArg (fun t ↦ t ≫ oldRow F j base D r (b F j base D h₀ h₁ r hr q) ≫
      JTNativeRowLabel.labelFromRow W (D.obj (b F j base D h₀ h₁ r hr q)).len ≫
      pre W (nativeMap F j base D h₀ h₁ r hr f).map) hα

private theorem front_natural {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    (front F j base D h₀ h₁ r hr).app p =
      std.map ((ordinals F j base D h₀ h₁ r hr).map f) ≫
        (front F j base D h₀ h₁ r hr).app q := by
  have h := (front F j base D h₀ h₁ r hr).naturality f
  simpa only [Category.comp_id] using h.symm

private theorem back_natural {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    (back F j base D h₀ h₁ r hr).app p =
      std.map ((ordinals F j base D h₀ h₁ r hr).map f) ≫
        (back F j base D h₀ h₁ r hr).app q := by
  have h := (back F j base D h₀ h₁ r hr).naturality f
  simpa only [Category.comp_id] using h.symm

private theorem pre_id : pre W (𝟙 E.toSSet) = 𝟙 _ := by
  unfold pre
  rw [show discreteFree.map (𝟙 E.toSSet) = 𝟙 _ from discreteFree.map_id _]
  exact diagramMappingPrecomp_id (discreteFree.obj E.toSSet) W

/-- The exact decorated operator around the unchanged old middle bead. -/
def labelMap {p q : Index F j base D h₀ h₁ r hr} (f : p ⟶ q) :
    JTThreePieceLabelOperators.index (data F j base D h₀ h₁ r hr p) ⟶
      JTThreePieceLabelOperators.index (data F j base D h₀ h₁ r hr q) :=
  JTThreePieceLabelOperators.indexMap (data F j base D h₀ h₁ r hr p)
    (data F j base D h₀ h₁ r hr q) (𝟙 E)
    (nativeMap F j base D h₀ h₁ r hr f) (𝟙 E)
    ((ordinals F j base D h₀ h₁ r hr).map f)
    (by
      change ((front F j base D h₀ h₁ r hr).app p ≫
          TwoBeadEndpointLabel.edgeLabelFromRow W) =
        std.map ((ordinals F j base D h₀ h₁ r hr).map f) ≫
          ((front F j base D h₀ h₁ r hr).app q ≫
            TwoBeadEndpointLabel.edgeLabelFromRow W) ≫ pre W (𝟙 E.toSSet)
      rw [pre_id, Category.comp_id, front_natural F j base D h₀ h₁ r hr f,
        Category.assoc])
    (oldMiddle_map F j base D h₀ h₁ r hr f)
    (by
      change ((back F j base D h₀ h₁ r hr).app p ≫
          TwoBeadEndpointLabel.edgeLabelFromRow W) =
        std.map ((ordinals F j base D h₀ h₁ r hr).map f) ≫
          ((back F j base D h₀ h₁ r hr).app q ≫
            TwoBeadEndpointLabel.edgeLabelFromRow W) ≫ pre W (𝟙 E.toSSet)
      rw [pre_id, Category.comp_id, back_natural F j base D h₀ h₁ r hr f,
        Category.assoc])

private abbrev projection :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W (z j) (z j))

private theorem hom_ext {a c : DecoratedNecklaceHomDiagram.Index W (z j) (z j)}
    {f g : a ⟶ c} (h : (projection (W := W) j).map f =
      (projection (W := W) j).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  exact congrArg Quiver.Hom.op h

private theorem labelMap_projection {p q : Index F j base D h₀ h₁ r hr}
    (f : p ⟶ q) :
    (projection (W := W) j).map (labelMap F j base D h₀ h₁ r hr f) =
      (wedgeMap (𝟙 E) (wedgeMap (nativeMap F j base D h₀ h₁ r hr f) (𝟙 E)),
        (ordinals F j base D h₀ h₁ r hr).map f) := rfl

private theorem nativeMap_id (p : Index F j base D h₀ h₁ r hr) :
    nativeMap F j base D h₀ h₁ r hr (𝟙 p) =
      𝟙 (single (D.obj (b F j base D h₀ h₁ r hr p)).len) := by
  simp only [nativeMap, oldArrow, (source F j base D h₀ h₁ r hr).map_id,
    (beadDiagram D h₀ h₁).map_id]
  rfl

private theorem nativeMap_comp {p q s : Index F j base D h₀ h₁ r hr}
    (f : p ⟶ q) (g : q ⟶ s) :
    nativeMap F j base D h₀ h₁ r hr (f ≫ g) =
      nativeMap F j base D h₀ h₁ r hr f ≫
        nativeMap F j base D h₀ h₁ r hr g := by
  simp only [nativeMap, oldArrow, (source F j base D h₀ h₁ r hr).map_comp,
    (beadDiagram D h₀ h₁).map_comp]

/-- Genuine normalized triple ordered labels on all chart, choice and chain arrows. -/
def labels : Index F j base D h₀ h₁ r hr ⥤
    DecoratedNecklaceHomDiagram.Index W (z j) (z j) where
  obj p := JTThreePieceLabelOperators.index (data F j base D h₀ h₁ r hr p)
  map f := labelMap F j base D h₀ h₁ r hr f
  map_id p := by
    apply hom_ext (j := j)
    rw [labelMap_projection, (projection (W := W) j).map_id,
      nativeMap_id F j base D h₀ h₁ r hr p,
      (ordinals F j base D h₀ h₁ r hr).map_id]
    apply Prod.ext
    · change wedgeMap (Hom.id E)
        (wedgeMap (Hom.id (single (D.obj (b F j base D h₀ h₁ r hr p)).len))
          (Hom.id E)) = Hom.id _
      rw [wedgeMap_id, wedgeMap_id]
    · rfl
  map_comp {p q s} f g := by
    apply hom_ext (j := j)
    rw [labelMap_projection, (projection (W := W) j).map_comp,
      labelMap_projection, labelMap_projection,
      nativeMap_comp F j base D h₀ h₁ r hr f g,
      (ordinals F j base D h₀ h₁ r hr).map_comp]
    apply Prod.ext
    · change wedgeMap (Hom.id E)
          (wedgeMap (Hom.comp (nativeMap F j base D h₀ h₁ r hr f)
            (nativeMap F j base D h₀ h₁ r hr g)) (Hom.id E)) =
          Hom.comp
            (wedgeMap (Hom.id E)
              (wedgeMap (nativeMap F j base D h₀ h₁ r hr f) (Hom.id E)))
            (wedgeMap (Hom.id E)
              (wedgeMap (nativeMap F j base D h₀ h₁ r hr g) (Hom.id E)))
      have hi := wedgeMap_comp (nativeMap F j base D h₀ h₁ r hr f)
        (Hom.id E) (nativeMap F j base D h₀ h₁ r hr g) (Hom.id E)
      have ho := wedgeMap_comp (Hom.id E)
        (wedgeMap (nativeMap F j base D h₀ h₁ r hr f) (Hom.id E))
        (Hom.id E) (wedgeMap (nativeMap F j base D h₀ h₁ r hr g) (Hom.id E))
      simpa only [Hom.id_comp, Hom.comp_id] using
        (congrArg (wedgeMap (Hom.id E)) hi).trans ho
    · rfl

end
end DaggerModels.PartII.JTJointBeadNormalizationDiagram
