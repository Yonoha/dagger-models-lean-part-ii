import DaggerModelsPartII.JTJointRelativeParameters
import DaggerModelsPartII.JTParametrizedTargetFamilies
import DaggerModelsPartII.JTGraphSpanLift
import DaggerModelsPartII.JTRestrictedLabelCoefficient
import DaggerModelsPartII.JTFiniteOrdinalConstraints
import DaggerModelsPartII.JTVertexAssignmentCover
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! Relative assembly of the actual decorated graph family before evaluation. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointRelativeGraphFamily

open JTJointRelativeParameters
open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph)
open JTTargetIntervalOverMapping (whole left right overlap leftToWhole rightToWhole)
open JTTargetJointMarks (Joint)
open JTNecklaceEndpointCylinder (cylinder isPushout boundary)
open NecklaceCylinderAugmentation (augmentation augmentation_cylinder)
open DecoratedCylinderNecklacePresentation (underCocone)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : I ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : I ⥤ SimplexCategory}
variable (F : Family Q L time)

private abbrev projection := OrderedLabelElements.projection W (boundaryPoint W x y)
private abbrev code (p : I) := (codes L).obj p

/-- The actual native collapse, functorial over the fixed necklace. -/
abbrev native := Over.lift (codes L) F.collapse

/-- The changing coefficient degree of the original labels. -/
abbrev coefficient := L ⋙ projection (x := x) (y := y) ⋙ CategoryTheory.Prod.snd _ _

private abbrev product := withTime Q.map J time (native F) (whole Q.code)

/-- The complete original graph parameter is a natural transformation. -/
def originalParameter : product F ⟶ coefficient (L := L) ⋙ J where
  app := F.parameter
  naturality p p' f := by
    change ((JTDecoratedIntervalDiagram.parameterize Q.map J time
      (native F ⋙ whole Q.code)).map f).left ≫ F.parameter p' =
        F.parameter p ≫ J.map ((projection.map (L.map f)).2)
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    exact F.parameter_map f

private abbrev rawProjection (p : I) :=
  fst (code (L := L) p).toSSet (J.obj (time.obj p)) ≫ (F.collapse.app p).map ≫ Q.map

private abbrev realization (p : I) :=
  (cylinder (code (L := L) p)).app ((coefficient (L := L)).obj p) ≫
    ((underCocone W x y).app (L.obj p)).right

/-- The exact raw-image condition on a chosen restriction of a graph parameter. -/
def RawOn {S : I ⥤ SSet.{0}} (u : S ⟶ product F) (s : S ⟶ coefficient (L := L) ⋙ J) :
    Prop :=
  ∀ p, lift (u.app p ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p))) (s.app p) ≫
    realization (L := L) p = u.app p ≫ rawProjection F p

/-- Every restriction of the exact original parameter retains its raw map. -/
theorem original_rawOn {S : I ⥤ SSet.{0}} (u : S ⟶ product F) :
    RawOn F u (u ≫ originalParameter F) := by
  intro p
  change lift (u.app p ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p)))
      (u.app p ≫ F.parameter p) ≫ realization (L := L) p = u.app p ≫ rawProjection F p
  rw [← CartesianMonoidalCategory.comp_lift, Category.assoc]
  have h := F.raw p
  change JTInterpolatedReducedCylinder.cylinderMap (code (L := L) p) (F.parameter p) ≫
      ((underCocone W x y).app (L.obj p)).right =
    augmentation (code (L := L) p) (time.obj p) ≫ (F.collapse.app p).map ≫ Q.map at h
  have h' := congrArg (fun r ↦ (cylinder (code (L := L) p)).app (time.obj p) ≫ r) h
  dsimp only at h'
  rw [← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_cylinder, Category.assoc,
    ← Category.assoc ((cylinder (code (L := L) p)).app _), augmentation_cylinder] at h'
  exact congrArg (fun r ↦ u.app p ≫ r) h'

private theorem raw_of_product (s : product F ⟶ coefficient (L := L) ⋙ J)
    (p : I)
    (h : lift (fst (code (L := L) p).toSSet (J.obj (time.obj p))) (s.app p) ≫
      realization (L := L) p = rawProjection F p) :
    (graph (i := L.obj p) (s.app p)).right ≫ ((underCocone W x y).app (L.obj p)).right =
      augmentation (code (L := L) p) (time.obj p) ≫ (F.collapse.app p).map ≫ Q.map := by
  let T := code (L := L) p
  let n := time.obj p
  let k := (coefficient (L := L)).obj p
  let a := s.app p
  let R := ((underCocone W x y).app (L.obj p)).right
  let f := (F.collapse.app p).map
  have hF : JTInterpolatedReducedCylinder.cylinderMap T (F.parameter p) ≫ R =
      augmentation T n ≫ f ≫ Q.map := F.raw p
  change JTInterpolatedReducedCylinder.cylinderMap T a ≫ R =
    augmentation T n ≫ f ≫ Q.map
  apply (isPushout T n).hom_ext
  · rw [← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_cylinder,
      Category.assoc, ← Category.assoc ((cylinder T).app n), augmentation_cylinder]
    exact h
  · rw [← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_boundary, ← hF,
      ← Category.assoc, JTInterpolatedReducedCylinder.cylinderMap_boundary]
    rfl

abbrev leftLeg (j : Joint Q.code) :=
  withTimeMap Q.map J time (native F) (leftToWhole Q.code j)
abbrev rightLeg (j : Joint Q.code) :=
  withTimeMap Q.map J time (native F) (rightToWhole Q.code j)

section Assembly

variable (j : Joint Q.code)
variable (trace : withTime Q.map J time (native F) (overlap Q.code j) ⟶
  coefficient (L := L) ⋙ J)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)

variable (hs : RawOn F (leftLeg F j) (extendLeft Q.map J time (native F) j trace s))
variable (ht : RawOn F (rightLeg F j) (extendRight Q.map J time (native F) j trace t))

private abbrev parameter := assemble Q J time (native F) j trace s t

include hs ht in
private theorem assembled_product_raw (p : I) :
    lift (fst (code (L := L) p).toSSet (J.obj (time.obj p)))
      ((parameter F j trace s t).app p) ≫ realization (L := L) p =
    rawProjection F p := by
  apply ((underlying_isPushout Q J time (native F) j).map ((evaluation I _).obj p)).hom_ext
  · change (leftLeg F j).app p ≫ _ = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    have hp := NatTrans.congr_app (assemble_left Q J time (native F) j trace s t) p
    change (leftLeg F j).app p ≫ (parameter F j trace s t).app p =
      (extendLeft Q.map J time (native F) j trace s).app p at hp
    rw [hp]
    exact hs p
  · change (rightLeg F j).app p ≫ _ = _
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift]
    have hp := NatTrans.congr_app (assemble_right Q J time (native F) j trace s t) p
    change (rightLeg F j).app p ≫ (parameter F j trace s t).app p =
      (extendRight Q.map J time (native F) j trace t).app p at hp
    rw [hp]
    exact ht p

/-- If the synchronized side parameters have the specified raw images on
their full domains, the resulting coherent family evaluates in the original comma. -/
def assembledFamily : Family Q L time where
  collapse := F.collapse
  parameter p := (parameter F j trace s t).app p
  parameter_map {p p'} f := by
    have hn := (parameter F j trace s t).naturality f
    change ((JTDecoratedIntervalDiagram.parameterize Q.map J time
      (native F ⋙ whole Q.code)).map f).left ≫ (parameter F j trace s t).app p' =
      (parameter F j trace s t).app p ≫ J.map ((projection.map (L.map f)).2) at hn
    rw [JTDecoratedIntervalDiagram.parameterize_map_left] at hn
    exact hn
  raw p := raw_of_product F (parameter F j trace s t) p
    (assembled_product_raw F j trace s t hs ht p)

end Assembly

/-- The graph family already used in the original span cover has these
joint-relative coefficient traces with all original span operators. -/
abbrev spanParameter (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :=
  originalParameter (JTGraphSpanLift.spanFamily Q)

section CoefficientRestrictions

open JTTargetIntervalOverMapping (overlapToLeft overlapToRight)
open JTRestrictedLabelCoefficient (factor bead_product_hom_ext)
open JTTargetIntervalPullback (sourceInterval)

private abbrev label (p : I) :=
  OrderedLabelElements.label W (boundaryPoint W x y) (L.obj p)

private abbrev ordered (p : I) :=
  JTRealizedLabelEndpoints.orderedLabel W x y (code (L := L) p)
    ((coefficient (L := L)).obj p) (label (L := L) p)

private abbrev readout {p : I} {T : NecklaceCode} (e : T.toSSet ⟶ (code (L := L) p).toSSet)
    (b : Option T.Bead) :=
  factor (T.pieceι b ≫ e) (ordered (L := L) p)

private theorem raw_eq_of_piece_projections {p : I} {T : NecklaceCode}
    (e : T.toSSet ⟶ (code (L := L) p).toSSet)
    (s t : T.toSSet ⊗ J.obj (time.obj p) ⟶ J.obj ((coefficient (L := L)).obj p))
    (h : ∀ b, (T.pieceι b ⊗ₘ 𝟙 _) ≫ s ≫ J.map (readout (L := L) e b).operator =
      (T.pieceι b ⊗ₘ 𝟙 _) ≫ t ≫ J.map (readout (L := L) e b).operator) :
    lift ((e ⊗ₘ 𝟙 _) ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p))) s ≫
      realization (L := L) p =
    lift ((e ⊗ₘ 𝟙 _) ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p))) t ≫
      realization (L := L) p := by
  let V := J.obj (time.obj p)
  let k := (coefficient (L := L)).obj p
  let C := code (L := L) p
  let R := JTNecklaceLabelRealization.realizedLabel C.toSSet W k (ordered (L := L) p)
  have hR : realization (L := L) p = R := by
    change (cylinder C).app k ≫
      JTNecklaceEndpointCylinder.descend W x y C k (label (L := L) p) = R
    exact JTNecklaceEndpointCylinder.descend_cylinder W x y C k (label (L := L) p)
  rw [hR, tensorHom_fst]
  apply bead_product_hom_ext T
  intro b
  let i := T.pieceι b
  let d := readout (L := L) e b
  have h' : ((i ⊗ₘ 𝟙 V) ≫ s) ≫ J.map d.operator =
      ((i ⊗ₘ 𝟙 V) ≫ t) ≫ J.map d.operator := by
    simpa only [Category.assoc] using h b
  simp only [← Category.assoc, comp_lift, tensorHom_fst]
  simpa only [Category.assoc] using
    d.graph_eq (i ≫ e) (ordered (L := L) p) (fst _ V) _ _ h'

variable (j : Joint Q.code)

private abbrev leftCode (p : I) :=
  sourceInterval ((native F).obj p).hom ⟨0, Q.code.first_mem⟩ j (Fin.zero_le _)
private abbrev rightCode (p : I) :=
  sourceInterval ((native F).obj p).hom j ⟨Fin.last Q.code.len, Q.code.last_mem⟩ (Fin.le_last _)

private abbrev leftHorizontal (p : I) :=
  ((leftToWhole Q.code j).app ((native F).obj p)).left
private abbrev rightHorizontal (p : I) :=
  ((rightToWhole Q.code j).app ((native F).obj p)).left

variable (trace : withTime Q.map J time (native F) (overlap Q.code j) ⟶
  coefficient (L := L) ⋙ J)
variable (s : withTime Q.map J time (native F) (left Q.code j) ⟶ coefficient (L := L) ⋙ J)
variable (t : withTime Q.map J time (native F) (right Q.code j) ⟶ coefficient (L := L) ⋙ J)

/-- The prescribed overlap must have the same remaining left coefficient at
each joint vertex after the nondegenerate reduction for its piece. -/
def LeftTraceMatches : Prop :=
  ∀ (p : I) (b : Option (leftCode F j p).Bead),
    TraceMatches ((withTimeMap Q.map J time (native F) (overlapToLeft Q.code j)).app p)
      (trace.app p) (s.app p) ((leftCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p)))
      (readout (L := L) (leftHorizontal F j p) b).operator

/-- The prescribed overlap must have the same remaining right coefficient at
each joint vertex after the nondegenerate reduction for its piece. -/
def RightTraceMatches : Prop :=
  ∀ (p : I) (b : Option (rightCode F j p).Bead),
    TraceMatches ((withTimeMap Q.map J time (native F) (overlapToRight Q.code j)).app p)
      (trace.app p) (t.app p) ((rightCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p)))
      (readout (L := L) (rightHorizontal F j p) b).operator

set_option maxHeartbeats 650000 in
/-- The left extension preserves the complete original raw map when its
beadwise coefficient restrictions agree at the joint. -/
theorem extendLeft_rawOn (hs : RawOn F (leftLeg F j) s)
    (hc : LeftTraceMatches F j trace s) :
    RawOn F (leftLeg F j) (extendLeft Q.map J time (native F) j trace s) := by
  intro p
  have h := hs p
  rw [withTimeMap_app] at h ⊢
  refine (raw_eq_of_piece_projections (L := L) (p := p) (T := leftCode F j p)
    (leftHorizontal F j p) _ (s.app p) ?_).trans h
  intro b
  exact extendLeft_project_on Q.map J time (native F) j
    (k := coefficient (L := L)) trace s p
    ((leftCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p)))
    (readout (L := L) (leftHorizontal F j p) b).operator (hc p b)

set_option maxHeartbeats 650000 in
/-- The right extension preserves the complete original raw map when its
beadwise coefficient restrictions agree at the joint. -/
theorem extendRight_rawOn (ht : RawOn F (rightLeg F j) t)
    (hc : RightTraceMatches F j trace t) :
    RawOn F (rightLeg F j) (extendRight Q.map J time (native F) j trace t) := by
  intro p
  have h := ht p
  rw [withTimeMap_app] at h ⊢
  refine (raw_eq_of_piece_projections (L := L) (p := p) (T := rightCode F j p)
    (rightHorizontal F j p) _ (t.app p) ?_).trans h
  intro b
  exact extendRight_project_on Q.map J time (native F) j
    (k := coefficient (L := L)) trace t p
    ((rightCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p)))
    (readout (L := L) (rightHorizontal F j p) b).operator (hc p b)

/-- Assemble and evaluate the graph after synchronizing its joint trace.
The input raw equations can be checked on the two unmodified sides. -/
def assembledFamilyOfPieceProjections
    (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t)
    (hleft : LeftTraceMatches F j trace s) (hright : RightTraceMatches F j trace t) :
    Family Q L time :=
  assembledFamily F j trace s t (extendLeft_rawOn F j trace s hs hleft)
    (extendRight_rawOn F j trace t ht hright)

section CommonTrace

open JTFiniteOrdinalConstraints (exists_least_common ordConnected_fiber)
open JTCodiscreteParameterPairing (coord)

private abbrev zero := op (⦋0⦌ : SimplexCategory)
private abbrev jointSource := withTime Q.map J time (native F) (overlap Q.code j)
private abbrev degree (p : I) := (coefficient (L := L)).obj p
private abbrev jointVertex (p : I) := ((jointSource F j).obj p).obj zero
private abbrev leftOverlap :=
  withTimeMap Q.map J time (native F) (overlapToLeft Q.code j)
private abbrev rightOverlap :=
  withTimeMap Q.map J time (native F) (overlapToRight Q.code j)
private abbrev leftPiece (p : I) (b : Option (leftCode F j p).Bead) :=
  (leftCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p))
private abbrev rightPiece (p : I) (b : Option (rightCode F j p).Bead) :=
  (rightCode F j p).pieceι b ⊗ₘ 𝟙 (J.obj (time.obj p))

private abbrev LeftPieces (p : I) (u : jointVertex F j p) :=
  {b : Option (leftCode F j p).Bead //
    ((leftOverlap F j).app p).app zero u ∈ Set.range ((leftPiece F j p b).app zero)}

private abbrev RightPieces (p : I) (u : jointVertex F j p) :=
  {b : Option (rightCode F j p).Bead //
    ((rightOverlap F j).app p).app zero u ∈ Set.range ((rightPiece F j p b).app zero)}

private abbrev leftValue (p : I) (u : jointVertex F j p) :=
  coord (degree (L := L) p) zero ((s.app p).app zero (((leftOverlap F j).app p).app zero u)) 0
private abbrev rightValue (p : I) (u : jointVertex F j p) :=
  coord (degree (L := L) p) zero ((t.app p).app zero (((rightOverlap F j).app p).app zero u)) 0

private abbrev leftOperator (p : I) (b : Option (leftCode F j p).Bead) :=
  (readout (L := L) (leftHorizontal F j p) b).operator.toOrderHom
private abbrev rightOperator (p : I) (b : Option (rightCode F j p).Bead) :=
  (readout (L := L) (rightHorizontal F j p) b).operator.toOrderHom

/-- The allowable coefficient vertices for one point or bead incident to the joint vertex. -/
def constraint (p : I) (u : jointVertex F j p)
    (c : LeftPieces F j p u ⊕ RightPieces F j p u) :
    Set (Fin ((degree (L := L) p).len + 1)) :=
  match c with
  | .inl b => {v | leftOperator F j p b.val v = leftOperator F j p b.val (leftValue F j s p u)}
  | .inr b => {v | rightOperator F j p b.val v = rightOperator F j p b.val (rightValue F j t p u)}

/-- Each joint vertex must satisfy the constraints of all its incident pieces. -/
def allowed (p : I) (u : jointVertex F j p) : Set (Fin ((degree (L := L) p).len + 1)) :=
  {v | ∀ b, v ∈ constraint F j s t p u b}

/-- The two trace conditions are exactly vertexwise membership in these sets. -/
theorem trace_matches_iff_allowed :
    LeftTraceMatches F j trace s ∧ RightTraceMatches F j trace t ↔
      ∀ p u, coord (degree (L := L) p) zero ((trace.app p).app zero u) 0 ∈ allowed F j s t p u := by
  constructor
  · intro ⟨hl, hr⟩ p u b
    cases b with
    | inl b => exact (traceMatches_iff _ _ _ _ _).mp (hl p b.val) u b.property
    | inr b => exact (traceMatches_iff _ _ _ _ _).mp (hr p b.val) u b.property
  · intro h
    constructor
    · intro p b
      apply (traceMatches_iff _ _ _ _ _).mpr
      intro u hu
      exact h p u (Sum.inl ⟨b, hu⟩)
    · intro p b
      apply (traceMatches_iff _ _ _ _ _).mpr
      intro u hu
      exact h p u (Sum.inr ⟨b, hu⟩)

/-- Only cross-side pairs need be checked: the preexisting value solves
all constraints for pieces from the same side. -/
def CrossAgreement : Prop :=
  ∀ (p : I) (u : jointVertex F j p)
    (b : LeftPieces F j p u) (c : RightPieces F j p u),
    (constraint F j s t p u (Sum.inl b) ∩ constraint F j s t p u (Sum.inr c)).Nonempty

private theorem constraint_ordConnected (p : I) (u : jointVertex F j p)
    (b : LeftPieces F j p u ⊕ RightPieces F j p u) :
    (constraint F j s t p u b).OrdConnected := by
  cases b with
  | inl b => exact ordConnected_fiber (leftOperator F j p b.val) _
  | inr b => exact ordConnected_fiber (rightOperator F j p b.val) _

/-- If each incident left and right piece has a pairwise common value,
there is a least coefficient satisfying every piece constraint at the vertex. -/
theorem exists_least_allowed (h : CrossAgreement F j s t) (p : I) (u : jointVertex F j p) :
    ∃ v, IsLeast (allowed F j s t p u) v := by
  apply exists_least_common _ (constraint_ordConnected F j s t p u)
  rintro (b | b) (c | c)
  · exact ⟨leftValue F j s p u, ⟨rfl, rfl⟩⟩
  · exact h p u b c
  · rw [Set.inter_comm]
    exact h p u c b
  · exact ⟨rightValue F j t p u, ⟨rfl, rfl⟩⟩

variable (h : CrossAgreement F j s t)

/-- The least valid coefficient of each actual joint vertex. -/
def leastAllowed (p : I) (u : jointVertex F j p) : Fin ((degree (L := L) p).len + 1) :=
  (exists_least_allowed F j s t h p u).choose

/-- The chosen value meets every piece constraint. -/
theorem leastAllowed_spec (p : I) (u : jointVertex F j p) :
    IsLeast (allowed F j s t p u) (leastAllowed F j s t h p u) :=
  (exists_least_allowed F j s t h p u).choose_spec

/-- Along an original operator, the allowed source values stay allowed at the target. -/
def AllowedMapsTo : Prop :=
  ∀ {p p' : I} (a : p ⟶ p') (u : jointVertex F j p),
    Set.MapsTo ((coefficient (L := L)).map a).toOrderHom (allowed F j s t p u)
      (allowed F j s t p' (((jointSource F j).map a).app zero u))

/-- The least allowed target value has a preimage among the actual source values. -/
def LeastAllowedInImage : Prop :=
  ∀ {p p' : I} (a : p ⟶ p') (u : jointVertex F j p),
    leastAllowed F j s t h p' (((jointSource F j).map a).app zero u) ∈
      ((coefficient (L := L)).map a).toOrderHom '' allowed F j s t p u

variable (hMap : AllowedMapsTo F j s t) (hImage : LeastAllowedInImage F j s t h)

include hMap hImage in
private theorem leastAllowed_natural {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :
    leastAllowed F j s t h p' (((jointSource F j).map a).app zero u) =
      ((coefficient (L := L)).map a).toOrderHom (leastAllowed F j s t h p u) := by
  let u' := ((jointSource F j).map a).app zero u
  let b := ((coefficient (L := L)).map a).toOrderHom
  have h₁ := leastAllowed_spec F j s t h p u
  have h₂ := leastAllowed_spec F j s t h p' u'
  apply le_antisymm (h₂.2 (hMap a u h₁.1))
  obtain ⟨v, hv, hv'⟩ := hImage a u
  exact (b.monotone (h₁.2 hv)).trans (le_of_eq hv')

/-- The actual common trace obtained from the least choices, including all higher simplices. -/
def traceOfLeastAllowed : jointSource F j ⟶ coefficient (L := L) ⋙ J :=
  parameterOfNaturalVertices (jointSource F j) (coefficient (L := L)) (leastAllowed F j s t h)
    (leastAllowed_natural F j s t h hMap hImage)

/-- The common trace satisfies the exact piece conditions on both sides. -/
theorem traceOfLeastAllowed_matches :
    LeftTraceMatches F j (traceOfLeastAllowed F j s t h hMap hImage) s ∧
      RightTraceMatches F j (traceOfLeastAllowed F j s t h hMap hImage) t := by
  apply (trace_matches_iff_allowed F j (traceOfLeastAllowed F j s t h hMap hImage) s t).mpr
  intro p u
  change coord (degree (L := L) p) zero
    ((parameterOfNaturalVertices (jointSource F j) (coefficient (L := L))
      (leastAllowed F j s t h) (leastAllowed_natural F j s t h hMap hImage)).app p |>.app zero u)
      0 ∈ allowed F j s t p u
  rw [parameterOfNaturalVertices_coord]
  exact (leastAllowed_spec F j s t h p u).1

/-- Build a graph family over the actual fixed target from the cross-side
vertex tests and the stated transport conditions on original operators. -/
def assembledFamilyOfLeastAllowed
    (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t) : Family Q L time :=
  assembledFamilyOfPieceProjections F j (traceOfLeastAllowed F j s t h hMap hImage) s t hs ht
    (traceOfLeastAllowed_matches F j s t h hMap hImage).1
    (traceOfLeastAllowed_matches F j s t h hMap hImage).2

section StableConstraints

private abbrev movedVertex {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :=
  ((jointSource F j).map a).app zero u

private abbrev coefficientMap {p p' : I} (a : p ⟶ p') :=
  ((coefficient (L := L)).map a).toOrderHom

/-- Retain precisely the values that satisfy the piece tests after every
original operator. This includes the tests at the given vertex. -/
def stableAllowed (p : I) (u : jointVertex F j p) : Set (Fin ((degree (L := L) p).len + 1)) :=
  {v | ∀ {p' : I} (a : p ⟶ p'), coefficientMap (L := L) a v ∈
    allowed F j s t p' (movedVertex F j a u)}

theorem stableAllowed_subset (p : I) (u : jointVertex F j p) :
    stableAllowed F j s t p u ⊆ allowed F j s t p u := by
  intro v hv
  have h := hv (𝟙 p)
  change coefficientMap (L := L) (𝟙 p) v ∈
    allowed F j s t p (movedVertex F j (𝟙 p) u) at h
  have hk : coefficientMap (L := L) (𝟙 p) v = v := by
    change ((coefficient (L := L)).map (𝟙 p)).toOrderHom v = v
    rw [(coefficient (L := L)).map_id, SimplexCategory.id_toOrderHom]
    rfl
  have hM : movedVertex F j (𝟙 p) u = u :=
    congrFun (NatTrans.congr_app ((jointSource F j).map_id p) zero) u
  rw [hk, hM] at h
  exact h

/-- Quantifying over the original operators makes preservation automatic. -/
theorem stableAllowed_mapsTo {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :
    Set.MapsTo (coefficientMap (L := L) a) (stableAllowed F j s t p u)
      (stableAllowed F j s t p' (movedVertex F j a u)) := by
  intro v hv p'' b
  have h := hv (a ≫ b)
  change coefficientMap (L := L) (a ≫ b) v ∈
    allowed F j s t p'' (movedVertex F j (a ≫ b) u) at h
  have hk : coefficientMap (L := L) (a ≫ b) v =
    coefficientMap (L := L) b (coefficientMap (L := L) a v) := by
    simp only [coefficientMap, Functor.map_comp]
    rfl
  have hM : movedVertex F j (a ≫ b) u = movedVertex F j b (movedVertex F j a u) := by
    simp only [movedVertex, Functor.map_comp]
    rfl
  rw [hk, hM] at h
  exact h

private theorem parameter_vertex_natural (P : jointSource F j ⟶ coefficient (L := L) ⋙ J)
    {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :
    coord (degree (L := L) p') zero ((P.app p').app zero (movedVertex F j a u)) 0 =
      coefficientMap (L := L) a (coord (degree (L := L) p) zero ((P.app p).app zero u) 0) := by
  have he := congrFun (NatTrans.congr_app (P.naturality a) zero) u
  change (P.app p').app zero (movedVertex F j a u) =
    (J.map ((coefficient (L := L)).map a)).app zero ((P.app p).app zero u) at he
  rw [he, JTCodiscreteParameterPairing.coord_map]

private theorem leftValue_natural {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :
    leftValue F j s p' (movedVertex F j a u) =
      coefficientMap (L := L) a (leftValue F j s p u) :=
  parameter_vertex_natural F j (leftOverlap F j ≫ s) a u

private theorem rightValue_natural {p p' : I} (a : p ⟶ p') (u : jointVertex F j p) :
    rightValue F j t p' (movedVertex F j a u) =
      coefficientMap (L := L) a (rightValue F j t p u) :=
  parameter_vertex_natural F j (rightOverlap F j ≫ t) a u

private abbrev LeftTests (p : I) (u : jointVertex F j p) :=
  Σ (p' : I) (a : p ⟶ p'), LeftPieces F j p' (movedVertex F j a u)

private abbrev RightTests (p : I) (u : jointVertex F j p) :=
  Σ (p' : I) (a : p ⟶ p'), RightPieces F j p' (movedVertex F j a u)

private def movedConstraint (p : I) (u : jointVertex F j p)
    (c : LeftTests F j p u ⊕ RightTests F j p u) : Set (Fin ((degree (L := L) p).len + 1)) :=
  match c with
  | .inl ⟨p', a, b⟩ => (coefficientMap (L := L) a) ⁻¹'
      constraint F j s t p' (movedVertex F j a u) (.inl b)
  | .inr ⟨p', a, b⟩ => (coefficientMap (L := L) a) ⁻¹'
      constraint F j s t p' (movedVertex F j a u) (.inr b)

private theorem movedConstraint_ordConnected (p : I) (u : jointVertex F j p)
    (b : LeftTests F j p u ⊕ RightTests F j p u) :
    (movedConstraint F j s t p u b).OrdConnected := by
  rcases b with ⟨p', a, b⟩ | ⟨p', a, b⟩
  · letI := constraint_ordConnected F j s t p' (movedVertex F j a u) (.inl b)
    exact Set.ordConnected_preimage _
  · letI := constraint_ordConnected F j s t p' (movedVertex F j a u) (.inr b)
    exact Set.ordConnected_preimage _

private theorem mem_movedConstraint_left (p : I) (u : jointVertex F j p)
    (b : LeftTests F j p u) :
    leftValue F j s p u ∈ movedConstraint F j s t p u (.inl b) := by
  rcases b with ⟨p', a, b⟩
  change leftOperator F j p' b.val (coefficientMap (L := L) a (leftValue F j s p u)) =
    leftOperator F j p' b.val (leftValue F j s p' (movedVertex F j a u))
  rw [leftValue_natural F j s a u]

private theorem mem_movedConstraint_right (p : I) (u : jointVertex F j p)
    (b : RightTests F j p u) :
    rightValue F j t p u ∈ movedConstraint F j s t p u (.inr b) := by
  rcases b with ⟨p', a, b⟩
  change rightOperator F j p' b.val (coefficientMap (L := L) a (rightValue F j t p u)) =
    rightOperator F j p' b.val (rightValue F j t p' (movedVertex F j a u))
  rw [rightValue_natural F j t a u]

/-- Each left test and right test, pulled back along possibly different
original operators, have a simultaneous solution in the source coefficient. -/
def CrossAgreementAlongOperators : Prop :=
  ∀ (p : I) (u : jointVertex F j p) (b : LeftTests F j p u) (c : RightTests F j p u),
    (movedConstraint F j s t p u (.inl b) ∩ movedConstraint F j s t p u (.inr c)).Nonempty

/-- A specified natural common trace is stable under all original operators
whenever its two piece conditions hold. -/
theorem stableAllowed_of_trace (hL : LeftTraceMatches F j trace s)
    (hR : RightTraceMatches F j trace t) (p : I) (u : jointVertex F j p) :
    coord (degree (L := L) p) zero ((trace.app p).app zero u) 0 ∈
      stableAllowed F j s t p u := by
  intro p' a
  have hv := (trace_matches_iff_allowed F j trace s t).mp ⟨hL, hR⟩
  change coefficientMap (L := L) a
      (coord (degree (L := L) p) zero ((trace.app p).app zero u) 0) ∈
    allowed F j s t p' (movedVertex F j a u)
  rw [← parameter_vertex_natural F j trace a u]
  exact hv p' (movedVertex F j a u)

/-- If the two restrictions to the original joint diagram are identical,
the chosen value from that diagram meets every pulled-back pair of tests. -/
theorem crossAgreement_of_restriction_eq
    (e : leftOverlap F j ≫ s = rightOverlap F j ≫ t) :
    CrossAgreementAlongOperators F j s t := by
  intro p u b c
  have v := congrFun (NatTrans.congr_app (NatTrans.congr_app e p) zero) u
  have v' := congrArg (fun z ↦ coord (degree (L := L) p) zero z 0) v
  change leftValue F j s p u = rightValue F j t p u at v'
  refine ⟨leftValue F j s p u, mem_movedConstraint_left F j s t p u b, ?_⟩
  rw [v']
  exact mem_movedConstraint_right F j s t p u c

/-- Cross-side pairwise tests along the original operators suffice for an
admissible choice which satisfies the piece constraints at every image. -/
theorem stableAllowed_nonempty (h : CrossAgreementAlongOperators F j s t)
    (p : I) (u : jointVertex F j p) : (stableAllowed F j s t p u).Nonempty := by
  have hc : ∀ b c, (movedConstraint F j s t p u b ∩ movedConstraint F j s t p u c).Nonempty := by
    rintro (b | b) (c | c)
    · exact ⟨_, mem_movedConstraint_left F j s t p u b, mem_movedConstraint_left F j s t p u c⟩
    · exact h p u b c
    · rw [Set.inter_comm]
      exact h p u c b
    · exact ⟨_, mem_movedConstraint_right F j s t p u b, mem_movedConstraint_right F j s t p u c⟩
  obtain ⟨v, hv⟩ := exists_least_common _ (movedConstraint_ordConnected F j s t p u) hc
  refine ⟨v, ?_⟩
  intro p' a b
  cases b with
  | inl b => exact hv.1 (.inl ⟨p', a, b⟩)
  | inr b => exact hv.1 (.inr ⟨p', a, b⟩)

end StableConstraints

section CoveredTrace

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

/-- Retain all admissible choices over every simplex of the actual joint diagram. -/
abbrev jointCover :=
  JTVertexAssignmentCover.cover (jointSource F j) (coefficient (L := L))
    (stableAllowed F j s t) (stableAllowed_mapsTo F j s t)

/-- The projection to the full original time-parametrized joint diagram. -/
abbrev jointCoverProjection : jointCover F j s t ⟶ jointSource F j :=
  JTVertexAssignmentCover.projection _ _ _ (stableAllowed_mapsTo F j s t)

/-- The componentwise trivial fibration follows from the cross-side tests
along the original operators. -/
theorem jointCover_trivialFibration (h : CrossAgreementAlongOperators F j s t) (p : I) :
    trivialFibrations SSet.{0} ((jointCoverProjection F j s t).app p) :=
  JTVertexAssignmentCover.projection_trivialFibration _ _ _ (stableAllowed_mapsTo F j s t)
    (stableAllowed_nonempty F j s t h) p

/-- The common coefficient parameter on the entire weak cover of the joint. -/
abbrev jointCoverTrace : jointCover F j s t ⟶ coefficient (L := L) ⋙ J :=
  JTVertexAssignmentCover.trace _ _ _ (stableAllowed_mapsTo F j s t)

private theorem jointCoverTrace_allowed (p : I) (u : ((jointCover F j s t).obj p).obj zero) :
    coord (degree (L := L) p) zero (((jointCoverTrace F j s t).app p).app zero u) 0 ∈
      allowed F j s t p (((jointCoverProjection F j s t).app p).app zero u) :=
  stableAllowed_subset F j s t p _
    (JTVertexAssignmentCover.trace_allowed (jointSource F j) (coefficient (L := L))
      (stableAllowed F j s t) (fun {_ _} a v ↦ stableAllowed_mapsTo F j s t a v) p u)

/-- The tautological trace has the prescribed coefficient on all
incident pieces, evaluated by the actual left and right projections. -/
theorem jointCoverTrace_matches (p : I) :
    (∀ b : Option (leftCode F j p).Bead,
      TraceMatches ((jointCoverProjection F j s t ≫ leftOverlap F j).app p)
        ((jointCoverTrace F j s t).app p) (s.app p) (leftPiece F j p b)
        (readout (L := L) (leftHorizontal F j p) b).operator) ∧
    (∀ b : Option (rightCode F j p).Bead,
      TraceMatches ((jointCoverProjection F j s t ≫ rightOverlap F j).app p)
        ((jointCoverTrace F j s t).app p) (t.app p) (rightPiece F j p b)
        (readout (L := L) (rightHorizontal F j p) b).operator) := by
  constructor
  · intro b
    apply (traceMatches_iff _ _ _ _ _).mpr
    intro u hu
    exact jointCoverTrace_allowed F j s t p u (Sum.inl ⟨b, hu⟩)
  · intro b
    apply (traceMatches_iff _ _ _ _ _).mpr
    intro u hu
    exact jointCoverTrace_allowed F j s t p u (Sum.inr ⟨b, hu⟩)

end CoveredTrace

section FullCover

open HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open JTVertexAssignmentCover (extendAllowed extendAllowed_on extendAllowed_mapsTo)

/-- The entire joint interval inside the original parametrized product. -/
abbrev jointInclusion : jointSource F j ⟶ product F :=
  withTimeMap Q.map J time (native F) (jointToWhole j)

theorem jointInclusion_left : leftOverlap F j ≫ leftLeg F j = jointInclusion F j := by
  change withTimeMap Q.map J time (native F) (overlapToLeft Q.code j) ≫
    withTimeMap Q.map J time (native F) (leftToWhole Q.code j) =
      withTimeMap Q.map J time (native F) (jointToWhole j)
  rw [← withTimeMap_comp, jointToWhole_left]

theorem jointInclusion_right : rightOverlap F j ≫ rightLeg F j = jointInclusion F j := by
  change withTimeMap Q.map J time (native F) (overlapToRight Q.code j) ≫
    withTimeMap Q.map J time (native F) (rightToWhole Q.code j) =
      withTimeMap Q.map J time (native F) (jointToWhole j)
  rw [← withTimeMap_comp, jointToWhole_right]

private abbrev referenceTrace := jointInclusion F j ≫ originalParameter F

/-- Away from the joint, the reference keeps the original side coefficients.
At the joint it uses the original graph trace. -/
abbrev referenceParameter : product F ⟶ coefficient (L := L) ⋙ J :=
  assemble Q J time (native F) j (referenceTrace F j) s t

/-- Allow every stable joint choice and retain precisely the reference
coefficient outside the joint. -/
abbrev fullAllowed :=
  extendAllowed (jointInclusion F j) (referenceParameter F j s t) (stableAllowed F j s t)

theorem fullAllowed_mapsTo {p p' : I} (a : p ⟶ p') (u : ((product F).obj p).obj zero) :
    Set.MapsTo (coefficientMap (L := L) a) (fullAllowed F j s t p u)
      (fullAllowed F j s t p' (((product F).map a).app zero u)) :=
  extendAllowed_mapsTo (jointInclusion F j) (referenceParameter F j s t) (stableAllowed F j s t)
    (joint_vertices_injective Q.map J time (native F) j)
    (joint_vertices_reflects Q.map J time (native F) j)
    (stableAllowed_mapsTo F j s t) a u

/-- The cover of the entire original product carrying the coefficient choices. -/
abbrev fullCover :=
  JTVertexAssignmentCover.cover (product F) (coefficient (L := L)) (fullAllowed F j s t)
    (fullAllowed_mapsTo F j s t)

/-- Projection retains the full original native and time coordinates. -/
abbrev fullCoverProjection : fullCover F j s t ⟶ product F :=
  JTVertexAssignmentCover.projection _ _ _ (fullAllowed_mapsTo F j s t)

/-- The common graph parameter on the entire covered product. -/
abbrev fullCoverParameter : fullCover F j s t ⟶ coefficient (L := L) ⋙ J :=
  JTVertexAssignmentCover.trace _ _ _ (fullAllowed_mapsTo F j s t)

theorem fullCover_trivialFibration (h : CrossAgreementAlongOperators F j s t) (p : I) :
    trivialFibrations SSet.{0} ((fullCoverProjection F j s t).app p) :=
  JTVertexAssignmentCover.projection_trivialFibration _ _ _ (fullAllowed_mapsTo F j s t)
    (JTVertexAssignmentCover.extendAllowed_nonempty _ _ _
      (joint_vertices_injective Q.map J time (native F) j)
      (stableAllowed_nonempty F j s t h)) p

private abbrev valueAt {p : I} (v : ((product F).obj p).obj zero) :=
  coord (degree (L := L) p) zero (((referenceParameter F j s t).app p).app zero v) 0

private abbrev coverValue {p : I} (v : ((fullCover F j s t).obj p).obj zero) :=
  coord (degree (L := L) p) zero (((fullCoverParameter F j s t).app p).app zero v) 0

private theorem coverValue_joint {p : I} (w : ((fullCover F j s t).obj p).obj zero)
    (u : jointVertex F j p)
    (hu : ((jointInclusion F j).app p).app zero u =
      ((fullCoverProjection F j s t).app p).app zero w) :
    coverValue F j s t w ∈ stableAllowed F j s t p u := by
  have h : coverValue F j s t w ∈ fullAllowed F j s t p
      (((fullCoverProjection F j s t).app p).app zero w) :=
    JTVertexAssignmentCover.trace_allowed _ _ _ (fullAllowed_mapsTo F j s t) p w
  rw [← hu] at h
  intro p' a
  exact extendAllowed_on _ _ _ p u h a

private theorem coverValue_away {p : I} (w : ((fullCover F j s t).obj p).obj zero)
    (hw : ((fullCoverProjection F j s t).app p).app zero w ∉
      Set.range ((jointInclusion F j).app p |>.app zero)) :
    coverValue F j s t w = valueAt F j s t (((fullCoverProjection F j s t).app p).app zero w) := by
  have h : coverValue F j s t w ∈ fullAllowed F j s t p
      (((fullCoverProjection F j s t).app p).app zero w) :=
    JTVertexAssignmentCover.trace_allowed _ _ _ (fullAllowed_mapsTo F j s t) p w
  exact h.2 hw

theorem reference_left_away {p : I}
    (v : ((withTime Q.map J time (native F) (left Q.code j)).obj p).obj zero)
    (hv : v ∉ Set.range (((leftOverlap F j).app p).app zero)) :
    valueAt F j s t (((leftLeg F j).app p).app zero v) =
      coord (degree (L := L) p) zero ((s.app p).app zero v) 0 := by
  have h := NatTrans.congr_app (assemble_left Q J time (native F) j (referenceTrace F j) s t) p
  have h' := congrFun (NatTrans.congr_app h zero) v
  change ((referenceParameter F j s t).app p).app zero (((leftLeg F j).app p).app zero v) =
    ((extendLeft Q.map J time (native F) j (referenceTrace F j) s).app p).app zero v at h'
  unfold valueAt
  rw [h']
  exact extendLeft_away Q.map J time (native F) j (referenceTrace F j) s p v hv

theorem reference_right_away {p : I}
    (v : ((withTime Q.map J time (native F) (right Q.code j)).obj p).obj zero)
    (hv : v ∉ Set.range (((rightOverlap F j).app p).app zero)) :
    valueAt F j s t (((rightLeg F j).app p).app zero v) =
      coord (degree (L := L) p) zero ((t.app p).app zero v) 0 := by
  have h := NatTrans.congr_app (assemble_right Q J time (native F) j (referenceTrace F j) s t) p
  have h' := congrFun (NatTrans.congr_app h zero) v
  change ((referenceParameter F j s t).app p).app zero (((rightLeg F j).app p).app zero v) =
    ((extendRight Q.map J time (native F) j (referenceTrace F j) t).app p).app zero v at h'
  unfold valueAt
  rw [h']
  exact extendRight_away Q.map J time (native F) j (referenceTrace F j) t p v hv

set_option maxHeartbeats 550000 in
private theorem left_cover_projection (p : I) (b : Option (leftCode F j p).Bead)
    {A : SSet.{0}} (g : A ⟶ (fullCover F j s t).obj p)
    (z : A ⟶ (((leftCode F j p).pieces b).toSSet ⊗ J.obj (time.obj p)))
    (h : g ≫ (fullCoverProjection F j s t).app p =
      z ≫ leftPiece F j p b ≫ (leftLeg F j).app p) :
    g ≫ (fullCoverParameter F j s t).app p ≫ J.map (readout (L := L) (leftHorizontal F j p) b).operator =
      z ≫ leftPiece F j p b ≫ s.app p ≫ J.map (readout (L := L) (leftHorizontal F j p) b).operator := by
  apply parameter_ext
  intro u
  let v := (leftPiece F j p b).app zero (z.app zero u)
  let w := g.app zero u
  let q := ((fullCoverProjection F j s t).app p).app zero w
  have hq : q = ((leftLeg F j).app p).app zero v :=
    congrFun (NatTrans.congr_app h zero) u
  change coord _ zero ((J.map _).app zero (((fullCoverParameter F j s t).app p).app zero w)) 0 =
    coord _ zero ((J.map _).app zero ((s.app p).app zero v)) 0
  rw [JTCodiscreteParameterPairing.coord_map, JTCodiscreteParameterPairing.coord_map]
  by_cases hj : q ∈ Set.range (((jointInclusion F j).app p).app zero)
  · obtain ⟨x, hx⟩ := hj
    have hjl := congrFun (NatTrans.congr_app (NatTrans.congr_app (jointInclusion_left F j) p) zero) x
    have hl : ((leftOverlap F j).app p).app zero x = v :=
      left_vertices_injective Q.map J time (native F) j p (hjl.trans (hx.trans hq))
    have hgood := stableAllowed_subset F j s t p x (coverValue_joint F j s t w x hx)
      (Sum.inl ⟨b, ⟨z.app zero u, hl.symm⟩⟩)
    change leftOperator F j p b (coverValue F j s t w) =
      leftOperator F j p b (coord (degree (L := L) p) zero
        ((s.app p).app zero (((leftOverlap F j).app p).app zero x)) 0) at hgood
    rw [hl] at hgood
    exact hgood
  · have hv : v ∉ Set.range (((leftOverlap F j).app p).app zero) := by
      rintro ⟨x, hx⟩
      apply hj
      have hjl := congrFun (NatTrans.congr_app (NatTrans.congr_app (jointInclusion_left F j) p) zero) x
      refine ⟨x, hjl.symm.trans ?_⟩
      exact (congrArg (((leftLeg F j).app p).app zero) hx).trans hq.symm
    exact congrArg (leftOperator F j p b) ((coverValue_away F j s t w hj).trans
      ((congrArg (valueAt F j s t) hq).trans (reference_left_away F j s t v hv)))

set_option maxHeartbeats 550000 in
private theorem right_cover_projection (p : I) (b : Option (rightCode F j p).Bead)
    {A : SSet.{0}} (g : A ⟶ (fullCover F j s t).obj p)
    (z : A ⟶ (((rightCode F j p).pieces b).toSSet ⊗ J.obj (time.obj p)))
    (h : g ≫ (fullCoverProjection F j s t).app p =
      z ≫ rightPiece F j p b ≫ (rightLeg F j).app p) :
    g ≫ (fullCoverParameter F j s t).app p ≫ J.map (readout (L := L) (rightHorizontal F j p) b).operator =
      z ≫ rightPiece F j p b ≫ t.app p ≫ J.map (readout (L := L) (rightHorizontal F j p) b).operator := by
  apply parameter_ext
  intro u
  let v := (rightPiece F j p b).app zero (z.app zero u)
  let w := g.app zero u
  let q := ((fullCoverProjection F j s t).app p).app zero w
  have hq : q = ((rightLeg F j).app p).app zero v :=
    congrFun (NatTrans.congr_app h zero) u
  change coord _ zero ((J.map _).app zero (((fullCoverParameter F j s t).app p).app zero w)) 0 =
    coord _ zero ((J.map _).app zero ((t.app p).app zero v)) 0
  rw [JTCodiscreteParameterPairing.coord_map, JTCodiscreteParameterPairing.coord_map]
  by_cases hj : q ∈ Set.range (((jointInclusion F j).app p).app zero)
  · obtain ⟨x, hx⟩ := hj
    have hjl := congrFun (NatTrans.congr_app (NatTrans.congr_app (jointInclusion_right F j) p) zero) x
    have hl : ((rightOverlap F j).app p).app zero x = v :=
      right_vertices_injective Q.map J time (native F) j p (hjl.trans (hx.trans hq))
    have hgood := stableAllowed_subset F j s t p x (coverValue_joint F j s t w x hx)
      (Sum.inr ⟨b, ⟨z.app zero u, hl.symm⟩⟩)
    change rightOperator F j p b (coverValue F j s t w) =
      rightOperator F j p b (coord (degree (L := L) p) zero
        ((t.app p).app zero (((rightOverlap F j).app p).app zero x)) 0) at hgood
    rw [hl] at hgood
    exact hgood
  · have hv : v ∉ Set.range (((rightOverlap F j).app p).app zero) := by
      rintro ⟨x, hx⟩
      apply hj
      have hjl := congrFun (NatTrans.congr_app (NatTrans.congr_app (jointInclusion_right F j) p) zero) x
      refine ⟨x, hjl.symm.trans ?_⟩
      exact (congrArg (((rightLeg F j).app p).app zero) hx).trans hq.symm
    exact congrArg (rightOperator F j p b) ((coverValue_away F j s t w hj).trans
      ((congrArg (valueAt F j s t) hq).trans (reference_right_away F j s t v hv)))

private abbrev fullRawMap (p : I) :=
  lift ((fullCoverProjection F j s t).app p ≫
      fst (code (L := L) p).toSSet (J.obj (time.obj p)))
    ((fullCoverParameter F j s t).app p) ≫ realization (L := L) p

set_option maxHeartbeats 450000 in
private theorem raw_covered_piece {p : I} {T : NecklaceCode} (b : Option T.Bead)
    (e : T.toSSet ⟶ (code (L := L) p).toSSet)
    (old : T.toSSet ⊗ J.obj (time.obj p) ⟶ J.obj (degree (L := L) p))
    {A : SSet.{0}} (g : A ⟶ (fullCover F j s t).obj p)
    (z : A ⟶ ((T.pieces b).toSSet ⊗ J.obj (time.obj p)))
    (h : g ≫ (fullCoverProjection F j s t).app p =
      z ≫ (T.pieceι b ⊗ₘ 𝟙 _) ≫ (e ⊗ₘ 𝟙 _))
    (hpar : g ≫ (fullCoverParameter F j s t).app p ≫ J.map (readout (L := L) e b).operator =
      z ≫ (T.pieceι b ⊗ₘ 𝟙 _) ≫ old ≫ J.map (readout (L := L) e b).operator)
    (hraw : lift ((e ⊗ₘ 𝟙 _) ≫ fst (code (L := L) p).toSSet (J.obj (time.obj p))) old ≫
        realization (L := L) p = (e ⊗ₘ 𝟙 _) ≫ rawProjection F p) :
    g ≫ fullRawMap F j s t p = g ≫ (fullCoverProjection F j s t).app p ≫ rawProjection F p := by
  let V := J.obj (time.obj p)
  let C := code (L := L) p
  let k := degree (L := L) p
  let i := T.pieceι b
  let d := readout (L := L) e b
  let r := realization (L := L) p
  let τ := (fullCoverParameter F j s t).app p
  let π := (fullCoverProjection F j s t).app p
  let R := JTNecklaceLabelRealization.realizedLabel C.toSSet W k (ordered (L := L) p)
  have hr : r = R := by
    change (cylinder C).app k ≫
      JTNecklaceEndpointCylinder.descend W x y C k (label (L := L) p) = R
    exact JTNecklaceEndpointCylinder.descend_cylinder W x y C k (label (L := L) p)
  have he' : (z ≫ (i ⊗ₘ 𝟙 V)) ≫ (e ⊗ₘ 𝟙 V) ≫ fst C.toSSet V =
      (z ≫ fst ((T.pieces b).toSSet) V) ≫ (i ≫ e) := by
    simp only [Category.assoc, tensorHom_fst_assoc, tensorHom_fst]
    rfl
  have he : g ≫ π ≫ fst C.toSSet V = (z ≫ fst ((T.pieces b).toSSet) V) ≫ (i ≫ e) := by
    calc
      _ = (g ≫ π) ≫ fst C.toSSet V := (Category.assoc _ _ _).symm
      _ = (z ≫ (i ⊗ₘ 𝟙 V) ≫ (e ⊗ₘ 𝟙 V)) ≫ fst C.toSSet V :=
        congrArg (fun u ↦ u ≫ fst C.toSSet V) h
      _ = _ := by simpa only [Category.assoc] using he'
  change g ≫ lift (π ≫ fst C.toSSet V) τ ≫ r = g ≫ π ≫ rawProjection F p
  calc
    _ = lift ((z ≫ fst ((T.pieces b).toSSet) V) ≫ (i ≫ e)) (g ≫ τ) ≫ R := by
      rw [← Category.assoc, comp_lift, he, hr]
    _ = lift ((z ≫ fst ((T.pieces b).toSSet) V) ≫ (i ≫ e))
        ((z ≫ (i ⊗ₘ 𝟙 V)) ≫ old) ≫ R :=
      d.graph_eq (i ≫ e) (ordered (L := L) p) (z ≫ fst _ V) _ _
        (by simpa only [Category.assoc] using hpar)
    _ = (z ≫ (i ⊗ₘ 𝟙 V)) ≫ lift ((e ⊗ₘ 𝟙 V) ≫ fst C.toSSet V) old ≫ r := by
      rw [← Category.assoc (z ≫ (i ⊗ₘ 𝟙 V)), comp_lift, he', hr]
    _ = g ≫ π ≫ rawProjection F p := by
      calc
        _ = (z ≫ (i ⊗ₘ 𝟙 V)) ≫ ((e ⊗ₘ 𝟙 V) ≫ rawProjection F p) :=
          congrArg (fun a ↦ (z ≫ (i ⊗ₘ 𝟙 V)) ≫ a) hraw
        _ = (z ≫ (i ⊗ₘ 𝟙 V) ≫ (e ⊗ₘ 𝟙 V)) ≫ rawProjection F p := by
          simp only [Category.assoc]
        _ = (g ≫ π) ≫ rawProjection F p := congrArg (fun a ↦ a ≫ rawProjection F p) h.symm
        _ = _ := Category.assoc _ _ _

theorem product_sides_cover (p : I) (q : SimplexCategoryᵒᵖ)
    (v : ((product F).obj p).obj q) :
    (∃ u, ((leftLeg F j).app p).app q u = v) ∨ ∃ u, ((rightLeg F j).app p).app q u = v :=
  Types.eq_or_eq_of_isPushout (((underlying_isPushout Q J time (native F) j).map
    ((evaluation I SSet.{0}).obj p)).map ((evaluation _ _).obj q)) v

set_option maxHeartbeats 900000 in
/-- The parameter of the whole covered product has the exact original
raw map, provided the unmodified sides have that map. -/
theorem fullCover_raw (hs : RawOn F (leftLeg F j) s) (ht : RawOn F (rightLeg F j) t) (p : I) :
    fullRawMap F j s t p = (fullCoverProjection F j s t).app p ≫ rawProjection F p := by
  apply NatTrans.ext
  funext q w
  induction q using Opposite.rec with
  | op q =>
    induction q using SimplexCategory.rec with
    | h n =>
      let q := op ⦋n⦌
      let π := (fullCoverProjection F j s t).app p
      let v := π.app q w
      let g := SSet.yonedaEquiv.symm w
      rcases product_sides_cover F j p q v with ⟨u, hu⟩ | ⟨u, hu⟩
      · obtain ⟨b, a, ha⟩ := JTRestrictedLabelCoefficient.bead_product_cover (leftCode F j p) u
        let z := SSet.yonedaEquiv.symm a
        have hz : g ≫ π = z ≫ leftPiece F j p b ≫ (leftLeg F j).app p := by
          apply SSet.yonedaEquiv.injective
          simp only [SSet.yonedaEquiv_comp, g, z, Equiv.apply_symm_apply]
          change v = ((leftLeg F j).app p).app q ((leftPiece F j p b).app q a)
          exact (congrArg (((leftLeg F j).app p).app q) ha).trans hu |>.symm
        have hs' := hs p
        rw [withTimeMap_app] at hs'
        have hz' := hz
        rw [withTimeMap_app] at hz'
        have h := raw_covered_piece F j s t b (leftHorizontal F j p) (s.app p) g z hz'
          (left_cover_projection F j s t p b g z hz) hs'
        simpa only [SSet.yonedaEquiv_comp, g, Equiv.apply_symm_apply] using
          congrArg SSet.yonedaEquiv h
      · obtain ⟨b, a, ha⟩ := JTRestrictedLabelCoefficient.bead_product_cover (rightCode F j p) u
        let z := SSet.yonedaEquiv.symm a
        have hz : g ≫ π = z ≫ rightPiece F j p b ≫ (rightLeg F j).app p := by
          apply SSet.yonedaEquiv.injective
          simp only [SSet.yonedaEquiv_comp, g, z, Equiv.apply_symm_apply]
          change v = ((rightLeg F j).app p).app q ((rightPiece F j p b).app q a)
          exact (congrArg (((rightLeg F j).app p).app q) ha).trans hu |>.symm
        have ht' := ht p
        rw [withTimeMap_app] at ht'
        have hz' := hz
        rw [withTimeMap_app] at hz'
        have h := raw_covered_piece F j s t b (rightHorizontal F j p) (t.app p) g z hz'
          (right_cover_projection F j s t p b g z hz) ht'
        simpa only [SSet.yonedaEquiv_comp, g, Equiv.apply_symm_apply] using
          congrArg SSet.yonedaEquiv h

section OriginalSection

abbrev originalLeft := leftLeg F j ≫ originalParameter F
abbrev originalRight := rightLeg F j ≫ originalParameter F

private theorem originalLeft_restriction :
    leftOverlap F j ≫ originalLeft F j = referenceTrace F j := by
  unfold originalLeft
  rw [← Category.assoc, jointInclusion_left]

private theorem originalRight_restriction :
    rightOverlap F j ≫ originalRight F j = referenceTrace F j := by
  unfold originalRight
  rw [← Category.assoc, jointInclusion_right]

theorem original_crossAgreement :
    CrossAgreementAlongOperators F j (originalLeft F j) (originalRight F j) :=
  crossAgreement_of_restriction_eq F j _ _
    ((originalLeft_restriction F j).trans (originalRight_restriction F j).symm)

theorem referenceParameter_original :
    referenceParameter F j (originalLeft F j) (originalRight F j) = originalParameter F := by
  change assemble Q J time (native F) j (jointInclusion F j ≫ originalParameter F)
    (originalLeft F j) (originalRight F j) = _
  rw [← jointInclusion_left F j, Category.assoc]
  exact assemble_of_restrictions Q J time (native F) j (originalParameter F)

private abbrev originalValue (p : I) (v : ((product F).obj p).obj zero) :=
  coord (degree (L := L) p) zero (((originalParameter F).app p).app zero v) 0

private theorem originalValue_allowed (p : I) (v : ((product F).obj p).obj zero) :
    originalValue F p v ∈ fullAllowed F j (originalLeft F j) (originalRight F j) p v := by
  constructor
  · intro u hu
    change coord (degree (L := L) p) zero (((originalParameter F).app p).app zero v) 0 ∈ _
    rw [← hu]
    change coord (degree (L := L) p) zero (((referenceTrace F j).app p).app zero u) 0 ∈ _
    apply stableAllowed_of_trace F j (referenceTrace F j)
      (originalLeft F j) (originalRight F j)
    · intro q b
      apply (traceMatches_iff _ _ _ _ _).mpr
      intro a _
      suffices hv : ((referenceTrace F j).app q).app zero a =
          ((originalLeft F j).app q).app zero (((leftOverlap F j).app q).app zero a) by
        rw [hv]
      exact (congrFun (NatTrans.congr_app
        (NatTrans.congr_app (originalLeft_restriction F j) q) zero) a).symm
    · intro q b
      apply (traceMatches_iff _ _ _ _ _).mpr
      intro a _
      suffices hv : ((referenceTrace F j).app q).app zero a =
          ((originalRight F j).app q).app zero (((rightOverlap F j).app q).app zero a) by
        rw [hv]
      exact (congrFun (NatTrans.congr_app
        (NatTrans.congr_app (originalRight_restriction F j) q) zero) a).symm
  · intro _
    change originalValue F p v =
      coord (degree (L := L) p) zero
        (((referenceParameter F j (originalLeft F j) (originalRight F j)).app p).app zero v) 0
    rw [referenceParameter_original]

private theorem originalValue_natural {p p' : I} (a : p ⟶ p')
    (v : ((product F).obj p).obj zero) :
    originalValue F p' (((product F).map a).app zero v) =
      coefficientMap (L := L) a (originalValue F p v) := by
  have e := congrFun (NatTrans.congr_app ((originalParameter F).naturality a) zero) v
  change ((originalParameter F).app p').app zero (((product F).map a).app zero v) =
    (J.map ((coefficient (L := L)).map a)).app zero (((originalParameter F).app p).app zero v) at e
  change coord _ zero (((originalParameter F).app p').app zero _) 0 =
    coefficientMap (L := L) a (originalValue F p v)
  rw [e, JTCodiscreteParameterPairing.coord_map]

/-- The original graph parameter gives a natural section over its two exact restrictions. -/
def originalCoverSection :
    product F ⟶ fullCover F j (originalLeft F j) (originalRight F j) :=
  JTVertexAssignmentCover.liftOfAssignments _ _ _
    (fullAllowed_mapsTo F j (originalLeft F j) (originalRight F j)) _ (𝟙 _)
    (originalValue F) (originalValue_natural F) (originalValue_allowed F j)

theorem originalCoverSection_projection :
    originalCoverSection F j ≫ fullCoverProjection F j (originalLeft F j) (originalRight F j) =
      𝟙 _ :=
  JTVertexAssignmentCover.liftOfAssignments_projection _ _ _
    (fullAllowed_mapsTo F j (originalLeft F j) (originalRight F j)) _ (𝟙 _)
    (originalValue F) (originalValue_natural F) (originalValue_allowed F j)

theorem originalCoverSection_parameter :
    originalCoverSection F j ≫ fullCoverParameter F j (originalLeft F j) (originalRight F j) =
      originalParameter F := by
  apply NatTrans.ext
  funext p
  apply JTJointRelativeParameters.parameter_ext
  intro v
  exact JTVertexAssignmentCover.liftOfAssignments_trace_vertex _ _ _
    (fullAllowed_mapsTo F j (originalLeft F j) (originalRight F j)) _ (𝟙 _)
    (originalValue F) (originalValue_natural F) (originalValue_allowed F j) p v

end OriginalSection

section CoveredBoundary

open JTNecklaceEndpointCylinder (endpointInclusion endpointInclusion_natural)
open NecklaceCode (pointAt pointAt_inclusion_apply)

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev boundaryTime := time ⋙ JTXiEndpointCollapse.boundaryCylinder

/-- The original cylinder boundary before the two endpoint lines are collapsed. -/
def productBoundary : boundaryTime (time := time) ⟶ product F where
  app p := endpointInclusion (code (L := L) p) ⊗ₘ 𝟙 (J.obj (time.obj p))
  naturality {p p'} f := by
    change (𝟙 B ⊗ₘ J.map (time.map f)) ≫
        (endpointInclusion (code (L := L) p') ⊗ₘ 𝟙 (J.obj (time.obj p'))) =
      (endpointInclusion (code (L := L) p) ⊗ₘ 𝟙 (J.obj (time.obj p))) ≫
        ((JTDecoratedIntervalDiagram.parameterize Q.map J time
          (native F ⋙ whole Q.code)).map f).left
    rw [JTDecoratedIntervalDiagram.parameterize_map_left]
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.id_comp,
      Category.comp_id, Category.id_comp]
    change endpointInclusion (code (L := L) p') ⊗ₘ J.map (time.map f) =
      (endpointInclusion (code (L := L) p) ≫ ((native F).map f).left.map) ⊗ₘ
        J.map (time.map f)
    exact congrArg (fun a ↦ a ⊗ₘ J.map (time.map f))
      (endpointInclusion_natural ((native F).map f).left).symm

private theorem rawBoundary_vertex (T : NecklaceCode) (v : B.obj zero) :
    T.inclusion.app zero ((endpointInclusion T).app zero v) 0 = 0 ∨
      T.inclusion.app zero ((endpointInclusion T).app zero v) 0 = Fin.last T.len := by
  have H := isColimitOfPreserves ((evaluation _ _).obj zero) SSet.boundary₁.isColimit
  obtain ⟨b, z, rfl⟩ := Types.jointly_surjective_of_isColimit H v
  rcases b with ⟨b⟩
  cases b with
  | left =>
    left
    change T.inclusion.app zero ((endpointInclusion T).app zero
      (SSet.boundary₁.ι₀.app zero z)) 0 = 0
    have h : SSet.boundary₁.ι₀ ≫ endpointInclusion T = pointAt T (ULift.up 0) := by
      change SSet.boundary₁.ι₀ ≫ SSet.boundary₁.desc T.first T.last = _
      rw [SSet.boundary₁.ι₀_desc]
      rfl
    have h' := congrFun (NatTrans.congr_app h zero) z
    change (endpointInclusion T).app zero (SSet.boundary₁.ι₀.app zero z) =
      (pointAt T (ULift.up 0)).app zero z at h'
    rw [h', pointAt_inclusion_apply]
  | right =>
    right
    change T.inclusion.app zero ((endpointInclusion T).app zero
      (SSet.boundary₁.ι₁.app zero z)) 0 = Fin.last T.len
    have h : SSet.boundary₁.ι₁ ≫ endpointInclusion T = pointAt T (ULift.up (Fin.last T.len)) := by
      change SSet.boundary₁.ι₁ ≫ SSet.boundary₁.desc T.first T.last = _
      rw [SSet.boundary₁.ι₁_desc]
      rfl
    have h' := congrFun (NatTrans.congr_app h zero) z
    change (endpointInclusion T).app zero (SSet.boundary₁.ι₁.app zero z) =
      (pointAt T (ULift.up (Fin.last T.len))).app zero z at h'
    rw [h', pointAt_inclusion_apply]

/-- At an internal joint, both original endpoint lines lie outside the overlap. -/
theorem productBoundary_off_joint (hfirst : j.val ≠ 0) (hlast : j.val ≠ Fin.last Q.code.len)
    (p : I) (v : ((boundaryTime (time := time)).obj p).obj zero) :
    ((productBoundary F).app p).app zero v ∉
      Set.range (((jointInclusion F j).app p).app zero) := by
  intro h
  have hh := (joint_vertex_range_iff Q.map J time (native F) j p
    (((productBoundary F).app p).app zero v)).mp h
  have hn := congrFun (NatTrans.congr_app
    (endpointInclusion_natural ((native F).obj p).hom) zero) v.1
  change (((native F).obj p).hom.map.app zero
    ((endpointInclusion (code (L := L) p)).app zero v.1)) =
      (endpointInclusion Q.code).app zero v.1 at hn
  change (((native F).obj p).hom.map.app zero
    ((endpointInclusion (code (L := L) p)).app zero v.1)) =
      (pointAt Q.code (ULift.up j.val)).app zero
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0}))) at hh
  rw [hn] at hh
  have hq := congrArg (fun z ↦ Q.code.inclusion.app zero z 0) hh
  change Q.code.inclusion.app (op ⦋0⦌)
      ((endpointInclusion Q.code).app (op ⦋0⦌) v.1) 0 =
    Q.code.inclusion.app (op ⦋0⦌) ((pointAt Q.code (ULift.up j.val)).app (op ⦋0⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{0})))) 0 at hq
  rw [pointAt_inclusion_apply] at hq
  rcases rawBoundary_vertex Q.code v.1 with h | h
  · exact hfirst (hq.symm.trans h)
  · exact hlast (hq.symm.trans h)

private abbrev boundaryValue (p : I) (v : ((boundaryTime (time := time)).obj p).obj zero) :=
  valueAt F j s t (((productBoundary F).app p).app zero v)

private theorem boundaryValue_natural {p p' : I} (a : p ⟶ p')
    (v : ((boundaryTime (time := time)).obj p).obj zero) :
    boundaryValue F j s t p' (((boundaryTime (time := time)).map a).app zero v) =
      coefficientMap (L := L) a (boundaryValue F j s t p v) := by
  let d := productBoundary F ≫ referenceParameter F j s t
  have he := congrFun (NatTrans.congr_app (d.naturality a) zero) v
  change (d.app p').app zero (((boundaryTime (time := time)).map a).app zero v) =
    (J.map ((coefficient (L := L)).map a)).app zero ((d.app p).app zero v) at he
  change coord _ zero ((d.app p').app zero _) 0 = coefficientMap (L := L) a
    (coord _ zero ((d.app p).app zero v) 0)
  rw [he, JTCodiscreteParameterPairing.coord_map]

variable (hfirst : j.val ≠ 0) (hlast : j.val ≠ Fin.last Q.code.len)

include hfirst hlast in
private theorem boundaryValue_allowed (p : I) (v : ((boundaryTime (time := time)).obj p).obj zero) :
    boundaryValue F j s t p v ∈ fullAllowed F j s t p
      (((productBoundary F).app p).app zero v) := by
  change boundaryValue F j s t p v ∈
    JTVertexAssignmentCover.extendAllowed (jointInclusion F j) (referenceParameter F j s t)
      (stableAllowed F j s t) p (((productBoundary F).app p).app zero v)
  rw [JTVertexAssignmentCover.extendAllowed_off (jointInclusion F j)
    (referenceParameter F j s t) (stableAllowed F j s t) p _
    (productBoundary_off_joint F j hfirst hlast p v)]
  rfl

/-- The endpoint lines lift naturally to the whole cover with their original coefficients. -/
def coveredBoundary : boundaryTime (time := time) ⟶ fullCover F j s t :=
  JTVertexAssignmentCover.liftOfAssignments _ _ _ (fullAllowed_mapsTo F j s t)
    _ (productBoundary F) (boundaryValue F j s t) (boundaryValue_natural F j s t)
    (boundaryValue_allowed F j s t hfirst hlast)

@[reassoc]
theorem coveredBoundary_projection :
    coveredBoundary F j s t hfirst hlast ≫ fullCoverProjection F j s t = productBoundary F :=
  JTVertexAssignmentCover.liftOfAssignments_projection _ _ _ (fullAllowed_mapsTo F j s t)
    _ (productBoundary F) (boundaryValue F j s t) (boundaryValue_natural F j s t)
    (boundaryValue_allowed F j s t hfirst hlast)

/-- Lifting the original endpoint lines by the original coefficient section
gives exactly the endpoint lines used to form the covered pushout. -/
theorem originalCoverSection_boundary :
    productBoundary F ≫ originalCoverSection F j =
      coveredBoundary F j (originalLeft F j) (originalRight F j) hfirst hlast := by
  unfold originalCoverSection coveredBoundary
  apply JTVertexAssignmentCover.comp_liftOfAssignments _ _ _
    (fullAllowed_mapsTo F j (originalLeft F j) (originalRight F j)) _ (𝟙 _)
    (originalValue F) (originalValue_natural F) (originalValue_allowed F j)
    (productBoundary F) (productBoundary F) (Category.comp_id _)
  intro p v
  change coord (degree (L := L) p) zero
      (((referenceParameter F j (originalLeft F j) (originalRight F j)).app p).app zero
        (((productBoundary F).app p).app zero v)) 0 = _
  rw [referenceParameter_original]

end CoveredBoundary

end FullCover

end CommonTrace

end CoefficientRestrictions

end

end DaggerModels.PartII.JTJointRelativeGraphFamily
