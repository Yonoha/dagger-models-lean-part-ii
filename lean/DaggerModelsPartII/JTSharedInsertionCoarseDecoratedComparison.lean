import DaggerModelsPartII.JTSharedInsertionCoarseComparisonNative
import DaggerModelsPartII.JTThreePieceCoefficientReassociation
import DaggerModelsPartII.JTActualJointGapPrism

/-!
# The actual corrected split compares as a complete decorated label

Keep the original common coefficient degree and all original operators. The
interval coefficient comparison restricts the SAME original full coefficient;
its inserted endpoint row is allowed to vary. Both outer correction pairs
remain unchanged. No raw equation or evaluation comparison is assumed here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTSharedInsertionCoarseDecoratedComparison

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue
  glue_first glue_last glue_left glue_right wedgeMappingPullback)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (f : X ⟶ Y) :=
  diagramMappingPrecomp (free.map f) W

private theorem pre_comp (W : Source) {X Y Z : SSet.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pre W (f ≫ g) = pre W g ≫ pre W f := by
  rw [pre, free.map_comp, diagramMappingPrecomp_comp]

private theorem interval_join (W : Source) (T : NecklaceCode) (k : SimplexCategory)
    (σ : std.obj k ⟶ labels W T) (a b c : Fin (T.len + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    (σ ≫ pre W (intervalι T a b hab)) ≫ lastRestriction W (intervalCode T a b hab) =
      (σ ≫ pre W (intervalι T b c hbc)) ≫ firstRestriction W (intervalCode T b c hbc) := by
  change (σ ≫ pre W (intervalι T a b hab)) ≫
      pre W (pointAt (intervalCode T a b hab) (ULift.up (Fin.last _))) =
    (σ ≫ pre W (intervalι T b c hbc)) ≫
      pre W (pointAt (intervalCode T b c hbc) (ULift.up 0))
  rw [Category.assoc, ← pre_comp, Category.assoc, ← pre_comp,
    intervalPoint_last, intervalPoint_first]

private theorem interval_concat_coefficient (W : Source) (T : NecklaceCode)
    (k : SimplexCategory) (σ : std.obj k ⟶ labels W T)
    (a b c : Fin (T.len + 1)) (hab : a ≤ b) (hbc : b ≤ c) :
    glue W (intervalCode T a b hab) (intervalCode T b c hbc) k
        (σ ≫ pre W (intervalι T a b hab)) (σ ≫ pre W (intervalι T b c hbc))
        (interval_join W T k σ a b c hab hbc) =
      (σ ≫ pre W (intervalι T a c (hab.trans hbc))) ≫
        pre W (JTJointCutSubdivision.concat T a b c hab hbc).hom.map := by
  apply (wedgeMappingPullback W (intervalCode T a b hab) (intervalCode T b c hbc)).hom_ext
  · rw [glue_left]
    have h := congrArg (fun u ↦ σ ≫ pre W u)
      (JTJointCutSubdivision.concat_first T a b c hab hbc)
    simpa only [pre_comp, Category.assoc] using h.symm
  · rw [glue_right]
    have h := congrArg (fun u ↦ σ ≫ pre W u)
      (JTJointCutSubdivision.concat_last T a b c hab hbc)
    simpa only [pre_comp, Category.assoc] using h.symm


private theorem pre_id (W : Source) (X : SSet.{0}) : pre W (𝟙 X) = 𝟙 _ := by
  rw [pre, free.map_id, diagramMappingPrecomp_id]

private theorem coefficient_id (W : Source) (T : NecklaceCode) (k : SimplexCategory)
    (a : std.obj k ⟶ labels W T) : a = a ≫ pre W (𝟙 T : T ⟶ T).map := by
  change a = a ≫ pre W (𝟙 T.toSSet)
  rw [pre_id]
  exact (Category.comp_id a).symm

private theorem glue_map {W : Source} {A B A' B' : NecklaceCode} {k : SimplexCategory}
    (f : A ⟶ A') (g : B ⟶ B')
    (a : std.obj k ⟶ labels W A) (b : std.obj k ⟶ labels W B)
    (a' : std.obj k ⟶ labels W A') (b' : std.obj k ⟶ labels W B')
    (hab : a ≫ lastRestriction W A = b ≫ firstRestriction W B)
    (hab' : a' ≫ lastRestriction W A' = b' ≫ firstRestriction W B')
    (ha : a = a' ≫ pre W f.map) (hb : b = b' ≫ pre W g.map) :
    glue W A B k a b hab = glue W A' B' k a' b' hab' ≫ pre W (wedgeMap f g).map := by
  have h := JTThreePieceLabelOperators.wedge_coefficient_map f g (𝟙 k)
    (glue W A B k a b hab) (glue W A' B' k a' b' hab')
    (by simpa only [std.map_id, Category.id_comp, ← Category.assoc, glue_left] using ha)
    (by simpa only [std.map_id, Category.id_comp, ← Category.assoc, glue_right] using hb)
  simpa only [std.map_id, Category.id_comp] using h

private abbrev E := single 1
private abbrev Z := single 0

private def invCode {T U : NecklaceCode} (e : T.toSSet ≅ U.toSSet)
    (hf : e.hom.app (op ⦋0⦌) T.first = U.first)
    (hl : e.hom.app (op ⦋0⦌) T.last = U.last) : U ⟶ T where
  map := e.inv
  first := by
    have h := congrArg (fun f : T.toSSet ⟶ T.toSSet ↦ f.app (op ⦋0⦌) T.first)
      e.hom_inv_id
    change e.inv.app (op ⦋0⦌) (e.hom.app (op ⦋0⦌) T.first) = T.first at h
    simpa only [hf] using h
  last := by
    have h := congrArg (fun f : T.toSSet ⟶ T.toSSet ↦ f.app (op ⦋0⦌) T.last)
      e.hom_inv_id
    change e.inv.app (op ⦋0⦌) (e.hom.app (op ⦋0⦌) T.last) = T.last at h
    simpa only [hl] using h

private def assocInv (P M R : NecklaceCode) : wedge P (wedge M R) ⟶ wedge (wedge P M) R :=
  invCode (wedgeAssoc P M R) (wedgeAssoc_first P M R) (wedgeAssoc_last P M R)

private structure PaddedCoefficients (W : Source) (A B C D K : NecklaceCode)
    (k : SimplexCategory) where
  a : std.obj k ⟶ labels W A
  e : std.obj k ⟶ labels W E
  b : std.obj k ⟶ labels W B
  z : std.obj k ⟶ labels W Z
  c : std.obj k ⟶ labels W C
  f : std.obj k ⟶ labels W E
  d : std.obj k ⟶ labels W D
  middle : std.obj k ⟶ labels W K
  ae : a ≫ lastRestriction W A = e ≫ firstRestriction W E
  eb : e ≫ lastRestriction W E = b ≫ firstRestriction W B
  bz : b ≫ lastRestriction W B = z ≫ firstRestriction W Z
  zc : z ≫ lastRestriction W Z = c ≫ firstRestriction W C
  cf : c ≫ lastRestriction W C = f ≫ firstRestriction W E
  fd : f ≫ lastRestriction W E = d ≫ firstRestriction W D
  bc : b ≫ lastRestriction W B = c ≫ firstRestriction W C
  eK : e ≫ lastRestriction W E = middle ≫ firstRestriction W K
  Kf : middle ≫ lastRestriction W K = f ≫ firstRestriction W E
  μ : wedge B C ⟶ K
  middle_eq : glue W B C k b c bc = middle ≫ pre W μ.map

private abbrev Ctx {W : Source} {A B C D K : NecklaceCode} {k : SimplexCategory} :=
  PaddedCoefficients W A B C D K k

variable {W : Source} {A B C D K : NecklaceCode} {k : SimplexCategory}

private def eb (S : Ctx (W := W) (A := A) (B := B) (C := C) (D := D) (K := K) (k := k)) :=
  glue W E B k S.e S.b S.eb
private def fd (S : Ctx (W := W) (A := A) (B := B) (C := C) (D := D) (K := K) (k := k)) :=
  glue W E D k S.f S.d S.fd
private def bc (S : Ctx (W := W) (A := A) (B := B) (C := C) (D := D) (K := K) (k := k)) :=
  glue W B C k S.b S.c S.bc
private def Kf (S : Ctx (W := W) (A := A) (B := B) (C := C) (D := D) (K := K) (k := k)) :=
  glue W K E k S.middle S.f S.Kf

variable (S : Ctx (W := W) (A := A) (B := B) (C := C) (D := D) (K := K) (k := k))

private def left := glue W A (wedge E B) k S.a (eb S) (by rw [eb, glue_first]; exact S.ae)
private def right := glue W C (wedge E D) k S.c (fd S) (by rw [fd, glue_first]; exact S.cf)
private def bcfd := glue W (wedge B C) (wedge E D) k (bc S) (fd S)
  (by rw [bc, fd, glue_last, glue_first]; exact S.cf)
private def Kfd := glue W K (wedge E D) k S.middle (fd S)
  (by rw [fd, glue_first]; exact S.Kf)
private def Kf_d := glue W (wedge K E) D k (Kf S) S.d
  (by rw [Kf, glue_last]; exact S.fd)
private def e_Kf := glue W E (wedge K E) k S.e (Kf S)
  (by rw [Kf, glue_first]; exact S.eK)

private def step0 : std.obj k ⟶ labels W
    (wedge (wedge A (wedge E B)) (wedge Z (wedge C (wedge E D)))) :=
  glue W (wedge A (wedge E B)) (wedge Z (wedge C (wedge E D))) k (left S)
    (glue W Z (wedge C (wedge E D)) k S.z (right S)
      (by rw [right, glue_first]; exact S.zc))
    (by rw [left, glue_last, eb, glue_last, glue_first]; exact S.bz)

private def step1 : std.obj k ⟶ labels W (wedge (wedge A (wedge E B)) (wedge C (wedge E D))) :=
  glue W (wedge A (wedge E B)) (wedge C (wedge E D)) k (left S) (right S)
    (by rw [left, glue_last, eb, glue_last, right, glue_first]; exact S.bc)

private def step2 : std.obj k ⟶ labels W (wedge A (wedge (wedge E B) (wedge C (wedge E D)))) :=
  glue W A (wedge (wedge E B) (wedge C (wedge E D))) k S.a
    (glue W (wedge E B) (wedge C (wedge E D)) k (eb S) (right S)
      (by rw [eb, glue_last, right, glue_first]; exact S.bc))
    (by rw [glue_first, eb, glue_first]; exact S.ae)

private def step3 : std.obj k ⟶ labels W (wedge A (wedge E (wedge B (wedge C (wedge E D))))) :=
  glue W A (wedge E (wedge B (wedge C (wedge E D)))) k S.a
    (glue W E (wedge B (wedge C (wedge E D))) k S.e
      (glue W B (wedge C (wedge E D)) k S.b (right S)
        (by rw [right, glue_first]; exact S.bc))
      (by rw [glue_first]; exact S.eb))
    (by rw [glue_first]; exact S.ae)

private def step4 : std.obj k ⟶ labels W (wedge A (wedge E (wedge (wedge B C) (wedge E D)))) :=
  glue W A (wedge E (wedge (wedge B C) (wedge E D))) k S.a
    (glue W E (wedge (wedge B C) (wedge E D)) k S.e (bcfd S)
      (by rw [bcfd, glue_first, bc, glue_first]; exact S.eb))
    (by rw [glue_first]; exact S.ae)

private def step5 : std.obj k ⟶ labels W (wedge A (wedge E (wedge K (wedge E D)))) :=
  glue W A (wedge E (wedge K (wedge E D))) k S.a
    (glue W E (wedge K (wedge E D)) k S.e (Kfd S)
      (by rw [Kfd, glue_first]; exact S.eK))
    (by rw [glue_first]; exact S.ae)

private def step6 : std.obj k ⟶ labels W (wedge A (wedge E (wedge (wedge K E) D))) :=
  glue W A (wedge E (wedge (wedge K E) D)) k S.a
    (glue W E (wedge (wedge K E) D) k S.e (Kf_d S)
      (by rw [Kf_d, glue_first, Kf, glue_first]; exact S.eK))
    (by rw [glue_first]; exact S.ae)

private def step7 : std.obj k ⟶ labels W (wedge A (wedge (wedge E (wedge K E)) D)) :=
  glue W A (wedge (wedge E (wedge K E)) D) k S.a
    (glue W (wedge E (wedge K E)) D k (e_Kf S) S.d
      (by rw [e_Kf, glue_last, Kf, glue_last]; exact S.fd))
    (by rw [glue_first, e_Kf, glue_first]; exact S.ae)


private theorem step01 : step0 S = step1 S ≫ pre W
    (wedgeMap (𝟙 (wedge A (wedge E B)))
      (JTNativeCutPointAssembly.zeroUnit Z (wedge C (wedge E D)) rfl)).map := by
  unfold step0 step1
  apply glue_map
  · exact coefficient_id W _ k (left S)
  · exact JTThreePieceCoefficientReassociation.zeroUnit_coefficient W k Z rfl
      (wedge C (wedge E D)) S.z (right S)
      (by rw [right, glue_first]; exact S.zc)

private theorem step12 : step1 S = step2 S ≫
    pre W (wedgeAssocHom A (wedge E B) (wedge C (wedge E D))) := by
  exact JTThreePieceCoefficientReassociation.associator_coefficient W A (wedge E B)
    (wedge C (wedge E D)) k S.a (eb S) (right S)
    (by rw [eb, glue_first]; exact S.ae)
    (by rw [eb, glue_last, right, glue_first]; exact S.bc)

private theorem step23 : step2 S = step3 S ≫ pre W
    (wedgeMap (𝟙 A) (wedgeAssocCodeHom E B (wedge C (wedge E D)))).map := by
  unfold step2 step3
  apply glue_map
  · exact coefficient_id W _ k S.a
  · exact JTThreePieceCoefficientReassociation.associator_coefficient W E B
      (wedge C (wedge E D)) k S.e S.b (right S) S.eb
      (by rw [right, glue_first]; exact S.bc)


private theorem step34 : step3 S = step4 S ≫ pre W
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv B C (wedge E D)))).map := by
  unfold step3 step4
  apply glue_map
  · exact coefficient_id W _ k S.a
  · apply glue_map
    · exact coefficient_id W _ k S.e
    · exact JTThreePieceCoefficientReassociation.inverse_associator_coefficient W B C
        (wedge E D) k S.b S.c (fd S) S.bc (by rw [fd, glue_first]; exact S.cf)

private theorem step45 : step4 S = step5 S ≫ pre W
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (wedgeMap S.μ (𝟙 (wedge E D))))).map := by
  unfold step4 step5
  apply glue_map
  · exact coefficient_id W _ k S.a
  · apply glue_map
    · exact coefficient_id W _ k S.e
    · unfold bcfd Kfd
      apply glue_map
      · exact S.middle_eq
      · exact coefficient_id W _ k (fd S)

private theorem step56 : step5 S = step6 S ≫ pre W
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv K E D))).map := by
  unfold step5 step6
  apply glue_map
  · exact coefficient_id W _ k S.a
  · apply glue_map
    · exact coefficient_id W _ k S.e
    · exact JTThreePieceCoefficientReassociation.inverse_associator_coefficient W K E D k
        S.middle S.f S.d S.Kf S.fd

private theorem step67 : step6 S = step7 S ≫ pre W
    (wedgeMap (𝟙 A) (assocInv E (wedge K E) D)).map := by
  unfold step6 step7
  apply glue_map
  · exact coefficient_id W _ k S.a
  · exact JTThreePieceCoefficientReassociation.inverse_associator_coefficient W E
      (wedge K E) D k S.e (Kf S) S.d
      (by rw [Kf, glue_first]; exact S.eK)
      (by rw [Kf, glue_last]; exact S.fd)

private def paddedNative :
    wedge (wedge A (wedge E B)) (wedge Z (wedge C (wedge E D))) ⟶
      wedge A (wedge (wedge E (wedge K E)) D) :=
  Hom.comp (Hom.comp (Hom.comp (Hom.comp (Hom.comp (Hom.comp
    (wedgeMap (𝟙 (wedge A (wedge E B)))
      (JTNativeCutPointAssembly.zeroUnit Z (wedge C (wedge E D)) rfl))
    (wedgeAssocCodeHom A (wedge E B) (wedge C (wedge E D))))
    (wedgeMap (𝟙 A) (wedgeAssocCodeHom E B (wedge C (wedge E D)))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv B C (wedge E D)))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (wedgeMap S.μ (𝟙 (wedge E D))))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv K E D))))
    (wedgeMap (𝟙 A) (assocInv E (wedge K E) D))

private theorem padded_coefficient : step0 S = step7 S ≫ pre W (paddedNative S).map := by
  rw [step01, step12, step23, step34, step45, step56, step67]
  simp only [Category.assoc, ← pre_comp]
  rfl


private theorem paddedNative_corrected (T : NecklaceCode) (a b c : Fin (T.len + 1))
    (hab : a ≤ b) (hbc : b ≤ c)
    (S : PaddedCoefficients W (wedge (cutLeft T a) E) (intervalCode T a b hab)
      (intervalCode T b c hbc) (wedge E (cutRight T c))
      (intervalCode T a c (hab.trans hbc)) k)
    (hμ : S.μ = (JTJointCutSubdivision.concat T a b c hab hbc).hom) :
    paddedNative S = (JTCorrectedCoarseIntervalComparison.comparisonOver T a b c hab hbc).hom := by
  unfold paddedNative
  rw [hμ]
  rfl

end

noncomputable section

open JTParametrizedTargetFamilies (Family codes)

private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private theorem index_coefficient {P R : NecklaceCode} {d : SimplexCategory}
    (C : JTComposedPrismLabels.Coefficients W P R d x y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge P R) d
        (JTComposedPrismLabels.orderedPoint C) = JTComposedPrismLabels.coefficient C := by
  unfold JTOrderedLabelBinaryGlue.coefficient
  rw [JTComposedPrismLabels.orderedPoint_coefficient]
  exact Equiv.symm_apply_apply _ _

private def fullCoefficient {P M R : NecklaceCode} {d : SimplexCategory}
    (C : JTThreePieceLabelOperators.Data W P M R d x y) :=
  JTComposedPrismLabels.coefficient (JTThreePieceLabelOperators.coefficients C)

private theorem data_coefficient {P M R : NecklaceCode} {d : SimplexCategory}
    (C : JTThreePieceLabelOperators.Data W P M R d x y) :
    JTOrderedLabelBinaryGlue.coefficient W x y (wedge P (wedge M R)) d
        (JTThreePieceLabelOperators.index C).unop.2 = fullCoefficient C :=
  index_coefficient (JTThreePieceLabelOperators.coefficients C)

/-- The unchanged common insertion chain with every original operator. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev original := JTSharedInsertionChainSupport.originalBase F j
private abbrev marks := JTSharedInsertionChainSupport.marks F j
private abbrev ordinals := JTSharedInsertionChoices.ordinals F j
private abbrev α := JTSharedInsertionChoices.toOriginal F j
private abbrev rows := JTSharedInsertionChainSupport.rows F j
private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j
private abbrev T (p : Index F j) := (codes L).obj ((original F j).obj p)
private abbrev a (p : Index F j) := ((marks F j 0).obj p).2.val
private abbrev b (p : Index F j) := ((marks F j 1).obj p).2.val
private abbrev c (p : Index F j) := ((marks F j 2).obj p).2.val
private abbrev hab (p : Index F j) :=
  ((JTSharedInsertionChoices.projection F j).obj
    ((JTSharedInsertionChoices.base F j).obj p)).2.property.1
private abbrev hbc (p : Index F j) :=
  ((JTSharedInsertionChoices.projection F j).obj
    ((JTSharedInsertionChoices.base F j).obj p)).2.property.2
private abbrev Acode (p : Index F j) := wedge (cutLeft (T F j p) (a F j p)) E
private abbrev Bcode (p : Index F j) := intervalCode (T F j p) (a F j p) (b F j p) (hab F j p)
private abbrev Ccode (p : Index F j) := intervalCode (T F j p) (b F j p) (c F j p) (hbc F j p)
private abbrev Dcode (p : Index F j) := wedge E (cutRight (T F j p) (c F j p))
private abbrev Kcode (p : Index F j) := intervalCode (T F j p) (a F j p) (c F j p)
  ((hab F j p).trans (hbc F j p))
private abbrev k (p : Index F j) := (ordinals F j).obj p

private def originalCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (T F j p) :=
  std.map ((α F j).app p) ≫ JTActualJointCutPrism.originalCoefficient ((original F j).obj p)
private def aCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (Acode F j p) :=
  ((JTSharedInsertionCoarseLabels.family F j).data p).left
private def dCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (Dcode F j p) :=
  ((JTSharedInsertionCoarseLabels.family F j).data p).right
private def eCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W E :=
  (JTSharedInsertionIncidentEdges.starting F j 0).app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
private def fCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W E :=
  (JTSharedInsertionIncidentEdges.ending F j 2).app p ≫ TwoBeadEndpointLabel.edgeLabelFromRow W
private def zCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W Z :=
  (rows F j 1).app p ≫ JTNativeRowLabel.labelFromRow W 0
private def bCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (Bcode F j p) :=
  originalCoefficient F j p ≫ pre W
    (intervalι (T F j p) (a F j p) (b F j p) (hab F j p))
private def cCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (Ccode F j p) :=
  originalCoefficient F j p ≫ pre W
    (intervalι (T F j p) (b F j p) (c F j p) (hbc F j p))
private def kCoefficient (p : Index F j) : std.obj (k F j p) ⟶ labels W (Kcode F j p) :=
  originalCoefficient F j p ≫ pre W
    (intervalι (T F j p) (a F j p) (c F j p) ((hab F j p).trans (hbc F j p)))

private theorem interval_first (p : Index F j) (v w : Fin ((T F j p).len + 1)) (h : v ≤ w) :
    (originalCoefficient F j p ≫ pre W (intervalι (T F j p) v w h)) ≫
        firstRestriction W (intervalCode (T F j p) v w h) =
      std.map ((α F j).app p) ≫
        (JTActualJointCutPrism.vertexRow ((original F j).obj p) v ≫
          TwoBeadEndpointLabel.jointLabelFromRow W) := by
  have hp := congrArg (fun t ↦ std.map ((α F j).app p) ≫ t)
    (JTActualJointGapPrism.coefficient_first (L := L) ((original F j).obj p) v w h)
  simpa only [originalCoefficient, JTActualJointGapPrism.coefficient, Category.assoc] using hp

private theorem interval_last (p : Index F j) (v w : Fin ((T F j p).len + 1)) (h : v ≤ w) :
    (originalCoefficient F j p ≫ pre W (intervalι (T F j p) v w h)) ≫
        lastRestriction W (intervalCode (T F j p) v w h) =
      std.map ((α F j).app p) ≫
        (JTActualJointCutPrism.vertexRow ((original F j).obj p) w ≫
          TwoBeadEndpointLabel.jointLabelFromRow W) := by
  have hp := congrArg (fun t ↦ std.map ((α F j).app p) ≫ t)
    (JTActualJointGapPrism.coefficient_last (L := L) ((original F j).obj p) v w h)
  simpa only [originalCoefficient, JTActualJointGapPrism.coefficient, Category.assoc] using hp

private theorem a_last (p : Index F j) :
    aCoefficient F j p ≫ lastRestriction W (Acode F j p) =
      term (std.obj (k F j p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) :=
  (JTJointPairWhiskeredSurroundings.surroundings F j).inner_left
    ((JTSharedInsertionCoarseLabels.base F j).obj p)

private theorem d_first (p : Index F j) :
    dCoefficient F j p ≫ firstRestriction W (Dcode F j p) =
      term (std.obj (k F j p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) :=
  (JTJointPairWhiskeredSurroundings.surroundings F j).inner_right
    ((JTSharedInsertionCoarseLabels.base F j).obj p)

private theorem e_first (p : Index F j) :
    eCoefficient F j p ≫ firstRestriction W E =
      term (std.obj (k F j p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) := by
  rw [eCoefficient, JTWhiskerEdgeCoefficient.first,
    (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.starting_endpoints F j 0 p)).1,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]

private theorem e_last (p : Index F j) :
    eCoefficient F j p ≫ lastRestriction W E =
      (rows F j 0).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  rw [eCoefficient, JTWhiskerEdgeCoefficient.last,
    (JTJointEndpointRelativeLift.reverseBoundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.starting_endpoints F j 0 p)).2]

private theorem f_first (p : Index F j) :
    fCoefficient F j p ≫ firstRestriction W E =
      (rows F j 2).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  rw [fCoefficient, JTWhiskerEdgeCoefficient.first,
    (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.ending_endpoints F j 2 p)).1]

private theorem f_last (p : Index F j) :
    fCoefficient F j p ≫ lastRestriction W E =
      term (std.obj (k F j p)) ≫ OrderedNecklaceVertexPoints.zeroPoint W (z j) := by
  rw [fCoefficient, JTWhiskerEdgeCoefficient.last,
    (JTJointEndpointRelativeLift.boundaryPair_endpoints W _ _
      (JTSharedInsertionIncidentEdges.ending_endpoints F j 2 p)).2,
    Category.assoc, TwoBeadEndpointLabel.jointLabelFromRow_vertex]


private theorem rowZero_first (W : Source) :
    JTNativeRowLabel.labelFromRow W 0 ≫ firstRestriction W Z =
      TwoBeadEndpointLabel.jointLabelFromRow W := by
  have h := JTNativeRowLabel.labelFromRow_vertex W 0 0
  have hv : JTMixedGraphEndpointLifts.rowVertex W ⦋0⦌ 0 = 𝟙 _ := by
    have hc : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    unfold JTMixedGraphEndpointLifts.rowVertex
    rw [hc]
    exact (JTRealizationDiagonal.ordinaryCurry.obj
      (JTReversalInput.ordinaryInput.obj W)).map_id _
  simpa only [firstRestriction, hv, Category.id_comp] using h

private theorem z_first (p : Index F j) :
    zCoefficient F j p ≫ firstRestriction W Z =
      (rows F j 1).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := by
  rw [zCoefficient, Category.assoc, rowZero_first]

private theorem z_last (p : Index F j) :
    zCoefficient F j p ≫ lastRestriction W Z =
      (rows F j 1).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W := z_first F j p

private theorem b_first (p : Index F j) :
    bCoefficient F j p ≫ firstRestriction W (Bcode F j p) =
      (rows F j 0).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_first F j p (a F j p) (b F j p) (hab F j p)

private theorem b_last (p : Index F j) :
    bCoefficient F j p ≫ lastRestriction W (Bcode F j p) =
      (rows F j 1).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_last F j p (a F j p) (b F j p) (hab F j p)

private theorem c_first (p : Index F j) :
    cCoefficient F j p ≫ firstRestriction W (Ccode F j p) =
      (rows F j 1).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_first F j p (b F j p) (c F j p) (hbc F j p)

private theorem c_last (p : Index F j) :
    cCoefficient F j p ≫ lastRestriction W (Ccode F j p) =
      (rows F j 2).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_last F j p (b F j p) (c F j p) (hbc F j p)

private theorem k_first (p : Index F j) :
    kCoefficient F j p ≫ firstRestriction W (Kcode F j p) =
      (rows F j 0).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_first F j p (a F j p) (c F j p) ((hab F j p).trans (hbc F j p))

private theorem k_last (p : Index F j) :
    kCoefficient F j p ≫ lastRestriction W (Kcode F j p) =
      (rows F j 2).app p ≫ TwoBeadEndpointLabel.jointLabelFromRow W :=
  interval_last F j p (a F j p) (c F j p) ((hab F j p).trans (hbc F j p))

private def actualData (p : Index F j) :
    PaddedCoefficients W (Acode F j p) (Bcode F j p) (Ccode F j p) (Dcode F j p)
      (Kcode F j p) (k F j p) where
  a := aCoefficient F j p
  e := eCoefficient F j p
  b := bCoefficient F j p
  z := zCoefficient F j p
  c := cCoefficient F j p
  f := fCoefficient F j p
  d := dCoefficient F j p
  middle := kCoefficient F j p
  ae := (a_last F j p).trans (e_first F j p).symm
  eb := (e_last F j p).trans (b_first F j p).symm
  bz := (b_last F j p).trans (z_first F j p).symm
  zc := (z_last F j p).trans (c_first F j p).symm
  cf := (c_last F j p).trans (f_first F j p).symm
  fd := (f_last F j p).trans (d_first F j p).symm
  bc := (b_last F j p).trans (c_first F j p).symm
  eK := (e_last F j p).trans (k_first F j p).symm
  Kf := (k_last F j p).trans (f_first F j p).symm
  μ := (JTJointCutSubdivision.concat (T F j p) (a F j p) (b F j p) (c F j p)
    (hab F j p) (hbc F j p)).hom
  middle_eq := interval_concat_coefficient W (T F j p) (k F j p)
    (originalCoefficient F j p) (a F j p) (b F j p) (c F j p) (hab F j p) (hbc F j p)

private theorem actual_coefficient (p : Index F j) :
    step0 (actualData F j p) = step7 (actualData F j p) ≫
      pre W (paddedNative (actualData F j p)).map := padded_coefficient (actualData F j p)


private def oldDataView (p : Index F j) :
    JTThreePieceLabelOperators.Data W (wedge (Acode F j p) (wedge E (Bcode F j p))) Z
      (wedge (Ccode F j p) (wedge E (Dcode F j p))) (k F j p) x y :=
  ((JTSharedInsertionNormalizedSeam.oldFamily F j).data p)

private def coarseDataView (p : Index F j) :
    JTThreePieceLabelOperators.Data W (Acode F j p) (wedge E (wedge (Kcode F j p) E))
      (Dcode F j p) (k F j p) x y := (JTSharedInsertionCoarseLabels.family F j).data p

private theorem oldDataView_left (p : Index F j) :
    (oldDataView F j p).left = left (actualData F j p) := by rfl

private theorem oldDataView_middle (p : Index F j) :
    (oldDataView F j p).middle = (actualData F j p).z := rfl

private theorem oldDataView_right (p : Index F j) :
    (oldDataView F j p).right = right (actualData F j p) := by rfl

private theorem oldCoefficient_view (p : Index F j) :
    fullCoefficient (oldDataView F j p) = step0 (actualData F j p) := by
  apply (wedgeMappingPullback W (wedge (Acode F j p) (wedge E (Bcode F j p)))
    (wedge Z (wedge (Ccode F j p) (wedge E (Dcode F j p))))).hom_ext
  · simpa only [fullCoefficient, JTComposedPrismLabels.coefficient,
      JTThreePieceLabelOperators.coefficients, step0, glue_left] using oldDataView_left F j p
  · apply (wedgeMappingPullback W Z (wedge (Ccode F j p) (wedge E (Dcode F j p)))).hom_ext
    · simpa only [fullCoefficient, JTComposedPrismLabels.coefficient,
        JTThreePieceLabelOperators.coefficients, JTThreePieceLabelOperators.inside, step0,
        glue_right, glue_left] using oldDataView_middle F j p
    · simpa only [fullCoefficient, JTComposedPrismLabels.coefficient,
        JTThreePieceLabelOperators.coefficients, JTThreePieceLabelOperators.inside, step0,
        glue_right] using oldDataView_right F j p

private theorem coarseDataView_middle (p : Index F j) :
    (coarseDataView F j p).middle = e_Kf (actualData F j p) := by
  have h := index_coefficient (JTJointPairGapChainLabels.coefficients F j
    ((JTSharedInsertionCoarseLabels.base F j).obj p))
  exact h.trans (by rfl)

private theorem coarseCoefficient_view (p : Index F j) :
    fullCoefficient (coarseDataView F j p) = step7 (actualData F j p) := by
  apply (wedgeMappingPullback W (Acode F j p)
    (wedge (wedge E (wedge (Kcode F j p) E)) (Dcode F j p))).hom_ext
  · simp only [fullCoefficient, JTComposedPrismLabels.coefficient,
      JTThreePieceLabelOperators.coefficients, step7, glue_left]
    rfl
  · apply (wedgeMappingPullback W (wedge E (wedge (Kcode F j p) E)) (Dcode F j p)).hom_ext
    · simpa only [fullCoefficient, JTComposedPrismLabels.coefficient,
        JTThreePieceLabelOperators.coefficients, JTThreePieceLabelOperators.inside, step7,
        glue_right, glue_left] using coarseDataView_middle F j p
    · simp only [fullCoefficient, JTComposedPrismLabels.coefficient,
        JTThreePieceLabelOperators.coefficients, JTThreePieceLabelOperators.inside, step7,
        glue_right]
      rfl

private theorem paddedNative_actual (p : Index F j) :
    HEq (paddedNative (actualData F j p))
      (JTCorrectedCoarseIntervalComparison.comparisonOver (T F j p) (a F j p)
        (b F j p) (c F j p) (hab F j p) (hbc F j p)).hom :=
  heq_of_eq (paddedNative_corrected (T F j p) (a F j p) (b F j p) (c F j p)
    (hab F j p) (hbc F j p) (actualData F j p) (by rfl))


private abbrev oldLabels := (JTSharedInsertionNormalizedSeam.oldFamily F j).labels
private abbrev coarseLabels := JTSharedInsertionCoarseLabels.labels F j
private abbrev splitCode (p : Index F j) :=
  wedge (wedge (Acode F j p) (wedge E (Bcode F j p)))
    (wedge Z (wedge (Ccode F j p) (wedge E (Dcode F j p))))
private abbrev targetCode (p : Index F j) :=
  wedge (Acode F j p) (wedge (wedge E (wedge (Kcode F j p) E)) (Dcode F j p))

private theorem oldLeft_code (p : Index F j) :
    (JTSharedInsertionSeamSurroundings.leftNative F j).obj p =
      wedge (Acode F j p) (wedge E (Bcode F j p)) := rfl
private theorem oldRight_code (p : Index F j) :
    (JTSharedInsertionSeamSurroundings.rightNative F j).obj p =
      wedge (Ccode F j p) (wedge E (Dcode F j p)) := rfl
private theorem coarseLeft_code (p : Index F j) :
    (JTSharedInsertionCoarseLabels.leftNative F j).obj p = Acode F j p := rfl
private theorem coarseMiddle_code (p : Index F j) :
    (JTSharedInsertionCoarseLabels.middleNative F j).obj p = wedge E (wedge (Kcode F j p) E) :=
  rfl
private theorem coarseRight_code (p : Index F j) :
    (JTSharedInsertionCoarseLabels.rightNative F j).obj p = Dcode F j p := rfl

private theorem fixedFamily_native {I : Type} [SmallCategory I]
    {P R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory} {M : NecklaceCode}
    (C : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K) (p : I) :
    (codes C.labels).obj p = wedge (P.obj p) (wedge M (R.obj p)) := rfl

private theorem old_code (p : Index F j) : (codes (oldLabels F j)).obj p = splitCode F j p := by
  have h := fixedFamily_native (JTSharedInsertionNormalizedSeam.oldFamily F j) p
  exact h.trans (congrArg₂ wedge (oldLeft_code F j p)
    (congrArg (wedge Z) (oldRight_code F j p)))

private theorem coarse_code (p : Index F j) :
    (codes (coarseLabels F j)).obj p = targetCode F j p :=
  (congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)).trans
    (congrArg₂ wedge (coarseLeft_code F j p)
      (congrArg₂ wedge (coarseMiddle_code F j p) (coarseRight_code F j p)))

private theorem fixedFamily_coefficient {I : Type} [SmallCategory I]
    {P R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory} {M : NecklaceCode}
    (C : JTWhiskeredSeamDiagram.Family (W := W) (x := x) (y := y) M P R K) (p : I) :
    JTOrderedLabelBinaryGlue.coefficient W x y ((codes C.labels).obj p) (K.obj p)
        (C.labels.obj p).unop.2 = fullCoefficient (C.data p) := data_coefficient (C.data p)

private theorem varyingFamily_coefficient {I : Type} [SmallCategory I]
    {P M R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}
    (C : JTVariableMiddleWhiskeredDiagram.Family
      (W := W) (x := x) (y := y) P M R K) (p : I) :
    JTOrderedLabelBinaryGlue.coefficient W x y ((codes C.labels).obj p) (K.obj p)
        (C.labels.obj p).unop.2 = fullCoefficient (C.data p) := data_coefficient (C.data p)

private def oldPointCoefficient (p : Index F j) :=
  JTOrderedLabelBinaryGlue.coefficient W x y ((codes (oldLabels F j)).obj p) (k F j p)
    ((oldLabels F j).obj p).unop.2
private def coarsePointCoefficient (p : Index F j) :=
  JTOrderedLabelBinaryGlue.coefficient W x y ((codes (coarseLabels F j)).obj p) (k F j p)
    ((coarseLabels F j).obj p).unop.2

private theorem oldFullCoefficient_heq (p : Index F j) :
    HEq (fullCoefficient ((JTSharedInsertionNormalizedSeam.oldFamily F j).data p))
      (fullCoefficient (oldDataView F j p)) := by rfl
private theorem coarseFullCoefficient_heq (p : Index F j) :
    HEq (fullCoefficient ((JTSharedInsertionCoarseLabels.family F j).data p))
      (fullCoefficient (coarseDataView F j p)) := by rfl

private theorem oldPointCoefficient_heq (p : Index F j) :
    HEq (oldPointCoefficient F j p) (fullCoefficient (oldDataView F j p)) :=
  (heq_of_eq (fixedFamily_coefficient (JTSharedInsertionNormalizedSeam.oldFamily F j) p)).trans
    (oldFullCoefficient_heq F j p)
private theorem coarsePointCoefficient_heq (p : Index F j) :
    HEq (coarsePointCoefficient F j p) (fullCoefficient (coarseDataView F j p)) :=
  (heq_of_eq (varyingFamily_coefficient (JTSharedInsertionCoarseLabels.family F j) p)).trans
    (coarseFullCoefficient_heq F j p)

private theorem coefficient_transport {N M N' M' : NecklaceCode} {d : SimplexCategory}
    (en : N = N') (em : M = M')
    (a : std.obj d ⟶ labels W N) (b : std.obj d ⟶ labels W M) (f : N ⟶ M)
    (a' : std.obj d ⟶ labels W N') (b' : std.obj d ⟶ labels W M') (f' : N' ⟶ M')
    (ha : HEq a a') (hb : HEq b b') (hf : HEq f f')
    (h : a' = b' ≫ pre W f'.map) : a = b ≫ pre W f.map := by
  subst N'
  subst M'
  have ha' : a = a' := eq_of_heq ha
  have hb' : b = b' := eq_of_heq hb
  have hf' : f = f' := eq_of_heq hf
  simpa only [ha', hb', hf'] using h

private theorem dataCoefficient_eq (p : Index F j) :
    oldPointCoefficient F j p = coarsePointCoefficient F j p ≫
      pre W ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p).map := by
  apply coefficient_transport (old_code F j p) (coarse_code F j p)
    (oldPointCoefficient F j p) (coarsePointCoefficient F j p)
    ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p)
    (fullCoefficient (oldDataView F j p)) (fullCoefficient (coarseDataView F j p))
    (paddedNative (actualData F j p)) (oldPointCoefficient_heq F j p)
    (coarsePointCoefficient_heq F j p)
    ((JTSharedInsertionCoarseComparisonNative.comparison_app F j p).trans
      (paddedNative_actual F j p).symm)
  rw [oldCoefficient_view, coarseCoefficient_view]
  exact actual_coefficient F j p

private abbrev proj (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private instance : (proj W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private def orderedMap (S T : DecoratedNecklaceHomDiagram.Index W x y)
    (f : OrderedLabelElements.necklace W (OrderedNecklaceVertexPoints.boundaryPoint W x y) S ⟶
      OrderedLabelElements.necklace W (OrderedNecklaceVertexPoints.boundaryPoint W x y) T)
    (r : OrderedLabelElements.degree W (OrderedNecklaceVertexPoints.boundaryPoint W x y) S ⟶
      OrderedLabelElements.degree W (OrderedNecklaceVertexPoints.boundaryPoint W x y) T)
    (h : JTOrderedLabelBinaryGlue.coefficient W x y ((proj W x y).obj S).1
        ((proj W x y).obj S).2 S.unop.2 = std.map r ≫
      JTOrderedLabelBinaryGlue.coefficient W x y ((proj W x y).obj T).1
        ((proj W x y).obj T).2 T.unop.2 ≫ pre W f.map) : S ⟶ T :=
  JTOrderedLabelWedge.indexHomOfCoefficient f r S.unop.2 T.unop.2 h

private theorem orderedMap_projection (S T : DecoratedNecklaceHomDiagram.Index W x y)
    (f : OrderedLabelElements.necklace W (OrderedNecklaceVertexPoints.boundaryPoint W x y) S ⟶
      OrderedLabelElements.necklace W (OrderedNecklaceVertexPoints.boundaryPoint W x y) T)
    (r : OrderedLabelElements.degree W (OrderedNecklaceVertexPoints.boundaryPoint W x y) S ⟶
      OrderedLabelElements.degree W (OrderedNecklaceVertexPoints.boundaryPoint W x y) T)
    (h : JTOrderedLabelBinaryGlue.coefficient W x y ((proj W x y).obj S).1
        ((proj W x y).obj S).2 S.unop.2 = std.map r ≫
      JTOrderedLabelBinaryGlue.coefficient W x y ((proj W x y).obj T).1
        ((proj W x y).obj T).2 T.unop.2 ≫ pre W f.map) :
    (proj W x y).map (orderedMap S T f r h) = (f, r) := rfl

private theorem componentEquation (p : Index F j) :
    oldPointCoefficient F j p = std.map (𝟙 (k F j p)) ≫ coarsePointCoefficient F j p ≫
      pre W ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p).map := by
  simpa only [std.map_id, Category.id_comp] using dataCoefficient_eq F j p

private def component (p : Index F j) :
    (oldLabels F j).obj p ⟶ (coarseLabels F j).obj p :=
  orderedMap ((oldLabels F j).obj p) ((coarseLabels F j).obj p)
    ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p) (𝟙 (k F j p))
    (componentEquation F j p)

private theorem component_projection (p : Index F j) :
    (proj W x y).map (component F j p) =
      ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p, 𝟙 (k F j p)) :=
  orderedMap_projection ((oldLabels F j).obj p) ((coarseLabels F j).obj p)
    ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p) (𝟙 (k F j p))
    (componentEquation F j p)

section ProjectionAssembly

variable {I : Type} [SmallCategory I]
variable {S T : I ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable (n : codes S ⟶ codes T)
variable (d : JTParametrizedTargetFamilyComparison.degrees S ⟶
  JTParametrizedTargetFamilyComparison.degrees T)
variable (c : ∀ p, S.obj p ⟶ T.obj p)
variable (h : ∀ p, (proj W x y).map (c p) = (n.app p, d.app p))

private def naturalFromProjection : S ⟶ T where
  app := c
  naturality {p q} f := by
    apply (proj W x y).map_injective
    rw [(proj W x y).map_comp, (proj W x y).map_comp, h q, h p]
    apply Prod.ext
    · exact n.naturality f
    · exact d.naturality f

private theorem naturalFromProjection_native :
    JTWhiskeredSeamTarget.nativeOf (naturalFromProjection n d c h) = n := by
  apply NatTrans.ext
  funext p
  exact congrArg Prod.fst (h p)

private theorem naturalFromProjection_degree :
    JTParametrizedTargetFamilyComparison.coefficient (naturalFromProjection n d c h) = d := by
  apply NatTrans.ext
  funext p
  exact congrArg Prod.snd (h p)

end ProjectionAssembly

/-- The ACTUAL old corrected split compares to the ACTUAL complete coarse decorated labels.
Every original operator and both outside correction pairs are retained on the SAME full chain. -/
def comparison : (JTSharedInsertionNormalizedSeam.oldFamily F j).labels ⟶
    JTSharedInsertionCoarseLabels.labels F j :=
  naturalFromProjection (JTSharedInsertionCoarseComparisonNative.comparison F j)
    (𝟙 (ordinals F j)) (component F j) (component_projection F j)

/-- Its exact original native operator and its identity coefficient operator are retained. -/
theorem projection_app (p : Index F j) :
    (proj W x y).map ((comparison F j).app p) =
      ((JTSharedInsertionCoarseComparisonNative.comparison F j).app p, 𝟙 (k F j p)) :=
  component_projection F j p

/-- The projected native comparison is exactly the already checked actual comparison. -/
theorem native_comparison : JTWhiskeredSeamTarget.nativeOf (comparison F j) =
    JTSharedInsertionCoarseComparisonNative.comparison F j :=
  naturalFromProjection_native (JTSharedInsertionCoarseComparisonNative.comparison F j)
    (𝟙 (ordinals F j)) (component F j) (component_projection F j)

/-- The complete common coefficient degree and every coefficient operator stay unchanged. -/
theorem coefficient_comparison :
    JTParametrizedTargetFamilyComparison.coefficient (comparison F j) = 𝟙 (ordinals F j) :=
  naturalFromProjection_degree (JTSharedInsertionCoarseComparisonNative.comparison F j)
    (𝟙 (ordinals F j)) (component F j) (component_projection F j)

/-- The decorated comparison reaches the SAME original Q through the exact native target. -/
theorem target_square : JTWhiskeredSeamTarget.nativeOf (comparison F j) ≫
    JTSharedInsertionCoarseNative.target F j = JTSharedInsertionOldGraph.target F j := by
  rw [native_comparison]
  change JTSharedInsertionCoarseComparisonNative.comparison F j ≫
      (JTSharedInsertionCoarseNative.assembly F j ≫
        Functor.whiskerLeft (original F j) F.collapse) =
    JTSharedInsertionSeamNative.oldAssembly F j ≫ Functor.whiskerLeft (original F j) F.collapse
  rw [← Category.assoc, JTSharedInsertionCoarseComparisonNative.comparison_assembly]

end
end DaggerModels.PartII.JTSharedInsertionCoarseDecoratedComparison
