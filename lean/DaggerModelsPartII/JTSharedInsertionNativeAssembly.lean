import DaggerModelsPartII.JTCorrectedIntervalAssembly
import DaggerModelsPartII.JTSharedInsertionSeamSurroundings
import DaggerModelsPartII.JTExactlyMarkedCutDiagrams

/-!
# Actual corrected surroundings collapse naturally to the original cuts

Both outer corrections are retained on each side of the inserted cut. Their
native maps into the original source are derived from the actual interval and
constant correction pieces. These maps induce natural collapses to the literal
old prefix and suffix at the inserted vertex. No raw-label equality is assumed
or asserted by this native assembly.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTSharedInsertionNativeAssembly

noncomputable section

private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev E := single 1

private theorem wedge_over_natural {X Y : SSet.{0}}
    {x₀ x₁ x₂ : X.obj (op ⦋0⦌)} {y₀ y₁ y₂ : Y.obj (op ⦋0⦌)}
    (P : NecklacesOver X x₀ x₁) (R : NecklacesOver X x₁ x₂)
    (P' : NecklacesOver Y y₀ y₁) (R' : NecklacesOver Y y₁ y₂)
    (f : P.code ⟶ P'.code) (g : R.code ⟶ R'.code) (n : X ⟶ Y)
    (hf : f.map ≫ P'.map = P.map ≫ n) (hg : g.map ≫ R'.map = R.map ≫ n) :
    (wedgeMap f g).map ≫ (NecklacesOver.wedge P' R').map =
      (NecklacesOver.wedge P R).map ≫ n := by
  apply (wedgeIsPushout P.code R.code).hom_ext
  · rw [← Category.assoc, wedgeMap_left, Category.assoc, NecklacesOver.wedge_left,
      ← Category.assoc, NecklacesOver.wedge_left, hf]
  · rw [← Category.assoc, wedgeMap_right, Category.assoc, NecklacesOver.wedge_right,
      ← Category.assoc, NecklacesOver.wedge_right, hg]

private theorem constant_over_natural {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (v : Fin (T.len + 1)) (w : Fin (U.len + 1)) (hv : orderMap g.map v = w) :
    (NecklaceCode.Hom.id.{0} E).map ≫ (JTCorrectedIntervalAssembly.constantOver E
        (U.verticesEquiv.symm (ULift.up w))).map =
      (JTCorrectedIntervalAssembly.constantOver E
        (T.verticesEquiv.symm (ULift.up v))).map ≫ g.map := by
  have hp : pointAt T (ULift.up v) ≫ g.map = pointAt U (ULift.up w) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact hv
  change (𝟙 E.toSSet) ≫ (term E.toSSet ≫ pointAt U (ULift.up w)) =
    (term E.toSSet ≫ pointAt T (ULift.up v)) ≫ g.map
  rw [Category.id_comp, Category.assoc, hp]

private theorem corrected_left_natural {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (a b : Fin (T.len + 1)) (a' b' : Fin (U.len + 1))
    (hab : a ≤ b) (hab' : a' ≤ b')
    (ha : orderMap g.map a = a') (hb : orderMap g.map b = b') :
    (wedgeMap (wedgeMap (cutLeftHom g a a' ha) (𝟙 E))
        (wedgeMap (𝟙 E) (intervalCodeHom g.map a b hab a' b' hab' ha hb))).map ≫
          (JTCorrectedIntervalAssembly.leftOver U a' b' hab').map =
      (JTCorrectedIntervalAssembly.leftOver T a b hab).map ≫ g.map := by
  let P := intervalOver T 0 a (Fin.zero_le a)
  let R := intervalOver T a b hab
  let e := JTCorrectedIntervalAssembly.constantOver E (T.verticesEquiv.symm (ULift.up a))
  let P' := intervalOver U 0 a' (Fin.zero_le a')
  let R' := intervalOver U a' b' hab'
  let e' := JTCorrectedIntervalAssembly.constantOver E (U.verticesEquiv.symm (ULift.up a'))
  exact wedge_over_natural (NecklacesOver.wedge P e) (NecklacesOver.wedge e R)
    (NecklacesOver.wedge P' e') (NecklacesOver.wedge e' R')
    (wedgeMap (cutLeftHom g a a' ha) (𝟙 E))
    (wedgeMap (𝟙 E) (intervalCodeHom g.map a b hab a' b' hab' ha hb)) g.map
    (wedge_over_natural P e P' e' (cutLeftHom g a a' ha) (𝟙 E) g.map
      (cutLeftHom_fac g a a' ha) (constant_over_natural g a a' ha))
    (wedge_over_natural e R e' R' (𝟙 E)
      (intervalCodeHom g.map a b hab a' b' hab' ha hb) g.map
      (constant_over_natural g a a' ha)
      (necklaceIntervalMap_fac g.map a b hab a' b' hab' ha.ge hb.le))

private theorem corrected_right_natural {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (b c : Fin (T.len + 1)) (b' c' : Fin (U.len + 1))
    (hbc : b ≤ c) (hbc' : b' ≤ c')
    (hb : orderMap g.map b = b') (hc : orderMap g.map c = c') :
    (wedgeMap (intervalCodeHom g.map b c hbc b' c' hbc' hb hc)
        (wedgeMap (𝟙 E) (wedgeMap (𝟙 E) (cutRightHom g c c' hc)))).map ≫
          (JTCorrectedIntervalAssembly.rightOver U b' c' hbc').map =
      (JTCorrectedIntervalAssembly.rightOver T b c hbc).map ≫ g.map := by
  let P := intervalOver T b c hbc
  let R := intervalOver T c (Fin.last T.len) (Fin.le_last c)
  let e := JTCorrectedIntervalAssembly.constantOver E (T.verticesEquiv.symm (ULift.up c))
  let P' := intervalOver U b' c' hbc'
  let R' := intervalOver U c' (Fin.last U.len) (Fin.le_last c')
  let e' := JTCorrectedIntervalAssembly.constantOver E (U.verticesEquiv.symm (ULift.up c'))
  exact wedge_over_natural P (NecklacesOver.wedge e (NecklacesOver.wedge e R))
    P' (NecklacesOver.wedge e' (NecklacesOver.wedge e' R'))
    (intervalCodeHom g.map b c hbc b' c' hbc' hb hc)
    (wedgeMap (𝟙 E) (wedgeMap (𝟙 E) (cutRightHom g c c' hc))) g.map
    (necklaceIntervalMap_fac g.map b c hbc b' c' hbc' hb.ge hc.le)
    (wedge_over_natural e (NecklacesOver.wedge e R) e' (NecklacesOver.wedge e' R')
      (𝟙 E) (wedgeMap (𝟙 E) (cutRightHom g c c' hc)) g.map
      (constant_over_natural g c c' hc)
      (wedge_over_natural e R e' R' (𝟙 E) (cutRightHom g c c' hc) g.map
        (constant_over_natural g c c' hc) (cutRightHom_fac g c c' hc)))

private theorem compare_natural {P P' C C' T T' : NecklaceCode}
    (f : P ⟶ P') (c : C ⟶ C') (l : P ⟶ C) (l' : P' ⟶ C')
    (ι : (C.toSSet : SSet.{0}) ⟶ T.toSSet) (ι' : C'.toSSet ⟶ T'.toSSet)
    [Mono ι'] (g : T ⟶ T') (s : P.toSSet ⟶ T.toSSet) (s' : P'.toSSet ⟶ T'.toSSet)
    (hf : f.map ≫ s' = s ≫ g.map) (hl : l.map ≫ ι = s) (hl' : l'.map ≫ ι' = s')
    (hc : c.map ≫ ι' = ι ≫ g.map) : f ≫ l' = l ≫ c := by
  apply NecklaceCode.Hom.ext
  apply (cancel_mono ι').mp
  change (f.map ≫ l'.map) ≫ ι' = (l.map ≫ c.map) ≫ ι'
  rw [Category.assoc, hl', Category.assoc, hc, ← Category.assoc, hl]
  exact hf

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : JTParametrizedTargetFamilies.Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

private theorem right_label_code_map
    {p q : JTActualJointChoiceChainGraph.Index F j} (f : p ⟶ q) :
    (JTParametrizedTargetFamilies.codes (JTActualJointChainSideLabels.rightLabels F j)).map f =
      wedgeMap (𝟙 E) ((JTExactlyMarkedCutDiagrams.rightNative F j).map
        ((JTActualJointChoiceChainGraph.base F j ⋙
          JTActualJointChoiceCover.projection F j).map f)) := rfl

/-- The actual common insertion chain, retaining its one full all-vertex tuple. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The unchanged original source object and every original source arrow. -/
abbrev originalBase := JTSharedInsertionChainSupport.originalBase F j

private abbrev marks := JTSharedInsertionChainSupport.marks F j
private abbrev codes := JTParametrizedTargetFamilies.codes L
private abbrev T (p : Index F j) := (codes (L := L)).obj ((originalBase F j).obj p)
private abbrev a (p : Index F j) := ((marks F j 0).obj p).2.val
private abbrev b (p : Index F j) := ((marks F j 1).obj p).2.val
private abbrev c (p : Index F j) := ((marks F j 2).obj p).2.val
private abbrev insertion (p : Index F j) :=
  (JTSharedInsertionChoices.projection F j).obj ((JTSharedInsertionChoices.base F j).obj p)
private abbrev hab (p : Index F j) := (insertion F j p).2.property.1
private abbrev hbc (p : Index F j) := (insertion F j p).2.property.2
private abbrev oldNative {p q : Index F j} (f : p ⟶ q) :=
  (codes (L := L)).map ((originalBase F j).map f)

/-- The literal old prefix at the actual inserted vertex b. -/
abbrev leftCuts := marks F j 1 ⋙ JTExactlyMarkedCutDiagrams.leftNative F j

/-- The literal old suffix at that same actual inserted vertex. -/
abbrev rightCuts := marks F j 1 ⋙ JTExactlyMarkedCutDiagrams.rightNative F j

/-- Collapse the two earlier corrections while retaining the complete original native map. -/
def leftToOriginal (p : Index F j) :
    ((JTSharedInsertionSeamSurroundings.leftNative F j).obj p).toSSet ⟶ (T F j p).toSSet :=
  (JTCorrectedIntervalAssembly.leftOver (T F j p) (a F j p) (b F j p) (hab F j p)).map

/-- Collapse the two later corrections while retaining that SAME original source. -/
def rightToOriginal (p : Index F j) :
    ((JTSharedInsertionSeamSurroundings.rightNative F j).obj p).toSSet ⟶ (T F j p).toSSet :=
  (JTCorrectedIntervalAssembly.rightOver (T F j p) (b F j p) (c F j p) (hbc F j p)).map

/-- The entire corrected left native square commutes under every actual original arrow. -/
theorem leftToOriginal_natural {p q : Index F j} (f : p ⟶ q) :
    ((JTSharedInsertionSeamSurroundings.leftNative F j).map f).map ≫ leftToOriginal F j q =
      leftToOriginal F j p ≫ (oldNative F j f).map := by
  exact corrected_left_natural (oldNative F j f) (a F j p) (b F j p) (a F j q) (b F j q)
    (hab F j p) (hab F j q)
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 0).map f))
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 1).map f))

private abbrev rightOuter := JTParametrizedTargetFamilies.codes
  (JTSharedInsertionChoices.laterChain F j ⋙ JTActualJointChainSideLabels.rightLabels F j)

private theorem right_native_top_map {p q : Index F j} (f : p ⟶ q) :
    (JTSharedInsertionSeamSurroundings.rightNative F j).map f =
      wedgeMap ((JTSharedInsertionSeamSurroundings.upperNative F j).map f)
        (wedgeMap (𝟙 E) ((rightOuter F j).map f)) := rfl

private theorem right_outer_map {p q : Index F j} (f : p ⟶ q) :
    (show wedge E (cutRight (T F j p) (c F j p)) ⟶
        wedge E (cutRight (T F j q) (c F j q)) from
      (rightOuter F j).map f) =
      wedgeMap (𝟙 E) (cutRightHom (oldNative F j f) (c F j p) (c F j q)
        (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 2).map f))) := by
  exact right_label_code_map F j ((JTSharedInsertionChoices.laterChain F j).map f)

set_option maxHeartbeats 850000 in
/-- The entire corrected right native square retains all actual original operators. -/
theorem rightToOriginal_natural {p q : Index F j} (f : p ⟶ q) :
    (show (JTCorrectedIntervalAssembly.rightOver (T F j p) (b F j p) (c F j p)
        (hbc F j p)).code.toSSet ⟶ (T F j q).toSSet from
      ((JTSharedInsertionSeamSurroundings.rightNative F j).map f).map ≫
        rightToOriginal F j q) =
    (show (JTCorrectedIntervalAssembly.rightOver (T F j p) (b F j p) (c F j p)
        (hbc F j p)).code.toSSet ⟶ (T F j q).toSSet from
      rightToOriginal F j p ≫ (oldNative F j f).map) := by
  have h := corrected_right_natural (oldNative F j f)
    (b F j p) (c F j p) (b F j q) (c F j q) (hbc F j p) (hbc F j q)
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 1).map f))
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 2).map f))
  have hr := right_outer_map F j f
  dsimp only at hr
  rw [right_native_top_map F j f, hr]
  exact h

private def leftComponent (p : Index F j) :
    (JTSharedInsertionSeamSurroundings.leftNative F j).obj p ⟶ (leftCuts F j).obj p :=
  JTCorrectedIntervalAssembly.leftToCut (T F j p) (a F j p) (b F j p) (hab F j p)

private def rightComponent (p : Index F j) :
    (JTSharedInsertionSeamSurroundings.rightNative F j).obj p ⟶ (rightCuts F j).obj p :=
  JTCorrectedIntervalAssembly.rightToCut (T F j p) (b F j p) (c F j p) (hbc F j p)

/-- The left collapse has the full original native factorization, including both edge pieces. -/
theorem leftComponent_fac (p : Index F j) :
    (leftComponent F j p).map ≫ cutLeftι (T F j p) (b F j p) = leftToOriginal F j p :=
  JTCorrectedIntervalAssembly.leftToCut_fac (T F j p) (a F j p) (b F j p) (hab F j p)

/-- The right collapse has the corresponding full factorization into the same original source. -/
theorem rightComponent_fac (p : Index F j) :
    (rightComponent F j p).map ≫ cutRightι (T F j p) (b F j p) = rightToOriginal F j p :=
  JTCorrectedIntervalAssembly.rightToCut_fac (T F j p) (b F j p) (c F j p) (hbc F j p)

/-- The actual corrected left surrounding collapses naturally to the old cut at b. -/
def leftToCut : JTSharedInsertionSeamSurroundings.leftNative F j ⟶ leftCuts F j where
  app := leftComponent F j
  naturality {p q} f := by
    haveI : Mono (cutLeftι (T F j q) (b F j q)) := by
      dsimp only [cutLeftι]
      infer_instance
    exact compare_natural _ _ _ _ (cutLeftι (T F j p) (b F j p))
      (cutLeftι (T F j q) (b F j q)) (oldNative F j f) _ _
      (leftToOriginal_natural F j f) (leftComponent_fac F j p) (leftComponent_fac F j q)
      (cutLeftHom_fac (oldNative F j f) (b F j p) (b F j q)
        (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 1).map f)))

/-- The actual corrected right surrounding collapses naturally to the old cut at b. -/
def rightToCut : JTSharedInsertionSeamSurroundings.rightNative F j ⟶ rightCuts F j where
  app := rightComponent F j
  naturality {p q} f := by
    haveI : Mono (cutRightι (T F j q) (b F j q)) := by
      dsimp only [cutRightι]
      infer_instance
    exact compare_natural _ _ _ _ (cutRightι (T F j p) (b F j p))
      (cutRightι (T F j q) (b F j q)) (oldNative F j f) _ _
      (rightToOriginal_natural F j f) (rightComponent_fac F j p) (rightComponent_fac F j q)
      (cutRightHom_fac (oldNative F j f) (b F j p) (b F j q)
        (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 1).map f)))

/-- The natural left collapse preserves its exact original native factorization. -/
theorem leftToCut_fac (p : Index F j) :
    ((leftToCut F j).app p).map ≫ cutLeftι (T F j p) (b F j p) = leftToOriginal F j p :=
  leftComponent_fac F j p

/-- The natural right collapse preserves its exact original native factorization. -/
theorem rightToCut_fac (p : Index F j) :
    ((rightToCut F j).app p).map ≫ cutRightι (T F j p) (b F j p) = rightToOriginal F j p :=
  rightComponent_fac F j p

end
end DaggerModels.PartII.JTSharedInsertionNativeAssembly
