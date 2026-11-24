import DaggerModelsPartII.JTCorrectedCoarseIntervalComparison
import DaggerModelsPartII.JTSharedInsertionCoarseLabels
import DaggerModelsPartII.JTSharedInsertionChainSupport

/-!
# The actual coarse corrected label assembles in the original source

All three original intervals and all four shared correction pieces are retained.
Native naturality follows from the exact cut/interval factorization and constant
vertex maps before composing with the original fixed-target collapse. This is a
native construction only; it adds no raw equation, product Family or section.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTSharedInsertionCoarseNative

noncomputable section

private abbrev E := single 1
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem wedge_natural {X Y : SSet.{0}}
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

private theorem constant_natural {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (a : Fin (T.len + 1)) (b : Fin (U.len + 1)) (h : orderMap g.map a = b) :
    (NecklaceCode.Hom.id.{0} E).map ≫ (JTCorrectedIntervalAssembly.constantOver E
        (U.verticesEquiv.symm (ULift.up b))).map =
      (JTCorrectedIntervalAssembly.constantOver E
        (T.verticesEquiv.symm (ULift.up a))).map ≫ g.map := by
  have hp : pointAt T (ULift.up a) ≫ g.map = pointAt U (ULift.up b) := by
    rw [pointAt_comp]
    congr 1
    apply ULift.ext
    exact h
  change (𝟙 E.toSSet) ≫ (term E.toSSet ≫ pointAt U (ULift.up b)) =
    (term E.toSSet ≫ pointAt T (ULift.up a)) ≫ g.map
  rw [Category.id_comp, Category.assoc, hp]

private def coarseMap {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (a c : Fin (T.len + 1)) (a' c' : Fin (U.len + 1))
    (hac : a ≤ c) (hac' : a' ≤ c')
    (ha : orderMap g.map a = a') (hc : orderMap g.map c = c') :
    (JTCorrectedCoarseIntervalComparison.coarseOver T a c hac).code ⟶
      (JTCorrectedCoarseIntervalComparison.coarseOver U a' c' hac').code :=
  wedgeMap (wedgeMap (cutLeftHom g a a' ha) (𝟙 E))
    (wedgeMap (wedgeMap (𝟙 E)
      (wedgeMap (intervalCodeHom g.map a c hac a' c' hac' ha hc) (𝟙 E)))
      (wedgeMap (𝟙 E) (cutRightHom g c c' hc)))

private theorem coarse_natural {T U : NecklaceCode} (g : NecklaceCode.Hom.{0} T U)
    (a c : Fin (T.len + 1)) (a' c' : Fin (U.len + 1))
    (hac : a ≤ c) (hac' : a' ≤ c')
    (ha : orderMap g.map a = a') (hc : orderMap g.map c = c') :
    coarseMap g a c a' c' hac hac' ha hc ≫
        JTCorrectedCoarseIntervalComparison.assembly U a' c' hac' =
      JTCorrectedCoarseIntervalComparison.assembly T a c hac ≫ g := by
  let P := intervalOver T 0 a (Fin.zero_le a)
  let M := intervalOver T a c hac
  let R := intervalOver T c (Fin.last T.len) (Fin.le_last c)
  let e := JTCorrectedIntervalAssembly.constantOver E (T.verticesEquiv.symm (ULift.up a))
  let s := JTCorrectedIntervalAssembly.constantOver E (T.verticesEquiv.symm (ULift.up c))
  let P' := intervalOver U 0 a' (Fin.zero_le a')
  let M' := intervalOver U a' c' hac'
  let R' := intervalOver U c' (Fin.last U.len) (Fin.le_last c')
  let e' := JTCorrectedIntervalAssembly.constantOver E (U.verticesEquiv.symm (ULift.up a'))
  let s' := JTCorrectedIntervalAssembly.constantOver E (U.verticesEquiv.symm (ULift.up c'))
  let l := cutLeftHom g a a' ha
  let m := intervalCodeHom g.map a c hac a' c' hac' ha hc
  let r := cutRightHom g c c' hc
  have hl : l.map ≫ P'.map = P.map ≫ g.map := cutLeftHom_fac g a a' ha
  have hm : m.map ≫ M'.map = M.map ≫ g.map :=
    necklaceIntervalMap_fac g.map a c hac a' c' hac' ha.ge hc.le
  have hr : r.map ≫ R'.map = R.map ≫ g.map := cutRightHom_fac g c c' hc
  have he := constant_natural g a a' ha
  have hs := constant_natural g c c' hc
  apply NecklaceCode.Hom.ext
  exact wedge_natural (NecklacesOver.wedge P e)
    (NecklacesOver.wedge (NecklacesOver.wedge e (NecklacesOver.wedge M s))
      (NecklacesOver.wedge s R))
    (NecklacesOver.wedge P' e')
    (NecklacesOver.wedge (NecklacesOver.wedge e' (NecklacesOver.wedge M' s'))
      (NecklacesOver.wedge s' R'))
    (wedgeMap l (𝟙 E))
    (wedgeMap (wedgeMap (𝟙 E) (wedgeMap m (𝟙 E))) (wedgeMap (𝟙 E) r)) g.map
    (wedge_natural P e P' e' l (𝟙 E) g.map hl he)
    (wedge_natural (NecklacesOver.wedge e (NecklacesOver.wedge M s))
      (NecklacesOver.wedge s R) (NecklacesOver.wedge e' (NecklacesOver.wedge M' s'))
      (NecklacesOver.wedge s' R') (wedgeMap (𝟙 E) (wedgeMap m (𝟙 E)))
      (wedgeMap (𝟙 E) r) g.map
      (wedge_natural e (NecklacesOver.wedge M s) e' (NecklacesOver.wedge M' s')
        (𝟙 E) (wedgeMap m (𝟙 E)) g.map he
        (wedge_natural M s M' s' m (𝟙 E) g.map hm hs))
      (wedge_natural s R s' R' (𝟙 E) r g.map hs hr))

private theorem transport_natural {N N' C C' T T' : NecklaceCode}
    (e : N = C) (e' : N' = C') (f : N ⟶ N') (g : C ⟶ C')
    (l : C ⟶ T) (l' : C' ⟶ T') (n : T ⟶ T')
    (h : HEq f g) (hn : g ≫ l' = l ≫ n) :
    f ≫ (eqToHom e' ≫ l') = (eqToHom e ≫ l) ≫ n := by
  subst C
  subst C'
  have hf : f = g := eq_of_heq h
  simpa only [eqToHom_refl, Category.id_comp, hf] using hn

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

/-- The original common insertion chain, with no new choices. -/
abbrev Index := JTSharedInsertionChoices.Index F j

/-- The original source object and every original arrow are retained. -/
abbrev original := JTSharedInsertionChainSupport.originalBase F j

private abbrev N := JTParametrizedTargetFamilies.codes (JTSharedInsertionCoarseLabels.labels F j)
private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev T (p : Index F j) :=
  (JTParametrizedTargetFamilies.codes L).obj ((pairs F j).obj p).1
private abbrev a (p : Index F j) := ((pairs F j).obj p).2.left.val
private abbrev c (p : Index F j) := ((pairs F j).obj p).2.right.val
private abbrev hac (p : Index F j) := ((pairs F j).obj p).2.le
private abbrev oldMap {p q : Index F j} (f : p ⟶ q) :=
  (JTParametrizedTargetFamilies.codes L).map ((pairs F j).map f).val

private abbrev pairOld := JTJointPairChainDiagram.base F j ⋙
  JTJointPairChoiceCover.projection F j

private theorem pair_native_map {p q : JTJointPairChainDiagram.Index F j} (f : p ⟶ q) :
    HEq (wedgeMap ((JTJointPairWhiskeredSurroundings.leftNative F j).map f)
      (wedgeMap ((JTJointPairGapChainLabels.native F j).map f)
        ((JTJointPairWhiskeredSurroundings.rightNative F j).map f)))
      (coarseMap ((JTParametrizedTargetFamilies.codes L).map ((pairOld F j).map f).val)
        ((pairOld F j).obj p).2.left.val ((pairOld F j).obj p).2.right.val
        ((pairOld F j).obj q).2.left.val ((pairOld F j).obj q).2.right.val
        ((pairOld F j).obj p).2.le ((pairOld F j).obj q).2.le
        (JTJointPairSourceDiagram.left_map F j ((pairOld F j).map f))
        (JTJointPairSourceDiagram.right_map F j ((pairOld F j).map f))) := by
  rfl

private theorem native_code_eq (p : Index F j) : (N F j).obj p =
    (JTCorrectedCoarseIntervalComparison.coarseOver (T F j p) (a F j p) (c F j p)
      (hac F j p)).code :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

private theorem native_map_heq {p q : Index F j} (f : p ⟶ q) :
    HEq ((N F j).map f) (coarseMap (oldMap F j f) (a F j p) (c F j p)
      (a F j q) (c F j q) (hac F j p) (hac F j q)
      (JTJointPairSourceDiagram.left_map F j ((pairs F j).map f))
      (JTJointPairSourceDiagram.right_map F j ((pairs F j).map f))) := by
  have h := congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_map_projection F j f)
  exact (heq_of_eq h).trans
    (pair_native_map F j ((JTSharedInsertionCoarseLabels.base F j).map f))

/-- Assemble the WHOLE actual coarse label into the original source BEFORE Q. -/
def assembly : N F j ⟶ original F j ⋙ JTParametrizedTargetFamilies.codes L where
  app p := eqToHom (native_code_eq F j p) ≫
    JTCorrectedCoarseIntervalComparison.assembly (T F j p) (a F j p) (c F j p) (hac F j p)
  naturality {p q} f := by
    exact transport_natural (native_code_eq F j p) (native_code_eq F j q)
      ((N F j).map f) _ _ _ (oldMap F j f) (native_map_heq F j f)
      (coarse_natural (oldMap F j f) (a F j p) (c F j p) (a F j q) (c F j q)
        (hac F j p) (hac F j q)
        (JTJointPairSourceDiagram.left_map F j ((pairs F j).map f))
        (JTJointPairSourceDiagram.right_map F j ((pairs F j).map f)))

/-- Its exact component uses only the canonical native-code identification. -/
theorem assembly_app (p : Index F j) : (assembly F j).app p =
    eqToHom (native_code_eq F j p) ≫
      JTCorrectedCoarseIntervalComparison.assembly (T F j p) (a F j p) (c F j p)
        (hac F j p) := rfl

/-- Postcompose ONLY with the original collapse into the SAME fixed Q and global endpoints. -/
def target : N F j ⟶ (Functor.const (Index F j)).obj Q.code :=
  assembly F j ≫ Functor.whiskerLeft (original F j) F.collapse

/-- The whole coarse target has its exact native factorization before Q. -/
theorem target_factor : target F j =
    assembly F j ≫ Functor.whiskerLeft (original F j) F.collapse := rfl

end
end DaggerModels.PartII.JTSharedInsertionCoarseNative
