import DaggerModelsPartII.JTSharedInsertionCoarseNative
import DaggerModelsPartII.JTSharedInsertionOldGraph
import DaggerModelsPartII.JTJointSubdivisionInsertion

/-!
# The actual corrected split compares natively to the complete coarse label

Retain both outer correction pairs and all original native operators. The
comparison removes the inserted point, reassociates the existing wedges and
concatenates the two actual intervals. Its complete triangle is in the ORIGINAL
source necklace before postcomposition with Q. No decorated coefficient, raw
or evaluation comparison, parameter section or higher descent is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget

namespace DaggerModels.PartII.JTSharedInsertionCoarseComparisonNative

noncomputable section

private abbrev E := single 1
private abbrev Z := single 0

private def wedgeDiagram {I : Type} [SmallCategory I]
    (P R : I ⥤ NecklaceCode) : I ⥤ NecklaceCode where
  obj p := wedge (P.obj p) (R.obj p)
  map f := wedgeMap (P.map f) (R.map f)
  map_id p := by rw [P.map_id, R.map_id]; exact wedgeMap_id
  map_comp f g := by rw [P.map_comp, R.map_comp]; exact wedgeMap_comp _ _ _ _

private def wedgeNat {I : Type} [SmallCategory I] {P P' R R' : I ⥤ NecklaceCode}
    (f : P ⟶ P') (g : R ⟶ R') : wedgeDiagram P R ⟶ wedgeDiagram P' R' where
  app p := wedgeMap (f.app p) (g.app p)
  naturality {p q} a := by
    change Hom.comp (wedgeMap (P.map a) (R.map a)) (wedgeMap (f.app q) (g.app q)) =
      Hom.comp (wedgeMap (f.app p) (g.app p)) (wedgeMap (P'.map a) (R'.map a))
    rw [← wedgeMap_comp, ← wedgeMap_comp]
    exact congrArg₂ wedgeMap (f.naturality a) (g.naturality a)

private theorem leftMap_T {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleLeftT P Q R ≫ (wedgeMap (wedgeMap f g) h).map =
      f.map ≫ tripleLeftT P' Q' R' := by
  unfold tripleLeftT
  rw [Category.assoc, wedgeMap_left, ← Category.assoc, wedgeMap_left, Category.assoc]

private theorem leftMap_U {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleLeftU P Q R ≫ (wedgeMap (wedgeMap f g) h).map =
      g.map ≫ tripleLeftU P' Q' R' := by
  unfold tripleLeftU
  rw [Category.assoc, wedgeMap_left, ← Category.assoc, wedgeMap_right, Category.assoc]

private theorem leftMap_V {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleLeftV P Q R ≫ (wedgeMap (wedgeMap f g) h).map =
      h.map ≫ tripleLeftV P' Q' R' := wedgeMap_right _ _

private theorem rightMap_T {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleRightT P Q R ≫ (wedgeMap f (wedgeMap g h)).map =
      f.map ≫ tripleRightT P' Q' R' := wedgeMap_left _ _

private theorem rightMap_U {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleRightU P Q R ≫ (wedgeMap f (wedgeMap g h)).map =
      g.map ≫ tripleRightU P' Q' R' := by
  unfold tripleRightU
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_left, Category.assoc]

private theorem rightMap_V {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    tripleRightV P Q R ≫ (wedgeMap f (wedgeMap g h)).map =
      h.map ≫ tripleRightV P' Q' R' := by
  unfold tripleRightV
  rw [Category.assoc, wedgeMap_right, ← Category.assoc, wedgeMap_right, Category.assoc]

private theorem assoc_natural {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    Hom.comp (wedgeMap (wedgeMap f g) h) (wedgeAssocCodeHom.{0} P' Q' R') =
      Hom.comp (wedgeAssocCodeHom.{0} P Q R) (wedgeMap f (wedgeMap g h)) := by
  apply NecklaceCode.Hom.ext
  change (wedgeMap (wedgeMap f g) h).map ≫ wedgeAssocHom P' Q' R' =
    wedgeAssocHom P Q R ≫ (wedgeMap f (wedgeMap g h)).map
  apply tripleLeft_hom_ext
  · calc
      _ = f.map ≫ tripleRightT P' Q' R' := by
        rw [← Category.assoc, leftMap_T, Category.assoc, wedgeAssocHom_T]
      _ = _ := by rw [← Category.assoc, wedgeAssocHom_T, rightMap_T]
  · calc
      _ = g.map ≫ tripleRightU P' Q' R' := by
        rw [← Category.assoc, leftMap_U, Category.assoc, wedgeAssocHom_U]
      _ = _ := by rw [← Category.assoc, wedgeAssocHom_U, rightMap_U]
  · calc
      _ = h.map ≫ tripleRightV P' Q' R' := by
        rw [← Category.assoc, leftMap_V, Category.assoc, wedgeAssocHom_V]
      _ = _ := by rw [← Category.assoc, wedgeAssocHom_V, rightMap_V]

private def invCode {T U : NecklaceCode} (e : (T.toSSet : SSet.{0}) ≅ U.toSSet)
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

private def assocInv (P Q R : NecklaceCode) : wedge P (wedge Q R) ⟶ wedge (wedge P Q) R :=
  invCode (wedgeAssoc P Q R) (wedgeAssoc_first P Q R) (wedgeAssoc_last P Q R)

private theorem assocInv_natural {P Q R P' Q' R' : NecklaceCode}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    wedgeMap f (wedgeMap g h) ≫ assocInv P' Q' R' =
      assocInv P Q R ≫ wedgeMap (wedgeMap f g) h := by
  apply NecklaceCode.Hom.ext
  change (wedgeMap f (wedgeMap g h)).map ≫ (wedgeAssoc P' Q' R').inv =
    (wedgeAssoc P Q R).inv ≫ (wedgeMap (wedgeMap f g) h).map
  apply (cancel_mono (wedgeAssoc P' Q' R').hom).mp
  have hn := congrArg (fun k ↦ k.map) (assoc_natural f g h)
  change (wedgeMap (wedgeMap f g) h).map ≫ (wedgeAssoc P' Q' R').hom =
    (wedgeAssoc P Q R).hom ≫ (wedgeMap f (wedgeMap g h)).map at hn
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hn,
    Iso.inv_hom_id_assoc]

private def assocNat {I : Type} [SmallCategory I] (P Q R : I ⥤ NecklaceCode) :
    wedgeDiagram (wedgeDiagram P Q) R ⟶ wedgeDiagram P (wedgeDiagram Q R) where
  app p := wedgeAssocCodeHom (P.obj p) (Q.obj p) (R.obj p)
  naturality _ _ f := assoc_natural (P.map f) (Q.map f) (R.map f)

private def assocInvNat {I : Type} [SmallCategory I] (P Q R : I ⥤ NecklaceCode) :
    wedgeDiagram P (wedgeDiagram Q R) ⟶ wedgeDiagram (wedgeDiagram P Q) R where
  app p := assocInv (P.obj p) (Q.obj p) (R.obj p)
  naturality _ _ f := assocInv_natural (P.map f) (Q.map f) (R.map f)

private def zeroNat {I : Type} [SmallCategory I] (R : I ⥤ NecklaceCode) :
    wedgeDiagram ((Functor.const I).obj Z) R ⟶ R where
  app p := JTNativeCutPointAssembly.zeroUnit Z (R.obj p) rfl
  naturality _ _ f := JTNativeCutPointAssembly.zeroUnit_natural Z rfl (R.map f)

private abbrev edgeDiagram (I : Type) [SmallCategory I] : I ⥤ NecklaceCode :=
  (Functor.const I).obj E

private abbrev paddedSource {I : Type} [SmallCategory I] (A B C D : I ⥤ NecklaceCode) :=
  wedgeDiagram (wedgeDiagram A (wedgeDiagram (edgeDiagram I) B))
    (wedgeDiagram ((Functor.const I).obj Z)
      (wedgeDiagram C (wedgeDiagram (edgeDiagram I) D)))

private abbrev paddedTarget {I : Type} [SmallCategory I] (A K D : I ⥤ NecklaceCode) :=
  wedgeDiagram A (wedgeDiagram
    (wedgeDiagram (edgeDiagram I) (wedgeDiagram K (edgeDiagram I))) D)

private def paddedNatural {I : Type} [SmallCategory I] (A B C D K : I ⥤ NecklaceCode)
    (μ : wedgeDiagram B C ⟶ K) : paddedSource A B C D ⟶ paddedTarget A K D :=
  wedgeNat (𝟙 (wedgeDiagram A (wedgeDiagram (edgeDiagram I) B)))
    (zeroNat (wedgeDiagram C (wedgeDiagram (edgeDiagram I) D))) ≫
    assocNat A (wedgeDiagram (edgeDiagram I) B)
      (wedgeDiagram C (wedgeDiagram (edgeDiagram I) D)) ≫
    wedgeNat (𝟙 A) (assocNat (edgeDiagram I) B
      (wedgeDiagram C (wedgeDiagram (edgeDiagram I) D))) ≫
    wedgeNat (𝟙 A) (wedgeNat (𝟙 (edgeDiagram I))
      (assocInvNat B C (wedgeDiagram (edgeDiagram I) D))) ≫
    wedgeNat (𝟙 A) (wedgeNat (𝟙 (edgeDiagram I))
      (wedgeNat μ (𝟙 (wedgeDiagram (edgeDiagram I) D)))) ≫
    wedgeNat (𝟙 A) (wedgeNat (𝟙 (edgeDiagram I)) (assocInvNat K (edgeDiagram I) D)) ≫
    wedgeNat (𝟙 A) (assocInvNat (edgeDiagram I) (wedgeDiagram K (edgeDiagram I)) D)


private def paddedArrow (A B C D K : NecklaceCode) (μ : wedge B C ⟶ K) :
    wedge (wedge A (wedge E B)) (wedge Z (wedge C (wedge E D))) ⟶
      wedge A (wedge (wedge E (wedge K E)) D) :=
  Hom.comp (Hom.comp (Hom.comp (Hom.comp (Hom.comp (Hom.comp
    (wedgeMap (𝟙 (wedge A (wedge E B)))
      (JTNativeCutPointAssembly.zeroUnit Z (wedge C (wedge E D)) rfl))
    (wedgeAssocCodeHom A (wedge E B) (wedge C (wedge E D))))
    (wedgeMap (𝟙 A) (wedgeAssocCodeHom E B (wedge C (wedge E D)))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv B C (wedge E D)))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (wedgeMap μ (𝟙 (wedge E D))))))
    (wedgeMap (𝟙 A) (wedgeMap (𝟙 E) (assocInv K E D))))
    (wedgeMap (𝟙 A) (assocInv E (wedge K E) D))

private theorem paddedNatural_app {I : Type} [SmallCategory I]
    (A B C D K : I ⥤ NecklaceCode) (μ : wedgeDiagram B C ⟶ K) (p : I) :
    (paddedNatural A B C D K μ).app p =
      paddedArrow (A.obj p) (B.obj p) (C.obj p) (D.obj p) (K.obj p) (μ.app p) := rfl

private theorem paddedArrow_corrected (T : NecklaceCode) (a b c : Fin (T.len + 1))
    (hab : a ≤ b) (hbc : b ≤ c) :
    paddedArrow (wedge (cutLeft T a) E) (intervalCode T a b hab)
        (intervalCode T b c hbc) (wedge E (cutRight T c))
        (intervalCode T a c (hab.trans hbc))
        (JTJointCutSubdivision.concat T a b c hab hbc).hom =
      (JTCorrectedCoarseIntervalComparison.comparisonOver T a b c hab hbc).hom := rfl

private theorem paddedArrow_heq {A B C D K A' B' C' D' K' : NecklaceCode}
    (ha : A = A') (hb : B = B') (hc : C = C') (hd : D = D') (hk : K = K')
    (μ : wedge B C ⟶ K) (μ' : wedge B' C' ⟶ K') (hμ : HEq μ μ') :
    HEq (paddedArrow A B C D K μ) (paddedArrow A' B' C' D' K' μ') := by
  subst A'
  subst B'
  subst C'
  subst D'
  subst K'
  cases eq_of_heq hμ
  rfl

private theorem corrected_assembly_unique (T : NecklaceCode) (a b c : Fin (T.len + 1))
    (hab : a ≤ b) (hbc : b ≤ c)
    (s : (JTCorrectedIntervalAssembly.wholeOver T a b c hab hbc Z).code ⟶ T)
    (hl : tripleRightT (JTCorrectedIntervalAssembly.leftOver T a b hab).code Z
        (JTCorrectedIntervalAssembly.rightOver T b c hbc).code ≫ s.map =
      (JTCorrectedIntervalAssembly.leftOver T a b hab).map)
    (hm : tripleRightU (JTCorrectedIntervalAssembly.leftOver T a b hab).code Z
        (JTCorrectedIntervalAssembly.rightOver T b c hbc).code ≫ s.map =
      SSet.stdSimplex.isTerminalObj₀.from Z.toSSet ≫ pointAt T (ULift.up b))
    (hr : tripleRightV (JTCorrectedIntervalAssembly.leftOver T a b hab).code Z
        (JTCorrectedIntervalAssembly.rightOver T b c hbc).code ≫ s.map =
      (JTCorrectedIntervalAssembly.rightOver T b c hbc).map) :
    s = JTCorrectedIntervalAssembly.assembly T a b c hab hbc Z := by
  apply NecklaceCode.Hom.ext
  apply tripleRight_hom_ext
  · exact hl.trans (JTCorrectedIntervalAssembly.assembly_left T a b c hab hbc Z).symm
  · exact hm.trans (JTCorrectedIntervalAssembly.assembly_middle T a b c hab hbc Z).symm
  · exact hr.trans (JTCorrectedIntervalAssembly.assembly_right T a b c hab hbc Z).symm

private theorem transport_hom_heq {S T N M : NecklaceCode}
    (es : S = N) (et : T = M) (k : N ⟶ M) :
    HEq (Hom.comp (Hom.comp (eqToHom es) k) (eqToHom et.symm)) k := by
  subst N
  subst M
  apply heq_of_eq
  apply NecklaceCode.Hom.ext
  change ((𝟙 _ ≫ k.map) ≫ 𝟙 _) = k.map
  simp only [Category.id_comp, Category.comp_id]

private theorem transport_left_heq {S N T : NecklaceCode} (e : S = N) (k : N ⟶ T) :
    HEq (Hom.comp (eqToHom e) k) k := by
  subst N
  apply heq_of_eq
  apply NecklaceCode.Hom.ext
  change (𝟙 _ ≫ k.map) = k.map
  exact Category.id_comp k.map

private theorem triangle_transport {S T N M U : NecklaceCode} (es : S = N) (et : T = M)
    (k : S ⟶ T) (n : T ⟶ U) (o : S ⟶ U)
    (k' : N ⟶ M) (n' : M ⟶ U) (o' : N ⟶ U)
    (hk : HEq k k') (hn : HEq n n') (ho : HEq o o')
    (h : Hom.comp k' n' = o') : Hom.comp k n = o := by
  subst N
  subst M
  have hk' : k = k' := eq_of_heq hk
  have hn' : n = n' := eq_of_heq hn
  have ho' : o = o' := eq_of_heq ho
  simpa only [hk', hn', ho'] using h

private theorem concat_natural {T U : NecklaceCode} (g : T ⟶ U)
    (a b c : Fin (T.len + 1)) (a' b' c' : Fin (U.len + 1))
    (hab : a ≤ b) (hbc : b ≤ c) (hab' : a' ≤ b') (hbc' : b' ≤ c')
    (ha : orderMap g.map a = a') (hb : orderMap g.map b = b')
    (hc : orderMap g.map c = c') :
    Hom.comp (wedgeMap (intervalCodeHom g.map a b hab a' b' hab' ha hb)
      (intervalCodeHom g.map b c hbc b' c' hbc' hb hc))
      (JTJointCutSubdivision.concat U a' b' c' hab' hbc').hom =
      Hom.comp (JTJointCutSubdivision.concat T a b c hab hbc).hom
        (intervalCodeHom g.map a c (hab.trans hbc) a' c' (hab'.trans hbc') ha hc) := by
  apply NecklaceCode.Hom.ext
  apply (cancel_mono (intervalι U a' c' (hab'.trans hbc'))).mp
  change ((wedgeMap (intervalCodeHom g.map a b hab a' b' hab' ha hb)
      (intervalCodeHom g.map b c hbc b' c' hbc' hb hc)).map ≫
      (JTJointCutSubdivision.concat U a' b' c' hab' hbc').hom.map) ≫ _ =
    ((JTJointCutSubdivision.concat T a b c hab hbc).hom.map ≫
      (intervalCodeHom g.map a c _ a' c' _ ha hc).map) ≫ _
  have hm : (intervalCodeHom g.map a c (hab.trans hbc) a' c' (hab'.trans hbc')
      ha hc).map ≫ intervalι U a' c' (hab'.trans hbc') =
      intervalι T a c (hab.trans hbc) ≫ g.map :=
    necklaceIntervalMap_fac g.map a c _ a' c' _ ha.ge hc.le
  rw [Category.assoc, Category.assoc, hm]
  apply (wedgeIsPushout (intervalCode T a b hab) (intervalCode T b c hbc)).hom_ext
  · have hl : (intervalCodeHom g.map a b hab a' b' hab' ha hb).map ≫
        intervalι U a' b' hab' = intervalι T a b hab ≫ g.map :=
      necklaceIntervalMap_fac g.map a b hab a' b' hab' ha.ge hb.le
    have hq := JTJointCutSubdivision.concat_first U a' b' c' hab' hbc'
    have hp := JTJointCutSubdivision.concat_first T a b c hab hbc
    have hpa := congrArg (fun u ↦ u ≫ g.map) hp
    simp only [Category.assoc] at hpa
    rw [← Category.assoc (wedgeιLeft _ _)
      (wedgeMap (intervalCodeHom g.map a b hab a' b' hab' ha hb)
        (intervalCodeHom g.map b c hbc b' c' hbc' hb hc)).map,
      wedgeMap_left, Category.assoc, hq, hl, hpa]
  · have hr : (intervalCodeHom g.map b c hbc b' c' hbc' hb hc).map ≫
        intervalι U b' c' hbc' = intervalι T b c hbc ≫ g.map :=
      necklaceIntervalMap_fac g.map b c hbc b' c' hbc' hb.ge hc.le
    have hq := JTJointCutSubdivision.concat_last U a' b' c' hab' hbc'
    have hp := JTJointCutSubdivision.concat_last T a b c hab hbc
    have hpa := congrArg (fun u ↦ u ≫ g.map) hp
    simp only [Category.assoc] at hpa
    rw [← Category.assoc (wedgeιRight _ _)
      (wedgeMap (intervalCodeHom g.map a b hab a' b' hab' ha hb)
        (intervalCodeHom g.map b c hbc b' c' hbc' hb hc)).map,
      wedgeMap_right, Category.assoc, hq, hr, hpa]

private theorem transport_component {S S' T T' N N' M M' : NecklaceCode}
    (es : S = N) (es' : S' = N') (et : T = M) (et' : T' = M')
    (f : S ⟶ S') (g : T ⟶ T') (nf : N ⟶ N') (mf : M ⟶ M')
    (k : N ⟶ M) (k' : N' ⟶ M') (hf : HEq f nf) (hg : HEq g mf)
    (hk : Hom.comp nf k' = Hom.comp k mf) :
    Hom.comp f (Hom.comp (Hom.comp (eqToHom es') k') (eqToHom et'.symm)) =
      Hom.comp (Hom.comp (Hom.comp (eqToHom es) k) (eqToHom et.symm)) g := by
  subst N
  subst N'
  subst M
  subst M'
  have hf' : f = nf := eq_of_heq hf
  have hg' : g = mf := eq_of_heq hg
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, hf', hg'] using hk

private def transportNat {I : Type} [SmallCategory I]
    (S T N M : I ⥤ NecklaceCode) (es : ∀ p, S.obj p = N.obj p)
    (et : ∀ p, T.obj p = M.obj p)
    (hs : ∀ {p q} (f : p ⟶ q), HEq (S.map f) (N.map f))
    (ht : ∀ {p q} (f : p ⟶ q), HEq (T.map f) (M.map f)) (k : N ⟶ M) : S ⟶ T where
  app p := eqToHom (es p) ≫ k.app p ≫ eqToHom (et p).symm
  naturality {p q} f :=
    transport_component (es p) (es q) (et p) (et q) (S.map f) (T.map f)
      (N.map f) (M.map f) (k.app p) (k.app q) (hs f) (ht f) (k.naturality f)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

open JTParametrizedTargetFamilies (Family codes)

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : JTTargetJointMarks.Joint Q.code)

/-- The unchanged actual shared insertion chain, retaining every original operator. -/
abbrev Index := JTSharedInsertionChoices.Index F j

private abbrev original := JTSharedInsertionChainSupport.originalBase F j
private abbrev marks := JTSharedInsertionChainSupport.marks F j
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
private abbrev outerLeft := JTSharedInsertionCoarseLabels.leftNative F j
private abbrev outerRight := JTSharedInsertionCoarseLabels.rightNative F j
private abbrev lower := JTSharedInsertionSeamSurroundings.lowerNative F j
private abbrev upper := JTSharedInsertionSeamSurroundings.upperNative F j
private abbrev pairs := JTSharedInsertionCoarseChoice.toPairChain F j ⋙
  JTJointPairChainDiagram.base F j ⋙ JTJointPairChoiceCover.projection F j
private abbrev middle := pairs F j ⋙ JTJointPairGapDiagram.native F j

private def concatenate : wedgeDiagram (lower F j) (upper F j) ⟶ middle F j where
  app p := (JTJointCutSubdivision.concat (T F j p) (a F j p) (b F j p) (c F j p)
    (hab F j p) (hbc F j p)).hom
  naturality {p q} f := concat_natural ((codes L).map ((original F j).map f))
    (a F j p) (b F j p) (c F j p) (a F j q) (b F j q) (c F j q)
    (hab F j p) (hbc F j p) (hab F j q) (hbc F j q)
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 0).map f))
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 1).map f))
    (JTExactlyMarkedSourceDiagram.cut_map F j ((marks F j 2).map f))

private abbrev splitSkeleton := paddedSource (outerLeft F j) (lower F j)
  (upper F j) (outerRight F j)
private abbrev coarseSkeleton := paddedTarget (outerLeft F j) (middle F j) (outerRight F j)
private abbrev oldCodes := codes (JTSharedInsertionNormalizedSeam.oldFamily F j).labels
private abbrev coarseCodes := codes (JTSharedInsertionCoarseLabels.labels F j)

private theorem split_code_eq (p : Index F j) :
    (oldCodes F j).obj p = (splitSkeleton F j).obj p := by
  rfl

private theorem split_map_heq {p q : Index F j} (f : p ⟶ q) :
    HEq ((oldCodes F j).map f) ((splitSkeleton F j).map f) := by
  have h := congrArg Prod.fst (JTWhiskeredSeamDiagram.Family.arrow_projection
    (JTSharedInsertionNormalizedSeam.oldFamily F j) f)
  exact (heq_of_eq h).trans (by rfl)

private theorem coarse_code_eq (p : Index F j) :
    (coarseCodes F j).obj p = (coarseSkeleton F j).obj p :=
  congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_projection F j p)

private theorem coarse_map_heq {p q : Index F j} (f : p ⟶ q) :
    HEq ((coarseCodes F j).map f) ((coarseSkeleton F j).map f) := by
  have h := congrArg Prod.fst (JTSharedInsertionCoarseLabels.labels_map_projection F j f)
  exact heq_of_eq h

/-- The complete corrected split compares natively to the actual coarse corrected label.
The two outer correction pairs and all zero intervals remain literal. -/
def comparison : oldCodes F j ⟶ coarseCodes F j :=
  transportNat (oldCodes F j) (coarseCodes F j) (splitSkeleton F j) (coarseSkeleton F j)
    (split_code_eq F j) (coarse_code_eq F j) (split_map_heq F j) (coarse_map_heq F j)
    (paddedNatural (outerLeft F j) (lower F j) (upper F j) (outerRight F j)
      (middle F j) (concatenate F j))


private theorem split_corrected_eq (p : Index F j) :
    (oldCodes F j).obj p =
      (JTCorrectedIntervalAssembly.wholeOver (T F j p) (a F j p) (b F j p) (c F j p)
        (hab F j p) (hbc F j p) Z).code := split_code_eq F j p

private theorem coarse_corrected_eq (p : Index F j) :
    (coarseCodes F j).obj p =
      (JTCorrectedCoarseIntervalComparison.coarseOver (T F j p) (a F j p) (c F j p)
        ((hab F j p).trans (hbc F j p))).code := coarse_code_eq F j p

private theorem outerLeft_code (p : Index F j) :
    (outerLeft F j).obj p = wedge (cutLeft (T F j p) (a F j p)) E := rfl

private theorem lower_code (p : Index F j) :
    (lower F j).obj p = intervalCode (T F j p) (a F j p) (b F j p) (hab F j p) := rfl

private theorem upper_code (p : Index F j) :
    (upper F j).obj p = intervalCode (T F j p) (b F j p) (c F j p) (hbc F j p) := rfl

private theorem outerRight_code (p : Index F j) :
    (outerRight F j).obj p = wedge E (cutRight (T F j p) (c F j p)) := rfl

private theorem middle_code (p : Index F j) :
    (middle F j).obj p = intervalCode (T F j p) (a F j p) (c F j p)
      ((hab F j p).trans (hbc F j p)) := rfl

private theorem padded_component_heq (p : Index F j) :
    HEq (paddedArrow ((outerLeft F j).obj p) ((lower F j).obj p) ((upper F j).obj p)
        ((outerRight F j).obj p) ((middle F j).obj p) ((concatenate F j).app p))
      (JTCorrectedCoarseIntervalComparison.comparisonOver (T F j p) (a F j p)
        (b F j p) (c F j p) (hab F j p) (hbc F j p)).hom := by
  have hp := paddedArrow_heq (outerLeft_code F j p) (lower_code F j p) (upper_code F j p)
    (outerRight_code F j p) (middle_code F j p) ((concatenate F j).app p)
    (JTJointCutSubdivision.concat (T F j p) (a F j p) (b F j p) (c F j p)
      (hab F j p) (hbc F j p)).hom (by rfl)
  exact hp.trans (heq_of_eq (paddedArrow_corrected (T F j p) (a F j p) (b F j p)
    (c F j p) (hab F j p) (hbc F j p)))

/-- Pointwise this is precisely the existing corrected concatenation over the original T.
HEq records only its canonical native-code representation, without changing any piece. -/
theorem comparison_app (p : Index F j) :
    HEq ((comparison F j).app p)
      (JTCorrectedCoarseIntervalComparison.comparisonOver (T F j p) (a F j p)
        (b F j p) (c F j p) (hab F j p) (hbc F j p)).hom := by
  have h := transport_hom_heq (split_code_eq F j p) (coarse_code_eq F j p)
    ((paddedNatural (outerLeft F j) (lower F j) (upper F j) (outerRight F j)
      (middle F j) (concatenate F j)).app p)
  change HEq ((comparison F j).app p) _ at h
  rw [paddedNatural_app] at h
  exact h.trans (padded_component_heq F j p)

private theorem coarseAssembly_app_heq (p : Index F j) :
    HEq ((JTSharedInsertionCoarseNative.assembly F j).app p)
      (JTCorrectedCoarseIntervalComparison.assembly (T F j p) (a F j p) (c F j p)
        ((hab F j p).trans (hbc F j p))) := by
  rw [JTSharedInsertionCoarseNative.assembly_app]
  exact transport_left_heq _ _

private def oldAssemblyView (p : Index F j) :
    (JTCorrectedIntervalAssembly.wholeOver (T F j p) (a F j p) (b F j p) (c F j p)
      (hab F j p) (hbc F j p) Z).code ⟶ T F j p :=
  (JTSharedInsertionSeamNative.oldAssembly F j).app p

private abbrev leftCode (p : Index F j) :=
  (JTCorrectedIntervalAssembly.leftOver (T F j p) (a F j p) (b F j p) (hab F j p)).code
private abbrev rightCode (p : Index F j) :=
  (JTCorrectedIntervalAssembly.rightOver (T F j p) (b F j p) (c F j p) (hbc F j p)).code

private theorem oldAssemblyView_left (p : Index F j) :
    tripleRightT (leftCode F j p) Z (rightCode F j p) ≫ (oldAssemblyView F j p).map =
      (JTCorrectedIntervalAssembly.leftOver (T F j p) (a F j p) (b F j p)
        (hab F j p)).map := JTSharedInsertionOldGraph.oldAssembly_left F j p

private theorem oldAssemblyView_middle (p : Index F j) :
    tripleRightU (leftCode F j p) Z (rightCode F j p) ≫ (oldAssemblyView F j p).map =
      SSet.stdSimplex.isTerminalObj₀.from Z.toSSet ≫ pointAt (T F j p) (ULift.up (b F j p)) :=
  JTSharedInsertionOldGraph.oldAssembly_middle F j p

private theorem oldAssemblyView_right (p : Index F j) :
    tripleRightV (leftCode F j p) Z (rightCode F j p) ≫ (oldAssemblyView F j p).map =
      (JTCorrectedIntervalAssembly.rightOver (T F j p) (b F j p) (c F j p)
        (hbc F j p)).map := JTSharedInsertionOldGraph.oldAssembly_right F j p

private theorem oldAssembly_app_heq (p : Index F j) :
    HEq ((JTSharedInsertionSeamNative.oldAssembly F j).app p)
      (JTCorrectedIntervalAssembly.assembly (T F j p) (a F j p) (b F j p) (c F j p)
        (hab F j p) (hbc F j p) Z) := by
  have h := corrected_assembly_unique (T F j p) (a F j p) (b F j p) (c F j p)
    (hab F j p) (hbc F j p) (oldAssemblyView F j p) (oldAssemblyView_left F j p)
    (oldAssemblyView_middle F j p) (oldAssemblyView_right F j p)
  exact (show HEq ((JTSharedInsertionSeamNative.oldAssembly F j).app p)
    (oldAssemblyView F j p) from HEq.rfl).trans (heq_of_eq h)

/-- The complete actual comparison commutes in the ORIGINAL source, before Q. -/
theorem comparison_assembly : comparison F j ≫ JTSharedInsertionCoarseNative.assembly F j =
    JTSharedInsertionSeamNative.oldAssembly F j := by
  ext p
  exact triangle_transport (split_corrected_eq F j p) (coarse_corrected_eq F j p)
    ((comparison F j).app p) ((JTSharedInsertionCoarseNative.assembly F j).app p)
    ((JTSharedInsertionSeamNative.oldAssembly F j).app p) _ _ _
    (comparison_app F j p) (coarseAssembly_app_heq F j p) (oldAssembly_app_heq F j p)
    (JTCorrectedCoarseIntervalComparison.comparison_assembly
      (T F j p) (a F j p) (b F j p) (c F j p) (hab F j p) (hbc F j p))

end
end DaggerModels.PartII.JTSharedInsertionCoarseComparisonNative
