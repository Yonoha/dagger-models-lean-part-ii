import DaggerModelsPartII.JTThreePieceCoefficientReassociation
import DaggerModelsPartII.JTThreePieceLabelOperators
import ChosenNecklaceWedgeFunctor

/-!
# Regroup five COMPLETE coefficients without changing their rows

The native reassociation retains each of the five pieces. Four intrinsic seam
laws glue arbitrary coefficient-simplex families; neither inner endpoint row is
required to be constant. No raw value, point target or epimorphism is assumed.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCoarseCoefficientRegrouping

open TripleBeadEndpointLabel (labels firstRestriction lastRestriction glue glue_first glue_last
  glue_left glue_right)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev free := ReversalDiscreteFreeColimits.discreteFree.{0}
private abbrev pre (W : Source) {X Y : SSet.{0}} (g : X ⟶ Y) :=
  diagramMappingPrecomp (free.map g) W

private theorem pre_comp (W : Source) {X Y Z : SSet.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    pre W (g ≫ h) = pre W h ≫ pre W g := by
  rw [pre, free.map_comp, diagramMappingPrecomp_comp]

private theorem pre_id (W : Source) (X : SSet.{0}) : pre W (𝟙 X) = 𝟙 _ := by
  rw [pre, free.map_id, diagramMappingPrecomp_id]

private def invCode {T U : NecklaceCode} (i : T.toSSet ≅ U.toSSet)
    (hf : i.hom.app (op ⦋0⦌) T.first = U.first)
    (hl : i.hom.app (op ⦋0⦌) T.last = U.last) : U ⟶ T where
  map := i.inv
  first := by
    have h := congrArg (fun g : T.toSSet ⟶ T.toSSet ↦ g.app (op ⦋0⦌) T.first) i.hom_inv_id
    change i.inv.app (op ⦋0⦌) (i.hom.app (op ⦋0⦌) T.first) = T.first at h
    simpa only [hf] using h
  last := by
    have h := congrArg (fun g : T.toSSet ⟶ T.toSSet ↦ g.app (op ⦋0⦌) T.last) i.hom_inv_id
    change i.inv.app (op ⦋0⦌) (i.hom.app (op ⦋0⦌) T.last) = T.last at h
    simpa only [hl] using h

private def assocIso (P M R : NecklaceCode) :
    wedge (wedge P M) R ≅ wedge P (wedge M R) where
  hom := wedgeAssocCodeHom.{0} P M R
  inv := invCode (wedgeAssoc.{0} P M R) (wedgeAssoc_first P M R) (wedgeAssoc_last P M R)
  hom_inv_id := NecklaceCode.Hom.ext (wedgeAssoc P M R).hom_inv_id
  inv_hom_id := NecklaceCode.Hom.ext (wedgeAssoc P M R).inv_hom_id

private def wedgeIso {P P' R R' : NecklaceCode} (g : P ≅ P') (h : R ≅ R') :
    wedge P R ≅ wedge P' R' where
  hom := wedgeMap.{0} g.hom h.hom
  inv := wedgeMap g.inv h.inv
  hom_inv_id := by
    change NecklaceCode.Hom.comp (wedgeMap g.hom h.hom) (wedgeMap g.inv h.inv) = _
    rw [← wedgeMap_comp]
    change wedgeMap (g.hom ≫ g.inv) (h.hom ≫ h.inv) = _
    rw [g.hom_inv_id, h.hom_inv_id]
    exact wedgeMap_id
  inv_hom_id := by
    change NecklaceCode.Hom.comp (wedgeMap g.inv h.inv) (wedgeMap g.hom h.hom) = _
    rw [← wedgeMap_comp]
    change wedgeMap (g.inv ≫ g.hom) (h.inv ≫ h.hom) = _
    rw [g.inv_hom_id, h.inv_hom_id]
    exact wedgeMap_id

variable (A e B f D : NecklaceCode)

/-- The given complete coarse parenthesization. -/
abbrev sourceCode := wedge A (wedge (wedge e (wedge B f)) D)

/-- Group the original left surrounding and its remaining right correction. -/
abbrev groupedCode := wedge (wedge A (wedge e B)) (wedge f D)

private abbrev step1 := wedgeIso (Iso.refl A) (assocIso e (wedge B f) D)
private abbrev step2 := wedgeIso (Iso.refl A) (wedgeIso (Iso.refl e) (assocIso B f D))
private abbrev step3 := wedgeIso (Iso.refl A) (assocIso e B (wedge f D)).symm
private abbrev step4 := (assocIso A (wedge e B) (wedge f D)).symm

/-- The four actual native associators, retaining all five original pieces. -/
def deltaCodeIso : sourceCode A e B f D ≅ groupedCode A e B f D :=
  step1 A e B f D ≪≫ step2 A e B f D ≪≫ step3 A e B f D ≪≫ step4 A e B f D

/-- The complete native SSet reassociation is an actual isomorphism. -/
def delta : (sourceCode A e B f D).toSSet ≅ (groupedCode A e B f D).toSSet :=
  NecklaceCode.simplicialFunctor.mapIso (deltaCodeIso A e B f D)

private theorem delta_hom : (delta A e B f D).hom =
    (step1 A e B f D).hom.map ≫ (step2 A e B f D).hom.map ≫
      (step3 A e B f D).hom.map ≫ (step4 A e B f D).hom.map := rfl

/-- Inclusion of the first complete piece in the source. -/
abbrev sourceA := wedgeιLeft A (wedge (wedge e (wedge B f)) D)
abbrev sourceE := wedgeιLeft e (wedge B f) ≫
  wedgeιLeft (wedge e (wedge B f)) D ≫ wedgeιRight A (wedge (wedge e (wedge B f)) D)
abbrev sourceB := wedgeιLeft B f ≫ wedgeιRight e (wedge B f) ≫
  wedgeιLeft (wedge e (wedge B f)) D ≫ wedgeιRight A (wedge (wedge e (wedge B f)) D)
abbrev sourceF := wedgeιRight B f ≫ wedgeιRight e (wedge B f) ≫
  wedgeιLeft (wedge e (wedge B f)) D ≫ wedgeιRight A (wedge (wedge e (wedge B f)) D)
abbrev sourceD := wedgeιRight (wedge e (wedge B f)) D ≫
  wedgeιRight A (wedge (wedge e (wedge B f)) D)

abbrev groupedA := wedgeιLeft A (wedge e B) ≫
  wedgeιLeft (wedge A (wedge e B)) (wedge f D)
abbrev groupedE := wedgeιLeft e B ≫ wedgeιRight A (wedge e B) ≫
  wedgeιLeft (wedge A (wedge e B)) (wedge f D)
abbrev groupedB := wedgeιRight e B ≫ wedgeιRight A (wedge e B) ≫
  wedgeιLeft (wedge A (wedge e B)) (wedge f D)
abbrev groupedF := wedgeιLeft f D ≫ wedgeιRight (wedge A (wedge e B)) (wedge f D)
abbrev groupedD := wedgeιRight f D ≫ wedgeιRight (wedge A (wedge e B)) (wedge f D)

private theorem wedge_left {P P' R R' : NecklaceCode} {X : SSet.{0}}
    (g : P ⟶ P') (h : R ⟶ R') (n : (wedge P' R').toSSet ⟶ X) :
    wedgeιLeft P R ≫ ((wedgeMap g h).map ≫ n) = g.map ≫ (wedgeιLeft P' R' ≫ n) := by
  rw [← Category.assoc, wedgeMap_left, Category.assoc]

private theorem wedge_right {P P' R R' : NecklaceCode} {X : SSet.{0}}
    (g : P ⟶ P') (h : R ⟶ R') (n : (wedge P' R').toSSet ⟶ X) :
    wedgeιRight P R ≫ ((wedgeMap g h).map ≫ n) = h.map ≫ (wedgeιRight P' R' ≫ n) := by
  rw [← Category.assoc, wedgeMap_right, Category.assoc]

private theorem assoc_T (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge P (wedge M R)).toSSet ⟶ X) :
    wedgeιLeft P M ≫ (wedgeιLeft (wedge P M) R ≫ (wedgeAssocHom P M R ≫ n)) =
      wedgeιLeft P (wedge M R) ≫ n := by
  simpa only [tripleLeftT, tripleRightT, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocHom_T P M R)

private theorem assoc_U (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge P (wedge M R)).toSSet ⟶ X) :
    wedgeιRight P M ≫ (wedgeιLeft (wedge P M) R ≫ (wedgeAssocHom P M R ≫ n)) =
      wedgeιLeft M R ≫ (wedgeιRight P (wedge M R) ≫ n) := by
  simpa only [tripleLeftU, tripleRightU, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocHom_U P M R)

private theorem assoc_V (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge P (wedge M R)).toSSet ⟶ X) :
    wedgeιRight (wedge P M) R ≫ (wedgeAssocHom P M R ≫ n) =
      wedgeιRight M R ≫ (wedgeιRight P (wedge M R) ≫ n) := by
  simpa only [tripleLeftV, tripleRightV, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocHom_V P M R)

private theorem inv_T (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge (wedge P M) R).toSSet ⟶ X) :
    wedgeιLeft P (wedge M R) ≫ (wedgeAssocInv P M R ≫ n) =
      wedgeιLeft P M ≫ (wedgeιLeft (wedge P M) R ≫ n) := by
  simpa only [tripleRightT, tripleLeftT, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocInv_T P M R)

private theorem inv_U (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge (wedge P M) R).toSSet ⟶ X) :
    wedgeιLeft M R ≫ (wedgeιRight P (wedge M R) ≫ (wedgeAssocInv P M R ≫ n)) =
      wedgeιRight P M ≫ (wedgeιLeft (wedge P M) R ≫ n) := by
  simpa only [tripleRightU, tripleLeftU, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocInv_U P M R)

private theorem inv_V (P M R : NecklaceCode) {X : SSet.{0}}
    (n : (wedge (wedge P M) R).toSSet ⟶ X) :
    wedgeιRight M R ≫ (wedgeιRight P (wedge M R) ≫ (wedgeAssocInv P M R ≫ n)) =
      wedgeιRight (wedge P M) R ≫ n := by
  simpa only [tripleRightV, tripleLeftV, Category.assoc] using
    congrArg (· ≫ n) (wedgeAssocInv_V P M R)

private theorem id_map (P : NecklaceCode) : (𝟙 P : P ⟶ P).map = 𝟙 P.toSSet := rfl

/-- Every point of the first original native piece is unchanged. -/
theorem delta_A : sourceA A e B f D ≫ (delta A e B f D).hom = groupedA A e B f D := by
  rw [← Category.comp_id (delta A e B f D).hom, delta_hom]
  dsimp only [sourceA, groupedA, step1, step2, step3, step4, wedgeIso, assocIso, invCode,
    Iso.symm, Iso.refl, wedgeAssocCodeHom, wedgeAssoc]
  simp only [Category.assoc, wedge_left, inv_T, id_map, Category.id_comp]
  simp only [Category.comp_id]

/-- Every point of the second original native piece is unchanged. -/
theorem delta_e : sourceE A e B f D ≫ (delta A e B f D).hom = groupedE A e B f D := by
  rw [← Category.comp_id (delta A e B f D).hom, delta_hom]
  dsimp only [sourceE, groupedE, step1, step2, step3, step4, wedgeIso, assocIso, invCode,
    Iso.symm, Iso.refl, wedgeAssocCodeHom, wedgeAssoc]
  simp only [Category.assoc, wedge_left, wedge_right, assoc_T, inv_T, inv_U, id_map,
    Category.id_comp]
  simp only [Category.comp_id]

/-- Every point of the third original native piece is unchanged. -/
theorem delta_B : sourceB A e B f D ≫ (delta A e B f D).hom = groupedB A e B f D := by
  rw [← Category.comp_id (delta A e B f D).hom, delta_hom]
  dsimp only [sourceB, groupedB, step1, step2, step3, step4, wedgeIso, assocIso, invCode,
    Iso.symm, Iso.refl, wedgeAssocCodeHom, wedgeAssoc]
  simp only [Category.assoc, wedge_right, assoc_T, assoc_U, inv_U]
  simp only [Category.comp_id]

/-- Every point of the fourth original native piece is unchanged. -/
theorem delta_f : sourceF A e B f D ≫ (delta A e B f D).hom = groupedF A e B f D := by
  rw [← Category.comp_id (delta A e B f D).hom, delta_hom]
  dsimp only [sourceF, groupedF, step1, step2, step3, step4, wedgeIso, assocIso, invCode,
    Iso.symm, Iso.refl, wedgeAssocCodeHom, wedgeAssoc]
  simp only [Category.assoc, wedge_right, assoc_U, inv_V]
  simp only [Category.comp_id]

/-- Every point of the last original native piece is unchanged. -/
theorem delta_D : sourceD A e B f D ≫ (delta A e B f D).hom = groupedD A e B f D := by
  rw [← Category.comp_id (delta A e B f D).hom, delta_hom]
  dsimp only [sourceD, groupedD, step1, step2, step3, step4, wedgeIso, assocIso, invCode,
    Iso.symm, Iso.refl, wedgeAssocCodeHom, wedgeAssoc]
  simp only [Category.assoc, wedge_right, assoc_V, inv_V]
  simp only [Category.comp_id]

/-- Five WHOLE coefficients with only their four consecutive intrinsic seam equations. -/
structure Data (W : Source) (k : SimplexCategory) where
  a : std.obj k ⟶ labels W A
  s : std.obj k ⟶ labels W e
  b : std.obj k ⟶ labels W B
  t : std.obj k ⟶ labels W f
  d : std.obj k ⟶ labels W D
  as_join : a ≫ lastRestriction W A = s ≫ firstRestriction W e
  sb_join : s ≫ lastRestriction W e = b ≫ firstRestriction W B
  bt_join : b ≫ lastRestriction W B = t ≫ firstRestriction W f
  td_join : t ≫ lastRestriction W f = d ≫ firstRestriction W D

variable {A e B f D} {W : Source} {k : SimplexCategory}
variable (C : Data A e B f D W k)

private def bf := glue W B f k C.b C.t C.bt_join
private def fd := glue W f D k C.t C.d C.td_join
private def eb := glue W e B k C.s C.b C.sb_join

private theorem s_bf : C.s ≫ lastRestriction W e = bf C ≫ firstRestriction W (wedge B f) := by
  rw [bf, glue_first]
  exact C.sb_join
private theorem bf_d : bf C ≫ lastRestriction W (wedge B f) = C.d ≫ firstRestriction W D := by
  rw [bf, glue_last]
  exact C.td_join
private theorem b_fd : C.b ≫ lastRestriction W B = fd C ≫ firstRestriction W (wedge f D) := by
  rw [fd, glue_first]
  exact C.bt_join
private theorem a_eb : C.a ≫ lastRestriction W A = eb C ≫ firstRestriction W (wedge e B) := by
  rw [eb, glue_first]
  exact C.as_join
private theorem eb_fd : eb C ≫ lastRestriction W (wedge e B) =
    fd C ≫ firstRestriction W (wedge f D) := by
  rw [eb, fd, glue_last, glue_first]
  exact C.bt_join

private def tail0 := JTThreePieceCoefficientReassociation.leftCoefficient W e (wedge B f) D k
  C.s (bf C) C.d (s_bf C) (bf_d C)
private def tail1 := JTThreePieceCoefficientReassociation.rightCoefficient W e (wedge B f) D k
  C.s (bf C) C.d (s_bf C) (bf_d C)
private def tailB0 := JTThreePieceCoefficientReassociation.leftCoefficient W B f D k
  C.b C.t C.d C.bt_join C.td_join
private def tailB1 := JTThreePieceCoefficientReassociation.rightCoefficient W B f D k
  C.b C.t C.d C.bt_join C.td_join

private theorem s_tail0 : C.s ≫ lastRestriction W e =
    tailB0 C ≫ firstRestriction W (wedge (wedge B f) D) := by
  rw [tailB0, JTThreePieceCoefficientReassociation.leftCoefficient, glue_first, glue_first]
  exact C.sb_join
private theorem s_tail1 : C.s ≫ lastRestriction W e =
    tailB1 C ≫ firstRestriction W (wedge B (wedge f D)) := by
  rw [tailB1, JTThreePieceCoefficientReassociation.rightCoefficient, glue_first]
  exact C.sb_join

private def tail2 := glue W e (wedge B (wedge f D)) k C.s (tailB1 C) (s_tail1 C)
private def tail3 := JTThreePieceCoefficientReassociation.leftCoefficient W e B (wedge f D) k
  C.s C.b (fd C) C.sb_join (b_fd C)

private theorem a_tail0 : C.a ≫ lastRestriction W A = tail0 C ≫ firstRestriction W _ := by
  rw [tail0, JTThreePieceCoefficientReassociation.leftCoefficient, glue_first, glue_first]
  exact C.as_join
private theorem a_tail1 : C.a ≫ lastRestriction W A = tail1 C ≫ firstRestriction W _ := by
  rw [tail1, JTThreePieceCoefficientReassociation.rightCoefficient, glue_first]
  exact C.as_join
private theorem a_tail2 : C.a ≫ lastRestriction W A = tail2 C ≫ firstRestriction W _ := by
  rw [tail2, glue_first]
  exact C.as_join
private theorem a_tail3 : C.a ≫ lastRestriction W A = tail3 C ≫ firstRestriction W _ := by
  rw [tail3, JTThreePieceCoefficientReassociation.leftCoefficient, glue_first, glue_first]
  exact C.as_join

/-- The five complete input maps in the original coarse parenthesization. -/
def sourceCoefficient := glue W A (wedge (wedge e (wedge B f)) D) k C.a (tail0 C) (a_tail0 C)
private def coefficient1 := glue W A (wedge e (wedge (wedge B f) D)) k
  C.a (tail1 C) (a_tail1 C)
private def coefficient2 := glue W A (wedge e (wedge B (wedge f D))) k
  C.a (tail2 C) (a_tail2 C)
private def coefficient3 := glue W A (wedge (wedge e B) (wedge f D)) k
  C.a (tail3 C) (a_tail3 C)

/-- The SAME five complete maps grouped into the original left and right surroundings. -/
def groupedCoefficient := JTThreePieceCoefficientReassociation.leftCoefficient W A
  (wedge e B) (wedge f D) k C.a (eb C) (fd C) (a_eb C) (eb_fd C)

private theorem glue_map {P P' R R' : NecklaceCode}
    (g : P ⟶ P') (h : R ⟶ R')
    (a : std.obj k ⟶ labels W P) (b : std.obj k ⟶ labels W R)
    (a' : std.obj k ⟶ labels W P') (b' : std.obj k ⟶ labels W R')
    (j : a ≫ lastRestriction W P = b ≫ firstRestriction W R)
    (j' : a' ≫ lastRestriction W P' = b' ≫ firstRestriction W R')
    (ha : a = a' ≫ pre W g.map) (hb : b = b' ≫ pre W h.map) :
    glue W P R k a b j = glue W P' R' k a' b' j' ≫ pre W (wedgeMap g h).map := by
  simpa only [std.map_id, Category.id_comp] using
    JTThreePieceLabelOperators.wedge_coefficient_map g h (𝟙 k)
      (glue W P R k a b j) (glue W P' R' k a' b' j')
      (by
        rw [glue_left, ha]
        simp only [std.map_id, Category.id_comp, ← Category.assoc, glue_left])
      (by
        rw [glue_right, hb]
        simp only [std.map_id, Category.id_comp, ← Category.assoc, glue_right])

private theorem coefficient_step1 : sourceCoefficient C =
    coefficient1 C ≫ pre W (step1 A e B f D).hom.map := by
  apply glue_map
  · change C.a = C.a ≫ pre W (𝟙 A.toSSet)
    rw [pre_id]
    exact (Category.comp_id C.a).symm
  · exact JTThreePieceCoefficientReassociation.associator_coefficient W e (wedge B f) D k
      C.s (bf C) C.d (s_bf C) (bf_d C)

private theorem coefficient_step2 : coefficient1 C =
    coefficient2 C ≫ pre W (step2 A e B f D).hom.map := by
  apply glue_map
  · change C.a = C.a ≫ pre W (𝟙 A.toSSet)
    rw [pre_id]
    exact (Category.comp_id C.a).symm
  · change glue W e _ k C.s (tailB0 C) (s_tail0 C) =
      tail2 C ≫ pre W (wedgeMap (𝟙 e) (wedgeAssocCodeHom B f D)).map
    apply glue_map
    · change C.s = C.s ≫ pre W (𝟙 e.toSSet)
      rw [pre_id]
      exact (Category.comp_id C.s).symm
    · exact JTThreePieceCoefficientReassociation.associator_coefficient W B f D k
        C.b C.t C.d C.bt_join C.td_join

private theorem coefficient_step3 : coefficient2 C =
    coefficient3 C ≫ pre W (step3 A e B f D).hom.map := by
  apply glue_map
  · change C.a = C.a ≫ pre W (𝟙 A.toSSet)
    rw [pre_id]
    exact (Category.comp_id C.a).symm
  · exact JTThreePieceCoefficientReassociation.inverse_associator_coefficient W e B
      (wedge f D) k C.s C.b (fd C) C.sb_join (b_fd C)

private theorem coefficient_step4 : coefficient3 C =
    groupedCoefficient C ≫ pre W (step4 A e B f D).hom.map :=
  JTThreePieceCoefficientReassociation.inverse_associator_coefficient W A (wedge e B)
    (wedge f D) k C.a (eb C) (fd C) (a_eb C) (eb_fd C)

/-- Regrouping preserves the WHOLE coefficient, with arbitrary varying inner rows. -/
theorem coefficient : sourceCoefficient C = groupedCoefficient C ≫
    pre W (delta A e B f D).hom := by
  rw [coefficient_step1, coefficient_step2, coefficient_step3, coefficient_step4]
  simp only [Category.assoc, ← pre_comp, delta_hom]

end
end DaggerModels.PartII.JTCoarseCoefficientRegrouping
