import DaggerModelsPartII.ChosenFiberLiftIndependence
import DaggerModelsPartII.ChosenHomotopyFiberTriangle
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# The actual chosen homotopy fiber as a functor after Kan localization

A pointed arrow is the original arrow together with its specified map from K
into the base. A map uses the selected factorization and the actual chosen
comparison lift. The identity and composition laws hold after localization,
by independence of lifts across the same factorization unit. No raw endpoint
arrow is assumed fibrant, and no equality of point-set lifts is asserted.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ChosenHomotopyFiberFunctor

open ChosenHomotopyFiberComparison DaggerNativeSSetFibrationSquareFibreWeak

noncomputable section

private theorem square_comp {X Y Z B D E : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (r : Z ⟶ E)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (a : Y ⟶ Z) (c : D ⟶ E) (h' : q ≫ c = a ≫ r) :
    p ≫ (g ≫ c) = (f ≫ a) ≫ r := by
  rw [← Category.assoc, h, Category.assoc, h', ← Category.assoc]

private theorem point_comp {K B D E : SSet.{u}}
    (b : K ⟶ B) (d : K ⟶ D) (e : K ⟶ E)
    (g : B ⟶ D) (c : D ⟶ E) (hb : b ≫ g = d) (hd : d ≫ c = e) :
    b ≫ (g ≫ c) = e := by
  rw [← Category.assoc, hb, hd]

/-- Composition of the literal fiber maps is the fiber map of the original
composite square, with the same point object and ordered point maps. -/
theorem fibreMap_comp {X Y Z B D E K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (r : Z ⟶ E)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (a : Y ⟶ Z) (c : D ⟶ E) (h' : q ≫ c = a ≫ r)
    (b : K ⟶ B) (d : K ⟶ D) (e : K ⟶ E)
    (hb : b ≫ g = d) (hd : d ≫ c = e) :
    fibreMap p q f g h b d hb ≫ fibreMap q r a c h' d e hd =
      fibreMap p r (f ≫ a) (g ≫ c) (square_comp p q r f g h a c h') b e
        (point_comp b d e g c hb hd) := by
  apply pullback.hom_ext <;> simp [fibreMap, Category.assoc]

/-- The literal fiber map of the identity square is the identity. -/
theorem fibreMap_id {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) :
    fibreMap p p (𝟙 X) (𝟙 B) (by simp) b b (by simp) = 𝟙 (pullback p b) := by
  apply pullback.hom_ext <;> simp [fibreMap]

private theorem resolved_square {X Y B D : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) :
    p ≫ g = (f ≫ (replacement q).i) ≫ (replacement q).p := by
  rw [Category.assoc, (replacement q).fac]
  exact h

private def totalLift {X Y B D : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) : (replacement p).Z ⟶ (replacement q).Z := by
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  exact comparisonTotal p (replacement q).p (f ≫ (replacement q).i) g
    (resolved_square p q f g h)

private theorem totalLift_i {X Y B D : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) :
    (replacement p).i ≫ totalLift p q f g h = f ≫ (replacement q).i := by
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  exact replacement_i_comparisonTotal p (replacement q).p
    (f ≫ (replacement q).i) g (resolved_square p q f g h)

private theorem totalLift_p {X Y B D : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) :
    totalLift p q f g h ≫ (replacement q).p = (replacement p).p ≫ g := by
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  exact comparisonTotal_projection p (replacement q).p
    (f ≫ (replacement q).i) g (resolved_square p q f g h)

/-- The actual chosen-fiber map of the original pointed square. It uses
the literal comparisonTotal lift into the chosen replacement of the target. -/
def chosenMap {X Y B D K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) :
    chosenFiber p b ⟶ chosenFiber q d :=
  fibreMap (replacement p).p (replacement q).p (totalLift p q f g h) g
    (totalLift_p p q f g h).symm b d hb

/-- The actual two-step chosen comparison and the one-step comparison agree
after localization. Neither original endpoint arrow is assumed fibrant. -/
theorem chosenMap_comp {X Y Z B D E K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (r : Z ⟶ E)
    (f : X ⟶ Y) (g : B ⟶ D) (h : p ≫ g = f ≫ q)
    (a : Y ⟶ Z) (c : D ⟶ E) (h' : q ≫ c = a ≫ r)
    (b : K ⟶ B) (d : K ⟶ D) (e : K ⟶ E)
    (hb : b ≫ g = d) (hd : d ≫ c = e) :
    (weakEquivalences SSet.{u}).Q.map (chosenMap p q f g h b d hb) ≫
        (weakEquivalences SSet.{u}).Q.map (chosenMap q r a c h' d e hd) =
      (weakEquivalences SSet.{u}).Q.map
        (chosenMap p r (f ≫ a) (g ≫ c) (square_comp p q r f g h a c h') b e
          (point_comp b d e g c hb hd)) := by
  let L := totalLift p q f g h
  let M := totalLift q r a c h'
  let N := totalLift p r (f ≫ a) (g ≫ c) (square_comp p q r f g h a c h')
  letI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  letI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  letI : Fibration (replacement r).p := (fibration_iff _).mpr (replacement r).hp
  have hu : (replacement p).p ≫ (g ≫ c) = (L ≫ M) ≫ (replacement r).p := by
    symm
    calc
      (L ≫ M) ≫ (replacement r).p = L ≫ (M ≫ (replacement r).p) :=
        Category.assoc _ _ _
      _ = L ≫ ((replacement q).p ≫ c) := by
        dsimp only [M]
        rw [totalLift_p]
      _ = (L ≫ (replacement q).p) ≫ c := (Category.assoc _ _ _).symm
      _ = ((replacement p).p ≫ g) ≫ c := by
        dsimp only [L]
        rw [totalLift_p]
      _ = (replacement p).p ≫ (g ≫ c) := Category.assoc _ _ _
  have hv : (replacement p).p ≫ (g ≫ c) = N ≫ (replacement r).p :=
    (totalLift_p p r (f ≫ a) (g ≫ c) (square_comp p q r f g h a c h')).symm
  have hi : (replacement p).i ≫ (L ≫ M) = (replacement p).i ≫ N := by
    dsimp only [L, M, N]
    rw [← Category.assoc, totalLift_i, Category.assoc, totalLift_i, ← Category.assoc,
      totalLift_i]
  have he := ChosenFiberLiftIndependence.fibreMap_localized_eq_of_same_restriction
    (i := (replacement p).i) (p := (replacement p).p) (q := (replacement r).p)
    (g := g ≫ c) (u := L ≫ M) (v := N) (hu := hu) (hv := hv)
    (b := b) (d := e) (hb := point_comp b d e g c hb hd) hi
  rw [← Functor.map_comp]
  dsimp only [chosenMap]
  rw [fibreMap_comp]
  exact he

/-- The actual chosen comparison of the identity pointed square becomes the
identity after localization, without asserting point-set lift uniqueness. -/
theorem chosenMap_id {X B K : SSet.{u}} (p : X ⟶ B) (b : K ⟶ B) :
    (weakEquivalences SSet.{u}).Q.map
        (chosenMap p p (𝟙 X) (𝟙 B) (by simp) b b (by simp)) =
      𝟙 ((weakEquivalences SSet.{u}).Q.obj (chosenFiber p b)) := by
  let L := totalLift p p (𝟙 X) (𝟙 B) (by simp)
  letI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  letI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  letI : Fibration (replacement p).p := (fibration_iff _).mpr (replacement p).hp
  have hu : (replacement p).p ≫ 𝟙 B = L ≫ (replacement p).p :=
    (totalLift_p p p (𝟙 X) (𝟙 B) (by simp)).symm
  have hv : (replacement p).p ≫ 𝟙 B =
      (𝟙 (replacement p).Z) ≫ (replacement p).p := by simp
  have hi : (replacement p).i ≫ L =
      (replacement p).i ≫ 𝟙 (replacement p).Z := by
    dsimp only [L]
    simpa only [Category.id_comp, Category.comp_id] using
      totalLift_i p p (𝟙 X) (𝟙 B) (by simp)
  have he := ChosenFiberLiftIndependence.fibreMap_localized_eq_of_same_restriction
    (i := (replacement p).i) (p := (replacement p).p) (q := (replacement p).p)
    (g := 𝟙 B) (u := L) (v := 𝟙 (replacement p).Z) (hu := hu) (hv := hv)
    (b := b) (d := b) (hb := by simp) hi
  change (weakEquivalences SSet.{u}).Q.map
      (fibreMap (replacement p).p (replacement p).p L (𝟙 B) hu b b (by simp)) = _
  rw [he, fibreMap_id]
  exact (weakEquivalences SSet.{u}).Q.map_id _

/-- The canonical strict-to-chosen inclusions are natural for the actual
chosen comparison and the literal original strict fiber map. This is an
exact point-set equation, not only a localized identification. -/
theorem inclusion_chosenMap {X Y B D K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d) :
    ChosenHomotopyFiberTriangle.inclusion p b ≫ chosenMap p q f g h b d hb =
      fibreMap p q f g h b d hb ≫ ChosenHomotopyFiberTriangle.inclusion q d := by
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  have hc := ChosenHomotopyFiberTriangle.inclusion_comparison p (replacement q).p
    (f ≫ (replacement q).i) g (resolved_square p q f g h) b d hb
  change ChosenHomotopyFiberTriangle.inclusion p b ≫ chosenMap p q f g h b d hb =
    fibreMap p (replacement q).p (f ≫ (replacement q).i) g
      (resolved_square p q f g h) b d hb at hc
  rw [hc]
  apply pullback.hom_ext <;>
    simp [ChosenHomotopyFiberTriangle.inclusion, fibreMap, Category.assoc]

/-- For a fibrant target arrow, the chosen-to-chosen action is the actual
chosen-to-strict comparison followed by the target's canonical inclusion,
after localization. The original source arrow need not be fibrant. -/
theorem chosenMap_comparison {X Y B D K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)
    [Fibration q] :
    (weakEquivalences SSet.{u}).Q.map (chosenMap p q f g h b d hb) =
      (weakEquivalences SSet.{u}).Q.map
        (comparison p q f g h b d hb ≫ ChosenHomotopyFiberTriangle.inclusion q d) := by
  let L := comparisonTotal p q f g h
  letI : Cofibration (replacement p).i :=
    (cofibration_iff _).mpr (replacement p).hi.1
  letI : WeakEquivalence (replacement p).i :=
    (weakEquivalence_iff _).mpr (replacement p).hi.2
  letI : Fibration (replacement q).p := (fibration_iff _).mpr (replacement q).hp
  have hu : (replacement p).p ≫ g =
      totalLift p q f g h ≫ (replacement q).p := (totalLift_p p q f g h).symm
  have hv : (replacement p).p ≫ g = (L ≫ (replacement q).i) ≫
      (replacement q).p := by
    rw [Category.assoc, (replacement q).fac]
    exact (comparisonTotal_projection p q f g h).symm
  have hi : (replacement p).i ≫ totalLift p q f g h =
      (replacement p).i ≫ (L ≫ (replacement q).i) := by
    rw [totalLift_i, ← Category.assoc]
    dsimp only [L]
    rw [replacement_i_comparisonTotal]
  have he := ChosenFiberLiftIndependence.fibreMap_localized_eq_of_same_restriction
    (i := (replacement p).i) (p := (replacement p).p) (q := (replacement q).p)
    (g := g) (u := totalLift p q f g h) (v := L ≫ (replacement q).i)
    (hu := hu) (hv := hv) (b := b) (d := d) (hb := hb) hi
  change (weakEquivalences SSet.{u}).Q.map
      (fibreMap (replacement p).p (replacement q).p (totalLift p q f g h) g hu b d hb) =
    (weakEquivalences SSet.{u}).Q.map
      (fibreMap (replacement p).p q L g
          (comparisonTotal_projection p q f g h).symm b d hb ≫
        ChosenHomotopyFiberTriangle.inclusion q d)
  dsimp only [ChosenHomotopyFiberTriangle.inclusion]
  rw [fibreMap_comp]
  simpa only [Category.comp_id] using he

/-- For actual fibrant endpoint arrows, a weak literal strict fiber map
induces a weak actual chosen-fiber map. No weakness of its total or base
maps is supplied as an extra hypothesis. -/
theorem chosenMap_weak_of_strict_weak {X Y B D K : SSet.{u}}
    (p : X ⟶ B) (q : Y ⟶ D) (f : X ⟶ Y) (g : B ⟶ D)
    (h : p ≫ g = f ≫ q) (b : K ⟶ B) (d : K ⟶ D) (hb : b ≫ g = d)
    [Fibration p] [Fibration q] [WeakEquivalence (fibreMap p q f g h b d hb)] :
    WeakEquivalence (chosenMap p q f g h b d hb) := by
  haveI : WeakEquivalence (ChosenHomotopyFiberTriangle.inclusion p b) :=
    ChosenHomotopyFiberTriangle.inclusion_weak p b
  haveI : WeakEquivalence (ChosenHomotopyFiberTriangle.inclusion q d) :=
    ChosenHomotopyFiberTriangle.inclusion_weak q d
  haveI : WeakEquivalence (fibreMap p q f g h b d hb ≫
      ChosenHomotopyFiberTriangle.inclusion q d) := inferInstance
  exact weakEquivalence_of_precomp_of_fac (inclusion_chosenMap p q f g h b d hb)

/-- Original arrows with a specified point map from K, using the native
structured-arrow category rather than a separate category implementation. -/
abbrev PointedArrow (K : SSet.{u}) :=
  StructuredArrow K (Arrow.rightFunc (C := SSet.{u}))

/-- The chosen original homotopy fiber is functorial in its pointed arrow
after Kan localization, for arbitrary original arrows and point object K. -/
def localizedFiberFunctor (K : SSet.{u}) :
    PointedArrow K ⥤ (weakEquivalences SSet.{u}).Localization where
  obj P := (weakEquivalences SSet.{u}).Q.obj (chosenFiber P.right.hom P.hom)
  map {P R} s := (weakEquivalences SSet.{u}).Q.map
    (chosenMap P.right.hom R.right.hom s.right.left s.right.right
      (Arrow.w s.right).symm P.hom R.hom (StructuredArrow.w s))
  map_id P := by
    simpa only [StructuredArrow.id_right, Arrow.id_left, Arrow.id_right] using
      chosenMap_id P.right.hom P.hom
  map_comp {P R T} s t := by
    symm
    simpa only [StructuredArrow.comp_right, Arrow.comp_left, Arrow.comp_right] using
      chosenMap_comp P.right.hom R.right.hom T.right.hom
        s.right.left s.right.right (Arrow.w s.right).symm
        t.right.left t.right.right (Arrow.w t.right).symm
        P.hom R.hom T.hom (StructuredArrow.w s) (StructuredArrow.w t)

end

end DaggerModels.PartII.ChosenHomotopyFiberFunctor
