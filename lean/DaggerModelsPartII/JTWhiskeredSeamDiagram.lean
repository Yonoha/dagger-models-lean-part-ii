import DaggerModelsPartII.JTWhiskeredSeamSpan

/-! Natural three-piece seam spans with varying surrounding labels and degree. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTWhiskeredSeamDiagram

open JTThreePieceLabelOperators (Data index indexMap indexMap_projection)
open JTWhiskeredMiddleRestriction (pullMiddle)
open JTWhiskeredSeamSpan (detour long collapsed)
open JTProjectiveOrderedFiberComparison (row)
open TripleBeadEndpointLabel (labels)
open ReversalDiscreteFreeColimits (discreteFree)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W
private abbrev E := single 1

variable {I : Type} [SmallCategory I] {W : Source} {x y : Vertex W}

private abbrev proj (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private instance : (proj W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private theorem pre_id (T : NecklaceCode) :
    pre W ((𝟙 T : T ⟶ T).map) = 𝟙 (labels W T) := by
  change diagramMappingPrecomp (discreteFree.map (𝟙 T.toSSet)) W = 𝟙 _
  rw [discreteFree.map_id]
  exact diagramMappingPrecomp_id _ W

/-- Three-piece coefficients varying naturally in both surrounding native
codes and in their common full coefficient degree. The middle code is fixed. -/
structure Family (M : NecklaceCode) (P R : I ⥤ NecklaceCode)
    (K : I ⥤ SimplexCategory) where
  data : ∀ a : I, Data W (P.obj a) M (R.obj a) (K.obj a) x y
  left_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).left = std.map (K.map g) ≫ (data b).left ≫ pre W (P.map g).map
  middle_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).middle = std.map (K.map g) ≫ (data b).middle
  right_nat : ∀ {a b : I} (g : a ⟶ b),
    (data a).right = std.map (K.map g) ≫ (data b).right ≫ pre W (R.map g).map

variable {M : NecklaceCode} {P R : I ⥤ NecklaceCode} {K : I ⥤ SimplexCategory}

private theorem Family.middle_operator
    (F : Family (W := W) (x := x) (y := y) M P R K)
    {a b : I} (g : a ⟶ b) :
    (F.data a).middle =
      std.map (K.map g) ≫ (F.data b).middle ≫ pre W ((𝟙 M : M ⟶ M).map) := by
  rw [F.middle_nat g, pre_id]
  simp only [Category.comp_id]

/-- The actual decorated operator determined by the three coefficient equations. -/
def Family.arrow (F : Family (W := W) (x := x) (y := y) M P R K)
    {a b : I} (g : a ⟶ b) : index (F.data a) ⟶ index (F.data b) :=
  indexMap (F.data a) (F.data b) (P.map g) (𝟙 M) (R.map g) (K.map g)
    (F.left_nat g) (F.middle_operator g) (F.right_nat g)

theorem Family.arrow_projection (F : Family (W := W) (x := x) (y := y) M P R K)
    {a b : I} (g : a ⟶ b) :
    (proj W x y).map (F.arrow g) =
      (wedgeMap (P.map g) (wedgeMap (𝟙 M) (R.map g)), K.map g) :=
  indexMap_projection (F.data a) (F.data b) (P.map g) (𝟙 M) (R.map g)
    (K.map g) (F.left_nat g) (F.middle_operator g) (F.right_nat g)

/-- All three varying coefficients form one genuine decorated-label functor. -/
def Family.labels (F : Family (W := W) (x := x) (y := y) M P R K) :
    I ⥤ DecoratedNecklaceHomDiagram.Index W x y where
  obj a := index (F.data a)
  map g := F.arrow g
  map_id a := by
    apply (proj W x y).map_injective
    rw [F.arrow_projection, (proj W x y).map_id,
      P.map_id, R.map_id, K.map_id]
    change (wedgeMap (𝟙 (P.obj a)) (wedgeMap (𝟙 M) (𝟙 (R.obj a))),
      𝟙 (K.obj a)) = (𝟙 (wedge (P.obj a) (wedge M (R.obj a))), 𝟙 (K.obj a))
    exact congrArg (fun u : (wedge (P.obj a) (wedge M (R.obj a))) ⟶
        wedge (P.obj a) (wedge M (R.obj a)) ↦ (u, 𝟙 (K.obj a)))
      ((congrArg (wedgeMap (𝟙 (P.obj a)))
        (wedgeMap_id (T := M) (U := R.obj a))).trans
        (wedgeMap_id (T := P.obj a) (U := wedge M (R.obj a))))
  map_comp g h := by
    apply (proj W x y).map_injective
    rw [F.arrow_projection, (proj W x y).map_comp,
      F.arrow_projection, F.arrow_projection, P.map_comp, R.map_comp, K.map_comp]
    apply Prod.ext
    · change wedgeMap (Hom.comp (P.map g) (P.map h))
          (wedgeMap (𝟙 M) (Hom.comp (R.map g) (R.map h))) =
        Hom.comp (wedgeMap (P.map g) (wedgeMap (𝟙 M) (R.map g)))
          (wedgeMap (P.map h) (wedgeMap (𝟙 M) (R.map h)))
      rw [← wedgeMap_comp, ← wedgeMap_comp]
      have hid : Hom.comp (𝟙 M) (𝟙 M) = 𝟙 M :=
        Hom.ext (Category.id_comp ((𝟙 M : M ⟶ M).map))
      rw [hid]
    · rfl

/-- Fixed middle arrows commute with all varying outer native operators. -/
private theorem native_square {A B C D M N : NecklaceCode}
    (p : A ⟶ B) (r : C ⟶ D) (u : M ⟶ N) :
    Hom.comp (wedgeMap p (wedgeMap (𝟙 M) r))
        (wedgeMap (𝟙 B) (wedgeMap u (𝟙 D))) =
      Hom.comp (wedgeMap (𝟙 A) (wedgeMap u (𝟙 C)))
        (wedgeMap p (wedgeMap (𝟙 N) r)) := by
  rw [← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp, ← wedgeMap_comp]
  have hp : Hom.comp p (𝟙 B) = p := Hom.ext (Category.comp_id p.map)
  have hq : Hom.comp (𝟙 A) p = p := Hom.ext (Category.id_comp p.map)
  have hu₀ : Hom.comp (𝟙 M) u = u := Hom.ext (Category.id_comp u.map)
  have hu₁ : Hom.comp u (𝟙 N) = u := Hom.ext (Category.comp_id u.map)
  have hr₀ : Hom.comp r (𝟙 D) = r := Hom.ext (Category.comp_id r.map)
  have hr₁ : Hom.comp (𝟙 C) r = r := Hom.ext (Category.id_comp r.map)
  rw [hp, hq, hu₀, hu₁, hr₀, hr₁]

/-- Pulling a fixed native middle arrow preserves all three coefficient
naturality equations, including the varying surrounding operators. -/
def Family.pull (F : Family (W := W) (x := x) (y := y) M P R K)
    {N : NecklaceCode} (u : N ⟶ M) :
    Family (W := W) (x := x) (y := y) N P R K where
  data a := pullMiddle (F.data a) u
  left_nat g := F.left_nat g
  middle_nat g := by
    change (F.data _).middle ≫ pre W u.map =
      std.map (K.map g) ≫ (F.data _).middle ≫ pre W u.map
    rw [F.middle_nat g]
    simp only [Category.assoc]
  right_nat g := F.right_nat g

/-- A natural triangle coefficient and a natural varying seam row, with the
long edge equal to the identity at that row. -/
structure SeamFamily (P R : I ⥤ NecklaceCode) (K : I ⥤ SimplexCategory) where
  triangle : Family (W := W) (x := x) (y := y) (single 2) P R K
  tau : ∀ a : I, std.obj (K.obj a) ⟶ row W ⦋2⦌
  tau_nat : ∀ {a b : I} (g : a ⟶ b),
    tau a = std.map (K.map g) ≫ tau b
  middle_eq : ∀ a : I,
    (triangle.data a).middle = tau a ≫ JTNativeRowLabel.labelFromRow W 2
  seamRow : ∀ a : I, std.obj (K.obj a) ⟶ row W ⦋0⦌
  seamRow_nat : ∀ {a b : I} (g : a ⟶ b),
    seamRow a = std.map (K.map g) ≫ seamRow b
  long_eq : ∀ a : I,
    tau a ≫ (Rows W).map (SimplexCategory.δ 1).op =
      seamRow a ≫ JTEndpointNormalizationLifts.identityFamily W

variable (F : SeamFamily (W := W) (x := x) (y := y) P R K)

/-- The two-edge detour retains the original varying outer coefficients. -/
def detourFamily : Family (W := W) (x := x) (y := y)
    (wedge E E) P R K := F.triangle.pull JTSeamNativeCoefficients.spine

/-- The long edge retains those same coefficients and degree. -/
def longFamily : Family (W := W) (x := x) (y := y)
    E P R K := F.triangle.pull JTSeamNativeCoefficients.longEdge

/-- Collapsing the identity edge changes only the native middle and its
coefficient; the two outer families and their operators remain literal. -/
def collapsedFamily : Family (W := W) (x := x) (y := y)
    (single 0) P R K where
  data a := collapsed (F.triangle.data a) (F.tau a) (F.middle_eq a)
    (F.seamRow a) (F.long_eq a)
  left_nat g := F.triangle.left_nat g
  middle_nat g := by
    change F.seamRow _ ≫ JTNativeRowLabel.labelFromRow W 0 =
      std.map (K.map g) ≫ F.seamRow _ ≫ JTNativeRowLabel.labelFromRow W 0
    rw [F.seamRow_nat g]
    simp only [Category.assoc]
  right_nat g := F.triangle.right_nat g

/-- The complete natural detour-to-triangle comparison in the original
decorated-label category. -/
def detourToTriangle : (detourFamily F).labels ⟶ F.triangle.labels where
  app a := JTWhiskeredSeamSpan.detourToTriangle (F.triangle.data a)
  naturality {a b} g := by
    apply (proj W x y).map_injective
    simp only [Functor.map_comp]
    change (proj W x y).map ((detourFamily F).arrow g) ≫ _ =
      _ ≫ (proj W x y).map (F.triangle.arrow g)
    rw [Family.arrow_projection, Family.arrow_projection,
      JTWhiskeredSeamSpan.detourToTriangle_projection,
      JTWhiskeredSeamSpan.detourToTriangle_projection]
    apply Prod.ext
    · exact native_square (P.map g) (R.map g) JTSeamNativeCoefficients.spine
    · rfl

/-- The long native edge compares naturally to the full triangle. -/
def longToTriangle : (longFamily F).labels ⟶ F.triangle.labels where
  app a := JTWhiskeredSeamSpan.longToTriangle (F.triangle.data a)
  naturality {a b} g := by
    apply (proj W x y).map_injective
    simp only [Functor.map_comp]
    change (proj W x y).map ((longFamily F).arrow g) ≫ _ =
      _ ≫ (proj W x y).map (F.triangle.arrow g)
    rw [Family.arrow_projection, Family.arrow_projection,
      JTWhiskeredSeamSpan.longToTriangle_projection,
      JTWhiskeredSeamSpan.longToTriangle_projection]
    apply Prod.ext
    · exact native_square (P.map g) (R.map g) JTSeamNativeCoefficients.longEdge
    · rfl

/-- The identity long edge descends naturally to the varying original seam
row while preserving both global endpoints. -/
def longToCollapsed : (longFamily F).labels ⟶ (collapsedFamily F).labels where
  app a := JTWhiskeredSeamSpan.longToCollapsed (F.triangle.data a)
    (F.tau a) (F.middle_eq a) (F.seamRow a) (F.long_eq a)
  naturality {a b} g := by
    apply (proj W x y).map_injective
    simp only [Functor.map_comp]
    change (proj W x y).map ((longFamily F).arrow g) ≫ _ =
      _ ≫ (proj W x y).map ((collapsedFamily F).arrow g)
    rw [Family.arrow_projection, Family.arrow_projection,
      JTWhiskeredSeamSpan.longToCollapsed_projection,
      JTWhiskeredSeamSpan.longToCollapsed_projection]
    apply Prod.ext
    · exact native_square (P.map g) (R.map g)
        JTSeamNativeCoefficients.collapseIdentity
    · rfl

/-- The detour comparison changes only its native middle by the spine map. -/
theorem detourToTriangle_projection (a : I) :
    (proj W x y).map ((detourToTriangle F).app a) =
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap JTSeamNativeCoefficients.spine (𝟙 (R.obj a))),
        𝟙 (K.obj a)) :=
  JTWhiskeredSeamSpan.detourToTriangle_projection (F.triangle.data a)

/-- The long comparison changes only its native middle by the long edge. -/
theorem longToTriangle_projection (a : I) :
    (proj W x y).map ((longToTriangle F).app a) =
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap JTSeamNativeCoefficients.longEdge (𝟙 (R.obj a))),
        𝟙 (K.obj a)) :=
  JTWhiskeredSeamSpan.longToTriangle_projection (F.triangle.data a)

/-- Collapsing the identity changes only the middle native code. -/
theorem longToCollapsed_projection (a : I) :
    (proj W x y).map ((longToCollapsed F).app a) =
      (wedgeMap (𝟙 (P.obj a))
        (wedgeMap JTSeamNativeCoefficients.collapseIdentity (𝟙 (R.obj a))),
        𝟙 (K.obj a)) :=
  JTWhiskeredSeamSpan.longToCollapsed_projection (F.triangle.data a)
    (F.tau a) (F.middle_eq a) (F.seamRow a) (F.long_eq a)

end
end DaggerModels.PartII.JTWhiskeredSeamDiagram
