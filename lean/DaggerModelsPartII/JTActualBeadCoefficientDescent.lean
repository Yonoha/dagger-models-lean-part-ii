import DaggerModelsPartII.JTPrismJointCoefficient
import DaggerModelsPartII.JTPrismHorizontalCoefficient

/-! Descend the full coefficient of an actual parametrized bead without changing its target. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTPrismRectangle (prismValue prismValue_section coefficient_eq_of_prismValue_splitEpi)
open JTNativeRowLabel (labelFromRow realized_nativeLabel)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTNecklaceLabelRealization (realizedLabel realizedLabel_natural_X)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Input (W : Source) := JTReversalInput.ordinaryInput.obj W
private abbrev Raw (W : Source) := OrdinaryJTRealization.realization.obj (Input W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev Δ (e : SimplexCategory) := std.obj e

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (a : A) (d : ℕ)
variable (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)

private abbrev k := ((OrderedLabelElements.projection W (boundaryPoint W x y)).obj (L.obj a)).2
private abbrev beadMap := (NecklaceCode.singleIso d).inv ≫ i
private abbrev w := SSet.yonedaEquiv (X := row W ⦋d⦌) (coefficient (a := a) d i)

set_option maxHeartbeats 700000 in
/-- The entire bead prism realizes to its literal native map, independently of time. -/
theorem fullBead_prismValue :
    prismValue (w a d i) (fullBeadParameter F a d i) =
      fst (Δ ⦋d⦌) (J.obj (time.obj a)) ≫ (beadMap a d i ≫ (F.collapse.app a).map ≫ Q.map) := by
  let T := (codes L).obj a
  let n := time.obj a
  let e := (NecklaceCode.singleIso d).inv
  let j := beadMap a d i
  let p := F.parameter a
  let q := fullBeadParameter F a d i
  let k₀ := k (L := L) a
  let η := orderedLabel W x y T k₀
    (OrderedLabelElements.label W (boundaryPoint W x y) (L.obj a))
  have hlabel :
      (e ⊗ₘ 𝟙 (J.obj k₀)) ≫
        realizedLabel (NecklaceCode.single d).toSSet W k₀ (beadLabel (a := a) d i) =
      JTRealizationGenerators.generator (Input W) (⦋d⦌, k₀) (w a d i) := by
    rw [← coefficient_label a d i, realized_nativeLabel,
      ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Iso.inv_hom_id]
    apply Category.id_comp
  have hrestrict :
      (e ⊗ₘ 𝟙 (J.obj k₀)) ≫
        realizedLabel (NecklaceCode.single d).toSSet W k₀ (beadLabel (a := a) d i) =
      (j ⊗ₘ 𝟙 (J.obj k₀)) ≫ realizedLabel T.toSSet W k₀ η := by
    have h := realizedLabel_natural_X i W k₀ η
    change (i ⊗ₘ 𝟙 (J.obj k₀)) ≫ realizedLabel T.toSSet W k₀ η =
      realizedLabel (NecklaceCode.single d).toSSet W k₀ (beadLabel (a := a) d i) at h
    rw [← h, ← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
  have hgraph :
      lift (fst (Δ ⦋d⦌) (J.obj n)) q ≫ (j ⊗ₘ 𝟙 (J.obj k₀)) =
        (j ⊗ₘ 𝟙 (J.obj n)) ≫ lift (fst T.toSSet (J.obj n)) p := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc]
      change lift (fst (Δ ⦋d⦌) (J.obj n)) q ≫ (j ⊗ₘ 𝟙 (J.obj k₀)) ≫
        fst T.toSSet (J.obj k₀) = (j ⊗ₘ 𝟙 (J.obj n)) ≫
          lift (fst T.toSSet (J.obj n)) p ≫ fst T.toSSet (J.obj k₀)
      rw [tensorHom_fst, lift_fst_assoc, lift_fst, tensorHom_fst]
    · rw [Category.assoc, Category.assoc]
      change lift (fst (Δ ⦋d⦌) (J.obj n)) q ≫ (j ⊗ₘ 𝟙 (J.obj k₀)) ≫
        snd T.toSSet (J.obj k₀) = (j ⊗ₘ 𝟙 (J.obj n)) ≫
          lift (fst T.toSSet (J.obj n)) p ≫ snd T.toSSet (J.obj k₀)
      rw [tensorHom_snd, Category.comp_id, lift_snd, lift_snd]
      rfl
  have hraw := JTParametrizedTargetFamilies.rawProduct F a
  change JTBinaryPrismRealization.realizeProduct W k₀ p η =
    fst T.toSSet (J.obj n) ≫ (F.collapse.app a).map ≫ Q.map at hraw
  calc
    _ = lift (fst (Δ ⦋d⦌) (J.obj n)) q ≫
        (j ⊗ₘ 𝟙 (J.obj k₀)) ≫ realizedLabel T.toSSet W k₀ η := by
      unfold prismValue
      rw [← hlabel, hrestrict]
    _ = (j ⊗ₘ 𝟙 (J.obj n)) ≫ JTBinaryPrismRealization.realizeProduct W k₀ p η := by
      rw [← Category.assoc, hgraph, Category.assoc]
      rfl
    _ = _ := by
      rw [hraw, tensorHom_fst_assoc]

variable {e : SimplexCategory} (u : ⦋d⦌ ⟶ e) (b : e ⟶ ⦋d⦌)

/-- A section gives a genuine restriction of the original coefficient. -/
def sectionCoefficient : (Input W).obj (op (e, k (L := L) a)) :=
  (Input W).map (show (e, k (L := L) a) ⟶ (⦋d⦌, k (L := L) a) from
    (b, 𝟙 (k (L := L) a))).op (w a d i)

variable (q : Δ e ⊗ J.obj (time.obj a) ⟶ J.obj (k (L := L) a)) (r : Δ e ⟶ Raw W)
variable (hs : b ≫ u = 𝟙 e)
variable (hp : fullBeadParameter F a d i = (std.map u ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ q)
variable (hr : beadMap a d i ≫ (F.collapse.app a).map ≫ Q.map = std.map u ≫ r)

include hr in
private theorem nativeValue_factors :
    prismValue (w a d i) (fullBeadParameter F a d i) =
      (std.map u ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ fst (Δ e) (J.obj (time.obj a)) ≫ r := by
  rw [fullBead_prismValue, hr, tensorHom_fst_assoc]

include hs hp hr in
/-- The section-restricted coefficient realizes to the exact descended map over
the original target at every time simplex. -/
theorem sectionCoefficient_prismValue :
    prismValue (sectionCoefficient a d i b) q = fst (Δ e) (J.obj (time.obj a)) ≫ r :=
  prismValue_section u b hs _ _ q _ hp (nativeValue_factors F a d i u r hr)

include hs hp hr in
/-- On every vertex used by the whole timed bead, the original coefficient is
the pullback of the section-restricted coefficient over the shorter simplex. -/
theorem fullBeadCoefficient_splitEpi :
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (⦋d⦌, k (L := L) a) from
      (𝟙 ⦋d⦌, fullBeadSupportInclusion F a d i)).op (w a d i) =
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (e, k (L := L) a) from
      (u, fullBeadSupportInclusion F a d i)).op (sectionCoefficient a d i b) :=
  coefficient_eq_of_prismValue_splitEpi u b hs _ _ q _ hp (nativeValue_factors F a d i u r hr)

end
end DaggerModels.PartII.JTParametrizedBeadGraph
