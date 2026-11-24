import DaggerModelsPartII.JTActualBeadCoefficientDescent
import DaggerModelsPartII.JTJointClippedParameters
import DaggerModelsPartII.JTNativeSimplexImage
import DaggerModelsPartII.JTPrismMixedCoefficient

/-! Compare the original bead coefficient with the coefficient on the actual clipped wedge. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTJointClippedBeadCoefficients

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open JTJointRelativeParameters (withTime withTimeMap_app)
open JTJointRelativeGraphFamily (native originalParameter coefficient)
open JTJointIntervalQuotient (joint)
open JTJointClippedGluing (nativeGlued simplicialComparison)
open JTJointClippedParameters (TraceFactors descendToNative actualParameter_pullback)
open JTParametrizedBeadGraph (fullBeadParameter fullBeadSupport fullBeadSupportInclusion
  sectionCoefficient sectionCoefficient_prismValue fullBeadCoefficient_splitEpi)
open JTTargetJointMarks (Joint)
open JTPrismRectangle (prismValue)

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
variable (F : Family Q L time) (j : Joint Q.code) (a : A)

private abbrev k := (coefficient (L := L)).obj a
private abbrev P := (native F).obj a

/-- The actual clipped native object over the original target. -/
abbrev clipped := (nativeGlued Q.code j).obj (P F a)

variable (trace : withTime Q.map J time (native F) (joint Q.code j) ⟶
  coefficient (L := L) ⋙ J)
variable (h : TraceFactors Q.code j Q.map J time (native F)
  (coefficient (L := L)) (originalParameter F) trace)

private abbrev descended :=
  (descendToNative Q.code j Q.map J time (native F)
    (coefficient (L := L)) (originalParameter F) trace h).app a

private abbrev compare := ((simplicialComparison Q.code j).app (P F a)).left

/-- The whole parameter on a simplex of the clipped wedge, at its original time. -/
def parameter {e : SimplexCategory} (v : Δ e ⟶ (clipped F j a).left.toSSet) :
    Δ e ⊗ J.obj (time.obj a) ⟶ J.obj (k (L := L) a) :=
  (v ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ descended F j a trace h

variable (d : ℕ) (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)

private abbrev xmap := (NecklaceCode.singleIso d).inv ≫ i

/-- The actual image of the original horizontal simplex in the clipped wedge. -/
def simplexImage : Δ ⦋d⦌ ⟶ (clipped F j a).left.toSSet :=
  xmap a d i ≫ compare F j a

variable {e : SimplexCategory} (u : ⦋d⦌ ⟶ e)
variable (v : Δ e ⟶ (clipped F j a).left.toSSet)
variable (hv : std.map u ≫ v = simplexImage F j a d i)

set_option maxHeartbeats 1400000 in
include hv in
/-- Any exact factorization of the actual image also factors the full original parameter. -/
theorem parameter_pullback :
    fullBeadParameter F a d i =
      (std.map u ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ parameter F j a trace h v := by
  have he := NatTrans.congr_app (actualParameter_pullback F j trace h) a
  simp only [NatTrans.comp_app, withTimeMap_app] at he
  let K := J.obj (time.obj a)
  let s := descended F j a trace h
  have he' : (compare F j a ⊗ₘ 𝟙 K) ≫ s = F.parameter a := by
    simpa only [JTJointRelativeGraphFamily.originalParameter] using he
  calc
    _ = (xmap a d i ⊗ₘ 𝟙 K) ≫ ((compare F j a ⊗ₘ 𝟙 K) ≫ s) :=
      congrArg ((xmap a d i ⊗ₘ 𝟙 K) ≫ ·) he'.symm
    _ = (simplexImage F j a d i ⊗ₘ 𝟙 K) ≫ s := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      rfl
    _ = _ := by
      change (simplexImage F j a d i ⊗ₘ 𝟙 K) ≫ s =
        (std.map u ⊗ₘ 𝟙 K) ≫ (v ⊗ₘ 𝟙 K) ≫ s
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hv]

private abbrev rawOn (v : Δ e ⟶ (clipped F j a).left.toSSet) :=
  v ≫ (clipped F j a).hom.map ≫ Q.map

include hv in
private theorem raw_pullback :
    xmap a d i ≫ (F.collapse.app a).map ≫ Q.map = std.map u ≫ rawOn F j a v := by
  have hw := Over.w ((simplicialComparison Q.code j).app (P F a))
  change compare F j a ≫ (clipped F j a).hom.map = (F.collapse.app a).map at hw
  unfold rawOn
  rw [← Category.assoc, ← Category.assoc, hv, simplexImage]
  simp only [Category.assoc]
  rw [← Category.assoc (compare F j a) ((clipped F j a).hom.map) Q.map, hw]

variable (b : e ⟶ ⦋d⦌) (hs : b ≫ u = 𝟙 e)

include hv hs in
/-- The descended coefficient evaluates to the literal map from the clipped chart. -/
theorem coefficient_realizes :
    prismValue (sectionCoefficient a d i b) (parameter F j a trace h v) =
      fst (Δ e) (J.obj (time.obj a)) ≫ rawOn F j a v :=
  sectionCoefficient_prismValue F a d i u b _ _ hs
    (parameter_pullback F j a trace h d i u v hv) (raw_pullback F j a d i u v hv)

include hv hs h in
/-- The original coefficient on every used vertex is pulled back from the exact
section coefficient for the clipped chart. -/
theorem coefficient_pullback :
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (⦋d⦌, k (L := L) a) from
      (𝟙 ⦋d⦌, fullBeadSupportInclusion F a d i)).op
      (SSet.yonedaEquiv (X := row W ⦋d⦌)
        (JTParametrizedBeadGraph.coefficient (a := a) d i)) =
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (e, k (L := L) a) from
      (u, fullBeadSupportInclusion F a d i)).op (sectionCoefficient a d i b) :=
  fullBeadCoefficient_splitEpi F a d i u b _ _ hs
    (parameter_pullback F j a trace h d i u v hv) (raw_pullback F j a d i u v hv)


/-- Every original simplex has a split ordinal image face in the actual clipped wedge. -/
def imageFactor :=
  JTNativeSimplexImage.factor (clipped F j a).left d (simplexImage F j a d i)

/-- The image face of an arbitrary original simplex has the exact original
native value on the whole prism after its horizontal degeneracy. -/
theorem imageCoefficient_realizes :
    let B := imageFactor F j a d i
    prismValue (sectionCoefficient a d i B.select) (parameter F j a trace h B.face) =
      fst (Δ B.middle) (J.obj (time.obj a)) ≫ rawOn F j a B.face := by
  let B := imageFactor F j a d i
  exact coefficient_realizes F j a trace h d i B.epi B.face B.factor B.select B.select_epi

include h in
/-- The coefficient of every original timed simplex agrees on its used
vertices with the pullback of the coefficient on its actual image face. -/
theorem imageCoefficient_pullback :
    let B := imageFactor F j a d i
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (⦋d⦌, k (L := L) a) from
      (𝟙 ⦋d⦌, fullBeadSupportInclusion F a d i)).op
      (SSet.yonedaEquiv (X := row W ⦋d⦌)
        (JTParametrizedBeadGraph.coefficient (a := a) d i)) =
    (Input W).map (show (⦋d⦌, fullBeadSupport F a d i) ⟶ (B.middle, k (L := L) a) from
      (B.epi, fullBeadSupportInclusion F a d i)).op (sectionCoefficient a d i B.select) := by
  let B := imageFactor F j a d i
  exact coefficient_pullback F j a trace h d i B.epi B.face B.factor B.select B.select_epi

section Transport

open JTPrismRectangle (usedCoefficient usedCoefficient_mixed sample)
open JTRowGraphParameterSupport (supportOrdinal)

variable {a}
variable {a' : A} (f : a ⟶ a')

private abbrev clippedMap :=
  (((native F ⋙ nativeGlued Q.code j).map f).left).map

variable {d' : ℕ}
variable (i' : (NecklaceCode.single d').toSSet ⟶ ((codes L).obj a').toSSet)

private abbrev oldFace := (imageFactor F j a d i).face
private abbrev newFace := (imageFactor F j a' d' i').face

variable (σ : (imageFactor F j a d i).middle ⟶ (imageFactor F j a' d' i').middle)
variable (hσ : oldFace F j d i ≫ clippedMap F j f = std.map σ ≫ newFace F j i')

set_option maxHeartbeats 1000000 in
include hσ in
/-- A horizontal arrow of actual image faces preserves the entire descended time parameter. -/
theorem imageParameter_mixed :
    (std.map σ ⊗ₘ J.map (time.map f)) ≫ parameter F j a' trace h (newFace F j i') =
      parameter F j a trace h (oldFace F j d i) ≫ J.map ((coefficient (L := L)).map f) := by
  let D := native F ⋙ (nativeGlued Q.code j ⋙ Over.post NecklaceCode.simplicialFunctor)
  let p := descendToNative Q.code j Q.map J time (native F)
    (coefficient (L := L)) (originalParameter F) trace h
  have hn := p.naturality f
  change ((JTDecoratedIntervalDiagram.parameterize Q.map J time D).map f).left ≫ p.app a' =
    p.app a ≫ J.map ((coefficient (L := L)).map f) at hn
  rw [JTDecoratedIntervalDiagram.parameterize_map_left] at hn
  change (clippedMap F j f ⊗ₘ J.map (time.map f)) ≫ p.app a' =
    p.app a ≫ J.map ((coefficient (L := L)).map f) at hn
  let v := oldFace F j d i
  let v' := newFace F j i'
  have hSquare : (std.map σ ⊗ₘ J.map (time.map f)) ≫
      (v' ⊗ₘ 𝟙 (J.obj (time.obj a'))) =
      (v ⊗ₘ 𝟙 (J.obj (time.obj a))) ≫ (clippedMap F j f ⊗ₘ J.map (time.map f)) := by
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    exact congrArg (fun g ↦ g ⊗ₘ J.map (time.map f)) hσ.symm
  change (std.map σ ⊗ₘ J.map (time.map f)) ≫ (v' ⊗ₘ 𝟙 _) ≫ p.app a' =
    ((v ⊗ₘ 𝟙 _) ≫ p.app a) ≫ J.map ((coefficient (L := L)).map f)
  rw [← Category.assoc, hSquare, Category.assoc, hn, Category.assoc]
  rfl

include hσ in
private theorem imageRaw_mixed :
    fst (Δ (imageFactor F j a d i).middle) (J.obj (time.obj a)) ≫
        rawOn F j a (oldFace F j d i) =
      (std.map σ ⊗ₘ J.map (time.map f)) ≫
        fst (Δ (imageFactor F j a' d' i').middle) (J.obj (time.obj a')) ≫
          rawOn F j a' (newFace F j i') := by
  have hw := congrArg NecklaceCode.Hom.map (Over.w ((native F ⋙ nativeGlued Q.code j).map f))
  change clippedMap F j f ≫ (clipped F j a').hom.map = (clipped F j a).hom.map at hw
  unfold rawOn
  rw [tensorHom_fst_assoc]
  have he : oldFace F j d i ≫ (clipped F j a).hom.map =
      std.map σ ≫ newFace F j i' ≫ (clipped F j a').hom.map := by
    rw [← Category.assoc, ← hσ, Category.assoc, hw]
  simpa only [Category.assoc] using
    (congrArg (fun r ↦ fst (Δ (imageFactor F j a d i).middle) (J.obj (time.obj a)) ≫
      r ≫ Q.map) he)

private abbrev sourceImageParam := parameter F j a trace h (oldFace F j d i)
private abbrev targetImageParam := parameter F j a' trace h (newFace F j i')

set_option maxHeartbeats 1200000 in
include hσ in
/-- The selected image coefficients commute with every compatible original
operator after restricting to the full used coefficient supports. -/
theorem imageCoefficient_mixed :
    let B := imageFactor F j a d i
    let B' := imageFactor F j a' d' i'
    let p := sourceImageParam F j trace h d i
    let q := targetImageParam F j trace h i'
    let c := JTPrismRectangle.supportMap p q (std.map σ ⊗ₘ J.map (time.map f))
      ((coefficient (L := L)).map f) (imageParameter_mixed F j trace h d i f i' σ hσ)
    usedCoefficient (sectionCoefficient a d i B.select) p =
      (Input W).map (show
        (B.middle, supportOrdinal (sample B.middle (time.obj a) ≫ p)) ⟶
          (B'.middle, supportOrdinal (sample B'.middle (time.obj a') ≫ q))
        from (σ, c)).op (usedCoefficient (sectionCoefficient a' d' i' B'.select) q) := by
  dsimp only
  apply usedCoefficient_mixed
  rw [imageCoefficient_realizes F j a trace h d i, imageCoefficient_realizes F j a' trace h d' i']
  exact imageRaw_mixed F j d i f i' σ hσ

variable (ρ : ⦋d⦌ ⟶ ⦋d'⦌)
variable (hρ : xmap a d i ≫ ((codes L).map f).map = std.map ρ ≫ xmap a' d' i')

/-- The induced horizontal operator on the actual image faces. -/
def imageOperator :
    (imageFactor F j a d i).middle ⟶ (imageFactor F j a' d' i').middle :=
  JTNativeSimplexImage.faceOperator (simplexImage F j a d i)
    (simplexImage F j a' d' i') ρ

include hρ in
private theorem simplexImage_natural :
    simplexImage F j a d i ≫ clippedMap F j f =
      std.map ρ ≫ simplexImage F j a' d' i' := by
  have h := (simplicialComparison Q.code j).naturality ((native F).map f)
  have hn := congrArg (fun g ↦ g.left) h
  change ((codes L).map f).map ≫ compare F j a' = compare F j a ≫ clippedMap F j f at hn
  unfold simplexImage
  rw [Category.assoc, ← hn, ← Category.assoc, hρ, Category.assoc]

include hρ in
/-- The image-face operator preserves the original clipped map on the whole simplex. -/
theorem imageOperator_square :
    oldFace F j d i ≫ clippedMap F j f =
      std.map (imageOperator F j d i (a' := a') (d' := d') i' ρ) ≫ newFace F j i' :=
  (JTNativeSimplexImage.faceOperator_square (simplexImage F j a d i)
    (simplexImage F j a' d' i') (clippedMap F j f) ρ
    (simplexImage_natural F j d i f i' ρ hρ)).symm

include hρ in
/-- The chosen operator on image faces commutes with the original ordinal degeneracies. -/
theorem imageOperator_fac :
    (imageFactor F j a d i).epi ≫ imageOperator F j d i (a' := a') (d' := d') i' ρ =
      ρ ≫ (imageFactor F j a' d' i').epi :=
  JTNativeSimplexImage.faceOperator_fac (simplexImage F j a d i)
    (simplexImage F j a' d' i') (clippedMap F j f) ρ
    (simplexImage_natural F j d i f i' ρ hρ)


set_option maxHeartbeats 1200000 in
include hρ in
/-- Every original compatible simplex operator induces a coefficient operator on the
actual image faces, preserving the coefficients on their full used supports. -/
theorem imageCoefficient_original_mixed :
    let B := imageFactor F j a d i
    let B' := imageFactor F j a' d' i'
    let p := sourceImageParam F j trace h d i
    let q := targetImageParam F j trace h i'
    let u := imageOperator F j d i (a' := a') (d' := d') i' ρ
    let c := JTPrismRectangle.supportMap p q (std.map u ⊗ₘ J.map (time.map f))
      ((coefficient (L := L)).map f) (imageParameter_mixed F j trace h d i f i' u
        (imageOperator_square F j d i f i' ρ hρ))
    usedCoefficient (sectionCoefficient a d i B.select) p =
      (Input W).map (show
        (B.middle, supportOrdinal (sample B.middle (time.obj a) ≫ p)) ⟶
          (B'.middle, supportOrdinal (sample B'.middle (time.obj a') ≫ q))
        from (u, c)).op (usedCoefficient (sectionCoefficient a' d' i' B'.select) q) :=
  imageCoefficient_mixed F j trace h d i f i'
    (imageOperator F j d i (a' := a') (d' := d') i' ρ)
    (imageOperator_square F j d i f i' ρ hρ)

end Transport

end
end DaggerModels.PartII.JTJointClippedBeadCoefficients
