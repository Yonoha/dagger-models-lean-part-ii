import DaggerModelsPartII.JTParametrizedBeadGraphHorizontal

/-! Mixed graph operators with a simplicial time map on each bead. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTParametrizedBeadGraph

open JTParametrizedTargetFamilies (Family codes)
open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev J := GroupoidSimplex.parameter
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

private theorem pasteParameters {X X' S S' T T' K K' : SSet.{0}}
    (D : X ⟶ X') (i : X' ⟶ S) (s : X' ⟶ T) (g : S ⟶ S') (v : T ⟶ T')
    (E : X ⟶ S' ⊗ T') (p : S ⊗ T ⟶ K) (q : S' ⊗ T' ⟶ K') (c : K ⟶ K')
    (hi : D ≫ i ≫ g = E ≫ fst S' T') (hs : D ≫ s ≫ v = E ≫ snd S' T')
    (h : (g ⊗ₘ v) ≫ q = p ≫ c) :
    D ≫ (lift i s ≫ p) ≫ c = E ≫ q := by
  have he : D ≫ lift i s ≫ (g ⊗ₘ v) = E := by
    apply CartesianMonoidalCategory.hom_ext
    · simpa only [Category.assoc, tensorHom_fst, lift_fst_assoc] using hi
    · simpa only [Category.assoc, tensorHom_snd, lift_snd_assoc] using hs
  rw [Category.assoc, ← h, ← Category.assoc D, ← Category.assoc, Category.assoc D, he]

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (R W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) {a b : A} (f : a ⟶ b) {d e : ℕ}
variable (i : (NecklaceCode.single d).toSSet ⟶ ((codes L).obj a).toSSet)
variable (j : (NecklaceCode.single e).toSSet ⟶ ((codes L).obj b).toSSet)
variable (s : (NecklaceCode.single d).toSSet ⟶ J.obj (time.obj a))
variable (t : (NecklaceCode.single e).toSSet ⟶ J.obj (time.obj b))
variable (u : ⦋d⦌ ⟶ ⦋e⦌)
variable (hi : (NecklaceCode.singleIso d).inv ≫ i ≫ ((codes L).map f).map =
  SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ j)
variable (ht : (NecklaceCode.singleIso d).inv ≫ s ≫ J.map (time.map f) =
  SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ t)

private abbrev operator := ((OrderedLabelElements.projection W (boundaryPoint W x y)).map
  (L.map f)).2

include hi ht in
/-- The graph parameters commute over a mixed source operator, with all time
coordinates retained on the bead. -/
theorem beadParameterWithTime_mixed :
    ((NecklaceCode.singleIso d).inv ≫ beadParameterWithTime F a d i s) ≫ J.map (operator (L := L) f) =
      SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ beadParameterWithTime F b e j t := by
  let D := (NecklaceCode.singleIso d).inv
  let E := SSet.stdSimplex.map u ≫ (NecklaceCode.singleIso e).inv ≫ lift j t
  let c := J.map (operator (L := L) f)
  let g := ((codes L).map f).map
  let v := J.map (time.map f)
  have h₁ : D ≫ i ≫ g = E ≫ fst _ _ := by
    simp only [E, Category.assoc, lift_fst]
    exact hi
  have h₂ : D ≫ s ≫ v = E ≫ snd _ _ := by
    simp only [E, Category.assoc, lift_snd]
    exact ht
  have h₃ := pasteParameters D i s g v E (F.parameter a) (F.parameter b) c h₁ h₂
    (F.parameter_map f)
  exact h₃.trans (by simp only [E, Category.assoc]; rfl)

include hi in
private theorem mixedCoefficient :
    SSet.stdSimplex.map (operator (L := L) f) ≫
      coefficient (a := b) e j ≫
        (JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)).map u.op =
    coefficient (a := a) d i := by
  rw [← coefficient_horizontal b (i ≫ ((codes L).map f).map) j u hi]
  exact coefficient_map f d i

/-- An actual mixed graph arrow with the unchanged original coefficient operator. -/
def mixedFiberGraphArrowWithTime :
    (fiberGraphWithTime F a d i s).obj ⟶ JTRowGraphResolution.restrictGraph u
      (fiberGraphWithTime F b e j t).obj where
  operator := operator (L := L) f
  coefficient := by
    have h := congrArg SSet.yonedaEquiv (mixedCoefficient f i j u hi)
    rw [SSet.yonedaEquiv_map_comp, SSet.yonedaEquiv_comp] at h
    exact h
  parameter := beadParameterWithTime_mixed F f i j s t u hi ht

end

end DaggerModels.PartII.JTParametrizedBeadGraph
