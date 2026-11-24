import DaggerModelsPartII.JTBinaryPrismTargetLift
import DaggerModelsPartII.JTInterpolatedCylinderSource
import DaggerModelsPartII.JTInterpolatedCylinderOutput
import DaggerModelsPartII.JTInterpolatedCylinderReindex
import DaggerModelsPartII.JTParameterBlockOperators

/-! Native side operators on actual binary comparisons and their full joint overlaps. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTBinaryPrismSideTransport

open JTProjectiveOrderedFiberComparison (row)
open JTBinaryPrismParameter (sideMap sideMap_left sideMap_middle sideMap_right
  parameter parameter_mapSides)
open JTBinaryPrismRealization (collapse collapse_left_map collapse_middle_map collapse_right_map)
open JTBinaryPrismOverlap (joint)
open JTTargetIntervalPullback (sourceMap sourceMap_fac)
open JTTargetIntervalGluing (middleInclusion)
open JTNecklaceEndpointCylinder

noncomputable section

private abbrev A := single 1
private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {L R L' R' : NecklaceCode}
variable (f : L ⟶ L') (g : R ⟶ R')
variable {W : Source} {x z y : Vertex W}
variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}
variable {c : L ⟶ P.code} {c' : L' ⟶ P.code} {e : R ⟶ Q.code} {e' : R' ⟶ Q.code}

/-- The joined operator is strictly over the original wedge whenever the
two side operators are over the corresponding original native targets. -/
theorem collapse_sideMap (hf : f ≫ c' = c) (hg : g ≫ e' = e) :
    sideMap f g ≫ collapse c' e' = collapse c e := by
  apply NecklaceCode.Hom.ext
  apply tripleRight_hom_ext
  · change tripleRightT L A R ≫ (sideMap f g).map ≫ (collapse c' e').map =
      tripleRightT L A R ≫ (collapse c e).map
    rw [← Category.assoc, sideMap_left, Category.assoc, collapse_left_map,
      collapse_left_map, ← Category.assoc]
    exact congrArg (fun h : L ⟶ P.code ↦ h.map ≫ wedgeιLeft P.code Q.code) hf
  · change tripleRightU L A R ≫ (sideMap f g).map ≫ (collapse c' e').map =
      tripleRightU L A R ≫ (collapse c e).map
    rw [← Category.assoc, sideMap_middle, collapse_middle_map, collapse_middle_map]
  · change tripleRightV L A R ≫ (sideMap f g).map ≫ (collapse c' e').map =
      tripleRightV L A R ≫ (collapse c e).map
    rw [← Category.assoc, sideMap_right, Category.assoc, collapse_right_map,
      collapse_right_map, ← Category.assoc]
    exact congrArg (fun h : R ⟶ Q.code ↦ h.map ≫ wedgeιRight P.code Q.code) hg

variable (K : SimplexCategory) (I : SSet.{0})
variable (u : L'.toSSet ⊗ I ⟶ J.obj K) (v : R'.toSSet ⊗ I ⟶ J.obj K)

/-- In the actual pullback over the original joint, the full parameter
commutes with the operator induced by the two original side arrows. -/
theorem parameter_overlap_mapSides (hf : f ≫ c' = c) (hg : g ≫ e' = e) :
    (sourceMap (collapse c e) (joint P.code Q.code) (joint P.code Q.code) le_rfl
      (sideMap f g) (collapse_sideMap f g hf hg) ⊗ₘ 𝟙 I) ≫
        (middleInclusion (collapse c' e') (joint P.code Q.code) ⊗ₘ 𝟙 I) ≫
          parameter L' R' K I u v =
      (middleInclusion (collapse c e) (joint P.code Q.code) ⊗ₘ 𝟙 I) ≫
        parameter L R K I (((f.map ⊗ₘ 𝟙 I) ≫ u)) (((g.map ⊗ₘ 𝟙 I) ≫ v)) := by
  calc
    _ = ((middleInclusion (collapse c e) (joint P.code Q.code) ≫ (sideMap f g).map) ⊗ₘ 𝟙 I) ≫
        parameter L' R' K I u v := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, sourceMap_fac]
    _ = (middleInclusion (collapse c e) (joint P.code Q.code) ⊗ₘ 𝟙 I) ≫
        ((sideMap f g).map ⊗ₘ 𝟙 I) ≫ parameter L' R' K I u v := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
    _ = _ := by rw [parameter_mapSides]


open JTInterpolatedReducedCylinder (cylinderMap)
open JTInterpolatedCylinderSource (cylinderMap_source)
open JTInterpolatedCylinderOutput (cylinderMap_output)
open JTInterpolatedCylinderReindex (cylinderMap_reindex)

/-- The two definitions of the reduced binary comparison agree on both
legs of its actual boundary-collapse pushout. -/
theorem binaryCylinder_eq_interpolated {T U : NecklaceCode} {k l n : SimplexCategory}
    (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l) :
    JTBinaryPrismTargetLift.cylinderMap s t =
      cylinderMap (JTOrderedLabelBinaryGlue.code T U) (JTBinaryPrismTargetLift.parameter s t) := by
  apply (isPushout (JTOrderedLabelBinaryGlue.code T U) n).hom_ext
  · rw [JTBinaryPrismTargetLift.cylinderMap_cylinder, JTInterpolatedReducedCylinder.cylinderMap_cylinder]
    rfl
  · rw [JTBinaryPrismTargetLift.cylinderMap_boundary,
      JTInterpolatedReducedCylinder.cylinderMap_boundary]

/-- The actual reduced graph comparison commutes with simultaneous native,
time and output operators whenever their full groupoid parameters agree. -/
theorem mixedCylinderSquare {S T : NecklaceCode} (h : S ⟶ T)
    {k k' n n' : SimplexCategory} (b : k ⟶ k') (j : n ⟶ n')
    (p : S.toSSet ⊗ J.obj n ⟶ J.obj k) (p' : T.toSSet ⊗ J.obj n' ⟶ J.obj k')
    (hp : (h.map ⊗ₘ J.map j) ≫ p' = p ≫ J.map b) :
    cylinderMap S p ≫ (nativeMap h k ≫ (value T).map b) =
      (nativeMap h n ≫ (value T).map j) ≫ cylinderMap T p' := by
  have hp' : (h.map ⊗ₘ 𝟙 (J.obj n)) ≫ ((𝟙 T.toSSet ⊗ₘ J.map j) ≫ p') =
      p ≫ J.map b := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp, hp]
  calc
    _ = (cylinderMap S p ≫ (value S).map b) ≫ nativeMap h k' := by
      simp only [Category.assoc, nativeMap_parameter_natural]
    _ = _ := by
      rw [cylinderMap_output]
      symm
      rw [Category.assoc, cylinderMap_reindex, ← cylinderMap_source, hp']


section MixedParameters

open JTOrderedLabelBinaryGlue (code)
open JTParameterBlocks (common leftIn rightIn)

variable {k l k' l' n n' : SimplexCategory}
variable {s : L.toSSet ⊗ J.obj n ⟶ J.obj k} {t : R.toSSet ⊗ J.obj n ⟶ J.obj l}
variable {s' : L'.toSSet ⊗ J.obj n' ⟶ J.obj k'} {t' : R'.toSSet ⊗ J.obj n' ⟶ J.obj l'}
variable (j : n ⟶ n')


variable (α : k ⟶ k') (β : l ⟶ l')

/-- Compatibility of the two whole side parameters supplies the mixed
parameter equation for the joined comparison. -/
theorem mixedParameterSquare
    (hl : (f.map ⊗ₘ J.map j) ≫ s' = s ≫ J.map α)
    (hr : (g.map ⊗ₘ J.map j) ≫ t' = t ≫ J.map β) :
    ((sideMap f g).map ⊗ₘ J.map j) ≫ JTBinaryPrismTargetLift.parameter s' t' =
      JTBinaryPrismTargetLift.parameter s t ≫ J.map (JTParameterBlockOperators.map α β) := by
  let αβ := JTParameterBlockOperators.map α β
  have hl' : (f.map ⊗ₘ 𝟙 (J.obj n)) ≫ (𝟙 L'.toSSet ⊗ₘ J.map j) ≫
        (s' ≫ J.map (leftIn k' l')) =
      (s ≫ J.map (leftIn k l)) ≫ J.map αβ := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      ← Category.assoc, hl]
    simp only [Category.assoc, ← J.map_comp, αβ, JTParameterBlockOperators.leftIn_map]
  have hr' : (g.map ⊗ₘ 𝟙 (J.obj n)) ≫ (𝟙 R'.toSSet ⊗ₘ J.map j) ≫
        (t' ≫ J.map (rightIn k' l')) =
      (t ≫ J.map (rightIn k l)) ≫ J.map αβ := by
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      ← Category.assoc, hr]
    simp only [Category.assoc, ← J.map_comp, αβ, JTParameterBlockOperators.rightIn_map]
  unfold JTBinaryPrismTargetLift.parameter
  calc
    _ = ((sideMap f g).map ⊗ₘ 𝟙 (J.obj n)) ≫
        (𝟙 (code L' R').toSSet ⊗ₘ J.map j) ≫
          parameter L' R' (common k' l') (J.obj n')
            (s' ≫ J.map (leftIn k' l')) (t' ≫ J.map (rightIn k' l')) := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    _ = _ := by
      rw [JTBinaryPrismParameter.parameter_mapTime, parameter_mapSides]
      change parameter L R (common k' l') (J.obj n)
        ((f.map ⊗ₘ 𝟙 (J.obj n)) ≫ (𝟙 L'.toSSet ⊗ₘ J.map j) ≫ s' ≫ J.map (leftIn k' l'))
        ((g.map ⊗ₘ 𝟙 (J.obj n)) ≫ (𝟙 R'.toSSet ⊗ₘ J.map j) ≫ t' ≫ J.map (rightIn k' l')) = _
      rw [hl', hr']
      exact (JTBinaryPrismParameter.parameter_postcomp L R (common k l) (J.obj n)
        (s ≫ J.map (leftIn k l)) (t ≫ J.map (rightIn k l)) αβ).symm

end MixedParameters

end

end DaggerModels.PartII.JTBinaryPrismSideTransport
