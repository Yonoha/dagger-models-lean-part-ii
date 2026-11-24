import DaggerModelsPartII.JTNecklaceEndpointCylinder
import DaggerModelsPartII.JTNecklaceCylinderSimplexLift
import DaggerModelsPartII.GroupoidSimplex
import DaggerModelsPartII.JTNativeRowLabel
import NativeKanTrivialFibrationWalkingLifts

/-!
# A connector inside one reduced necklace-cylinder fiber

The connector is constant after passing to the original reduced cylinder.
The edge in the actual completed-simplex parameter is filled against its
trivial-fibration augmentation.  If the two parameters differ, equality in the
reduced pushout forces the horizontal vertex into the original boundary; the
entire connector then maps to the same constant boundary vertex.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory HomotopicalAlgebra DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTNecklaceCylinderConnector

open JTNecklaceEndpointCylinder

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev B := JTXiEndpointCollapse.boundary
private abbrev E := single 1

private def terminalFrom (X : SSet.{0}) : X ⟶ (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.from X

private theorem pointAt_terminal (i : Fin 2) :
    pointAt E (ULift.up i) ≫ terminalFrom E.toSSet = 𝟙 (Δ[0] : SSet.{0}) :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

/-- The pushout relation collapses an entire parameter map above a boundary map. -/
theorem boundary_collapse (T : NecklaceCode) (k : SimplexCategory)
    {X : SSet.{0}} (b : X ⟶ B) (s : X ⟶ J.obj k) :
    lift (b ≫ endpointInclusion T) s ≫ (cylinder T).app k =
      b ≫ (boundary T).app k := by
  let z : X ⟶ B ⊗ J.obj k := lift b s
  have hz : z ≫ (endpointInclusion T ⊗ₘ 𝟙 (J.obj k)) =
      lift (b ≫ endpointInclusion T) s := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [z, Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
        CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_fst_assoc]
    · simp only [z, Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
        CartesianMonoidalCategory.lift_snd, Category.comp_id]
  calc
    lift (b ≫ endpointInclusion T) s ≫ (cylinder T).app k =
        z ≫ (endpointInclusion T ⊗ₘ 𝟙 (J.obj k)) ≫ (cylinder T).app k := by
      rw [← Category.assoc, hz]
    _ = z ≫ CartesianMonoidalCategory.fst B (J.obj k) ≫ (boundary T).app k := by
      rw [(isPushout T k).w]
    _ = b ≫ (boundary T).app k := by
      rw [← Category.assoc, show z ≫ CartesianMonoidalCategory.fst B (J.obj k) = b from
        CartesianMonoidalCategory.lift_fst _ _]

/-- An arbitrary pair of parameter vertices has a native one-bead connector. -/
private theorem parameter_connector (k : SimplexCategory)
    (u v : (Δ[0] : SSet.{0}) ⟶ J.obj k) :
    ∃ s : E.toSSet ⟶ J.obj k,
      pointAt E (ULift.up 0) ≫ s = u ∧
      pointAt E (ULift.up (Fin.last E.len)) ≫ s = v := by
  haveI : Fibration (terminal.from (J.obj k)) :=
    (fibration_iff _).mpr (GroupoidSimplex.augmentation_trivialFibration k).1
  haveI : WeakEquivalence (terminal.from (J.obj k)) :=
    (weakEquivalence_iff _).mpr (GroupoidSimplex.augmentation_trivialFibration k).2
  haveI : Cofibration (SSet.boundary.{0} 1).ι :=
    (SSet.modelCategoryQuillen.cofibration_iff _).mpr inferInstance
  let sq : CommSq (SSet.boundary₁.desc (SSet.yonedaEquiv u) (SSet.yonedaEquiv v)) (SSet.boundary.{0} 1).ι
      (terminal.from (J.obj k)) (terminal.from (Δ[1] : SSet.{0})) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  let s : E.toSSet ⟶ J.obj k := (singleIso 1).hom ≫ sq.lift
  refine ⟨s, ?_, ?_⟩
  · have h := congrArg (fun f ↦ SSet.boundary₁.ι₀ ≫ f) sq.fac_left
    have hs : SSet.stdSimplex.δ 1 ≫ sq.lift = u := by
      simpa only [← Category.assoc, SSet.boundary₁.ι₀_ι,
        SSet.boundary₁.ι₀_desc, Equiv.symm_apply_apply] using h
    change pointAt E (ULift.up 0) ≫ (singleIso 1).hom ≫ sq.lift = u
    rw [← Category.assoc, JTNativeRowLabel.nativeVertex]
    rw [SSet.stdSimplex.δ_one] at hs
    exact hs
  · have h := congrArg (fun f ↦ SSet.boundary₁.ι₁ ≫ f) sq.fac_left
    have hs : SSet.stdSimplex.δ 0 ≫ sq.lift = v := by
      simpa only [← Category.assoc, SSet.boundary₁.ι₁_ι,
        SSet.boundary₁.ι₁_desc, Equiv.symm_apply_apply] using h
    change pointAt E (ULift.up (Fin.last E.len)) ≫
      (singleIso 1).hom ≫ sq.lift = v
    rw [← Category.assoc, JTNativeRowLabel.nativeVertex]
    rw [SSet.stdSimplex.δ_zero] at hs
    exact hs

/-- Equal reduced-cylinder vertices are joined by an edge whose entire image
is the common vertex, including for the zero-length necklace. -/
theorem exists_connector (T : NecklaceCode) (k : SimplexCategory)
    (a : (Δ[0] : SSet.{0}) ⟶ T.toSSet)
    (u v : (Δ[0] : SSet.{0}) ⟶ J.obj k)
    (h : lift a u ≫ (cylinder T).app k =
      lift a v ≫ (cylinder T).app k) :
    ∃ s : E.toSSet ⟶ J.obj k,
      pointAt E (ULift.up 0) ≫ s = u ∧
      pointAt E (ULift.up (Fin.last E.len)) ≫ s = v ∧
      lift (terminalFrom E.toSSet ≫ a) s ≫ (cylinder T).app k =
        terminalFrom E.toSSet ≫ (lift a u ≫ (cylinder T).app k) := by
  classical
  by_cases huv : u = v
  · subst v
    let s : E.toSSet ⟶ J.obj k := terminalFrom E.toSSet ≫ u
    refine ⟨s, ?_, ?_, ?_⟩
    · change pointAt E (ULift.up 0) ≫ terminalFrom E.toSSet ≫ u = u
      rw [← Category.assoc, pointAt_terminal, Category.id_comp]
    · change pointAt E (ULift.up (Fin.last E.len)) ≫ terminalFrom E.toSSet ≫ u = u
      rw [← Category.assoc, pointAt_terminal, Category.id_comp]
    · have hs : lift (terminalFrom E.toSSet ≫ a) s =
          terminalFrom E.toSSet ≫ lift a u := by
        apply CartesianMonoidalCategory.hom_ext
        · simp only [s, CartesianMonoidalCategory.lift_fst,
            Category.assoc]
        · simp only [s, CartesianMonoidalCategory.lift_snd,
            Category.assoc]
      rw [hs, Category.assoc]
  · let p := SSet.yonedaEquiv (lift a u)
    let p' := SSet.yonedaEquiv (lift a v)
    have hp : ((cylinder T).app k).app (op ⦋0⦌) p =
        ((cylinder T).app k).app (op ⦋0⦌) p' := by
      simpa only [p, p', SSet.yonedaEquiv_comp] using
        congrArg SSet.yonedaEquiv h
    obtain hparam | ⟨b, hb⟩ :=
      JTNecklaceCylinderSimplexLift.equal_lifts_parameter_or_boundary
        T k 0 p p' hp
    · have heq : u = v := by
        apply SSet.yonedaEquiv.injective
        have hparam' : SSet.yonedaEquiv
            (lift a u ≫ CartesianMonoidalCategory.snd T.toSSet (J.obj k)) =
            SSet.yonedaEquiv
              (lift a v ≫ CartesianMonoidalCategory.snd T.toSSet (J.obj k)) := by
          simpa only [p, p', SSet.yonedaEquiv_comp] using hparam
        simpa only [CartesianMonoidalCategory.lift_snd] using hparam'
      exact (huv heq).elim
    · let bmap : (Δ[0] : SSet.{0}) ⟶ B := SSet.yonedaEquiv.symm b
      have ha : bmap ≫ endpointInclusion T = a := by
        apply SSet.yonedaEquiv.injective
        simpa only [bmap, p, SSet.yonedaEquiv_comp,
          Equiv.apply_symm_apply, CartesianMonoidalCategory.lift_fst] using hb
      obtain ⟨s, hs0, hs1⟩ := parameter_connector k u v
      refine ⟨s, hs0, hs1, ?_⟩
      calc
        lift (terminalFrom E.toSSet ≫ a) s ≫ (cylinder T).app k =
            lift ((terminalFrom E.toSSet ≫ bmap) ≫ endpointInclusion T) s ≫
              (cylinder T).app k := by
          rw [Category.assoc, ha]
        _ = (terminalFrom E.toSSet ≫ bmap) ≫ (boundary T).app k :=
          boundary_collapse T k (terminalFrom E.toSSet ≫ bmap) s
        _ = terminalFrom E.toSSet ≫ (bmap ≫ (boundary T).app k) :=
          Category.assoc _ _ _
        _ = terminalFrom E.toSSet ≫ (lift a u ≫ (cylinder T).app k) := by
          rw [← ha, boundary_collapse T k bmap u]

end

end DaggerModels.PartII.JTNecklaceCylinderConnector
