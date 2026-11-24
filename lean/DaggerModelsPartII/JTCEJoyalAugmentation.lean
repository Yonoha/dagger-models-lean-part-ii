import DaggerModelsPartII.JTCEAugmentation
import DaggerModelsPartII.JTParameterContraction
import DaggerModelsPartII.PushoutSectionTensor
import NativeOriginalWeakPushoutTensor
import NativeSimplicialPushoutTensorMono
import NativeJoyalFirstFactorization

/-!
# Original Joyal weakness of the literal CE augmentation

A vertex section of the actual groupoid parameter gives a weak monomorphism
`Δ[0] → J^k`. Its pushout tensor with the ordered interval boundary is the
cell attached in a second presentation of the literal CE pushout. The
original weak-monomorphism cobase theorem and the strict augmentation equation
then prove that every CE augmentation component is an original Joyal weak map.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Simplicial
  HomotopicalAlgebra DaggerModels

namespace DaggerModels.PartII.JTCEJoyalAugmentation

open JTXiEndpointCollapse JTCEAugmentation GroupoidSimplex
open DaggerNativeJoyalMappingTest

noncomputable section

private def i : boundary ⟶ interval := (SSet.boundary 1).ι

private local instance : Mono i := by
  dsimp only [i]
  infer_instance

private theorem iso_weak {X Y : SSet.{0}} (f : X ⟶ Y) [IsIso f] :
    weakCategoricalEquivalences f := by
  let e : Arrow.mk (𝟙 X) ≅ Arrow.mk f :=
    Arrow.isoMk (Iso.refl X) (asIso f) (by simp)
  exact weakCategoricalEquivalences.of_retract (Retract.ofIso e.symm)
    (weakCategoricalEquivalences.id_mem X)

private def point (k : SimplexCategory) :
    (parameter.obj k).obj (Opposite.op ⦋0⦌) :=
  SSet.yonedaEquiv (JTParameterContraction.parameterVertex k 0)

private def s (k : SimplexCategory) :
    (Δ[0] : SSet.{0}) ⟶ parameter.obj k :=
  parameterVertexMap k (point k)

private theorem s_mono (k : SimplexCategory) : Mono (s k) :=
  SSet.stdSimplex.isTerminalObj₀.mono_from (s k)

private theorem s_augmentation (k : SimplexCategory) :
    s k ≫ terminal.from (parameter.obj k) =
      terminal.from (Δ[0] : SSet.{0}) :=
  terminalIsTerminal.hom_ext _ _

private theorem s_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (s k) := by
  have haug : weakCategoricalEquivalences (terminal.from (parameter.obj k)) :=
    (DaggerNativeJoyalFirstFactorization.kan_trivial_le_candidate_trivial
      (terminal.from (parameter.obj k))
      (GroupoidSimplex.augmentation_trivialFibration k)).2
  have hcomp : weakCategoricalEquivalences
      (s k ≫ terminal.from (parameter.obj k)) := by
    rw [s_augmentation]
    haveI : IsIso (terminal.from (Δ[0] : SSet.{0})) := by
      let e := SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso
        (terminalIsTerminal : IsTerminal (⊤_ SSet.{0}))
      have he : terminal.from (Δ[0] : SSet.{0}) = e.hom :=
        terminalIsTerminal.hom_ext _ _
      rw [he]
      infer_instance
    exact iso_weak _
  exact weakCategoricalEquivalences.of_postcomp
    (s k) (terminal.from (parameter.obj k)) haug hcomp

private def t (k : SimplexCategory) : SSet.PushoutTensor i (s k) :=
  Functor.PushoutObjObj.ofHasPushout _ _ _

private theorem t_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (t k).ι := by
  letI : Mono (s k) := s_mono k
  have hflip : weakCategoricalEquivalences (t k).flip.ι :=
    DaggerNativeOriginalWeakPushoutTensor.pushout_tensor_weak
      (s k) (s_weak k) i (t k).flip
  exact weakCategoricalEquivalences.of_retract
    (Retract.ofIso (t k).flipArrowIso.symm) hflip

private theorem t_mono (k : SimplexCategory) : Mono (t k).ι := by
  letI : Mono (s k) := s_mono k
  change Mono (t k).ι
  exact DaggerNativeSimplicialPushoutTensorMono.mono_ι i (s k) (t k)

private def E : SSet.{0} := interval ⊗ (Δ[0] : SSet.{0})

private def c : boundary ⟶ E :=
  CartesianMonoidalCategory.lift i
    (SSet.stdSimplex.isTerminalObj₀.from boundary)

private def r (k : SimplexCategory) : E ⟶ interval ⊗ parameter.obj k :=
  interval ◁ s k

private theorem p_condition (k : SimplexCategory) :
    (boundary ◁ s k) ≫
      (cylinderProjection.app k ≫ c) =
        (i ▷ (Δ[0] : SSet.{0})) ≫ 𝟙 E := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · exact Subsingleton.elim _ _

private def p (k : SimplexCategory) : (t k).pt ⟶ E :=
  (t k).isPushout.flip.desc (cylinderProjection.app k ≫ c) (𝟙 E)
    (p_condition k)

private theorem c_r (k : SimplexCategory) :
    c ≫ r k = i ≫ intervalSectionInput k (point k) := by
  apply NatTrans.ext
  funext q x
  apply Prod.ext
  · rfl
  · exact congrArg ((s k).app q) (Subsingleton.elim _ _)

private theorem c_r_CE (k : SimplexCategory) :
    c ≫ r k ≫ CE_interval.app k = CE_boundary.app k := by
  rw [← Category.assoc, c_r, Category.assoc]
  exact boundary_intervalSection k (point k)

private theorem secondPushout (k : SimplexCategory) :
    IsPushout (t k).ι (p k) (CE_interval.app k)
      (r k ≫ CE_interval.app k) := by
  let hCE := (IsPushout.of_hasPushout cylinderInclusion cylinderProjection).map
    ((evaluation SimplexCategory SSet.{0}).obj k)
  have hCE' : IsPushout (cylinderInclusion.app k)
      (cylinderProjection.app k) (CE_interval.app k) (CE_boundary.app k) := hCE
  let hP := (t k).isPushout.flip
  apply PushoutSectionTensor.isPushout hCE' hP (t k).ι (p k)
    (r k) c
  · exact (t k).inr_ι
  · exact (t k).inl_ι
  · exact hP.inl_desc _ _ _
  · exact hP.inr_desc _ _ _
  · exact c_r_CE k

private theorem r_CE_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (r k ≫ CE_interval.app k) := by
  letI : Mono (t k).ι := t_mono k
  exact DaggerNativeOriginalWeakMonoPushout.weak_of_isPushout
    (secondPushout k) (t_weak k)

private theorem fst_isIso :
    IsIso (CartesianMonoidalCategory.fst interval (Δ[0] : SSet.{0})) := by
  exact (BinaryFan.isLimit_iff_isIso_fst
    SSet.stdSimplex.isTerminalObj₀
    (BinaryFan.mk
      (CartesianMonoidalCategory.fst interval (Δ[0] : SSet.{0}))
      (CartesianMonoidalCategory.snd interval (Δ[0] : SSet.{0})))).1
        ⟨CartesianMonoidalCategory.tensorProductIsBinaryProduct interval
          (Δ[0] : SSet.{0})⟩

private theorem fst_weak :
    weakCategoricalEquivalences
      (CartesianMonoidalCategory.fst interval (Δ[0] : SSet.{0})) := by
  letI : IsIso (CartesianMonoidalCategory.fst interval (Δ[0] : SSet.{0})) :=
    fst_isIso
  exact iso_weak _

private theorem r_augmentation (k : SimplexCategory) :
    r k ≫ CE_interval.app k ≫ CEAugmentation.app k =
      CartesianMonoidalCategory.fst interval (Δ[0] : SSet.{0}) := by
  rw [CEAugmentation_interval]
  change (𝟙 interval ⊗ₘ s k) ≫
    CartesianMonoidalCategory.fst interval (parameter.obj k) = _
  simpa only [Category.comp_id] using
    CartesianMonoidalCategory.tensorHom_fst (𝟙 interval) (s k)

/-- Every actual endpoint-collapsed CE augmentation component is weak in
the original ordinary Joyal model, with the literal chosen augmentation. -/
theorem CEAugmentation_weak (k : SimplexCategory) :
    weakCategoricalEquivalences (CEAugmentation.app k) := by
  have hcomp : weakCategoricalEquivalences
      ((r k ≫ CE_interval.app k) ≫ CEAugmentation.app k) := by
    rw [Category.assoc, r_augmentation]
    exact fst_weak
  exact weakCategoricalEquivalences.of_precomp
    (r k ≫ CE_interval.app k) (CEAugmentation.app k)
      (r_CE_weak k) hcomp

/-- Every actual cosimplicial structure map of CE is also original Joyal
weak, by naturality and the componentwise weak augmentation. -/
theorem CE_map_weak {k l : SimplexCategory} (f : k ⟶ l) :
    weakCategoricalEquivalences (CE.map f) := by
  have hnat : CE.map f ≫ CEAugmentation.app l = CEAugmentation.app k := by
    simpa only [Functor.const_obj_map, Category.comp_id] using
      CEAugmentation.naturality f
  have hcomp : weakCategoricalEquivalences
      (CE.map f ≫ CEAugmentation.app l) := by
    rw [hnat]
    exact CEAugmentation_weak k
  exact weakCategoricalEquivalences.of_postcomp
    (CE.map f) (CEAugmentation.app l) (CEAugmentation_weak l) hcomp

end

end DaggerModels.PartII.JTCEJoyalAugmentation
