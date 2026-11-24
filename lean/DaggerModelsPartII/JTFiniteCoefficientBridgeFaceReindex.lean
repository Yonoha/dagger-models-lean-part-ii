import DaggerModelsPartII.JTFiniteCoefficientBridgeRelativeVertex
import DaggerModelsPartII.JTFiniteCoefficientBridgeTimeFaceRange
import DaggerModelsPartII.JTChangingCoefficientBridgeLift

/-!
# The prescribed face maps on the original smaller bridge parameters
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory CartesianMonoidalCategory

universe v

namespace DaggerModels.PartII.JTFiniteCoefficientBridgeFaceReindex

open JTFiniteCoefficientBridgeOrder (base bridge mapCopies_base)
open JTFiniteCoefficientBridgeTime (time)
open JTFiniteCoefficientBridgePrism (prism vertical verticalSection_prism)
open JTFiniteCoefficientBridgeSubcollection (coefficientOperator_mono timeOperator_mono)
open JTFiniteCoefficientBridgeReindex (prism_mapCopies)
open JTFiniteCoefficientBridgeCopyFace
open JTFiniteCoefficientBridgeFaceCover (facePrism)
open SSet.Subcomplex

noncomputable section

private abbrev simplex (n : SimplexCategory) := SSet.stdSimplex.{v}.obj n
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

variable {m : ℕ} {k b' : SimplexCategory} {b : Fin (m + 1) → SimplexCategory}
variable (c : ∀ e, k ⟶ b e) (u : k ⟶ b') (n : SimplexCategory)
variable (S : Finset (Fin (m + 1))) (hS : S.Nonempty)

abbrev smallTimeOperator :=
  JTFiniteCoefficientBridgeSubcollection.timeOperator n (copyInclusion S hS)
    (JTHigherInterleavedParameter.timeInclusion_injective S hS)

/-- Realize the chosen coefficient face by the original smaller bridge. -/
def coefficientIso :
    simplex.{v} (bridge k n (smallDegree S).len) ≅ (copyFace.{v} c u n S).toSSet := by
  let j := smallOperator c u n S hS
  haveI : Mono j := coefficientOperator_mono _ _ _ _ _ _ _
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{v} j
  exact asIso (toRange (SSet.stdSimplex.{v}.map j)) ≪≫
    SSet.Subcomplex.eqToIso (copyFace_eq_subcollectionRange c u n S hS).symm

@[reassoc]
theorem coefficientIso_ι :
    (coefficientIso.{v} c u n S hS).hom ≫ (copyFace c u n S).ι =
      SSet.stdSimplex.map (smallOperator c u n S hS) := by
  simp [coefficientIso, Category.assoc]

/-- Realize the chosen time face by the original smaller joining time. -/
def timeIso :
    simplex.{v} (time (smallDegree S).len n) ≅ (timeFace.{v} n S).toSSet := by
  let j := smallTimeOperator n S hS
  haveI : Mono j := timeOperator_mono _ _ _
  haveI := JTHigherInterleavedParameter.stdSimplex_map_mono_of_mono.{v} j
  exact asIso (toRange (SSet.stdSimplex.{v}.map j)) ≪≫
    SSet.Subcomplex.eqToIso (timeFace_eq_range n S hS).symm

@[reassoc]
theorem timeIso_ι :
    (timeIso.{v} n S hS).hom ≫ (timeFace n S).ι =
      SSet.stdSimplex.map (smallTimeOperator n S hS) := by
  simp [timeIso, Category.assoc]

/-- The restriction to a subcollection is the full prism on its original parameter. -/
theorem facePrism_compare :
    (simplex.{v} k ◁ (timeIso.{v} n S hS).hom) ≫ facePrism c u n S =
      prism (smallCoefficients c S hS) u n ≫ (coefficientIso c u n S hS).hom := by
  rw [← cancel_mono (copyFace.{v} c u n S).ι]
  simp only [facePrism, Category.assoc, fromPreimage_ι, coefficientIso_ι,
    JTPrismTimeFaceExtension.preimageIso_ι_assoc]
  rw [← Category.assoc (simplex.{v} k ◁ (timeIso.{v} n S hS).hom),
    ← whiskerLeft_comp, timeIso_ι]
  exact (prism_mapCopies (smallCoefficients c S hS) c u n (copyInclusion S hS)
    (JTHigherInterleavedParameter.timeInclusion_injective S hS)
    (smallCoefficient_agrees c n S hS)).symm

theorem smallOperator_base :
    smallOperator c u n S hS ≫ base c u n = base (smallCoefficients c S hS) u n :=
  mapCopies_base _ _ _ _ _ _ _

/-- Regard a map on the original smaller parameter as a map on the face. -/
def faceMap {X : SSet.{v}} (E : simplex (bridge k n (smallDegree S).len) ⟶ X) :
    (copyFace.{v} c u n S).toSSet ⟶ X :=
  (coefficientIso c u n S hS).inv ≫ E

@[reassoc]
theorem coefficientIso_faceMap {X : SSet.{v}}
    (E : simplex (bridge k n (smallDegree S).len) ⟶ X) :
    (coefficientIso.{v} c u n S hS).hom ≫ faceMap c u n S hS E = E := by
  simp [faceMap]

theorem faceMap_base {X Y : SSet.{v}} {p : X ⟶ Y}
    (g : simplex b' ⟶ Y) (E : simplex (bridge k n (smallDegree S).len) ⟶ X)
    (h : E ≫ p = SSet.stdSimplex.map (base (smallCoefficients c S hS) u n) ≫ g) :
    faceMap c u n S hS E ≫ p = (copyFace c u n S).ι ≫ SSet.stdSimplex.map (base c u n) ≫ g := by
  apply (cancel_epi (coefficientIso.{v} c u n S hS).hom).1
  rw [coefficientIso_faceMap_assoc, coefficientIso_ι_assoc, ← Category.assoc
    (SSet.stdSimplex.map (smallOperator c u n S hS)), ← SSet.stdSimplex.map_comp,
    smallOperator_base]
  exact h

theorem faceMap_stationary {A X : SSet.{v}} {i : A ⟶ simplex k} {t : A ⟶ X}
    (E : simplex (bridge k n (smallDegree S).len) ⟶ X)
    (h : (i ▷ simplex (time (smallDegree S).len n)) ≫
        prism (smallCoefficients c S hS) u n ≫ E =
      fst A (simplex (time (smallDegree S).len n)) ≫ t) :
    (i ▷ (timeFace.{v} n S).toSSet) ≫ facePrism c u n S ≫ faceMap c u n S hS E =
      fst A (timeFace.{v} n S).toSSet ≫ t := by
  let j := (timeIso.{v} n S hS).hom
  haveI : IsIso (A ◁ j) := (inferInstance : IsIso ((tensorLeft A).map j))
  apply (cancel_epi (A ◁ j)).1
  rw [← Category.assoc (A ◁ j), whisker_exchange, Category.assoc,
    ← Category.assoc (simplex.{v} k ◁ j), facePrism_compare, Category.assoc,
    coefficientIso_faceMap, whiskerLeft_fst_assoc]
  exact h

/-- A stationary entire vertical simplex gives the original stationary
equation after passing to the copy face. -/
theorem faceMap_stationary_of_vertical {X : SSet.{v}}
    (a : Fin (k.len + 1)) (t : simplex ⦋0⦌ ⟶ X)
    (E : simplex (bridge k n (smallDegree S).len) ⟶ X)
    (h : SSet.stdSimplex.map (vertical (smallCoefficients c S hS) u n a) ≫ E =
      term (simplex (time (smallDegree S).len n)) ≫ t) :
    (JTFiniteCoefficientBridgeRelativeVertex.vertex k a ▷ (timeFace.{v} n S).toSSet) ≫
      facePrism c u n S ≫ faceMap c u n S hS E =
      fst (simplex ⦋0⦌) (timeFace.{v} n S).toSSet ≫ t := by
  apply faceMap_stationary
  rw [JTChangingCoefficientBridgeLift.vertex_tensor, Category.assoc, ← Category.assoc
    (JTHigherInterleavedParameter.verticalSection k (time (smallDegree S).len n) a),
    verticalSection_prism, h, ← Category.assoc]
  congr 1
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

end

end DaggerModels.PartII.JTFiniteCoefficientBridgeFaceReindex
