import DaggerModelsPartII.JTJointPairSubdivisionDiagram
import Mathlib.CategoryTheory.Category.Cat.Op

/-!
The actual cut-subdivision source with only its fiber arrows reversed.
Original pair arrows retain their original direction. A remaining fiber arrow
is a coarsening of the literal native image, as required by fine-to-coarse
native interval concatenation. No normalized evaluation functor or seam
coherence is asserted by this variance correction.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode
open DaggerOriginalProductGadget DaggerSSetGluing DaggerNerveHomotopy
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTJointSubdivisionCoarsenings

open JTParametrizedTargetFamilies (Family codes)
open JTTargetJointMarks (Joint)
open JTProjectiveOrderedFiberComparison (row)
open JTJointPairSubdivisionDiagram (Subdivision greatest greatestIsTerminal transport)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y}
variable {time : A ⥤ SimplexCategory} (F : Family Q L time) (j : Joint Q.code)

private abbrev E := JTJointPairSourceDiagram.Index F j

/-- Reverse only the subdivision fibers; every original pair map remains covariant. -/
abbrev diagram : E F j ⥤ Cat.{0, 0} :=
  JTJointPairSubdivisionDiagram.diagram F j ⋙ Cat.opFunctor

/-- Original exact pairs with actual cut coarsenings after literal native transport. -/
abbrev Index := Grothendieck (diagram F j)

/-- Retain each original pair arrow in its unchanged direction. -/
abbrev projection : Index F j ⥤ E F j := Grothendieck.forget (diagram F j)

/-- The actual original cut set, with its concrete subdivision type retained. -/
def cuts (X : Index F j) : Subdivision F j X.base := X.fiber.unop

/-- The opposite of the original full cut set is initial in the coarsening fiber. -/
def initial (p : E F j) : IsInitial (op (greatest F j p)) :=
  IsInitial.ofUniqueHom (fun C ↦ ((greatestIsTerminal F j p).from C.unop).op)
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- A literal inclusion D ≤ C becomes the required native-direction coarsening C → D. -/
def coarsening (p : E F j) (C D : Subdivision F j p) (h : D ≤ C) :
    (⟨p, op C⟩ : Index F j) ⟶ ⟨p, op D⟩ :=
  (Grothendieck.ι (diagram F j) p).map ((homOfLE h : D ⟶ C).op)

/-- A cut coarsening lies over the unchanged original pair and source arrow. -/
theorem coarsening_base (p : E F j) (C D : Subdivision F j p) (h : D ≤ C) :
    (coarsening F j p C D h).base = 𝟙 p := rfl

/-- The complete actual target cut set is contained in the source's literal native image. -/
theorem image_contains {X Y : Index F j} (f : X ⟶ Y) :
    cuts F j Y ≤ transport F j f.base (cuts F j X) :=
  leOfHom (X := Subdivision F j Y.base) (x := cuts F j Y)
    (y := transport F j f.base (cuts F j X)) f.fiber.unop

/-- The remaining vertical part of every actual coarsening arrow. -/
def vertical {X Y : Index F j} (f : X ⟶ Y) : X.transport f.base ⟶ Y :=
  ⟨𝟙 Y.base, eqToHom (by simp) ≫ f.fiber⟩

/-- This coarsening part keeps the original exact target pair fixed. -/
theorem vertical_base {X Y : Index F j} (f : X ⟶ Y) :
    (vertical F j f).base = 𝟙 Y.base := rfl

/-- Every actual arrow factors as original native transport followed by cut coarsening. -/
theorem arrow_factor {X Y : Index F j} (f : X ⟶ Y) :
    Grothendieck.toTransport X f.base ≫ vertical F j f = f := by
  apply Grothendieck.ext
  · simp [vertical]
  · simp [vertical]

/-- Each actual reversed fiber contracts to its initial full cut set. -/
theorem fiber_point_GW (p : E F j) :
    GW (pointMap (nerve (Subdivision F j p)ᵒᵖ)) := by
  let C := (Subdivision F j p)ᵒᵖ
  let q : C ⥤ Discrete PUnit := (Functor.const _).obj ⟨PUnit.unit⟩
  let s : Discrete PUnit ⥤ C := (Functor.const _).obj (op (greatest F j p))
  let η : q ⋙ s ⟶ 𝟭 C :=
    { app := (initial F j p).to
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  let ε : s ⋙ q ⟶ 𝟭 (Discrete PUnit) :=
    { app := fun _ ↦ eqToHom (Subsingleton.elim _ _)
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  haveI : WeakEquivalence (nerveMap q) := (weakEquivalence_iff_GW _).mpr
    (nerveMap_geometricW q s (.rel _ _ ⟨η⟩) (.rel _ _ ⟨ε⟩))
  have h : nerveMap q ≫
      (DaggerOriginalFlagFlankification.nerveDiscreteIso PUnit).hom =
        pointMap (nerve C) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← h]
  infer_instance

/-- The coarsening source weakly covers the exact pair category, with no whole-source claim. -/
theorem projection_weak : WeakEquivalence (nerveMap (projection F j)) :=
  GrothendieckContractibleFibers.projection_weak (diagram F j) (fiber_point_GW F j)

end
end DaggerModels.PartII.JTJointSubdivisionCoarsenings
