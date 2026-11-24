import DaggerModelsPartII.CosimplicialQuillenComparison
import DaggerModelsPartII.LocalEquivalenceClasses
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.Opposite

/-!
# Weak comparison of mate-related left Quillen functors

A natural map of left Quillen functors is weak on cofibrant objects if its
right mate is weak on every fibrant object. The argument uses derived mapping
spaces and a fibrant-target detection lemma, without asserting any particular
ordinary model structure or JT-frame comparison.
-/

set_option autoImplicit false

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v u u'

namespace DaggerModels.PartII.QuillenMateWeakComparison

noncomputable section

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]

/-- Mapping-space tests into every fibrant object detect every weak
equivalence, including maps whose endpoints are not fibrant. -/
private theorem weak_of_all_fibrant_mappingTests {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (Z : C) [IsFibrant Z], homotopyMappingWeakEquivalences Z f) :
    weakEquivalences C f := by
  let S : MorphismProperty C := ⊥
  let P := Localization.localEquivalences S
  have hfLocal : P f := by
    intro Z hZ
    letI : IsFibrant Z := hZ.1
    exact hf Z
  let a := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (terminal.from X)
  let b := MorphismProperty.factorizationData
    (trivialCofibrations C) (fibrations C) (terminal.from Y)
  have haFib : IsFibrant a.Z := by
    change Fibration (terminal.from a.Z)
    have heq : a.p = terminal.from a.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr a.hp
  have hbFib : IsFibrant b.Z := by
    change Fibration (terminal.from b.Z)
    have heq : b.p = terminal.from b.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr b.hp
  let sq : CommSq (f ≫ b.i) a.i b.p a.p := CommSq.mk (by
    rw [Category.assoc, b.fac, a.fac]
    exact terminalIsTerminal.hom_ext _ _)
  haveI : Cofibration a.i := (cofibration_iff _).mpr a.hi.1
  haveI : WeakEquivalence a.i := (weakEquivalence_iff _).mpr a.hi.2
  haveI : Fibration b.p := (fibration_iff _).mpr b.hp
  letI : HasLiftingProperty a.i b.p := inferInstance
  let g : a.Z ⟶ b.Z := sq.lift
  have hs : a.i ≫ g = f ≫ b.i := sq.fac_left
  have haLocal : P a.i :=
    Localization.weakEquivalences_le_localEquivalences S a.i a.hi.2
  have hbLocal : P b.i :=
    Localization.weakEquivalences_le_localEquivalences S b.i b.hi.2
  have hgLocal : P g := by
    apply P.of_precomp a.i g haLocal
    rw [hs]
    exact P.comp_mem f b.i hfLocal hbLocal
  have haObj : Localization.localObject S a.Z := ⟨haFib, bot_le⟩
  have hbObj : Localization.localObject S b.Z := ⟨hbFib, bot_le⟩
  have hg : weakEquivalences C g :=
    (Localization.localEquivalence_iff_weak_of_local S g haObj hbObj).mp hgLocal
  have hcomp : weakEquivalences C (f ≫ b.i) := by
    rw [← hs]
    exact (weakEquivalences C).comp_mem a.i g a.hi.2 hg
  exact (weakEquivalences C).of_postcomp f b.i b.hi.2 hcomp

/-- The weak-equivalence localization of the given model category reflects its
weak equivalences. The fibrant mapping-space tests detect the original class. -/
theorem weak_of_localization_isIso {H : Type*} [Category* H] (Q : C ⥤ H)
    [Q.IsLocalization (weakEquivalences C)] {X Y : C} (f : X ⟶ Y)
    [IsIso (Q.map f)] : weakEquivalences C f := by
  apply weak_of_all_fibrant_mappingTests f
  intro Z hZ
  let F := homotopyMappingFunctor Z
  have hF : (weakEquivalences C).op.IsInvertedBy F := by
    intro A B g hg
    exact (homotopyMappingWeakEquivalences_iff_isIso Z g.unop).mp
      (weakEquivalences_le_homotopyMappingWeakEquivalences Z _ hg)
  let G := Localization.lift F hF Q.op
  let e := Localization.fac F hF Q.op
  apply (homotopyMappingWeakEquivalences_iff_isIso Z f).mpr
  apply (NatIso.isIso_map_iff e f.op).mp
  change IsIso (G.map (Q.map f).op)
  infer_instance

variable {D : Type u'} [Category.{v} D] [ModelCategory D]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]

omit [HasColimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} D] in
/-- A right Quillen functor carries fibrant objects to fibrant objects. -/
private theorem right_obj_fibrant {L : C ⥤ D} {G : D ⥤ C}
    (adj : L ⊣ G) [adj.IsQuillenAdjunction]
    (Z : D) [IsFibrant Z] : IsFibrant (G.obj Z) := by
  letI : G.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations adj
  letI : PreservesLimits G := adj.rightAdjoint_preservesLimits
  have hG : Fibration (G.map (terminal.from Z)) := inferInstance
  have hT : IsTerminal (G.obj (⊤_ D)) :=
    terminalIsTerminal.isTerminalObj G (⊤_ D)
  exact (isFibrant_iff_of_isTerminal (G.map (terminal.from Z)) hT).mpr hG

/-- A true mate comparison with weak right components on fibrant targets
has weak left components on every cofibrant source. -/
theorem weak_on_cofibrant_of_mate_weak_on_fibrant
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
    {L' : C ⥤ D} {G' : D ⥤ C} (adj' : L' ⊣ G')
    [adj.IsQuillenAdjunction] [adj'.IsQuillenAdjunction]
    (α : L ⟶ L') (β : G' ⟶ G)
    (mates : ∀ {A : C} {Z : D} (q : L'.obj A ⟶ Z),
      adj.homEquiv A Z (α.app A ≫ q) = adj'.homEquiv A Z q ≫ β.app Z)
    (hβ : ∀ (Z : D) [IsFibrant Z], weakEquivalences C (β.app Z))
    {A : C} [IsCofibrant A] : weakEquivalences D (α.app A) := by
  apply weak_of_all_fibrant_mappingTests (α.app A)
  intro Z hZ
  letI : IsFibrant (G.obj Z) := right_obj_fibrant adj Z
  letI : IsFibrant (G'.obj Z) := right_obj_fibrant adj' Z
  let R := cosimplicialResolution A
  apply (homotopyMappingWeakEquivalences_of_mates adj adj'
    α β mates R Z).2
  exact R.mappingSSet_map_weak (β.app Z) (hβ Z)

end

end DaggerModels.PartII.QuillenMateWeakComparison
