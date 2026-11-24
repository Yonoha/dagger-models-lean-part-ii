import TopCatModelCategory.QuillenAdjunction
import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Right cancellation for Quillen equivalences

With all objects of the first two model categories cofibrant, a Quillen
equivalence followed by a Quillen adjunction is a Quillen equivalence only
if the second adjunction is itself a Quillen equivalence.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits HomotopicalAlgebra

universe u v w

namespace DaggerModels.PartII.QuillenEquivalenceRightCancellation

noncomputable section

variable {C : Type u} {D : Type v} {E : Type w}
  [Category C] [Category D] [Category E]
  [ModelCategory C] [ModelCategory D] [ModelCategory E]
  (F : C ⥤ D) (G : D ⥤ C) (L : D ⥤ E) (R : E ⥤ D)
  (adj₁ : F ⊣ G) (adj₂ : L ⊣ R)

private theorem left_map_weak_of_cofibrant
    {X Y : D} [IsCofibrant X] [IsCofibrant Y]
    [L.PreservesTrivialCofibrations] (f : X ⟶ Y) [WeakEquivalence f] :
    WeakEquivalence (L.map f) := by
  let b : CofibrantBrownFactorization f := Classical.choice inferInstance
  haveI : Cofibration b.i := (cofibration_iff _).mpr b.hi
  haveI : Cofibration b.s := b.cofibration_s
  haveI : WeakEquivalence b.i := inferInstance
  haveI : WeakEquivalence b.s := inferInstance
  haveI : WeakEquivalence (L.map b.i) := inferInstance
  haveI : WeakEquivalence (L.map b.s) := inferInstance
  have hsp : L.map b.s ≫ L.map b.p = 𝟙 (L.obj Y) := by
    rw [← L.map_comp, b.s_p, L.map_id]
  haveI : WeakEquivalence (L.map b.p) :=
    weakEquivalence_of_precomp_of_fac hsp
  rw [← b.fac, L.map_comp]
  infer_instance

private theorem fibrant_source_iff
    (hF : adj₁.IsQuillenEquivalence) (hL : adj₂.IsQuillenAdjunction)
    (hComp : (adj₁.comp adj₂).IsQuillenEquivalence)
    (hC : ∀ A : C, IsCofibrant A) (hD : ∀ Y : D, IsCofibrant Y)
    {Y : D} [IsFibrant Y] {Z : E} [IsFibrant Z] (f : L.obj Y ⟶ Z) :
    WeakEquivalence ((adj₂.homEquiv Y Z) f) ↔ WeakEquivalence f := by
  letI : adj₁.IsQuillenEquivalence := hF
  letI : adj₂.IsQuillenAdjunction := hL
  letI : (adj₁.comp adj₂).IsQuillenEquivalence := hComp
  letI : L.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations adj₂
  letI : R.PreservesFibrations :=
    Adjunction.IsQuillenAdjunction.preservesFibrations adj₂
  letI : PreservesLimitsOfSize.{0, 0} R := adj₂.rightAdjoint_preservesLimits
  letI : IsFibrant (R.obj Z) := by
    exact (isFibrant_iff_of_isTerminal
      (R.map (terminal.from Z)) (terminalIsTerminal.isTerminalObj R)).mpr inferInstance
  letI : IsCofibrant (G.obj Y) := hC _
  letI : IsCofibrant (F.obj (G.obj Y)) := hD _
  letI : IsCofibrant Y := hD _
  let u : F.obj (G.obj Y) ⟶ Y := adj₁.counit.app Y
  have hu : WeakEquivalence u := by
    apply (adj₁.weakEquivalence_homEquiv_iff u).mp
    have he : (adj₁.homEquiv (G.obj Y) Y) u = 𝟙 (G.obj Y) := by
      change adj₁.unit.app (G.obj Y) ≫ G.map (adj₁.counit.app Y) = 𝟙 _
      exact adj₁.right_triangle_components Y
    rw [he]
    infer_instance
  letI : WeakEquivalence u := hu
  let g : Y ⟶ R.obj Z := (adj₂.homEquiv Y Z) f
  haveI : WeakEquivalence (L.map u) := by
    exact left_map_weak_of_cofibrant L u
  have hm : ((adj₁.comp adj₂).homEquiv (G.obj Y) Z) (L.map u ≫ f) =
      (adj₁.homEquiv (G.obj Y) (R.obj Z)) (u ≫ g) := by
    rw [Adjunction.comp_homEquiv]
    change (adj₁.homEquiv (G.obj Y) (R.obj Z))
      ((adj₂.homEquiv (F.obj (G.obj Y)) Z) (L.map u ≫ f)) =
        (adj₁.homEquiv (G.obj Y) (R.obj Z)) (u ≫ g)
    rw [adj₂.homEquiv_naturality_left]
  have h₁ : WeakEquivalence f ↔ WeakEquivalence (L.map u ≫ f) :=
    (weakEquivalence_precomp_iff (L.map u) f).symm
  have h₂ : WeakEquivalence (L.map u ≫ f) ↔
      WeakEquivalence ((adj₁.comp adj₂).homEquiv (G.obj Y) Z (L.map u ≫ f)) :=
    ((adj₁.comp adj₂).weakEquivalence_homEquiv_iff _).symm
  have h₂' : WeakEquivalence (L.map u ≫ f) ↔
      WeakEquivalence ((adj₁.homEquiv (G.obj Y) (R.obj Z)) (u ≫ g)) := by
    simpa only [hm] using h₂
  have h₃ : WeakEquivalence ((adj₁.homEquiv (G.obj Y) (R.obj Z)) (u ≫ g)) ↔
      WeakEquivalence (u ≫ g) := adj₁.weakEquivalence_homEquiv_iff _
  have h₄ : WeakEquivalence (u ≫ g) ↔ WeakEquivalence g :=
    weakEquivalence_precomp_iff u g
  change WeakEquivalence g ↔ WeakEquivalence f
  exact (h₃.trans h₄).symm.trans (h₂'.symm.trans h₁.symm)

/-- Cancel a first Quillen equivalence from a composite Quillen equivalence.
The source and middle categories have only cofibrant objects. -/
theorem isQuillenEquivalence
    (hF : adj₁.IsQuillenEquivalence) (hL : adj₂.IsQuillenAdjunction)
    (hComp : (adj₁.comp adj₂).IsQuillenEquivalence)
    (hC : ∀ A : C, IsCofibrant A) (hD : ∀ Y : D, IsCofibrant Y) :
    adj₂.IsQuillenEquivalence := by
  letI : adj₂.IsQuillenAdjunction := hL
  letI : L.PreservesTrivialCofibrations :=
    Adjunction.IsQuillenAdjunction.preservesTrivialCofibrations adj₂
  refine { toIsQuillenAdjunction := hL, weakEquivalence_homEquiv_iff := ?_ }
  intro Y Z hY hZ f
  let d := MorphismProperty.factorizationData
    (trivialCofibrations D) (fibrations D) (terminal.from Y)
  haveI : IsFibrant d.Z := by
    change Fibration (terminal.from d.Z)
    have heq : d.p = terminal.from d.Z := terminalIsTerminal.hom_ext _ _
    rw [← heq]
    exact (fibration_iff _).mpr d.hp
  letI : IsCofibrant d.Z := hD _
  haveI : Cofibration d.i := (cofibration_iff _).mpr d.hi.1
  haveI : WeakEquivalence d.i := (weakEquivalence_iff _).mpr d.hi.2
  haveI : WeakEquivalence (L.map d.i) :=
    left_map_weak_of_cofibrant L d.i
  let sq : CommSq f (L.map d.i) (terminal.from Z)
      (terminal.from (L.obj d.Z)) := CommSq.mk (terminalIsTerminal.hom_ext _ _)
  letI : HasLiftingProperty (L.map d.i) (terminal.from Z) := inferInstance
  let f' : L.obj d.Z ⟶ Z := sq.lift
  have hfac : L.map d.i ≫ f' = f := sq.fac_left
  have hmate : (adj₂.homEquiv Y Z) f =
      d.i ≫ (adj₂.homEquiv d.Z Z) f' := by
    rw [← hfac, adj₂.homEquiv_naturality_left]
  rw [hmate, ← hfac]
  exact (weakEquivalence_precomp_iff d.i _).trans
    ((fibrant_source_iff F G L R adj₁ adj₂ hF hL hComp hC hD f').trans
      (weakEquivalence_precomp_iff (L.map d.i) f').symm)

#print axioms isQuillenEquivalence

end

end DaggerModels.PartII.QuillenEquivalenceRightCancellation
