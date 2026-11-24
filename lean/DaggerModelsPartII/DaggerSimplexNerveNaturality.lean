import DaggerModelsPartII.DaggerSimplexNerveRepresentable

/-!
# Reversal naturality of the free dagger simplex nerve

Precomposition by the change-of-index dagger functor is compared with the
native reversal presheaf action on chains.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexFreeProperty
open DaggerModels.PartII.DaggerSimplexPartIIndex
open DaggerModels.PartII.DaggerSimplexNerveRepresentable

namespace DaggerModels.PartII.DaggerSimplexNerveNaturality

noncomputable section

/-- A chain associated to a dagger functor evaluates a finite-ordinal arrow
by the corresponding forward word. -/
theorem pathHomChainEquiv_map (m n : ℕ)
    (F : (⟨m⟩ : DaggerSimplex) ⟶ ⟨n⟩)
    {i j : Fin (m + 1)} (h : i ⟶ j) :
    (pathHomChainEquiv m n F).map h =
      F.toFunctor.map (forwardWord m i.val j.val
        (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
        (CategoryTheory.leOfHom h)) := by
  exact wordValue_restrict m (FreeDaggerSimplex n)
    ⟨F.toFunctor, F.map_dagger⟩ _

/-- On vertices, precomposition by every reversal map acts by its actual
underlying function. -/
theorem pathHomChainEquiv_precomp_obj {l m : ReverseSimplex}
    (α : l ⟶ m) (n : ℕ)
    (F : (⟨m.len⟩ : DaggerSimplex) ⟶ ⟨n⟩)
    (i : Fin (l.len + 1)) :
    (pathHomChainEquiv l.len n (u.map α ≫ F)).obj i =
      (pathHomChainEquiv m.len n F).obj (α.toFun i) := rfl

/-- A monotone reversal morphism acts on chains by ordinary nerve
precomposition. -/
theorem pathHomChainEquiv_precomp_monotone {l m : ReverseSimplex}
    (α : l ⟶ m) (hα : Monotone α.toFun) (n : ℕ)
    (F : (⟨m.len⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    pathHomChainEquiv l.len n (u.map α ≫ F) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extensionMap α (pathHomChainEquiv m.len n F) := by
  rw [DaggerSSet.extensionMap_monotone
    (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex n)) α hα]
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    rfl
  case h_map =>
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [pathHomChainEquiv_map]
    change F.toFunctor.map
      (mapPath α (forwardWord l.len i.val j.val
        (Nat.lt_succ_iff.mp i.isLt) (Nat.lt_succ_iff.mp j.isLt)
        (CategoryTheory.leOfHom h))) = _
    rw [mapPath_forwardWord]
    rw [intervalWord_forward m.len _ _ (mapLine_mono α hα (CategoryTheory.leOfHom h))]
    let h' : α.toFun i ⟶ α.toFun j :=
      CategoryTheory.homOfLE (hα (CategoryTheory.leOfHom h))
    change F.toFunctor.map (forwardWord m.len (α.toFun i).val (α.toFun j).val
      (Nat.lt_succ_iff.mp (α.toFun i).isLt)
      (Nat.lt_succ_iff.mp (α.toFun j).isLt)
      (hα (CategoryTheory.leOfHom h))) =
        (pathHomChainEquiv m.len n F).map h'
    exact (pathHomChainEquiv_map m.len n F h').symm

/-- Reversal of a free dagger simplex acts on the associated chain by
reversing its entries and daggering its arrows. -/
theorem pathHomChainEquiv_precomp_reversal (m : ReverseSimplex) (n : ℕ)
    (F : (⟨m.len⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    pathHomChainEquiv m.len n (u.map (ReverseSimplex.reversal m) ≫ F) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extensionMap (ReverseSimplex.reversal m)
        (pathHomChainEquiv m.len n F) := by
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex n)
  have ha : Antitone (ReverseSimplex.reversal m).toFun := by
    intro i j h
    simpa only [ReverseSimplex.reversal_apply, Fin.rev_le_rev] using h
  rw [X.extensionMap_antitone (ReverseSimplex.reversal m) ha]
  have hid : ReverseSimplex.antitoneHom (ReverseSimplex.reversal m) ha = 𝟙 ⦋m.len⦌ := by
    ext i
    simp [ReverseSimplex.antitoneHom]
  rw [hid, op_id, X.toSSet.map_id]
  change pathHomChainEquiv m.len n (u.map (ReverseSimplex.reversal m) ≫ F) =
    SSet.opObjEquiv
      ((DaggerNativeOrdinaryDaggerNerve.reversal (FreeDaggerSimplex n)).app
        (op ⦋m.len⦌) (pathHomChainEquiv m.len n F))
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro i
    exact (DaggerNativeOrdinaryDaggerNerve.reversal_obj
      (FreeDaggerSimplex n) ⦋m.len⦌ (pathHomChainEquiv m.len n F) i).symm
  case h_map =>
    intro i j h
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [pathHomChainEquiv_map]
    change F.toFunctor.map (mapPath (ReverseSimplex.reversal m)
      (forwardWord m.len i.val j.val (Nat.lt_succ_iff.mp i.isLt)
        (Nat.lt_succ_iff.mp j.isLt) (CategoryTheory.leOfHom h))) = _
    rw [mapPath_forwardWord]
    rw [DaggerNativeOrdinaryDaggerNerve.reversal_map]
    have hanti :
        (mapLine (ReverseSimplex.reversal m)
          (lineAt m.len j.val (Nat.lt_succ_iff.mp j.isLt))).val ≤
        (mapLine (ReverseSimplex.reversal m)
          (lineAt m.len i.val (Nat.lt_succ_iff.mp i.isLt))).val :=
      mapLine_anti (ReverseSimplex.reversal m) ha (CategoryTheory.leOfHom h)
    rw [intervalWord_backward_le m.len _ _ hanti]
    letI : DaggerFunctor F.toFunctor := F.map_dagger
    rw [DaggerFunctor.map_dagger]
    let h' : j.rev ⟶ i.rev :=
      CategoryTheory.homOfLE (Fin.rev_le_rev.mpr (CategoryTheory.leOfHom h))
    congr 1
    change F.toFunctor.map (forwardWord m.len j.rev.val i.rev.val
      (Nat.lt_succ_iff.mp j.rev.isLt)
      (Nat.lt_succ_iff.mp i.rev.isLt)
      (Fin.rev_le_rev.mpr (CategoryTheory.leOfHom h))) =
        (pathHomChainEquiv m.len n F).map h'
    exact (pathHomChainEquiv_map m.len n F h').symm

/-- The native dagger nerve action agrees with path-index precomposition
for every antitone morphism, including the constant maps. -/
theorem pathHomChainEquiv_precomp_antitone {l m : ReverseSimplex}
    (α : l ⟶ m) (hα : Antitone α.toFun) (n : ℕ)
    (F : (⟨m.len⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    pathHomChainEquiv l.len n (u.map α ≫ F) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extensionMap α (pathHomChainEquiv m.len n F) := by
  let β : l ⟶ m := ReverseSimplex.inclusion.map
    (ReverseSimplex.antitoneHom α hα)
  have hβ : Monotone β.toFun :=
    (ReverseSimplex.antitoneHom α hα).toOrderHom.monotone
  have hfac : β ≫ ReverseSimplex.reversal m = α :=
    ReverseSimplex.antitone_factorization α hα
  let X := DaggerNativeOrdinaryDaggerNerveLift.daggerNerve (FreeDaggerSimplex n)
  calc
    pathHomChainEquiv l.len n (u.map α ≫ F) =
        pathHomChainEquiv l.len n
          (u.map β ≫ (u.map (ReverseSimplex.reversal m) ≫ F)) := by
            rw [← Category.assoc, ← u.map_comp, hfac]
    _ = X.extensionMap β
          (pathHomChainEquiv m.len n
            (u.map (ReverseSimplex.reversal m) ≫ F)) :=
          pathHomChainEquiv_precomp_monotone β hβ n _
    _ = X.extensionMap β
          (X.extensionMap (ReverseSimplex.reversal m)
            (pathHomChainEquiv m.len n F)) := by
          rw [pathHomChainEquiv_precomp_reversal]
    _ = X.extensionMap α (pathHomChainEquiv m.len n F) := by
          rw [← X.extensionMap_comp, hfac]

/-- Source naturality holds for every morphism of the reversal simplex
category, regardless of its orientation. -/
theorem pathHomChainEquiv_precomp {l m : ReverseSimplex}
    (α : l ⟶ m) (n : ℕ)
    (F : (⟨m.len⟩ : DaggerSimplex) ⟶ ⟨n⟩) :
    pathHomChainEquiv l.len n (u.map α ≫ F) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extensionMap α (pathHomChainEquiv m.len n F) := by
  rcases α.monotone_or_antitone with hα | hα
  · exact pathHomChainEquiv_precomp_monotone α hα n F
  · exact pathHomChainEquiv_precomp_antitone α hα n F

/-- Source naturality for all enriched dagger functors between the actual
Part I free dagger simplices. -/
theorem actualHomNativeNerveEquiv_precomp {l m : ReverseSimplex}
    (α : l ⟶ m) (n : ℕ)
    (F : (⟨m.len⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) :
    actualHomNativeNerveEquiv l.len n (actualU.map α ≫ F) =
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extensionMap α
          (actualHomNativeNerveEquiv m.len n F) := by
  have hcomp :
      (actualHomEquiv ⟨l.len⟩ ⟨n⟩).symm (actualU.map α ≫ F) =
        u.map α ≫ (actualHomEquiv ⟨m.len⟩ ⟨n⟩).symm F := by
    apply (actualHomEquiv ⟨l.len⟩ ⟨n⟩).injective
    change pathToActual.map
      ((actualHomEquiv ⟨l.len⟩ ⟨n⟩).symm (actualU.map α ≫ F)) =
      pathToActual.map
        (u.map α ≫ (actualHomEquiv ⟨m.len⟩ ⟨n⟩).symm F)
    rw [pathToActual.map_comp]
    change
      (actualHomEquiv ⟨l.len⟩ ⟨n⟩)
        ((actualHomEquiv ⟨l.len⟩ ⟨n⟩).symm (actualU.map α ≫ F)) =
      actualU.map α ≫ (actualHomEquiv ⟨m.len⟩ ⟨n⟩)
        ((actualHomEquiv ⟨m.len⟩ ⟨n⟩).symm F)
    simp
    rfl
  change pathHomChainEquiv l.len n
      ((actualHomEquiv ⟨l.len⟩ ⟨n⟩).symm (actualU.map α ≫ F)) = _
  rw [hcomp, pathHomChainEquiv_precomp]
  rfl

/-- The degreewise all-functor classification, including the universe lift
in the represented presheaf. -/
def actualHomNativeNerveUliftEquiv (m n : ℕ) :
    ULift ((⟨m⟩ : ActualDaggerSimplex) ⟶ ⟨n⟩) ≃
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extension.obj (op (ReverseSimplex.mk m)) where
  toFun f := actualHomNativeNerveEquiv m n f.down
  invFun x := ULift.up ((actualHomNativeNerveEquiv m n).symm x)
  left_inv f := by cases f; simp
  right_inv x := by simp

/-- The represented actual Part I free simplex is naturally the native
dagger nerve of its path presentation, as a presheaf of sets on all
reversal morphisms. -/
def actualRepresentableNativePresheafIso (n : ℕ) :
    actualU.op ⋙ (uliftYoneda.{0, 0}.obj (⟨n⟩ : ActualDaggerSimplex)) ≅
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex n)).extension :=
  NatIso.ofComponents
    (fun m ↦ Equiv.toIso (actualHomNativeNerveUliftEquiv m.unop.len n)) (by
      intro m l α
      funext f
      exact actualHomNativeNerveEquiv_precomp α.unop n f.down)

/-- The restricted actual representable simplicial presheaf is the discrete
native dagger nerve of the free path simplex. Naturality includes every
order-reversing source morphism. -/
def actualRepresentableNativeDaggerSpaceIso (n : ℕ) :
    (restrictIndex actualU).obj
      ((simplicialYoneda ActualDaggerSimplex).obj
        (⟨n⟩ : ActualDaggerSimplex)) ≅
      SegalLocalizers.discreteDagger.obj
        (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
          (FreeDaggerSimplex n)) :=
  NatIso.ofComponents
    (fun m ↦ NatIso.ofComponents
      (fun _ ↦ Equiv.toIso (actualHomNativeNerveUliftEquiv m.unop.len n))
      (by intros; rfl)) (by
    intro m l α
    ext q f
    exact actualHomNativeNerveEquiv_precomp α.unop n f.down)

/-- At a representable, the change-of-index unit becomes the chain
classified by the actual enriched dagger functor `actualU.map f`. -/
theorem actualUnit_native_chain_apply (m n : ReverseSimplex)
    (q : SimplexCategoryᵒᵖ) (f : m ⟶ n) :
    ((actualRepresentableNativeDaggerSpaceIso n.len).hom.app (op m)).app q
      ((((ActualIndexProjectiveModel.actualLeftAdjunction.{0}).unit.app
        ((simplicialYoneda.{0, 0} ReverseSimplex).obj n) ≫
        (ActualIndexProjectiveModel.actualRestriction.{0}).map
          ((ActualIndexProjectiveModel.actualLeftExtension_simplicialYoneda.{0}).hom.app n)).app
        (op m)).app q (ULift.up f)) =
      actualHomNativeNerveEquiv m.len n.len (actualU.map f) := by
  rw [actualUnit_representable_apply]
  rfl


end

end DaggerModels.PartII.DaggerSimplexNerveNaturality
