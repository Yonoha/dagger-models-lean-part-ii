import DaggerModelsPartII.DiagramPushoutProduct
import DaggerModelsPartII.ProjectiveKanDiagram
import DaggerModelsPartII.ProjectiveInjectiveComparison
import DaggerModelsPartII.InjectiveSimplicialAxiom
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Simplicial pushout-product for the projective Kan diagram model

The pushout-product cofibration property is proved using the pointwise
cotensor corner and the projective lifting characterization.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory MonoidalClosed MorphismProperty HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.ProjectiveKanDiagram

variable (C : Type u) [Category.{u} C]

noncomputable section

/-- The pointwise internal-Hom functor, contravariant in its simplicial
parameter. -/
def diagramCotensorSource :
    SSet.{u}ᵒᵖ ⥤ (C ⥤ SSet.{u}) ⥤ (C ⥤ SSet.{u}) where
  obj K := (Functor.whiskeringRight C SSet.{u} SSet.{u}).obj (ihom K.unop)
  map i := (Functor.whiskeringRight C SSet.{u} SSet.{u}).map (MonoidalClosed.pre i.unop)
  map_id K := by simp
  map_comp i j := by simp

/-- Diagramwise tensor and pointwise cotensor form a parametrized adjunction
in the simplicial-set variable. -/
def diagramTensorCotensorAdjunction :
    (InjectiveKanDiagram.curriedDiagramTensor C).flip ⊣₂ diagramCotensorSource C :=
  ParametrizedAdjunction.mk'
    (fun K ↦ ((ihom.adjunction K).whiskerRight C).ofNatIsoLeft
      ((Functor.whiskeringRight C SSet.{u} SSet.{u}).mapIso
        (tensorLeftIsoTensorRight K)))
    (by
      intro K L j A W q
      apply NatTrans.ext
      funext c
      change MonoidalClosed.curry
          ((β_ K (A.obj c)).hom ≫ (A.obj c ◁ j) ≫ q.app c) =
        MonoidalClosed.curry ((β_ L (A.obj c)).hom ≫ q.app c) ≫
          (MonoidalClosed.pre j).app (W.obj c)
      rw [MonoidalClosed.curry_pre_app]
      rw [← Category.assoc, ← BraidedCategory.braiding_naturality_left j (A.obj c),
        Category.assoc])

/-- The pointwise cotensor corner for a simplicial map and a diagram map. -/
def diagramCotensorCorner {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y) :
    (diagramCotensorSource C).PullbackObjObj j p :=
  Functor.PullbackObjObj.ofHasPullback _ _ _

/-- Evaluation of the diagram corner is the ordinary simplicial cotensor
corner, up to the canonical choice of pullback object. -/
def diagramCotensorCornerAtIso {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y) (c : C) :
    (diagramCotensorCorner C j p).pt.obj c ≅
      pullback ((ihom K).map (p.app c)) ((MonoidalClosed.pre j).app (Y.obj c)) := by
  let sq := diagramCotensorCorner C j p
  have h := IsPullback.map ((evaluation C SSet.{u}).obj c) sq.isPullback
  exact h.isoPullback

/-- The evaluated corner arrow agrees with the chosen ordinary corner map
under the canonical pullback isomorphism. -/
theorem diagramCotensorCornerAtIso_π {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y) (c : C) :
    (diagramCotensorCorner C j p).π.app c ≫
      (diagramCotensorCornerAtIso C j p c).hom =
        SSet.ihomToPullback j (p.app c) := by
  apply pullback.hom_ext
  · have hfst : (diagramCotensorCornerAtIso C j p c).hom ≫
        pullback.fst ((ihom K).map (p.app c))
          ((MonoidalClosed.pre j).app (Y.obj c)) =
          (diagramCotensorCorner C j p).fst.app c := by
      exact (IsPullback.map ((evaluation C SSet.{u}).obj c)
        (diagramCotensorCorner C j p).isPullback).isoPullback_hom_fst
    rw [Category.assoc, hfst]
    simpa only [NatTrans.comp_app, SSet.ihomToPullback, pullback.lift_fst] using
      congrArg (fun f ↦ f.app c) (diagramCotensorCorner C j p).π_fst
  · have hsnd : (diagramCotensorCornerAtIso C j p c).hom ≫
        pullback.snd ((ihom K).map (p.app c))
          ((MonoidalClosed.pre j).app (Y.obj c)) =
          (diagramCotensorCorner C j p).snd.app c := by
      exact (IsPullback.map ((evaluation C SSet.{u}).obj c)
        (diagramCotensorCorner C j p).isPullback).isoPullback_hom_snd
    rw [Category.assoc, hsnd]
    simpa only [NatTrans.comp_app, SSet.ihomToPullback, pullback.lift_snd] using
      congrArg (fun f ↦ f.app c) (diagramCotensorCorner C j p).π_snd

/-- A simplicial monomorphism and a levelwise trivial Kan fibration give a
levelwise trivial fibration on the diagram cotensor corner. -/
theorem diagramCotensorCorner_trivialFibration {K L : SSet.{u}} (j : K ⟶ L)
    [Mono j] {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (hp : (trivialFibrations SSet.{u}).functorCategory C p) :
    (trivialFibrations SSet.{u}).functorCategory C
      (diagramCotensorCorner C j p).π := by
  intro c
  have hpc := (mem_trivialFibrations_iff (p.app c)).mp (hp c)
  letI : Fibration (p.app c) := hpc.1
  letI : WeakEquivalence (p.app c) := hpc.2
  have hcorner := DaggerSSetSM7.corner_trivial_of_trivial j (p.app c)
  have htriv : trivialFibrations SSet.{u} (SSet.ihomToPullback j (p.app c)) :=
    (mem_trivialFibrations_iff _).mpr hcorner
  let e : Arrow.mk ((diagramCotensorCorner C j p).π.app c) ≅
      Arrow.mk (SSet.ihomToPullback j (p.app c)) :=
    Arrow.isoMk (Iso.refl _) (diagramCotensorCornerAtIso C j p c)
      (by simpa using (diagramCotensorCornerAtIso_π C j p c).symm)
  exact ((trivialFibrations SSet.{u}).arrow_mk_iso_iff e).mpr htriv

local instance projectiveSimplicialModel : ModelCategory (C ⥤ SSet.{u}) := modelCategory C

/-- The diagram pushout-product of a projective cofibration and a simplicial
cofibration is again a projective cofibration. -/
theorem model_pushoutProduct_cofibration {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (InjectiveKanDiagram.curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι := by
  rw [model_cofibrations C] at hi ⊢
  intro X Y p hp
  letI : Mono j := (SSet.modelCategoryQuillen.cofibration_iff j).mp
    ((cofibration_iff j).mpr hj)
  have hpt : (trivialFibrations SSet.{u}).functorCategory C p := by
    rw [← boundaryGenerators_rlp C]
    exact hp
  have hcorner := diagramCotensorCorner_trivialFibration C j p hpt
  have hcornerRLP : (boundaryGenerators C).rlp (diagramCotensorCorner C j p).π := by
    rw [boundaryGenerators_rlp C]
    exact hcorner
  have hlift : HasLiftingProperty i (diagramCotensorCorner C j p).π :=
    hi _ hcornerRLP
  have h := (diagramTensorCotensorAdjunction C).hasLiftingProperty_iff
    sq.flip (diagramCotensorCorner C j p)
  rw [Functor.PushoutObjObj.ι_flip] at h
  exact h.mpr hlift

/-- SM7 for the projective Kan diagram model. Projective cofibrations are
closed under the diagram pushout-product, and the result is weakly equivalent
when either input is weakly equivalent. -/
theorem model_pushoutProduct_sm7 {A B : C ⥤ SSet.{u}} (i : A ⟶ B)
    {K L : SSet.{u}} (j : K ⟶ L)
    (hi : HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) i)
    (hj : HomotopicalAlgebra.cofibrations SSet.{u} j)
    (sq : Functor.PushoutObjObj (InjectiveKanDiagram.curriedDiagramTensor C) i j) :
    HomotopicalAlgebra.cofibrations (C ⥤ SSet.{u}) sq.ι ∧
      ((HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) i ∨
          HomotopicalAlgebra.weakEquivalences SSet.{u} j) →
        HomotopicalAlgebra.weakEquivalences (C ⥤ SSet.{u}) sq.ι) := by
  refine ⟨model_pushoutProduct_cofibration C i j hi hj sq, ?_⟩
  intro hweak
  have hiInj : (InjectiveKanDiagram.modelCategory C).categoryWithCofibrations.cofibrations i :=
    ProjectiveInjectiveComparison.cofibrations_le C i hi
  have hweakInj :
      (InjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences i ∨
        HomotopicalAlgebra.weakEquivalences SSet.{u} j := by
    rcases hweak with hwi | hwj
    · exact Or.inl ((ProjectiveInjectiveComparison.weakEquivalences_eq C) ▸ hwi)
    · exact Or.inr hwj
  have hboxInj :
      (InjectiveKanDiagram.modelCategory C).categoryWithWeakEquivalences.weakEquivalences
        sq.ι := by
    letI : ModelCategory (C ⥤ SSet.{u}) := InjectiveKanDiagram.modelCategory C
    exact (InjectiveKanDiagram.model_pushoutProduct_sm7 C i j hiInj hj sq).2 hweakInj
  change (modelCategory C).categoryWithWeakEquivalences.weakEquivalences sq.ι
  rw [ProjectiveInjectiveComparison.weakEquivalences_eq C]
  exact hboxInj

end

end DaggerModels.PartII.ProjectiveKanDiagram
