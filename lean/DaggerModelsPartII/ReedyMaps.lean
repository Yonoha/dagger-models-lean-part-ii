import DaggerModelsPartII.ResolutionAdjunction
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Relative matching and latching maps for simplicial objects

For the outer index `Δᵒᵖ`, the matching category at `[n]` consists of proper
faces `[m] ⟶ [n]` in `Δ`, and the latching category consists of proper
degeneracy indices `[n] ⟶ [m]` in `Δ`. Their triangles are taken in
`Δᵒᵖ`. The constructions work for any complete and cocomplete coefficient
category and will be used with the Part I dagger Joyal model.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

/-- Proper faces into `[n]` index matching in the opposite simplex category. -/
def matchingIndexProperty (n : ℕ) :
    ObjectProperty (StructuredArrow (op ⦋n⦌) (𝟭 SimplexCategoryᵒᵖ)) :=
  fun s ↦ s.right.unop.len < n ∧ Mono s.hom.unop

/-- Proper surjections out of `[n]` index latching in the opposite simplex category. -/
def latchingIndexProperty (n : ℕ) :
    ObjectProperty (CostructuredArrow (𝟭 SimplexCategoryᵒᵖ) (op ⦋n⦌)) :=
  fun s ↦ s.left.unop.len < n ∧ Epi s.hom.unop

abbrev MatchingIndex (n : ℕ) := (matchingIndexProperty n).FullSubcategory
abbrev LatchingIndex (n : ℕ) := (latchingIndexProperty n).FullSubcategory

def matchingProjection (n : ℕ) : MatchingIndex n ⥤ SimplexCategoryᵒᵖ :=
  (matchingIndexProperty n).ι ⋙ StructuredArrow.proj _ _

def latchingProjection (n : ℕ) : LatchingIndex n ⥤ SimplexCategoryᵒᵖ :=
  (latchingIndexProperty n).ι ⋙ CostructuredArrow.proj _ _

/-- The triangle maps in the matching index are themselves opposite faces. -/
theorem matchingIndex_map_mono {n : ℕ} {s t : MatchingIndex n} (f : s ⟶ t) :
    Mono f.hom.right.unop := by
  letI : Mono t.obj.hom.unop := t.property.2
  have h := congrArg Quiver.Hom.unop (StructuredArrow.w f.hom)
  change f.hom.right.unop ≫ s.obj.hom.unop = t.obj.hom.unop at h
  exact mono_of_mono_fac h

/-- The triangle maps in the latching index are themselves opposite surjections. -/
theorem latchingIndex_map_epi {n : ℕ} {s t : LatchingIndex n} (f : s ⟶ t) :
    Epi f.hom.left.unop := by
  letI : Epi s.obj.hom.unop := s.property.2
  have h := congrArg Quiver.Hom.unop (CostructuredArrow.w f.hom)
  change t.obj.hom.unop ≫ f.hom.left.unop = s.obj.hom.unop at h
  exact epi_of_epi_fac h

instance matchingIndexZeroIsEmpty : IsEmpty (MatchingIndex 0) :=
  ⟨fun s ↦ Nat.not_lt_zero _ s.property.1⟩

instance latchingIndexZeroIsEmpty : IsEmpty (LatchingIndex 0) :=
  ⟨fun s ↦ Nat.not_lt_zero _ s.property.1⟩

noncomputable section

variable {C : Type u} [Category.{v} C]

/-- The cone with vertex `W_n` formed by the proper face maps of `W`. -/
def matchingCone (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    Cone (matchingProjection n ⋙ W) where
  pt := W.obj (op ⦋n⦌)
  π :=
    { app := fun s ↦ W.map s.obj.hom
      naturality := by
        intro s t f
        change 𝟙 _ ≫ W.map t.obj.hom = W.map s.obj.hom ≫ W.map f.hom.right
        rw [Category.id_comp, ← W.map_comp]
        exact W.congr_map (StructuredArrow.w f.hom).symm }

/-- The cocone with vertex `W_n` formed by the proper degeneracy maps of `W`. -/
def latchingCocone (n : ℕ) (W : SimplexCategoryᵒᵖ ⥤ C) :
    Cocone (latchingProjection n ⋙ W) where
  pt := W.obj (op ⦋n⦌)
  ι :=
    { app := fun s ↦ W.map s.obj.hom
      naturality := by
        intro s t f
        change W.map f.hom.left ≫ W.map t.obj.hom = W.map s.obj.hom ≫ 𝟙 _
        rw [Category.comp_id, ← W.map_comp]
        exact W.congr_map (CostructuredArrow.w f.hom) }

section Matching

variable [HasLimitsOfSize.{0, 0} C]

/-- Matching object, functorial in the simplicial diagram. -/
def matchingFunctor (n : ℕ) : (SimplexCategoryᵒᵖ ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ _).obj (matchingProjection n) ⋙ lim

/-- The canonical map `W_n ⟶ M_n W`. -/
def matchingComparison (n : ℕ) :
    (evaluation _ C).obj (op ⦋n⦌) ⟶ matchingFunctor n where
  app W := limit.lift _ (matchingCone n W)
  naturality W V f := by
    apply limit.hom_ext
    intro s
    change (f.app _ ≫ limit.lift _ (matchingCone n V)) ≫ limit.π _ s =
      (limit.lift _ (matchingCone n W) ≫ limMap (Functor.whiskerLeft _ f)) ≫ limit.π _ s
    simp only [Category.assoc, limMap_π, limit.lift_π_assoc, limit.lift_π]
    exact (f.naturality s.obj.hom).symm

/-- The degree-zero matching object is terminal. -/
def matchingZeroIsTerminal (W : SimplexCategoryᵒᵖ ⥤ C) :
    IsTerminal ((matchingFunctor 0).obj W) :=
  isLimitEquivIsTerminalOfIsEmpty C (limit.cone (matchingProjection 0 ⋙ W))
    (limit.isLimit _)

/-- The relative matching map `W_n ⟶ M_n W ×[M_n V] V_n`. -/
def relativeMatchingMap (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    W.obj (op ⦋n⦌) ⟶ pullback ((matchingFunctor n).map f) ((matchingComparison n).app V) :=
  pullback.lift ((matchingComparison n).app W) (f.app (op ⦋n⦌))
    ((matchingComparison n).naturality f).symm

/-- The target of the degree-zero relative matching map is canonically `V_0`. -/
def relativeMatchingZeroTargetIso {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    pullback ((matchingFunctor 0).map f) ((matchingComparison 0).app V) ≅ V.obj (op ⦋0⦌) where
  hom := pullback.snd _ _
  inv := pullback.lift ((matchingZeroIsTerminal W).from _) (𝟙 _)
    ((matchingZeroIsTerminal V).hom_ext _ _)
  hom_inv_id := by
    apply pullback.hom_ext
    · exact (matchingZeroIsTerminal W).hom_ext _ _
    · simp
  inv_hom_id := by simp

/-- Under the canonical isomorphism the degree-zero relative map is `f_0`. -/
theorem relativeMatchingMap_zero {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    relativeMatchingMap 0 f ≫ (relativeMatchingZeroTargetIso f).hom = f.app (op ⦋0⦌) :=
  pullback.lift_snd _ _ _

end Matching

section Latching

variable [HasColimitsOfSize.{0, 0} C]

/-- Latching object, functorial in the simplicial diagram. -/
def latchingFunctor (n : ℕ) : (SimplexCategoryᵒᵖ ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ _).obj (latchingProjection n) ⋙ colim

/-- The canonical map `L_n W ⟶ W_n`. -/
def latchingComparison (n : ℕ) :
    latchingFunctor n ⟶ (evaluation _ C).obj (op ⦋n⦌) where
  app W := colimit.desc _ (latchingCocone n W)
  naturality W V f := by
    apply colimit.hom_ext
    intro s
    change colimit.ι _ s ≫ colimMap (Functor.whiskerLeft _ f) ≫
        colimit.desc _ (latchingCocone n V) =
      colimit.ι _ s ≫ colimit.desc _ (latchingCocone n W) ≫ f.app _
    simp only [ι_colimMap_assoc, colimit.ι_desc_assoc, colimit.ι_desc]
    exact (f.naturality s.obj.hom).symm

/-- The degree-zero latching object is initial. -/
def latchingZeroIsInitial (W : SimplexCategoryᵒᵖ ⥤ C) :
    IsInitial ((latchingFunctor 0).obj W) :=
  isColimitEquivIsInitialOfIsEmpty C (colimit.cocone (latchingProjection 0 ⋙ W))
    (colimit.isColimit _)

/-- The relative latching map `W_n ⨿[L_n W] L_n V ⟶ V_n`. -/
def relativeLatchingMap (n : ℕ) {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    pushout ((latchingComparison n).app W) ((latchingFunctor n).map f) ⟶ V.obj (op ⦋n⦌) :=
  pushout.desc (f.app (op ⦋n⦌)) ((latchingComparison n).app V)
    ((latchingComparison n).naturality f).symm

/-- The source of the degree-zero relative latching map is canonically `W_0`. -/
def relativeLatchingZeroSourceIso {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    pushout ((latchingComparison 0).app W) ((latchingFunctor 0).map f) ≅ W.obj (op ⦋0⦌) where
  hom := pushout.desc (𝟙 _) ((latchingZeroIsInitial V).to _)
    ((latchingZeroIsInitial W).hom_ext _ _)
  inv := pushout.inl _ _
  hom_inv_id := by
    apply pushout.hom_ext
    · simp
    · exact (latchingZeroIsInitial V).hom_ext _ _
  inv_hom_id := by simp

/-- Under the canonical isomorphism the degree-zero relative map is `f_0`. -/
theorem relativeLatchingMap_zero {W V : SimplexCategoryᵒᵖ ⥤ C} (f : W ⟶ V) :
    (relativeLatchingZeroSourceIso f).inv ≫ relativeLatchingMap 0 f = f.app (op ⦋0⦌) :=
  pushout.inl_desc _ _ _

end Latching

end

end DaggerModels.PartII
