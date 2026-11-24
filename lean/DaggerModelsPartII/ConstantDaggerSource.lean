import DaggerModelsPartII.DaggerSimplexFreeProperty
import NativeDaggerDegreeCotensor

/-!
# Constant-source dagger enriched functors

The mapping space of simplicial maps from a constant simplicial set is
controlled by degree zero.  This lifts to enriched dagger functors whose
source is an ordinary dagger category with constant mapping spaces.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerOriginalSimplicialDegreeCategory DaggerNativeDaggerDegreeCotensor
open DaggerUnitaryDiscrete

universe u

namespace DaggerModels.PartII.ConstantDaggerSource

noncomputable section

/-- A map out of a constant simplicial set, specified by its degree-zero values. -/
def fromZero (S : Type u) (X : SSet.{u})
    (f : S → X.obj (op ⦋0⦌)) : constSSet S ⟶ X where
  app q s := X.map (SimplexCategory.const q.unop ⦋0⦌ 0).op (f s)
  naturality q r α := by
    funext s
    have h : (SimplexCategory.const q.unop ⦋0⦌ 0).op ≫ α =
        (SimplexCategory.const r.unop ⦋0⦌ 0).op := by
      apply Quiver.Hom.unop_inj
      exact SimplexCategory.eq_const_to_zero _
    change X.map (SimplexCategory.const r.unop ⦋0⦌ 0).op (f s) =
      X.map α (X.map (SimplexCategory.const q.unop ⦋0⦌ 0).op (f s))
    rw [← FunctorToTypes.map_comp_apply, h]

/-- Evaluation at degree zero of a map out of a constant simplicial set. -/
def toZero (S : Type u) (X : SSet.{u}) (f : constSSet S ⟶ X) :
    S → X.obj (op ⦋0⦌) := f.app (op ⦋0⦌)

@[simp] theorem toZero_fromZero (S : Type u) (X : SSet.{u})
    (f : S → X.obj (op ⦋0⦌)) : toZero S X (fromZero S X f) = f := by
  funext s
  simp [toZero, fromZero, SimplexCategory.const_eq_id]

@[simp] theorem fromZero_toZero (S : Type u) (X : SSet.{u})
    (f : constSSet S ⟶ X) : fromZero S X (toZero S X f) = f := by
  apply NatTrans.ext
  funext q s
  have h := congrFun (f.naturality
    (SimplexCategory.const q.unop ⦋0⦌ 0).op) s
  exact h.symm

def fromZeroEquiv (S : Type u) (X : SSet.{u}) :
    (S → X.obj (op ⦋0⦌)) ≃ (constSSet S ⟶ X) where
  toFun := fromZero S X
  invFun := toZero S X
  left_inv := toZero_fromZero S X
  right_inv := fromZero_toZero S X

variable {A : Type u} [Category.{u} A] [DaggerCategory A]
  {D : DaggerSimplicialCat.{u, u}}

local instance ordinarySourceCategory : Category.{u} (ordinaryEnrichment A).Obj :=
  inferInstanceAs (Category.{u} A)

local instance degreeZeroDagger : DaggerCategory
    (degreeObjects D.toSimplicialCat (op ⦋0⦌)) :=
  degreeDaggerCategory D (op ⦋0⦌)

/-- Restrict a constant-source dagger functor to degree zero. -/
def toOrdinary (F : ordinaryEnrichment A ⟶ D) :
    A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) :=
  degreeFunctor F.toEnrichedFunctor (op ⦋0⦌)

instance toOrdinary_preservesDagger (F : ordinaryEnrichment A ⟶ D) :
    DaggerFunctor (toOrdinary F) where
  map_dagger f := by
    exact (congrFun (congr_app (F.map_dagger _ _) (op ⦋0⦌)) f).symm

/-- Extend a degree-zero ordinary functor over all simplicial degrees. -/
def fromOrdinary (G : A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌))
    [DaggerFunctor G] : ordinaryEnrichment A ⟶ D where
  toEnrichedFunctor := {
    obj := G.obj
    map x y := fromZero ((x : A) ⟶ (y : A)) (D.enriched.Hom (G.obj x) (G.obj y))
      (fun f => G.map f)
    map_id x := by
      apply NatTrans.ext
      funext q s
      let p : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
      have h := congrFun ((D.enriched.id (G.obj x)).naturality p) PUnit.unit
      change (D.enriched.Hom (G.obj x) (G.obj x)).map p (G.map (𝟙 x)) =
        (D.enriched.id (G.obj x)).app q PUnit.unit
      rw [G.map_id]
      exact h.symm
    map_comp x y z := by
      apply NatTrans.ext
      funext q fg
      let p : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
      have h := congrFun ((D.enriched.comp (G.obj x) (G.obj y) (G.obj z)).naturality p)
        (G.map fg.1, G.map fg.2)
      change (D.enriched.Hom (G.obj x) (G.obj z)).map p (G.map (fg.1 ≫ fg.2)) =
        (D.enriched.comp (G.obj x) (G.obj y) (G.obj z)).app q
          ((D.enriched.Hom (G.obj x) (G.obj y)).map p (G.map fg.1),
            (D.enriched.Hom (G.obj y) (G.obj z)).map p (G.map fg.2))
      rw [G.map_comp]
      exact h.symm
  }
  map_dagger x y := by
    apply NatTrans.ext
    funext q f
    let p : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
    have h := congrFun ((D.daggerStructure.dagger (G.obj x) (G.obj y)).naturality p)
      (G.map f)
    change (D.daggerStructure.dagger (G.obj x) (G.obj y)).app q
        ((D.enriched.Hom (G.obj x) (G.obj y)).map p (G.map f)) =
      (D.enriched.Hom (G.obj y) (G.obj x)).map p (G.map (dagger f))
    rw [DaggerFunctor.map_dagger]
    exact h

@[simp] theorem to_from
    (G : {G : A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) // DaggerFunctor G}) :
    toOrdinary (@fromOrdinary A _ _ D G.1 G.2) = G.1 := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro x
    rfl
  case h_map =>
    intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact congrFun (toZero_fromZero (x ⟶ y)
      (D.enriched.Hom (G.1.obj x) (G.1.obj y)) (fun h => G.1.map h)) f

@[simp] theorem from_to (F : ordinaryEnrichment A ⟶ D) :
    @fromOrdinary A _ _ D (toOrdinary F) (toOrdinary_preservesDagger F) = F := by
  apply DaggerSimplicialCat.Hom.ext
  apply EnrichedFunctor.ext SSet
    (F := (@fromOrdinary A _ _ D (toOrdinary F)
      (toOrdinary_preservesDagger F)).toEnrichedFunctor)
    (G := F.toEnrichedFunctor) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact fromZero_toZero (x ⟶ y) (D.enriched.Hom (F.obj x) (F.obj y)) (F.map x y)

/-- Constant-source enriched dagger functors are precisely degree-zero dagger functors. -/
def homEquiv :
    {G : A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) // DaggerFunctor G} ≃
      (ordinaryEnrichment A ⟶ D) where
  toFun G := @fromOrdinary A _ _ D G.1 G.2
  invFun F := ⟨toOrdinary F, toOrdinary_preservesDagger F⟩
  left_inv G := Subtype.ext (to_from G)
  right_inv := from_to

section Ordinary

variable {E : SimplicialCat.{u, u}}

local instance constantSourceCategory : Category.{u}
    (DaggerActualConstantSimplicialCategory.constant A).Obj :=
  inferInstanceAs (Category.{u} A)

local instance constantSourceEnriched : EnrichedCategory SSet.{u}
    (DaggerActualConstantSimplicialCategory.constant A).Obj :=
  (DaggerActualConstantSimplicialCategory.constant A).enriched

/-- The ordinary version, without a dagger condition, for the forgetful side
of the free dagger simplicial category adjunction. -/
def fromOrdinarySimplicial
    (G : A ⥤ degreeObjects E (op ⦋0⦌)) :
    DaggerActualConstantSimplicialCategory.constant A ⟶ E where
  obj := G.obj
  map x y := fromZero ((x : A) ⟶ (y : A))
    (E.enriched.Hom (G.obj x) (G.obj y)) (fun f => G.map f)
  map_id x := by
    apply NatTrans.ext
    funext q s
    let p : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
    have h := congrFun ((E.enriched.id (G.obj x)).naturality p) PUnit.unit
    change (E.enriched.Hom (G.obj x) (G.obj x)).map p (G.map (𝟙 x)) =
      (E.enriched.id (G.obj x)).app q PUnit.unit
    rw [G.map_id]
    exact h.symm
  map_comp x y z := by
    apply NatTrans.ext
    funext q fg
    let p : op ⦋0⦌ ⟶ q := (SimplexCategory.const q.unop ⦋0⦌ 0).op
    have h := congrFun ((E.enriched.comp (G.obj x) (G.obj y) (G.obj z)).naturality p)
      (G.map fg.1, G.map fg.2)
    change (E.enriched.Hom (G.obj x) (G.obj z)).map p (G.map (fg.1 ≫ fg.2)) =
      (E.enriched.comp (G.obj x) (G.obj y) (G.obj z)).app q
        ((E.enriched.Hom (G.obj x) (G.obj y)).map p (G.map fg.1),
          (E.enriched.Hom (G.obj y) (G.obj z)).map p (G.map fg.2))
    rw [G.map_comp]
    exact h.symm

def toOrdinarySimplicial
    (F : DaggerActualConstantSimplicialCategory.constant A ⟶ E) :
    A ⥤ degreeObjects E (op ⦋0⦌) := degreeFunctor F (op ⦋0⦌)

omit [DaggerCategory A] in
@[simp] theorem to_fromSimplicial
    (G : A ⥤ degreeObjects E (op ⦋0⦌)) :
    toOrdinarySimplicial (fromOrdinarySimplicial G) = G := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro x
    rfl
  case h_map =>
    intro x y f
    simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrFun (toZero_fromZero (x ⟶ y)
        (E.enriched.Hom (G.obj x) (G.obj y)) (fun h => G.map h)) f

omit [DaggerCategory A] in
@[simp] theorem from_toSimplicial
    (F : DaggerActualConstantSimplicialCategory.constant A ⟶ E) :
    fromOrdinarySimplicial (toOrdinarySimplicial F) = F := by
  apply EnrichedFunctor.ext SSet
    (F := fromOrdinarySimplicial (toOrdinarySimplicial F))
    (G := F) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  exact fromZero_toZero (x ⟶ y) (E.enriched.Hom (F.obj x) (F.obj y)) (F.map x y)

/-- Every simplicial functor from a constant enrichment is determined in degree zero. -/
def simplicialHomEquiv :
    (A ⥤ degreeObjects E (op ⦋0⦌)) ≃
      (DaggerActualConstantSimplicialCategory.constant A ⟶ E) where
  toFun := fromOrdinarySimplicial
  invFun := toOrdinarySimplicial
  left_inv := to_fromSimplicial
  right_inv := from_toSimplicial

end Ordinary

end

end DaggerModels.PartII.ConstantDaggerSource
