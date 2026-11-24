import DaggerModelsPartII.OrdinaryBergnerGenerators
import OriginalOrdinaryCellComparisonGeometricRecovered
import DaggerModels.SimplicialObjectAdjunctions
import OriginalOrdinaryEndpointTransportReconciled
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Adding one ordinary discrete object

The coproduct of an arbitrary original ordinary simplicial category with the
identity-only point has the original Homs on old objects, the point Hom on
the new object, and empty mixed Homs. The explicit construction permits a
local geometric comparison on the same original maps.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory DaggerModels
open OriginalOrdinaryEndpointTransport
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryPointCoproduct

noncomputable section

abbrev point : SimplicialCat.{u, u} := OrdinaryBergnerGenerators.point.{u}

def emptyHom : SSet.{u} := TwoObjectDaggerGraph.empty

def hom (C : SimplicialCat.{u, u}) :
    C.Obj ⊕ PUnit.{u + 1} → C.Obj ⊕ PUnit.{u + 1} → SSet.{u}
  | .inl x, .inl y => C.enriched.Hom x y
  | .inr x, .inr y => point.enriched.Hom x y
  | _, _ => emptyHom

def identity (C : SimplicialCat.{u, u}) (x : C.Obj ⊕ PUnit.{u + 1}) :
    𝟙_ SSet.{u} ⟶ hom C x x := by
  cases x with
  | inl x => exact C.enriched.id x
  | inr x => exact point.enriched.id x

def composition (C : SimplicialCat.{u, u})
    (x y z : C.Obj ⊕ PUnit.{u + 1}) : hom C x y ⊗ hom C y z ⟶ hom C x z := by
  cases x <;> cases y <;> cases z
  · exact C.enriched.comp _ _ _
  all_goals first
    | exact point.enriched.comp _ _ _
    | exact { app := fun _ p ↦ by first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2,
              naturality := by
                intros; funext p
                first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2 }

def enrichment (C : SimplicialCat.{u, u}) :
    EnrichedCategory SSet.{u} (C.Obj ⊕ PUnit.{u + 1}) where
  Hom := hom C
  id := identity C
  comp := composition C
  id_comp x y := by
    rcases x with x | x <;> rcases y with y | y
    · exact C.enriched.id_comp x y
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · exact point.enriched.id_comp x y
  comp_id x y := by
    rcases x with x | x <;> rcases y with y | y
    · exact C.enriched.comp_id x y
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · apply NatTrans.ext; funext q p; exact PEmpty.elim p
    · exact point.enriched.comp_id x y
  assoc x y z t := by
    rcases x with x | x <;> rcases y with y | y <;>
      rcases z with z | z <;> rcases t with t | t
    case inl.inl.inl.inl => exact C.enriched.assoc x y z t
    case inr.inr.inr.inr => exact point.enriched.assoc x y z t
    all_goals
      apply NatTrans.ext
      funext q p
      first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2.1 | exact PEmpty.elim p.2.2

/-- Literal ordinary category with its old and new objects tagged. -/
def cat (C : SimplicialCat.{u, u}) : SimplicialCat.{u, u} :=
  ⟨C.Obj ⊕ PUnit.{u + 1}, enrichment C⟩

def inOld (C : SimplicialCat.{u, u}) : C ⟶ cat C where
  obj := Sum.inl
  map _ _ := 𝟙 _
  map_id _ := by change _ ≫ (𝟙 _) = _; exact Category.comp_id _
  map_comp x y z := by
    change C.enriched.comp x y z ≫ (𝟙 _) =
      ((𝟙 _) ⊗ₘ (𝟙 _)) ≫ C.enriched.comp x y z
    simp

def inPoint (C : SimplicialCat.{u, u}) : point ⟶ cat C where
  obj := Sum.inr
  map _ _ := 𝟙 _
  map_id _ := by change _ ≫ (𝟙 _) = _; exact Category.comp_id _
  map_comp x y z := by
    change point.enriched.comp x y z ≫ (𝟙 _) =
      ((𝟙 _) ⊗ₘ (𝟙 _)) ≫ point.enriched.comp x y z
    simp

@[simp] theorem inOld_obj (C : SimplicialCat.{u, u}) (x : C.Obj) :
    (inOld C).obj x = Sum.inl x := rfl

@[simp] theorem inPoint_obj (C : SimplicialCat.{u, u}) (x : PUnit.{u + 1}) :
    (inPoint C).obj x = Sum.inr x := rfl

@[simp] theorem inOld_map (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    (inOld C).map x y = 𝟙 (C.enriched.Hom x y) := rfl

@[simp] theorem inPoint_map (C : SimplicialCat.{u, u}) (x y : PUnit.{u + 1}) :
    (inPoint C).map x y = 𝟙 (point.enriched.Hom x y) := rfl

theorem inOld_obj_injective (C : SimplicialCat.{u, u}) :
    Function.Injective (inOld C).obj := Sum.inl_injective

instance inOld_map_isIso (C : SimplicialCat.{u, u}) (x y : C.Obj) :
    IsIso ((inOld C).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

/-- A pair of enriched functors determines a functor from the explicit sum. -/
def desc {C D : SimplicialCat.{u, u}} (F : C ⟶ D) (g : point ⟶ D) : cat C ⟶ D where
  obj
    | .inl x => F.obj x
    | .inr x => g.obj x
  map
    | .inl x, .inl y => F.map x y
    | .inr x, .inr y => g.map x y
    | .inl _, .inr _ => TwoObjectDaggerGraph.emptyMap _
    | .inr _, .inl _ => TwoObjectDaggerGraph.emptyMap _
  map_id x := by
    cases x with
    | inl x => exact F.map_id x
    | inr x => exact g.map_id x
  map_comp x y z := by
    cases x <;> cases y <;> cases z
    · exact F.map_comp _ _ _
    all_goals first
      | exact g.map_comp _ _ _
      | apply NatTrans.ext
        funext q p
        first | exact PEmpty.elim p.1 | exact PEmpty.elim p.2

@[simp] theorem inOld_desc {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (g : point ⟶ D) : inOld C ≫ desc F g = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  change (𝟙 _) ≫ F.map x y = F.map x y
  simp

@[simp] theorem inPoint_desc {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (g : point ⟶ D) : inPoint C ≫ desc F g = g := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro x y
  change (𝟙 _) ≫ g.map x y = g.map x y
  simp

/-- Two functors from the sum agree when their old and point restrictions
agree; mixed Hom maps are unique from the empty simplicial set. -/
theorem hom_ext {C D : SimplicialCat.{u, u}} {H J : cat C ⟶ D}
    (hOld : inOld C ≫ H = inOld C ≫ J)
    (hPoint : inPoint C ≫ H = inPoint C ≫ J) : H = J := by
  apply EnrichedFunctor.ext SSet (fun z ↦ by
    cases z with
    | inl x => exact congrArg (fun T : C ⟶ D ↦ T.obj x) hOld
    | inr x => exact congrArg (fun T : point ⟶ D ↦ T.obj x) hPoint)
  intro a b
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      simpa only [SimplicialCat.comp_map, inOld_map, Category.id_comp]
        using map_of_eq hOld a b
    | inr b =>
      exact (TwoObjectDaggerGraph.emptyMap_unique _).trans
        (TwoObjectDaggerGraph.emptyMap_unique _).symm
  | inr a =>
    cases b with
    | inl b =>
      exact (TwoObjectDaggerGraph.emptyMap_unique _).trans
        (TwoObjectDaggerGraph.emptyMap_unique _).symm
    | inr b =>
      simpa only [SimplicialCat.comp_map, inPoint_map, Category.id_comp]
        using map_of_eq hPoint a b

/-- The explicit category is the binary coproduct of the original category
and the original ordinary identity-only point. -/
def isColimit (C : SimplicialCat.{u, u}) :
    IsColimit (BinaryCofan.mk (inOld C) (inPoint C)) :=
  BinaryCofan.IsColimit.mk _ (fun F g ↦ desc F g)
    (fun F g ↦ inOld_desc F g)
    (fun F g ↦ inPoint_desc F g)
    (fun F g _H hOld hPoint ↦
      hom_ext (hOld.trans (inOld_desc F g).symm)
        (hPoint.trans (inPoint_desc F g).symm))

/-- The old inclusion has the exact embedding properties needed for
filtered local comparison. -/
theorem inOld_embedding (C : SimplicialCat.{u, u}) :
    Function.Injective (inOld C).obj ∧
      ∀ x y : C.Obj, Mono ((inOld C).map x y) := by
  refine ⟨inOld_obj_injective C, ?_⟩
  intro x y
  letI : IsIso ((inOld C).map x y) := inOld_map_isIso C x y
  infer_instance

/-- The actual comparison induced by a functor and the identity on the
new discrete point. -/
def extension {C D : SimplicialCat.{u, u}} (F : C ⟶ D) : cat C ⟶ cat D :=
  desc (F ≫ inOld D) (inPoint D)

@[simp] theorem extension_old {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    inOld C ≫ extension F = F ≫ inOld D := inOld_desc _ _

@[simp] theorem extension_point {C D : SimplicialCat.{u, u}} (F : C ⟶ D) :
    inPoint C ≫ extension F = inPoint D := inPoint_desc _ _

@[simp] theorem extension_obj_old {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : C.Obj) :
    (extension F).obj (Sum.inl x) = Sum.inl (F.obj x) := rfl

@[simp] theorem extension_obj_point {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : PUnit.{u + 1}) :
    (extension F).obj (Sum.inr x) = Sum.inr x := rfl

@[simp] theorem extension_map_old {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x y : C.Obj) :
    (extension F).map (Sum.inl x) (Sum.inl y) = F.map x y := by
  change F.map x y ≫ 𝟙 _ = F.map x y
  simp

@[simp] theorem extension_map_point {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x y : PUnit.{u + 1}) :
    (extension F).map (Sum.inr x) (Sum.inr y) = 𝟙 _ := rfl

@[simp] theorem extension_map_mixed_left {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : C.Obj) (y : PUnit.{u + 1}) :
    (extension F).map (Sum.inl x) (Sum.inr y) = 𝟙 emptyHom := by
  exact (TwoObjectDaggerGraph.emptyMap_unique _).trans
    (TwoObjectDaggerGraph.emptyMap_unique (𝟙 emptyHom)).symm

@[simp] theorem extension_map_mixed_right {C D : SimplicialCat.{u, u}}
    (F : C ⟶ D) (x : PUnit.{u + 1}) (y : C.Obj) :
    (extension F).map (Sum.inr x) (Sum.inl y) = 𝟙 emptyHom := by
  exact (TwoObjectDaggerGraph.emptyMap_unique _).trans
    (TwoObjectDaggerGraph.emptyMap_unique (𝟙 emptyHom)).symm

private theorem GW_id (X : SSet.{u}) :
    DaggerOrdinaryCellComparisonGeometric.GW (𝟙 X) := by
  change SSet.KanComplex.W
    (TopCat.toSSet.map (SSet.toTop.map (𝟙 X)))
  exact (KanQuillenReuse.weakEquivalence_iff_geometric (𝟙 X)).mp inferInstance

/-- Adding the same identity-only object preserves the original local
geometric weak equivalence on every Hom of the comparison. -/
theorem extension_local {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (hF : ∀ x y : C.Obj,
      DaggerOrdinaryCellComparisonGeometric.GW (F.map x y))
    (x y : (cat C).Obj) :
    DaggerOrdinaryCellComparisonGeometric.GW ((extension F).map x y) := by
  cases x with
  | inl x =>
    cases y with
    | inl y => simpa only [extension_map_old] using hF x y
    | inr y => simpa only [extension_map_mixed_left] using GW_id emptyHom
  | inr x =>
    cases y with
    | inl y => simpa only [extension_map_mixed_right] using GW_id emptyHom
    | inr y => simpa only [extension_map_point] using GW_id (point.enriched.Hom x y)

private def emptyIsInitial : IsInitial OrdinaryBergnerGenerators.empty.{u} := by
  letI : PreservesColimitsOfSize.{0, 0} DaggerSimplicialCat.forget.{u, u} :=
    DaggerSimplicialCat.Cofree.forget_preservesColimitsOfSize
  exact DaggerDiscreteObjects.emptyIsInitial.isInitialObj
    DaggerSimplicialCat.forget DaggerDiscreteObjects.empty

/-- The actual ordinary empty-to-point generator has the explicit point sum
as its pushout along every map from the initial category. -/
theorem point_cell_isPushout (C : SimplicialCat.{u, u})
    (a : OrdinaryBergnerGenerators.empty.{u} ⟶ C) :
    IsPushout a OrdinaryBergnerGenerators.emptyToPoint
      (inOld C) (inPoint C) := by
  have h := IsPushout.of_is_coproduct' (isColimit C) emptyIsInitial
  have ha : a = emptyIsInitial.to C := emptyIsInitial.hom_ext _ _
  have hp : OrdinaryBergnerGenerators.emptyToPoint.{u} =
      emptyIsInitial.to point := emptyIsInitial.hom_ext _ _
  rw [ha, hp]
  exact h

end

end DaggerModels.OrdinaryPointCoproduct
