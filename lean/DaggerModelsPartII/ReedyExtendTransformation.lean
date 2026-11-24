import DaggerModelsPartII.ReedyDegreeFactorization
import DaggerModelsPartII.SimplexReedyFactorization

/-!
# Extending a natural transformation through one degree

For two already-defined simplicial objects, a compatible degree map and
the lower natural transformation determine a natural transformation one
degree further. Naturality for arbitrary maps uses the actual simplex image
factorization, including the identity case in the new highest degree.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace DaggerModels.PartII

/-- The new object when increasing the strict degree bound from `n` to `n+1`. -/
def degreeTop (n : ℕ) : BelowDegree (n + 1) :=
  ⟨op ⦋n⦌, Nat.lt_succ_self n⟩

theorem eq_degreeTop_of_not_below {n : ℕ} (s : BelowDegree (n + 1))
    (h : ¬ s.obj.unop.len < n) : s = degreeTop n := by
  apply ObjectProperty.FullSubcategory.ext
  have hs : s.obj.unop.len < n + 1 := s.property
  exact congrArg op (SimplexCategory.ext _ _ (by
    change s.obj.unop.len = n
    omega))

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]
  {n : ℕ} {Y U : SimplexCategoryᵒᵖ ⥤ C}
  {l : lowerDiagram n Y ⟶ lowerDiagram n U}
  (L : DegreeExtension.Hom l (DegreeExtension.ofDiagram n Y) (DegreeExtension.ofDiagram n U))

/-- The new degree component commutes with each proper face. -/
theorem degreeHom_natural_matching (s : MatchingIndex n) :
    Y.map s.obj.hom ≫ l.app ((matchingBelow n).obj s) = L.app ≫ U.map s.obj.hom := by
  have h := congrArg (fun k ↦ k ≫ limit.π (matchingProjection n ⋙ U) s)
    L.matching_naturality
  change (L.app ≫ limit.lift _ (matchingCone n U)) ≫ limit.π _ s =
    (limit.lift _ (matchingCone n Y) ≫ limMap (Functor.whiskerLeft (matchingBelow n) l)) ≫
      limit.π _ s at h
  simp only [Category.assoc, limMap_π, limit.lift_π_assoc, limit.lift_π] at h
  exact h.symm

/-- The new degree component commutes with each proper degeneracy index. -/
theorem degreeHom_natural_latching (s : LatchingIndex n) :
    Y.map s.obj.hom ≫ L.app = l.app ((latchingBelow n).obj s) ≫ U.map s.obj.hom := by
  have h := congrArg (fun k ↦ colimit.ι (latchingProjection n ⋙ Y) s ≫ k)
    L.latching_naturality
  change colimit.ι _ s ≫ colimMap (Functor.whiskerLeft (latchingBelow n) l) ≫
      colimit.desc _ (latchingCocone n U) =
    colimit.ι _ s ≫ colimit.desc _ (latchingCocone n Y) ≫ L.app at h
  simp only [ι_colimMap_assoc, colimit.ι_desc_assoc] at h
  change l.app ((latchingBelow n).obj s) ≫ colimit.ι (latchingProjection n ⋙ U) s ≫
      colimit.desc _ (latchingCocone n U) = Y.map s.obj.hom ≫ L.app at h
  rw [colimit.ι_desc] at h
  exact h.symm

/-- The components of the extended transformation. -/
def extendDegreeApp (s : BelowDegree (n + 1)) : Y.obj s.obj ⟶ U.obj s.obj :=
  if h : s.obj.unop.len < n then
    l.app ⟨s.obj, h⟩
  else
    let e := eq_degreeTop_of_not_below s h
    eqToHom (congrArg (fun (j : BelowDegree (n + 1)) ↦ Y.obj j.obj) e) ≫ L.app ≫
      eqToHom (congrArg (fun (j : BelowDegree (n + 1)) ↦ U.obj j.obj) e.symm)

theorem extendDegreeApp_of_below (s : BelowDegree (n + 1)) (h : s.obj.unop.len < n) :
    extendDegreeApp L s = l.app ⟨s.obj, h⟩ := by
  rw [extendDegreeApp, dif_pos h]

@[simp] theorem extendDegreeApp_top : extendDegreeApp L (degreeTop n) = L.app := by
  have h : ¬ (degreeTop n).obj.unop.len < n := Nat.lt_irrefl n
  simp only [extendDegreeApp, dif_neg h, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Naturality when the arrow lowers degree through an opposite face. -/
theorem extendDegreeApp_natural_inverse {s t : BelowDegree (n + 1)} (f : s.obj ⟶ t.obj)
    [Mono f.unop] (ht : t.obj.unop.len < n) :
    Y.map f ≫ extendDegreeApp L t = extendDegreeApp L s ≫ U.map f := by
  rw [extendDegreeApp_of_below L t ht]
  by_cases hs : s.obj.unop.len < n
  · rw [extendDegreeApp_of_below L s hs]
    exact l.naturality (ObjectProperty.homMk (X := ⟨s.obj, hs⟩) (Y := ⟨t.obj, ht⟩) f)
  · obtain rfl := eq_degreeTop_of_not_below s hs
    rw [extendDegreeApp_top]
    exact degreeHom_natural_matching L ⟨StructuredArrow.mk f, ⟨ht, show Mono f.unop from inferInstance⟩⟩

/-- Naturality when the arrow raises degree through an opposite surjection. -/
theorem extendDegreeApp_natural_direct {s t : BelowDegree (n + 1)} (f : s.obj ⟶ t.obj)
    [Epi f.unop] (hs : s.obj.unop.len < n) :
    Y.map f ≫ extendDegreeApp L t = extendDegreeApp L s ≫ U.map f := by
  rw [extendDegreeApp_of_below L s hs]
  by_cases ht : t.obj.unop.len < n
  · rw [extendDegreeApp_of_below L t ht]
    exact l.naturality (ObjectProperty.homMk (X := ⟨s.obj, hs⟩) (Y := ⟨t.obj, ht⟩) f)
  · obtain rfl := eq_degreeTop_of_not_below t ht
    rw [extendDegreeApp_top]
    exact degreeHom_natural_latching L ⟨CostructuredArrow.mk f, ⟨hs, show Epi f.unop from inferInstance⟩⟩

/-- The compatible degree component extends the lower natural transformation. -/
def extendDegreeTransformation : lowerDiagram (n + 1) Y ⟶ lowerDiagram (n + 1) U where
  app := extendDegreeApp L
  naturality s t f := by
    change Y.map f.hom ≫ extendDegreeApp L t = extendDegreeApp L s ≫ U.map f.hom
    by_cases hm : (simplexReedyMid f.hom).unop.len < n
    · let m : BelowDegree (n + 1) :=
        ⟨simplexReedyMid f.hom, Nat.lt_succ_of_lt hm⟩
      have hi := extendDegreeApp_natural_inverse L (s := s) (t := m)
        (simplexReedyInverse f.hom) hm
      have hd := extendDegreeApp_natural_direct L (s := m) (t := t)
        (simplexReedyDirect f.hom) hm
      rw [← simplexReedyFactor_fac f.hom, Y.map_comp, U.map_comp, Category.assoc, hd,
        ← Category.assoc (Y.map (simplexReedyInverse f.hom)), hi, Category.assoc]
    · have hs : ¬ s.obj.unop.len < n :=
        fun h ↦ hm (lt_of_le_of_lt (simplexReedyMid_le_source f.hom) h)
      have ht : ¬ t.obj.unop.len < n :=
        fun h ↦ hm (lt_of_le_of_lt (simplexReedyMid_le_target f.hom) h)
      obtain rfl := eq_degreeTop_of_not_below s hs
      obtain rfl := eq_degreeTop_of_not_below t ht
      have hf : f.hom = 𝟙 _ := by
        by_contra h
        exact hm (simplexReedyMid_lt_of_ne_id f.hom h)
      rw [hf, Y.map_id, U.map_id, Category.id_comp, Category.comp_id]

end

end DaggerModels.PartII
