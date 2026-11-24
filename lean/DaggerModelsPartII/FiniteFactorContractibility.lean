import SSetGluingPushouts
import TopCatModelCategory.SSet.FactorThruFinite

/-! A finite-support criterion for weak contractibility of a simplicial set. -/

set_option autoImplicit false

open CategoryTheory Limits Simplicial HomotopicalAlgebra MonoidalCategory
open DaggerSSetGluing CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.FiniteFactorContractibility

noncomputable section

universe u

private abbrev singularRealization (X : SSet.{u}) := TopCat.toSSet.obj (SSet.toTop.obj X)

private abbrev toPoint (X : SSet.{u}) := SSet.stdSimplex.isTerminalObj₀.from X

private theorem unit_point (X : SSet.{u}) :
    sSetTopAdj.unit.app X ≫ toPoint (singularRealization X) = toPoint X :=
  SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

private theorem singular_point_weak (X : SSet.{u}) :
    WeakEquivalence (toPoint (singularRealization X)) ↔ WeakEquivalence (toPoint X) := by
  rw [← weakEquivalence_precomp_iff (sSetTopAdj.unit.app X), unit_point]

private theorem boundary_extension (Y : SSet.{u}) (hY : GW (toPoint Y))
    (n : ℕ) (f : (SSet.boundary.{u} n).toSSet ⟶ singularRealization Y) :
    ∃ g : (Δ[n] : SSet.{u}) ⟶ singularRealization Y, (SSet.boundary.{u} n).ι ≫ g = f := by
  have hf : Fibration (toPoint (singularRealization Y)) :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  have hw := (singular_point_weak Y).mpr ((weakEquivalence_iff_GW _).mpr hY)
  haveI := (DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial _).mpr ⟨hf, hw⟩ n
  let sq : CommSq f (SSet.boundary.{u} n).ι (toPoint (singularRealization Y)) (toPoint _) :=
    ⟨SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

private theorem boundary_extension_of_homotopy {Z : SSet.{u}} [IsFibrant Z]
    {n : ℕ} {f g : (SSet.boundary.{u} n).toSSet ⟶ Z} (H : SSet.Homotopy f g)
    (l : (Δ[n] : SSet.{u}) ⟶ Z) (hl : (SSet.boundary.{u} n).ι ≫ l = g) :
    ∃ m : (Δ[n] : SSet.{u}) ⟶ Z, (SSet.boundary.{u} n).ι ≫ m = f := by
  let p := toPoint Z
  haveI : Fibration p :=
    (isFibrant_iff_of_isTerminal _ SSet.stdSimplex.isTerminalObj₀).mp inferInstance
  obtain ⟨ψ, _, hψ, _⟩ := SSet.homotopy_extension_property₁
    (SSet.boundary.{u} n).ι p H.h l (hl.trans H.h₁.symm)
    (toPoint ((Δ[n] : SSet.{u}) ⊗ Δ[1]))
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
    (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _)
  refine ⟨SSet.ι₀ ≫ ψ, ?_⟩
  rw [← SSet.ι₀_comp_assoc, hψ, H.h₀]

/-- It suffices for the inclusion of each finite subcomplex to be homotopic,
after singular realization, to a map through a weakly contractible simplicial set. -/
theorem point_GW_of_finite_factor_up_to_homotopy (X : SSet.{u})
    (h : ∀ A : X.Subcomplex, A.toSSet.IsFinite →
      ∃ (Y : SSet.{u}) (i : A.toSSet ⟶ Y) (j : Y ⟶ X), GW (toPoint Y) ∧
        Nonempty (SSet.Homotopy
          (TopCat.toSSet.map (SSet.toTop.map A.ι))
          (TopCat.toSSet.map (SSet.toTop.map (i ≫ j))))) :
    GW (toPoint X) := by
  apply (weakEquivalence_iff_GW _).mp
  apply (singular_point_weak X).mp
  apply And.right
    ((DaggerModels.KanQuillenReuse.boundary_lifting_iff_trivial
      (toPoint (singularRealization X))).mp ?_)
  intro n
  constructor
  intro f g _sq
  let e := sSetTopAdj.homEquiv (SSet.boundary.{u} n).toSSet (SSet.toTop.obj X)
  obtain ⟨A, hA, k, hk⟩ := SSet.exists_factor_thru_finite_of_topCatHom (e.symm f)
  obtain ⟨Y, i, j, hY, ⟨H⟩⟩ := h A hA
  let fA := (sSetTopAdj.homEquiv _ (SSet.toTop.obj A.toSSet)) k
  let fY := fA ≫ TopCat.toSSet.map (SSet.toTop.map i)
  obtain ⟨l, hl⟩ := boundary_extension Y hY n fY
  have hleft : fA ≫ TopCat.toSSet.map (SSet.toTop.map A.ι) = f := by
    dsimp only [fA]
    rw [← sSetTopAdj.homEquiv_naturality_right, ← hk]
    exact e.apply_symm_apply f
  have hright : fA ≫ TopCat.toSSet.map (SSet.toTop.map (i ≫ j)) =
      fY ≫ TopCat.toSSet.map (SSet.toTop.map j) := by
    rw [SSet.toTop.map_comp, TopCat.toSSet.map_comp, ← Category.assoc]
  have hH := (H.precomp fA).congr hleft hright
  obtain ⟨m, hm⟩ := boundary_extension_of_homotopy hH
    (l ≫ TopCat.toSSet.map (SSet.toTop.map j)) (by rw [← Category.assoc, hl])
  exact ⟨⟨m, hm, SSet.stdSimplex.isTerminalObj₀.hom_ext _ _⟩⟩

/-- A simplicial set is weakly contractible if every finite subcomplex
inclusion factors through a weakly contractible simplicial set. -/
theorem point_GW_of_finite_factor (X : SSet.{u})
    (h : ∀ A : X.Subcomplex, A.toSSet.IsFinite →
      ∃ (Y : SSet.{u}) (i : A.toSSet ⟶ Y) (j : Y ⟶ X), GW (toPoint Y) ∧ i ≫ j = A.ι) :
    GW (toPoint X) := by
  apply point_GW_of_finite_factor_up_to_homotopy
  intro A hA
  obtain ⟨Y, i, j, hY, hij⟩ := h A hA
  refine ⟨Y, i, j, hY, ?_⟩
  rw [hij]
  exact ⟨SSet.Homotopy.mk (fst _ _ ≫ TopCat.toSSet.map (SSet.toTop.map A.ι))
    (by simp) (by simp)⟩

/-- Nullhomotopies of the inclusions of the finite subcomplexes suffice for
weak contractibility. Each homotopy may choose its own vertex. -/
theorem point_GW_of_finite_nullhomotopy (X : SSet.{u})
    (h : ∀ A : X.Subcomplex, A.toSSet.IsFinite →
      ∃ v : (Δ[0] : SSet.{u}) ⟶ X,
        Nonempty (SSet.Homotopy
          (TopCat.toSSet.map (SSet.toTop.map A.ι))
          (TopCat.toSSet.map (SSet.toTop.map (toPoint A.toSSet ≫ v))))) :
    GW (toPoint X) := by
  apply point_GW_of_finite_factor_up_to_homotopy
  intro A hA
  obtain ⟨v, hv⟩ := h A hA
  refine ⟨Δ[0], toPoint A.toSSet, v, ?_, hv⟩
  have ht : toPoint (Δ[0] : SSet.{u}) = 𝟙 _ :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht, ← weakEquivalence_iff_GW]
  infer_instance

end

end DaggerModels.PartII.FiniteFactorContractibility
