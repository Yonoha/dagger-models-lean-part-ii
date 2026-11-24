import SSetFamilyBasedPi
import SimplicialSetLocalSystemMorphismFibration
import NativeBasedPiWeakPullback
import NativeSimplicialReplacement

/-!
# Positive based homotopy groups of the original simplicial replacement

The row comparison retains the entire base chain. Its source is the
original replacement, and its target is the local system of the original
total based homotopy-group functor.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Simplicial Opposite HomotopicalAlgebra
open SSet.KanComplex
open DaggerNativeSimplicialReplacementCells (first initialArrow family)
open DaggerNativeBasedPiFreeEvaluationPullback (basedRows vertexRows basedProjection)
open DaggerNativeTotalBasedPiFunctor (totalPiFunctor vertexProjection)
open DaggerOriginalProductGadget (familyInclusion)
open DaggerSSetFamilyBasedPi (familyTotalPiEquiv familyTotalPiEquiv_apply)
open DaggerModels.PartII.SimplicialSetLocalSystem
open DaggerModels.PartII.SimplicialSetLocalSystemMorphismFibration
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.SimplicialReplacementBasedPi

noncomputable section

variable {C : Type u} [Category.{u} C] (G : C ⥤ SSet.{u})
variable [∀ a, IsFibrant (G.obj a)] (n : ℕ)

private instance familyValueFibrant (q : SimplexCategoryᵒᵖ) :
    ∀ c : (nerve C).obj q, IsFibrant ((family G q) c) :=
  fun c ↦ show IsFibrant (G.obj (first c)) from inferInstance

private theorem familyTotalPiEquiv_pair {I : Type u} (X : I → SSet.{u})
    [∀ i, IsFibrant (X i)] (i : I) (z : (totalPiFunctor (n + 1)).obj (X i)) :
    familyTotalPiEquiv X n ⟨i, z⟩ =
      (totalPiFunctor (n + 1)).map (familyInclusion X i) z := by
  rcases z with ⟨x, s⟩
  rw [familyTotalPiEquiv_apply]
  rfl

omit [∀ a, IsFibrant (G.obj a)] in
/-- The inclusion of one original value commutes with the complete
horizontal replacement operator, including the initial-arrow map. -/
private theorem familyInclusion_horizontal {q r : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (c : (nerve C).obj q) :
    familyInclusion (family G q) c ≫
        (DaggerNativeSimplicialReplacement.replacement G).map α =
      G.map (initialArrow α c) ≫
        familyInclusion (family G r) ((nerve C).map α c) := by
  apply NatTrans.ext
  rfl

/-- Naturality on every complete chain and every actual based class. -/
private theorem familyTotalPiEquiv_horizontal {q r : SimplexCategoryᵒᵖ}
    (α : q ⟶ r) (c : (nerve C).obj q)
    (z : (totalPiFunctor (n + 1)).obj (G.obj (first c))) :
    (totalPiFunctor (n + 1)).map
        ((DaggerNativeSimplicialReplacement.replacement G).map α)
        (familyTotalPiEquiv (family G q) n ⟨c, z⟩) =
      familyTotalPiEquiv (family G r) n
        ⟨(nerve C).map α c,
          (totalPiFunctor (n + 1)).map (G.map (initialArrow α c)) z⟩ := by
  letI : ∀ d : (nerve C).obj q, IsFibrant ((family G q) d) := fun _ ↦ inferInstance
  letI : ∀ d : (nerve C).obj r, IsFibrant ((family G r) d) := fun _ ↦ inferInstance
  rw [familyTotalPiEquiv_pair n (family G q) c z]
  rw [familyTotalPiEquiv_pair n (family G r)]
  calc
    (totalPiFunctor (n + 1)).map
        ((DaggerNativeSimplicialReplacement.replacement G).map α)
        ((totalPiFunctor (n + 1)).map (familyInclusion (family G q) c) z) =
      (totalPiFunctor (n + 1)).map
        (familyInclusion (family G q) c ≫
          (DaggerNativeSimplicialReplacement.replacement G).map α) z := by
            rw [(totalPiFunctor (n + 1)).map_comp]
            rfl
    _ = (totalPiFunctor (n + 1)).map
        (G.map (initialArrow α c) ≫
          familyInclusion (family G r) ((nerve C).map α c)) z := by
            rw [familyInclusion_horizontal]
    _ = (totalPiFunctor (n + 1)).map
        (familyInclusion (family G r) ((nerve C).map α c))
          ((totalPiFunctor (n + 1)).map (G.map (initialArrow α c)) z) := by
            rw [(totalPiFunctor (n + 1)).map_comp]
            rfl

/-- The exact local-system comparison, in the direction from the
original based rows to the chain-indexed local system. -/
def basedRowsIso :
    basedRows (DaggerNativeSimplicialReplacement.replacement G) (n + 1) ≅
      localSystem (G ⋙ totalPiFunctor (n + 1)) :=
  (NatIso.ofComponents (fun q ↦ by
    letI : ∀ c : (nerve C).obj q, IsFibrant ((family G q) c) :=
      fun _ ↦ inferInstance
    exact (familyTotalPiEquiv (family G q) n).toIso) (by
      intro q r α
      funext z
      rcases z with ⟨c, z⟩
      exact (familyTotalPiEquiv_horizontal G n α c z).symm)).symm

/-- The original vertex rows are literally indexed by the same
complete chains and their initial-object vertices. -/
def vertexRowsIso :
    vertexRows (DaggerNativeSimplicialReplacement.replacement G) ≅
      localSystem (G ⋙ SSet.evaluation.obj (op ⦋0⦌)) :=
  NatIso.ofComponents (fun q ↦ Iso.refl _) (by
    intro q r α
    rfl)

/-- The actual original based projection is the local-system map
of the whiskered original vertex projection. -/
theorem basedProjection_square :
    (basedRowsIso G n).hom ≫
        mapSystem (Functor.whiskerLeft G (vertexProjection (n + 1))) =
      basedProjection (DaggerNativeSimplicialReplacement.replacement G) (n + 1) ≫
        (vertexRowsIso G).hom := by
  apply NatTrans.ext
  funext q z
  letI : ∀ c : (nerve C).obj q, IsFibrant ((family G q) c) :=
    fun _ ↦ inferInstance
  let e := familyTotalPiEquiv (family G q) n
  obtain ⟨⟨c, ⟨x, s⟩⟩, rfl⟩ := e.surjective z
  change (⟨c, x⟩ :
      (localSystem (G ⋙ SSet.evaluation.obj (op ⦋0⦌))).obj q) =
    (e ⟨c, ⟨x, s⟩⟩).1
  rw [familyTotalPiEquiv_apply]

/-- The fiber of the whiskered vertex projection at an original
vertex is the original based homotopy group at that vertex. -/
def fiberPiEquiv (a : C) (x : (G.obj a) _⦋0⦌) :
    fiber (Functor.whiskerLeft G (vertexProjection (n + 1))) a x ≃
      π (n + 1) (G.obj a) x where
  toFun z := by
    rcases z with ⟨⟨y, s⟩, h⟩
    change y = x at h
    cases h
    exact s
  invFun s := ⟨⟨x, s⟩, rfl⟩
  left_inv z := by
    rcases z with ⟨⟨y, s⟩, h⟩
    change y = x at h
    cases h
    rfl
  right_inv s := rfl

private theorem fiberTransport_pi (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b),
    WeakEquivalence (G.map f)) {a b : C} (f : a ⟶ b)
    (x : (G.obj a) _⦋0⦌) :
    Function.Bijective (fiberTransport
      (Functor.whiskerLeft G (vertexProjection (n + 1))) f x) := by
  let e₀ := fiberPiEquiv G n a x
  let e₁ := fiberPiEquiv G n b ((G.map f).app _ x)
  have h := DaggerNativeBasedPiWeakPullback.based_mapπ_bijective
    (G.map f) (hG f) (n + 1) x
  have hc (z : fiber
      (Functor.whiskerLeft G (vertexProjection (n + 1))) a x) :
      e₁ (fiberTransport
        (Functor.whiskerLeft G (vertexProjection (n + 1))) f x z) =
        mapπ (G.map f) (n + 1) x _ rfl (e₀ z) := by
    rcases z with ⟨⟨y, s⟩, hz⟩
    change y = x at hz
    cases hz
    rfl
  constructor
  · intro z w hzw
    apply e₀.injective
    apply h.injective
    calc
      mapπ (G.map f) (n + 1) x _ rfl (e₀ z) =
          e₁ (fiberTransport
            (Functor.whiskerLeft G (vertexProjection (n + 1))) f x z) := (hc z).symm
      _ = e₁ (fiberTransport
            (Functor.whiskerLeft G (vertexProjection (n + 1))) f x w) :=
              congrArg e₁ hzw
      _ = mapπ (G.map f) (n + 1) x _ rfl (e₀ w) := hc w
  · intro w
    obtain ⟨s, hs⟩ := h.surjective (e₁ w)
    refine ⟨e₀.symm s, ?_⟩
    apply e₁.injective
    rw [hc, e₀.apply_symm_apply]
    exact hs

/-- Weak original value transports make the literal based projection
of the full simplicial replacement a Kan fibration. -/
theorem basedProjection_fibration
    (hG : ∀ ⦃a b : C⦄ (f : a ⟶ b), WeakEquivalence (G.map f)) :
    Fibration (basedProjection
      (DaggerNativeSimplicialReplacement.replacement G) (n + 1)) := by
  let φ := Functor.whiskerLeft G (vertexProjection (n + 1))
  have hφ : ∀ ⦃a b : C⦄ (f : a ⟶ b)
      (x : (G ⋙ SSet.evaluation.obj (op ⦋0⦌)).obj a),
      Function.Bijective (fiberTransport φ f x) := by
    intro a b f x
    exact fiberTransport_pi G n hG f x
  have hp : Fibration (mapSystem φ) := mapSystem_fibration φ hφ
  let arrowIso : Arrow.mk (basedProjection
      (DaggerNativeSimplicialReplacement.replacement G) (n + 1)) ≅
      Arrow.mk (mapSystem φ) :=
    Arrow.isoMk (basedRowsIso G n) (vertexRowsIso G)
      (basedProjection_square G n)
  exact (fibration_iff _).mpr
    (((fibrations SSet.{u}).arrow_mk_iso_iff arrowIso).mpr
      ((fibration_iff _).mp hp))

#print axioms basedRowsIso
#print axioms vertexRowsIso
#print axioms basedProjection_square
#print axioms basedProjection_fibration

end
end DaggerModels.PartII.SimplicialReplacementBasedPi
