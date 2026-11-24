import DaggerModelsPartII.JTRelativeEndpointPrism
import DaggerModelsPartII.ParameterVertexLiftSpace
import DaggerModelsPartII.JTFixedLiftSpaceTimeEquiv

/-! The full fixed lift space for relative homotopies with both endpoints prescribed. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra
open MonoidalCategory CartesianMonoidalCategory
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.PartII.JTRelativePrismChoiceSpace

open JTRelativeEndpointPrism

noncomputable section

variable {A B X Y : SSet.{u}}
variable (i : A ⟶ B) (p : X ⟶ Y)
variable (b : B ⟶ Y) (t : A ⟶ X)
variable (c₀ c₁ : B ⟶ X)
variable (hc₀ : c₀ ≫ p = b) (hc₁ : c₁ ≫ p = b)
variable (hi₀ : i ≫ c₀ = t) (hi₁ : i ≫ c₁ = t)

private abbrev sq := relativeCylinderSquare i
private abbrev bd := endpointBoundary c₀ c₁
private abbrev st := fst A (Δ[1] : SSet.{u}) ≫ t
private abbrev base := fst B (Δ[1] : SSet.{u}) ≫ b

include hi₀ hi₁ in
/-- Endpoint labels and the stationary support agree on their intersection. -/
theorem boundary_support :
    (i ▷ (SSet.boundary 1 : SSet.{u})) ≫ bd c₀ c₁ =
      (A ◁ (SSet.boundary 1).ι) ≫ st t := by
  apply SSet.boundary₁.hom_ext_leftTensor
  · rw [MonoidalCategory.whisker_exchange_assoc, endpointBoundary_zero]
    apply NatTrans.ext
    funext q x
    exact congrFun (NatTrans.congr_app hi₀ q) x.1
  · rw [MonoidalCategory.whisker_exchange_assoc, endpointBoundary_one]
    apply NatTrans.ext
    funext q x
    exact congrFun (NatTrans.congr_app hi₁ q) x.1

include hc₀ hc₁ in
/-- The two prescribed endpoint maps project to the fixed base. -/
theorem boundary_base :
    bd c₀ c₁ ≫ p =
      (B ◁ (SSet.boundary 1).ι) ≫ base b := by
  apply SSet.boundary₁.hom_ext_leftTensor
  · change (B ◁ SSet.boundary₁.ι₀) ≫ endpointBoundary c₀ c₁ ≫ p = _
    rw [← Category.assoc, endpointBoundary_zero, Category.assoc, hc₀]
    apply NatTrans.ext
    rfl
  · change (B ◁ SSet.boundary₁.ι₁) ≫ endpointBoundary c₀ c₁ ≫ p = _
    rw [← Category.assoc, endpointBoundary_one, Category.assoc, hc₁]
    apply NatTrans.ext
    rfl

include c₀ hc₀ hi₀ in
/-- The stationary support has the same fixed base. -/
theorem support_base :
    st t ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ base b := by
  have htp : t ≫ p = i ≫ b := by
    calc
      t ≫ p = (i ≫ c₀) ≫ p := by rw [hi₀]
      _ = i ≫ b := by rw [Category.assoc, hc₀]
  dsimp only [st, base]
  rw [Category.assoc, htp, ← Category.assoc,
    CartesianMonoidalCategory.whiskerRight_fst_assoc, Category.assoc]

include hi₀ hi₁ in
/-- The actual fixed map on the pushout boundary, before any prism is chosen. -/
def top : (sq i).pt ⟶ X :=
  (sq i).isPushout.desc (bd c₀ c₁) (st t)
    (boundary_support i t c₀ c₁ hi₀ hi₁)

include hc₀ hc₁ hi₀ hi₁ in
/-- The exact fixed lifting square for a same-degree relative homotopy. -/
def fixedSquare : CommSq (top i t c₀ c₁ hi₀ hi₁)
    (sq i).ι p (base b) := by
  constructor
  apply (sq i).isPushout.hom_ext
  · dsimp only [top]
    rw [← Category.assoc, IsPushout.inl_desc,
      ← Category.assoc, (sq i).inl_ι]
    exact boundary_base p b c₀ c₁ hc₀ hc₁
  · dsimp only [top]
    rw [← Category.assoc, IsPushout.inr_desc,
      ← Category.assoc, (sq i).inr_ι]
    exact support_base i p b t c₀ hc₀ hi₀

include hc₀ hc₁ hi₀ hi₁ in
/-- All-dimensional relative homotopies with both endpoints and base fixed. -/
def space : SSet.{u} :=
  SSet.ihomToPullbackFiber
    (fixedSquare i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁)

/-- The relative cylinder boundary is a monomorphism. -/
theorem cylinder_mono [Mono i] : Mono (sq i).ι := by
  change Mono (DaggerSSetSM7.pushoutTensor i (SSet.boundary 1).ι).ι
  rw [DaggerSSetSM7.pushoutTensor_ι]
  exact DaggerSSetSM7.pushoutProduct_mono i (SSet.boundary 1).ι

/-- The same boundary inclusion is an ordinary Kan weak equivalence. -/
theorem cylinder_weak [Mono i] [WeakEquivalence i] : WeakEquivalence (sq i).ι := by
  letI : Cofibration i := SSet.modelCategoryQuillen.cofibration_of_mono i
  have hi : SSet.anodyneExtensions i :=
    DaggerNativeKanTrivialCofibrationRestriction.trivial_anodyne i
  have hs : SSet.anodyneExtensions (sq i).ι :=
    SSet.anodyneExtensions.pushoutTensorι₁ (sq i) hi
  have htriv : trivialCofibrations SSet.{u} (sq i).ι := by
    rw [← fibrations_llp]
    intro C D q hq
    letI : Fibration q := (HomotopicalAlgebra.fibration_iff q).mpr hq
    exact hs.hasLeftLiftingProperty q
  exact (mem_trivialCofibrations_iff _).mp htriv |>.2

/-- The exact relative prism choice space is Kan. -/
theorem space_kan [Mono i] [Fibration p] :
    (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).KanComplex := by
  letI : Mono (sq i).ι := cylinder_mono i
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_kan
    (fixedSquare i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁)

/-- The exact relative prism choice space is weakly contractible. -/
theorem space_toPoint_weak [Mono i] [WeakEquivalence i] [Fibration p] :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from
      (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁)) := by
  letI : Mono (sq i).ι := cylinder_mono i
  letI : WeakEquivalence (sq i).ι := cylinder_weak i
  exact ParameterVertexLiftSpace.fixedSquare_liftSpace_toPoint_weak
    (fixedSquare i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁)

/-- A fixed-square lift space is also weakly contractible when its right map
is a trivial fibration; the left map only needs to be a monomorphism. -/
theorem fixedSquare_toPoint_weak_of_right
    {C D E F : SSet.{u}} {j : C ⟶ D} {q : E ⟶ F}
    [Mono j] [Fibration q] [WeakEquivalence q]
    {a : C ⟶ E} {d : D ⟶ F} (h : CommSq a j q d) :
    WeakEquivalence (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.ihomToPullbackFiber h : SSet.{u})) := by
  haveI : Fibration (SSet.ihomToPullback j q) :=
    (DaggerSSetSM7.corner_sm7 j q).1
  haveI : WeakEquivalence (SSet.ihomToPullback j q) :=
    (DaggerSSetSM7.corner_sm7 j q).2 (Or.inr inferInstance)
  change WeakEquivalence
    (SSet.stdSimplex.isTerminalObj₀.from
      (SSet.Subcomplex.fiber (SSet.ihomToPullback j q)
        (SSet.ihomToPullbackTgt₀Mk h) : SSet.{u}))
  exact SSet.modelCategoryQuillen.weakEquivalence_of_fibration_of_isPullback
    (SSet.Subcomplex.fiber_isPullback (SSet.ihomToPullback j q)
      (SSet.ihomToPullbackTgt₀Mk h))

/-- Every simplex of the choice space is a complete time-dependent prism. -/
def timeMap (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    (B ⊗ (Δ[1] : SSet.{u})) ⊗ SSet.stdSimplex.obj n ⟶ X :=
  JTFixedLiftSpaceTimeEquiv.timeMap
    (fixedSquare i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁) n v

/-- The parameterized prism keeps the entire pushout boundary and base fixed. -/
theorem timeMap_conditions (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    ((sq i).ι ▷ SSet.stdSimplex.obj n) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      fst (sq i).pt (SSet.stdSimplex.obj n) ≫
        top i t c₀ c₁ hi₀ hi₁ ∧
      timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v ≫ p =
        fst (B ⊗ (Δ[1] : SSet.{u})) (SSet.stdSimplex.obj n) ≫ base b := by
  exact JTFixedLiftSpaceTimeEquiv.timeMap_conditions
    (fixedSquare i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁) n v

/-- The complete endpoint boundary stays fixed in every simplicial degree. -/
theorem timeMap_boundary (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    ((B ◁ (SSet.boundary 1).ι) ▷ SSet.stdSimplex.obj n) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      fst (B ⊗ (SSet.boundary 1 : SSet.{u})) (SSet.stdSimplex.obj n) ≫
        endpointBoundary c₀ c₁ := by
  let N := SSet.stdSimplex.obj n
  have h := (timeMap_conditions i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v).1
  calc
    ((B ◁ (SSet.boundary 1).ι) ▷ N) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      (((sq i).inl ≫ (sq i).ι) ▷ N) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v := by
          exact congrArg (fun g ↦ (g ▷ N) ≫
            timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) (sq i).inl_ι.symm
    _ = ((sq i).inl ▷ N) ≫
        (((sq i).ι ▷ N) ≫ timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = ((sq i).inl ▷ N) ≫
        (fst (sq i).pt N ≫ top i t c₀ c₁ hi₀ hi₁) := by rw [h]
    _ = fst (B ⊗ (SSet.boundary 1 : SSet.{u})) N ≫
        ((sq i).inl ≫ top i t c₀ c₁ hi₀ hi₁) := by
          rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc]
          rfl
    _ = fst (B ⊗ (SSet.boundary 1 : SSet.{u})) N ≫
        endpointBoundary c₀ c₁ := by
          rw [top, IsPushout.inl_desc]

/-- The whole relative support remains stationary in every degree. -/
theorem timeMap_support (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    ((i ▷ (Δ[1] : SSet.{u})) ▷ SSet.stdSimplex.obj n) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      fst (A ⊗ (Δ[1] : SSet.{u})) (SSet.stdSimplex.obj n) ≫
        fst A (Δ[1] : SSet.{u}) ≫ t := by
  let N := SSet.stdSimplex.obj n
  have h := (timeMap_conditions i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v).1
  calc
    ((i ▷ (Δ[1] : SSet.{u})) ▷ N) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      (((sq i).inr ≫ (sq i).ι) ▷ N) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v := by
          exact congrArg (fun g ↦ (g ▷ N) ≫
            timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) (sq i).inr_ι.symm
    _ = ((sq i).inr ▷ N) ≫
        (((sq i).ι ▷ N) ≫ timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) := by
          rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = ((sq i).inr ▷ N) ≫
        (fst (sq i).pt N ≫ top i t c₀ c₁ hi₀ hi₁) := by rw [h]
    _ = fst (A ⊗ (Δ[1] : SSet.{u})) N ≫
        ((sq i).inr ≫ top i t c₀ c₁ hi₀ hi₁) := by
          rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
            Category.assoc]
          rfl
    _ = fst (A ⊗ (Δ[1] : SSet.{u})) N ≫
        fst A (Δ[1] : SSet.{u}) ≫ t := by
          rw [top, IsPushout.inr_desc]

/-- The zero time face is exactly the first prescribed lift in every degree. -/
theorem timeMap_zero (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    (((B ◁ SSet.boundary₁.ι₀) ≫
      (B ◁ (SSet.boundary 1).ι)) ▷ SSet.stdSimplex.obj n) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      fst (B ⊗ (Δ[0] : SSet.{u})) (SSet.stdSimplex.obj n) ≫
        fst B (Δ[0] : SSet.{u}) ≫ c₀ := by
  let N := SSet.stdSimplex.obj n
  calc
    (((B ◁ SSet.boundary₁.ι₀) ≫
        (B ◁ (SSet.boundary 1).ι)) ▷ N) ≫
          timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      ((B ◁ SSet.boundary₁.ι₀) ▷ N) ≫
        (((B ◁ (SSet.boundary 1).ι) ▷ N) ≫
          timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) := by
            rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = ((B ◁ SSet.boundary₁.ι₀) ▷ N) ≫
        (fst (B ⊗ (SSet.boundary 1 : SSet.{u})) N ≫
          endpointBoundary c₀ c₁) := by
            rw [timeMap_boundary]
    _ = fst (B ⊗ (Δ[0] : SSet.{u})) N ≫
        ((B ◁ SSet.boundary₁.ι₀) ≫ endpointBoundary c₀ c₁) := by
            rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
              Category.assoc]
    _ = fst (B ⊗ (Δ[0] : SSet.{u})) N ≫
        fst B (Δ[0] : SSet.{u}) ≫ c₀ := by
          rw [endpointBoundary_zero]

/-- The one time face is exactly the second prescribed lift in every degree. -/
theorem timeMap_one (n : SimplexCategory)
    (v : (space i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁).obj (op n)) :
    (((B ◁ SSet.boundary₁.ι₁) ≫
      (B ◁ (SSet.boundary 1).ι)) ▷ SSet.stdSimplex.obj n) ≫
        timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      fst (B ⊗ (Δ[0] : SSet.{u})) (SSet.stdSimplex.obj n) ≫
        fst B (Δ[0] : SSet.{u}) ≫ c₁ := by
  let N := SSet.stdSimplex.obj n
  calc
    (((B ◁ SSet.boundary₁.ι₁) ≫
        (B ◁ (SSet.boundary 1).ι)) ▷ N) ≫
          timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v =
      ((B ◁ SSet.boundary₁.ι₁) ▷ N) ≫
        (((B ◁ (SSet.boundary 1).ι) ▷ N) ≫
          timeMap i p b t c₀ c₁ hc₀ hc₁ hi₀ hi₁ n v) := by
            rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = ((B ◁ SSet.boundary₁.ι₁) ▷ N) ≫
        (fst (B ⊗ (SSet.boundary 1 : SSet.{u})) N ≫
          endpointBoundary c₀ c₁) := by
            rw [timeMap_boundary]
    _ = fst (B ⊗ (Δ[0] : SSet.{u})) N ≫
        ((B ◁ SSet.boundary₁.ι₁) ≫ endpointBoundary c₀ c₁) := by
            rw [← Category.assoc, CartesianMonoidalCategory.whiskerRight_fst,
              Category.assoc]
    _ = fst (B ⊗ (Δ[0] : SSet.{u})) N ≫
        fst B (Δ[0] : SSet.{u}) ≫ c₁ := by
          rw [endpointBoundary_one]

end

end DaggerModels.PartII.JTRelativePrismChoiceSpace
