import OriginalSimplicialCategoryVertexTransportWeakEquivalence
import OriginalSimplicialCategoryWholeTransportNaturality

/-!
# Ordinary component-isomorphism transport of both Hom endpoints

The original component category and the original whole Hom simplicial sets are
used throughout. No Kan or dagger structure is required on the Hom objects.
-/
set_option autoImplicit false
open CategoryTheory MonoidalCategory Opposite Simplicial DaggerModels HomotopicalAlgebra
open DaggerOriginalSimplicialPiZeroCategory
open DaggerOriginalSimplicialCategoryVertexComposition
open DaggerOriginalSimplicialCategoryVertexEdgeHomotopy
open DaggerOriginalSimplicialCategoryVertexTransportWeakEquivalence
open DaggerOriginalSimplicialCategoryWholeTransportNaturality
open DaggerOriginalSimplicialDegreeCategory
universe u
namespace DaggerModels.OrdinaryHomotopyEndpointTransport
noncomputable section

/-- An original edge gives a homotopy of postcomposition on the whole Hom object. -/
def postcomposeVertexEdgeHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    {a b : (C.enriched.Hom x y).obj (op ⦋0⦌)} (e : SSet.Edge a b) (w : C.Obj) :
    SSet.Homotopy (postcomposeVertex C w a) (postcomposeVertex C w b) :=
  (((vertexPointEdgeHomotopy C e).whiskerLeft (C.enriched.Hom w x)).precomp
    (ρ_ (C.enriched.Hom w x)).inv).postcomp (C.enriched.comp w x y)

/-- Equality in the actual component category gives homotopic postcomposition maps. -/
theorem postcomposeVertex_componentHomotopy (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a b : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (h : SSet.π₀.mk a = SSet.π₀.mk b) (w : C.Obj) :
    Nonempty (SSet.Homotopy (DaggerNerveHomotopy.R.map (postcomposeVertex C w a))
      (DaggerNerveHomotopy.R.map (postcomposeVertex C w b))) := by
  have he : Relation.EqvGen (@SSet.π₀Rel (C.enriched.Hom x y)) a b := Quot.eq.mp h
  clear h
  induction he with
  | rel a b h =>
      obtain ⟨e, h₀, h₁⟩ := h
      exact ⟨(postcomposeVertexEdgeHomotopy C ⟨e, h₀, h₁⟩ w).toTop.toSSet⟩
  | refl a =>
      exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.ofEq rfl⟩
  | symm a b _ ih =>
      obtain ⟨h⟩ := ih
      exact ⟨SSet.Subcomplex.RelativeMorphism.Homotopy.symm h⟩
  | trans a b c _ _ ih₁ ih₂ =>
      obtain ⟨h₁⟩ := ih₁
      obtain ⟨h₂⟩ := ih₂
      exact ⟨SSet.Homotopy.trans h₁ h₂⟩

/-- Postcomposition by vertices composes on every simplex of the original Hom. -/
theorem postcomposeVertex_comp (C : SimplicialCat.{u, u}) {x y z : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y z).obj (op ⦋0⦌)) (w : C.Obj) :
    postcomposeVertex C w a ≫ postcomposeVertex C w b =
      postcomposeVertex C w ((C.enriched.comp x y z).app (op ⦋0⦌) (a, b)) := by
  apply NatTrans.ext
  funext n h
  change (postcomposeVertex C w b).app n ((postcomposeVertex C w a).app n h) = _
  rw [postcomposeVertex_apply, postcomposeVertex_apply, postcomposeVertex_apply,
    vertexPoint_comp]
  exact @Category.assoc (degreeObjects C n) (degreeCategory C n) w x y z
    h ((vertexPoint C a).app n PUnit.unit) ((vertexPoint C b).app n PUnit.unit)

/-- Inverse original component vertices give a realized Hom homotopy equivalence. -/
def postcomposeVertexHomotopyEquiv (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (b : (C.enriched.Hom y x).obj (op ⦋0⦌))
    (hab : SSet.π₀.mk ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b)) =
      SSet.π₀.mk ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit))
    (hba : SSet.π₀.mk ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a)) =
      SSet.π₀.mk ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit)) (w : C.Obj) :
    (DaggerNerveHomotopy.R.obj (C.enriched.Hom w x)).HomotopyEquiv
      (DaggerNerveHomotopy.R.obj (C.enriched.Hom w y)) where
  hom := DaggerNerveHomotopy.R.map (postcomposeVertex C w a)
  inv := DaggerNerveHomotopy.R.map (postcomposeVertex C w b)
  homInvId := by
    let h := Classical.choice (postcomposeVertex_componentHomotopy C
      ((C.enriched.comp x y x).app (op ⦋0⦌) (a, b))
      ((C.enriched.id x).app (op ⦋0⦌) PUnit.unit) hab w)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, postcomposeVertex_comp]
    · rw [postcomposeVertex_id, DaggerNerveHomotopy.R.map_id]
  invHomId := by
    let h := Classical.choice (postcomposeVertex_componentHomotopy C
      ((C.enriched.comp y x y).app (op ⦋0⦌) (b, a))
      ((C.enriched.id y).app (op ⦋0⦌) PUnit.unit) hba w)
    refine SSet.Homotopy.congr h ?_ ?_
    · rw [← DaggerNerveHomotopy.R.map_comp, postcomposeVertex_comp]
    · rw [postcomposeVertex_id, DaggerNerveHomotopy.R.map_id]

/-- An isomorphism in the actual component category gives weak postcomposition. -/
theorem postcomposeVertex_weakEquivalence (C : SimplicialCat.{u, u}) {x y : C.Obj}
    (a : (C.enriched.Hom x y).obj (op ⦋0⦌))
    (ha : @IsIso (componentObjects C) (componentCategory C) x y (SSet.π₀.mk a))
    (w : C.Obj) : WeakEquivalence (postcomposeVertex C w a) := by
  let ca : @Quiver.Hom (componentObjects C) inferInstance x y := SSet.π₀.mk a
  have : @IsIso (componentObjects C) (componentCategory C) x y ca := ha
  obtain ⟨b, hb⟩ := SSet.π₀.mk_surjective (inv ca)
  apply (SSet.modelCategoryQuillen.weakEquivalence_iff _).mpr
  apply (TopCat.modelCategory.weakEquivalence_iff _).mpr
  refine SSet.KanComplex.W.homotopyEquivHom
    (postcomposeVertexHomotopyEquiv C a b ?_ ?_ w)
  · change @CategoryStruct.comp (componentObjects C) (componentCategory C).toCategoryStruct
      x y x ca (SSet.π₀.mk b) =
      @CategoryStruct.id (componentObjects C) (componentCategory C).toCategoryStruct x
    rw [hb]
    exact IsIso.hom_inv_id ca
  · change @CategoryStruct.comp (componentObjects C) (componentCategory C).toCategoryStruct
      y x y (SSet.π₀.mk b) ca =
      @CategoryStruct.id (componentObjects C) (componentCategory C).toCategoryStruct y
    rw [hb]
    exact IsIso.inv_hom_id ca

/-- Every original enriched functor preserves vertex postcomposition on whole Homs. -/
theorem postcomposeVertex_natural {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    (w : C.Obj) {x y : C.Obj} (a : (C.enriched.Hom x y).obj (op ⦋0⦌)) :
    F.map w x ≫ postcomposeVertex D (F.obj w)
      ((F.map x y).app (op ⦋0⦌) a) =
      postcomposeVertex C w a ≫ F.map w y := by
  apply NatTrans.ext
  funext n b
  change (postcomposeVertex D (F.obj w) ((F.map x y).app (op ⦋0⦌) a)).app n
      ((F.map w x).app n b) = (F.map w y).app n ((postcomposeVertex C w a).app n b)
  rw [postcomposeVertex_apply, postcomposeVertex_apply]
  have hp := congrFun (NatTrans.congr_app (vertexPoint_natural F a) n) PUnit.unit
  change (F.map x y).app n ((vertexPoint C a).app n PUnit.unit) =
    (vertexPoint D ((F.map x y).app (op ⦋0⦌) a)).app n PUnit.unit at hp
  have hc := congrFun (NatTrans.congr_app (F.map_comp w x y) n)
    (b, (vertexPoint C a).app n PUnit.unit)
  change _ = (D.enriched.comp (F.obj w) (F.obj x) (F.obj y)).app n
    ((F.map w x).app n b,
      (F.map x y).app n ((vertexPoint C a).app n PUnit.unit)) at hc
  rw [hp] at hc
  exact hc.symm

/-- Weak equivalence transfers across a commuting square with weak vertical maps. -/
private theorem weak_iff_of_square {A B C D : SSet.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (l : A ⟶ C) (r : B ⟶ D)
    (sq : f ≫ r = l ≫ g)
    (hl : WeakEquivalence l) (hr : WeakEquivalence r) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  letI : WeakEquivalence l := hl
  letI : WeakEquivalence r := hr
  constructor
  · intro hf
    letI : WeakEquivalence f := hf
    haveI : WeakEquivalence (l ≫ g) := by rw [← sq]; infer_instance
    exact weakEquivalence_of_precomp l g
  · intro hg
    letI : WeakEquivalence g := hg
    haveI : WeakEquivalence (f ≫ r) := by rw [sq]; infer_instance
    exact weakEquivalence_of_postcomp f r

/-- Weakness of an actual Hom map is invariant under component-isomorphic endpoints. -/
theorem local_map_weak_iff_of_endpoint_isos {C D : SimplicialCat.{u, u}} (F : C ⟶ D)
    {a a' b b' : C.Obj}
    (α : (C.enriched.Hom a a').obj (op ⦋0⦌))
    (hα : @IsIso (componentObjects C) (componentCategory C) a a' (SSet.π₀.mk α))
    (β : (C.enriched.Hom b b').obj (op ⦋0⦌))
    (hβ : @IsIso (componentObjects C) (componentCategory C) b b' (SSet.π₀.mk β)) :
    WeakEquivalence (F.map a b) ↔ WeakEquivalence (F.map a' b') := by
  have hFα : @IsIso (componentObjects D) (componentCategory D)
      (F.obj a) (F.obj a') (SSet.π₀.mk ((F.map a a').app (op ⦋0⦌) α)) := by
    letI : @IsIso (componentObjects C) (componentCategory C) a a' (SSet.π₀.mk α) := hα
    change IsIso ((componentFunctor F).map (SSet.π₀.mk α))
    infer_instance
  have hFβ : @IsIso (componentObjects D) (componentCategory D)
      (F.obj b) (F.obj b') (SSet.π₀.mk ((F.map b b').app (op ⦋0⦌) β)) := by
    letI : @IsIso (componentObjects C) (componentCategory C) b b' (SSet.π₀.mk β) := hβ
    change IsIso ((componentFunctor F).map (SSet.π₀.mk β))
    infer_instance
  have hsource : WeakEquivalence (F.map a b) ↔ WeakEquivalence (F.map a' b) := by
    apply (weak_iff_of_square (F.map a' b) (F.map a b)
      (precomposeVertex C α b)
      (precomposeVertex D ((F.map a a').app (op ⦋0⦌) α) (F.obj b))
      (precomposeVertex_natural F α b)
      (precomposeVertex_weakEquivalence C α hα b)
      (precomposeVertex_weakEquivalence D
        ((F.map a a').app (op ⦋0⦌) α) hFα (F.obj b))).symm
  have htarget : WeakEquivalence (F.map a' b) ↔ WeakEquivalence (F.map a' b') := by
    exact weak_iff_of_square (F.map a' b) (F.map a' b')
      (postcomposeVertex C a' β)
      (postcomposeVertex D (F.obj a') ((F.map b b').app (op ⦋0⦌) β))
      (postcomposeVertex_natural F a' β)
      (postcomposeVertex_weakEquivalence C β hβ a')
      (postcomposeVertex_weakEquivalence D
        ((F.map b b').app (op ⦋0⦌) β) hFβ (F.obj a'))
  exact hsource.trans htarget

end
end DaggerModels.OrdinaryHomotopyEndpointTransport
