import DaggerModelsPartII.ConstantDaggerSource
import OriginalDaggerAdjunctionWitnessRecovered

/-!
# Comparison with the Part I free dagger simplicial category

The path presentation and the Part I free construction represent the same
functor on dagger simplicial categories.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex
open DaggerModels.PartII.DaggerSimplexFreeProperty
open DaggerModels.PartII.ConstantDaggerSource
open DaggerNativeDaggerDegreeCotensor
open DaggerOriginalSimplicialDegreeCategory

namespace DaggerModels.PartII.DaggerSimplexPartIComparison

noncomputable section

def source (n : ℕ) : SimplicialCat.{0, 0} :=
  DaggerActualConstantSimplicialCategory.constant (Fin (n + 1))

def partIFree (n : ℕ) : DaggerSimplicialCat.{0, 0} :=
  OrdinaryRigidification.daggerRigidificationLiftWitness.{0}.freeSCat.obj (source n)

def pathFree (n : ℕ) : DaggerSimplicialCat.{0, 0} :=
  enrichedDaggerSimplex ⟨n⟩

private instance targetDagger (D : DaggerSimplicialCat.{0, 0}) :
    DaggerCategory (degreeObjects D.toSimplicialCat (op ⦋0⦌)) :=
  degreeDaggerCategory D (op ⦋0⦌)

/-- The two constructions have the same mapping property against every
dagger simplicial category. -/
def comparisonEquiv (n : ℕ) (D : DaggerSimplicialCat.{0, 0}) :
    (partIFree n ⟶ D) ≃ (pathFree n ⟶ D) := by
  exact
    (OrdinaryRigidification.daggerRigidificationLiftWitness.{0}.freeSCatAdjunction.homEquiv
      (source n) D).trans
    ((simplicialHomEquiv (A := Fin (n + 1)) (E := D.toSimplicialCat)).symm.trans
    ((freeDaggerSimplexOrdinalEquiv n
      (degreeObjects D.toSimplicialCat (op ⦋0⦌))).symm.trans
    (homEquiv (A := FreeDaggerSimplex n) (D := D))))

private theorem simplicialDegree_comp (n : ℕ)
    {D E : DaggerSimplicialCat.{0, 0}}
    (F : source n ⟶ D.toSimplicialCat) (g : D ⟶ E) :
    toOrdinarySimplicial (A := Fin (n + 1))
      (F ≫ g.toEnrichedFunctor) =
      toOrdinarySimplicial (A := Fin (n + 1)) F ⋙
        degreeFunctor g.toEnrichedFunctor (op ⦋0⦌) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro x; rfl
  case h_map =>
    intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

private instance degreeFunctor_dagger {D E : DaggerSimplicialCat.{0, 0}}
    (g : D ⟶ E) : DaggerFunctor
      (degreeFunctor g.toEnrichedFunctor (op ⦋0⦌)) where
  map_dagger f :=
    (congrFun (congr_app (g.map_dagger _ _) (op ⦋0⦌)) f).symm

private def mapChainData (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (K : C ⥤ B) (W : ChainData n C) : ChainData n B where
  obj a := K.obj (W.obj a)
  edge e := K.map (W.edge e)

private theorem edgeValue_mapChainData (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (K : C ⥤ B) [DaggerFunctor K] (W : ChainData n C)
    {a b : Line n} (e : (symmLineQuiver n).Hom a b) :
    edgeValue n B (mapChainData n K W) e = K.map (edgeValue n C W e) := by
  change (lineQuiver n).Hom a b ⊕ (lineQuiver n).Hom b a at e
  cases e with
  | inl e => rfl
  | inr e => exact (DaggerFunctor.map_dagger (F := K) (W.edge e)).symm

private theorem wordValue_mapChainData (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (K : C ⥤ B) [DaggerFunctor K] (W : ChainData n C)
    {a b : Line n}
    (p : @Quiver.Path (Quiver.Symmetrify (Line n)) (symmLineQuiver n) a b) :
    wordValue n B (mapChainData n K W) p = K.map (wordValue n C W p) := by
  induction p with
  | nil => simp [wordValue, mapChainData]
  | @cons b c p e ih =>
    rw [wordValue_cons, wordValue_cons, K.map_comp, ih,
      edgeValue_mapChainData]

private theorem extend_mapChainData (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (K : C ⥤ B) [DaggerFunctor K] (W : ChainData n C) :
    extend n B (mapChainData n K W) = extend n C W ⋙ K := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro x; rfl
  case h_map =>
    intro x y p
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact wordValue_mapChainData n K W p

private theorem chainOfOrdinalFunctor_comp (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (G : Fin (n + 1) ⥤ C) (K : C ⥤ B) :
    chainOfOrdinalFunctor n B (G ⋙ K) =
      mapChainData n K (chainOfOrdinalFunctor n C G) := by
  rfl

private theorem freeOrdinal_natural (n : ℕ) {C B : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    (G : Fin (n + 1) ⥤ C) (K : C ⥤ B) [DaggerFunctor K] :
    ((freeDaggerSimplexOrdinalEquiv n B).symm (G ⋙ K)).1 =
      ((freeDaggerSimplexOrdinalEquiv n C).symm G).1 ⋙ K := by
  change extend n B (chainOfOrdinalFunctor n B (G ⋙ K)) =
    extend n C (chainOfOrdinalFunctor n C G) ⋙ K
  rw [chainOfOrdinalFunctor_comp]
  exact extend_mapChainData n K _

private instance daggerFunctor_comp {C B E : Type}
    [Category C] [DaggerCategory C] [Category B] [DaggerCategory B]
    [Category E] [DaggerCategory E]
    (F : C ⥤ B) (G : B ⥤ E) [DaggerFunctor F] [DaggerFunctor G] :
    DaggerFunctor (F ⋙ G) where
  map_dagger f := by
    change G.map (F.map (dagger f)) = dagger (G.map (F.map f))
    rw [DaggerFunctor.map_dagger, DaggerFunctor.map_dagger]

private theorem toOrdinary_comp {A : Type} [Category A] [DaggerCategory A]
    {D E : DaggerSimplicialCat.{0, 0}}
    (F : DaggerUnitaryDiscrete.ordinaryEnrichment A ⟶ D)
    (g : D ⟶ E) :
    toOrdinary (A := A) (F ≫ g) =
      toOrdinary (A := A) F ⋙ degreeFunctor g.toEnrichedFunctor (op ⦋0⦌) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro x; rfl
  case h_map =>
    intro x y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

private def postcomposeDagger {A : Type} [Category A] [DaggerCategory A]
    {D E : DaggerSimplicialCat.{0, 0}}
    (H : {F : A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) // DaggerFunctor F})
    (g : D ⟶ E) :
    {F : A ⥤ degreeObjects E.toSimplicialCat (op ⦋0⦌) // DaggerFunctor F} := by
  letI : DaggerFunctor H.1 := H.2
  exact ⟨H.1 ⋙ degreeFunctor g.toEnrichedFunctor (op ⦋0⦌), inferInstance⟩

private theorem homEquiv_natural {A : Type} [Category A] [DaggerCategory A]
    {D E : DaggerSimplicialCat.{0, 0}}
    (H : {F : A ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) // DaggerFunctor F})
    (g : D ⟶ E) :
    (homEquiv (A := A) (D := E)) (postcomposeDagger H g) =
      (homEquiv (A := A) (D := D)) H ≫ g := by
  apply (homEquiv (A := A) (D := E)).symm.injective
  apply Subtype.ext
  change toOrdinary (A := A) (homEquiv (A := A) (D := E)
      (postcomposeDagger H g)) =
    toOrdinary (A := A) ((homEquiv (A := A) (D := D)) H ≫ g)
  rw [toOrdinary_comp]
  rw [show toOrdinary (A := A) ((homEquiv (A := A) (D := E))
    (postcomposeDagger H g)) = (postcomposeDagger H g).1 from
      to_from (A := A) (D := E) (postcomposeDagger H g)]
  rw [show toOrdinary (A := A) ((homEquiv (A := A) (D := D)) H) = H.1 from
    to_from (A := A) (D := D) H]
  rfl

private theorem freeOrdinal_natural_dagger (n : ℕ)
    {D E : DaggerSimplicialCat.{0, 0}}
    (G : Fin (n + 1) ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌))
    (g : D ⟶ E) :
    (freeDaggerSimplexOrdinalEquiv n
      (degreeObjects E.toSimplicialCat (op ⦋0⦌))).symm
        (G ⋙ degreeFunctor g.toEnrichedFunctor (op ⦋0⦌)) =
      postcomposeDagger
        ((freeDaggerSimplexOrdinalEquiv n
          (degreeObjects D.toSimplicialCat (op ⦋0⦌))).symm G) g := by
  apply Subtype.ext
  exact freeOrdinal_natural n G (degreeFunctor g.toEnrichedFunctor (op ⦋0⦌))

/-- The comparison of representable mapping sets respects postcomposition
in every dagger simplicial target. -/
theorem comparisonEquiv_natural (n : ℕ)
    {D E : DaggerSimplicialCat.{0, 0}}
    (f : partIFree n ⟶ D) (g : D ⟶ E) :
    comparisonEquiv n E (f ≫ g) = comparisonEquiv n D f ≫ g := by
  let adj := OrdinaryRigidification.daggerRigidificationLiftWitness.{0}.freeSCatAdjunction
  let F : source n ⟶ D.toSimplicialCat := adj.homEquiv (source n) D f
  let G : Fin (n + 1) ⥤ degreeObjects D.toSimplicialCat (op ⦋0⦌) :=
    (simplicialHomEquiv (A := Fin (n + 1)) (E := D.toSimplicialCat)).symm F
  change (homEquiv (A := FreeDaggerSimplex n) (D := E))
      ((freeDaggerSimplexOrdinalEquiv n
        (degreeObjects E.toSimplicialCat (op ⦋0⦌))).symm
        ((simplicialHomEquiv (A := Fin (n + 1))
          (E := E.toSimplicialCat)).symm
          (adj.homEquiv (source n) E (f ≫ g)))) =
    (homEquiv (A := FreeDaggerSimplex n) (D := D))
      ((freeDaggerSimplexOrdinalEquiv n
        (degreeObjects D.toSimplicialCat (op ⦋0⦌))).symm G) ≫ g
  rw [adj.homEquiv_naturality_right]
  change (homEquiv (A := FreeDaggerSimplex n) (D := E))
      ((freeDaggerSimplexOrdinalEquiv n
        (degreeObjects E.toSimplicialCat (op ⦋0⦌))).symm
        (toOrdinarySimplicial (A := Fin (n + 1))
          (F ≫ g.toEnrichedFunctor))) = _
  rw [simplicialDegree_comp]
  change (homEquiv (A := FreeDaggerSimplex n) (D := E))
      ((freeDaggerSimplexOrdinalEquiv n
        (degreeObjects E.toSimplicialCat (op ⦋0⦌))).symm
        (G ⋙ degreeFunctor g.toEnrichedFunctor (op ⦋0⦌))) = _
  rw [freeOrdinal_natural_dagger]
  exact homEquiv_natural _ g

/-- The Part I witness free dagger simplicial category on the constant
finite ordinal is canonically isomorphic to the constant enrichment of the
free dagger path category.  The forward arrow is from the Part I free object
to the path presentation. -/
def comparisonIso (n : ℕ) : partIFree n ≅ pathFree n :=
  Coyoneda.ext (partIFree n) (pathFree n)
    (fun {D} f => comparisonEquiv n D f)
    (fun {D} f => (comparisonEquiv n D).symm f)
    (by intro D f; exact (comparisonEquiv n D).symm_apply_apply f)
    (by intro D f; exact (comparisonEquiv n D).apply_symm_apply f)
    (by
      intro D E f g
      apply (comparisonEquiv n E).injective
      rw [comparisonEquiv_natural]
      simp)

end

end DaggerModels.PartII.DaggerSimplexPartIComparison
