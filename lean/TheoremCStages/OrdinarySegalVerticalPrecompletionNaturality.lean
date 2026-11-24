import OrdinarySegalVerticalPrecompletion
import OrdinarySegalRestrictionTargetNaturality
import OrdinarySegalMappingTargetSquares

/-!
# Functoriality of the corrected vertical precompletion

The outer groupoid-simplex cotensor resolution acts on target maps by the
existing whole-cotensor postcomposition. Flipping and taking the vertical
diagonal gives the corrected precompletion map. The original constant
section is natural in the target, so the actual unit commutes with this map.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalVerticalPrecompletionNaturality

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre post)
open OrdinarySegalHorizontalCotensorPoint (pointIso constantSection)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

private abbrev E (q : SimplexCategoryᵒᵖ) : SSet.{0} :=
  GroupoidSimplex.parameter.obj q.unop

/-- Target postcomposition is natural in the original groupoid-simplex
parameter, including every horizontal and vertical operator. -/
def resolutionPost {W V : Space} (f : W ⟶ V) :
    OrdinarySegalPrecompletion.resolution W ⟶
      OrdinarySegalPrecompletion.resolution V where
  app q := post (E q) f
  naturality := by
    intro q r θ
    change pre (GroupoidSimplex.parameter.map θ.unop) W ≫
        post (E r) f =
      post (E q) f ≫
        pre (GroupoidSimplex.parameter.map θ.unop) V
    exact OrdinarySegalHorizontalCotensor.pre_post
      (GroupoidSimplex.parameter.map θ.unop) f

/-- The outer target action preserves the identity map. -/
theorem resolutionPost_id (W : Space) :
    resolutionPost (𝟙 W) =
      𝟙 (OrdinarySegalPrecompletion.resolution W) := by
  apply NatTrans.ext
  funext q
  change post (E q) (𝟙 W) = 𝟙 (cotensor (E q) W)
  exact OrdinarySegalHorizontalCotensor.post_id (E q) W

/-- The outer target action preserves literal composition. -/
theorem resolutionPost_comp {W V U : Space} (f : W ⟶ V) (g : V ⟶ U) :
    resolutionPost (f ≫ g) = resolutionPost f ≫ resolutionPost g := by
  apply NatTrans.ext
  funext q
  change post (E q) (f ≫ g) = post (E q) f ≫ post (E q) g
  exact OrdinarySegalHorizontalCotensor.post_comp (E q) f g

/-- Flip the whole target action and take the actual vertical diagonal. -/
def precompletionMap {W V : Space} (f : W ⟶ V) :
    OrdinarySegalVerticalPrecompletion.precompletion W ⟶
      OrdinarySegalVerticalPrecompletion.precompletion V :=
  Functor.whiskerRight
    ((flipFunctor SimplexCategoryᵒᵖ SimplexCategoryᵒᵖ SSet.{0}).map
      (resolutionPost f)) diagonalFunctor

/-- The exact action at horizontal degree `n` and vertical degree `q`
is postcomposition in the full `E[q]` cotensor. -/
theorem precompletionMap_app_app {W V : Space} (f : W ⟶ V)
    (n q : SimplexCategoryᵒᵖ) :
    ((precompletionMap f).app n).app q =
      ((post (E q) f).app n).app q := rfl

/-- The corrected precompletion action preserves identities. -/
theorem precompletionMap_id (W : Space) :
    precompletionMap (𝟙 W) =
      𝟙 (OrdinarySegalVerticalPrecompletion.precompletion W) := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q
  rw [precompletionMap_app_app]
  have h := OrdinarySegalHorizontalCotensor.post_id (E q) W
  exact congrArg (fun a : cotensor (E q) W ⟶ cotensor (E q) W ↦
    (a.app n).app q) h

/-- The corrected precompletion action preserves composition. -/
theorem precompletionMap_comp {W V U : Space} (f : W ⟶ V) (g : V ⟶ U) :
    precompletionMap (f ≫ g) =
      precompletionMap f ≫ precompletionMap g := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q
  rw [precompletionMap_app_app]
  have h := OrdinarySegalHorizontalCotensor.post_comp (E q) f g
  exact congrArg (fun a : cotensor (E q) W ⟶ cotensor (E q) U ↦
    (a.app n).app q) h

/-- The point-parameter cotensor identification is natural in the
whole target simplicial space. -/
theorem pointIso_post {W V : Space} (f : W ⟶ V) :
    post (Δ[0] : SSet.{0}) f ≫ (pointIso V).hom =
      (pointIso W).hom ≫ f := by
  apply NatTrans.ext
  funext n
  cases n using Opposite.rec with
  | op n =>
    induction n using SimplexCategory.rec with
    | _ m =>
        change diagramMappingPostcomp
            (discrete.obj ((Δ[0] : SSet.{0}) ⊗ (Δ[m] : SSet.{0}))) f ≫
              (diagramMappingPrecomp
                  (discrete.map
                    (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) V ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso V m).hom) =
          (diagramMappingPrecomp
              (discrete.map
                (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) W ≫
            (OrdinarySegalWalkingEvaluation.simplexMappingIso W m).hom) ≫
              f.app (op ⦋m⦌)
        calc
          diagramMappingPostcomp
              (discrete.obj ((Δ[0] : SSet.{0}) ⊗ (Δ[m] : SSet.{0}))) f ≫
                (diagramMappingPrecomp
                    (discrete.map
                      (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) V ≫
                  (OrdinarySegalWalkingEvaluation.simplexMappingIso V m).hom) =
            (diagramMappingPrecomp
                (discrete.map
                  (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) W ≫
              diagramMappingPostcomp (discrete.obj (Δ[m] : SSet.{0})) f) ≫
                (OrdinarySegalWalkingEvaluation.simplexMappingIso V m).hom := by
                  rw [← Category.assoc,
                    ← OrdinarySegalMappingTargetSquares.pre_post]
          _ = diagramMappingPrecomp
                (discrete.map
                  (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) W ≫
              ((OrdinarySegalWalkingEvaluation.simplexMappingIso W m).hom ≫
                f.app (op ⦋m⦌)) := by
                  rw [Category.assoc,
                    OrdinarySegalRestrictionTargetNaturality.simplexMappingIso_post]
          _ = (diagramMappingPrecomp
                (discrete.map
                  (SSet.stdSimplex.leftUnitor (Δ[m] : SSet.{0})).inv) W ≫
              (OrdinarySegalWalkingEvaluation.simplexMappingIso W m).hom) ≫
                f.app (op ⦋m⦌) := by rw [Category.assoc]

/-- Target postcomposition commutes with the chosen inverse point
identification. -/
theorem pointIso_inv_post {W V : Space} (f : W ⟶ V) :
    f ≫ (pointIso V).inv =
      (pointIso W).inv ≫ post (Δ[0] : SSet.{0}) f := by
  apply (cancel_mono (pointIso V).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, pointIso_post, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Constant sections are natural in the original target map, for
every horizontal parameter, not only at the chosen vertex. -/
theorem constantSection_post (K : SSet.{0}) {W V : Space} (f : W ⟶ V) :
    constantSection K W ≫ post K f =
      f ≫ constantSection K V := by
  let t : K ⟶ (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.from K
  change ((pointIso W).inv ≫ pre t W) ≫ post K f =
    f ≫ ((pointIso V).inv ≫ pre t V)
  rw [Category.assoc,
    OrdinarySegalHorizontalCotensor.pre_post t f,
    ← Category.assoc, ← pointIso_inv_post,
    Category.assoc]

/-- The original constant-section unit is natural in the target, with
the correct vertical groupoid-simplex index. -/
theorem unit_natural {W V : Space} (f : W ⟶ V) :
    OrdinarySegalVerticalPrecompletion.unit W ≫ precompletionMap f =
      f ≫ OrdinarySegalVerticalPrecompletion.unit V := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q
  change ((constantSection (E q) W).app n).app q ≫
      ((post (E q) f).app n).app q =
    (f.app n).app q ≫ ((constantSection (E q) V).app n).app q
  exact congrArg (fun a : W ⟶ cotensor (E q) V ↦ (a.app n).app q)
    (constantSection_post (E q) f)

/-- The corrected vertical precompletion is a functor on ordinary
simplicial spaces. -/
def precompletionFunctor : Space ⥤ Space where
  obj W := OrdinarySegalVerticalPrecompletion.precompletion W
  map f := precompletionMap f
  map_id W := precompletionMap_id W
  map_comp f g := precompletionMap_comp f g

#print axioms resolutionPost
#print axioms precompletionMap_app_app
#print axioms pointIso_post
#print axioms constantSection_post
#print axioms unit_natural
#print axioms precompletionFunctor

end

end DaggerModels.PartII.OrdinarySegalVerticalPrecompletionNaturality
