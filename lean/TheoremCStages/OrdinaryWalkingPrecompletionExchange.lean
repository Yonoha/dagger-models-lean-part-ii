import OrdinarySegalCotensorParameterNaturality
import OrdinarySegalCotensorRowSwitch
import OrdinarySegalCotensorZeroIso
import OrdinarySegalVerticalPrecompletion
import NativeBisimplicialDiagonal

/-!
# Exchange of the walking cotensor and the corrected vertical resolution

The outer groupoid-simplex parameter remains the original `E[q]`. Strict
Fubini, the original simplicial braiding, and the degree-zero right unitor
identify the two outer diagrams before taking their vertical diagonal.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinaryWalkingPrecompletionExchange

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalHorizontalCotensor (cotensor pre)
open DaggerNativeBisimplicialDiagonal (diagonalFunctor)

noncomputable section

private abbrev J := SimplexCategoryᵒᵖ
private abbrev E (q : J) : SSet.{0} := GroupoidSimplex.parameter.obj q.unop
private abbrev E₁ : SSet.{0} := GroupoidSimplex.parameter.obj ⦋1⦌
private abbrev zero : J := op ⦋0⦌

/-- Mapping the original `E[1]` into each original outer resolution stage. -/
def walkingMappingResolution (W : Space) : J ⥤ SSet.{0} :=
  OrdinarySegalPrecompletion.resolution W ⋙
    diagramMappingTarget (discrete.obj E₁)

/-- The zero horizontal row of the iterated original cotensor resolution. -/
def iteratedZeroResolution (W : Space) : J ⥤ SSet.{0} :=
  OrdinarySegalPrecompletion.resolution (cotensor E₁ W) ⋙
    (evaluation J SSet.{0}).obj zero

/-- The original Fubini map from a walking mapping space into a single
ordered tensor parameter. -/
private def sourceIso (W : Space) (q : J) :
    (walkingMappingResolution W).obj q ≅
      diagramMappingSpace (discrete.obj (E q ⊗ E₁)) W :=
  OrdinarySegalCotensorMappingIso.mappingIso (E q) E₁ W

/-- The original braid reverses the two exact parameters. -/
private def braidIso (W : Space) (q : J) :
    diagramMappingSpace (discrete.obj (E q ⊗ E₁)) W ≅
      diagramMappingSpace (discrete.obj (E₁ ⊗ E q)) W :=
  OrdinarySegalCotensorRowSwitch.braidMappingIso (E q) E₁ W

/-- The iterated row-zero cotensor maps into the opposite ordered tensor. -/
private def targetIso (W : Space) (q : J) :
    (iteratedZeroResolution W).obj q ≅
      diagramMappingSpace (discrete.obj (E₁ ⊗ E q)) W :=
  OrdinarySegalCotensorZeroIso.mappingIso (E q) (cotensor E₁ W) ≪≫
    OrdinarySegalCotensorMappingIso.mappingIso E₁ (E q) W

/-- The right-unitor comparison in horizontal degree zero is natural in
the unchanged contravariant cotensor parameter. -/
private theorem zeroIso_natural {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    (pre f W).app zero ≫ (OrdinarySegalCotensorZeroIso.mappingIso K W).hom =
      (OrdinarySegalCotensorZeroIso.mappingIso L W).hom ≫
        diagramMappingPrecomp (discrete.map f) W := by
  rw [OrdinarySegalCotensorZeroIso.mappingIso_hom,
    OrdinarySegalCotensorZeroIso.mappingIso_hom]
  change diagramMappingPrecomp (discrete.map (f ▷ (Δ[0] : SSet.{0}))) W ≫
      diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.rightUnitor K).inv) W =
    diagramMappingPrecomp
        (discrete.map (SSet.stdSimplex.rightUnitor L).inv) W ≫
      diagramMappingPrecomp (discrete.map f) W
  rw [← diagramMappingPrecomp_comp, ← diagramMappingPrecomp_comp,
    ← discrete.map_comp, ← discrete.map_comp]
  have h : (SSet.stdSimplex.rightUnitor K).inv ≫
      f ▷ (Δ[0] : SSet.{0}) =
      f ≫ (SSet.stdSimplex.rightUnitor L).inv := by
    apply NatTrans.ext
    funext q x
    rfl
  exact congrArg (fun g ↦ diagramMappingPrecomp (discrete.map g) W)
    h

/-- The target Fubini comparison is natural for every original outer
groupoid-simplex operator. -/
private theorem targetIso_natural (W : Space) {q r : J} (θ : q ⟶ r) :
    (iteratedZeroResolution W).map θ ≫ (targetIso W r).hom =
      (targetIso W q).hom ≫
        diagramMappingPrecomp
          (discrete.map (E₁ ◁ GroupoidSimplex.parameter.map θ.unop)) W := by
  let f : E r ⟶ E q := GroupoidSimplex.parameter.map θ.unop
  change (pre f (cotensor E₁ W)).app zero ≫
      ((OrdinarySegalCotensorZeroIso.mappingIso (E r) (cotensor E₁ W)).hom ≫
        (OrdinarySegalCotensorMappingIso.mappingIso E₁ (E r) W).hom) =
    ((OrdinarySegalCotensorZeroIso.mappingIso (E q) (cotensor E₁ W)).hom ≫
      (OrdinarySegalCotensorMappingIso.mappingIso E₁ (E q) W).hom) ≫
        diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W
  rw [← Category.assoc, zeroIso_natural f (cotensor E₁ W),
    Category.assoc,
    OrdinarySegalCotensorMappingIso.mappingIso_natural_source E₁ f W,
    ← Category.assoc]

/-- Strict Fubini and braiding identify the complete outer diagrams,
including every original parameter operator. -/
def outerExchangeIso (W : Space) :
    walkingMappingResolution W ≅ iteratedZeroResolution W :=
  NatIso.ofComponents
    (fun q ↦ sourceIso W q ≪≫ braidIso W q ≪≫ (targetIso W q).symm)
    (by
      intro q r θ
      let f : E r ⟶ E q := GroupoidSimplex.parameter.map θ.unop
      let s := (walkingMappingResolution W).map θ
      let t := (iteratedZeroResolution W).map θ
      let Fq := (sourceIso W q).hom
      let Fr := (sourceIso W r).hom
      let Bq := (braidIso W q).hom
      let Br := (braidIso W r).hom
      let Tq := (targetIso W q).hom
      let Tr := (targetIso W r).hom
      have hs : s ≫ Fr = Fq ≫
          diagramMappingPrecomp (discrete.map (f ▷ E₁)) W :=
        OrdinarySegalCotensorParameterNaturality.mappingIso_natural_parameter
          f E₁ W
      have hb : diagramMappingPrecomp (discrete.map (f ▷ E₁)) W ≫ Br =
          Bq ≫ diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W :=
        OrdinarySegalCotensorRowSwitch.braidMappingIso_natural f E₁ W
      have ht : t ≫ Tr = Tq ≫
          diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W :=
        targetIso_natural W θ
      have hmain : s ≫ Fr ≫ Br =
          Fq ≫ Bq ≫
            diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W := by
        calc
          s ≫ Fr ≫ Br =
              (Fq ≫ diagramMappingPrecomp (discrete.map (f ▷ E₁)) W) ≫ Br := by
                simpa only [Category.assoc] using
                  congrArg (fun m ↦ m ≫ Br) hs
          _ = Fq ≫
              (diagramMappingPrecomp (discrete.map (f ▷ E₁)) W ≫ Br) :=
                Category.assoc _ _ _
          _ = Fq ≫
              (Bq ≫ diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W) := by
                rw [hb]
          _ = _ := (Category.assoc _ _ _).symm
      change s ≫ ((Fr ≫ Br) ≫ (targetIso W r).inv) =
        ((Fq ≫ Bq) ≫ (targetIso W q).inv) ≫ t
      apply (cancel_mono Tr).mp
      calc
        (s ≫ ((Fr ≫ Br) ≫ (targetIso W r).inv)) ≫ Tr =
            s ≫ Fr ≫ Br := by
              dsimp only [Tr]
              simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        _ = Fq ≫ Bq ≫
              diagramMappingPrecomp (discrete.map (E₁ ◁ f)) W := hmain
        _ = (((Fq ≫ Bq) ≫ (targetIso W q).inv) ≫ t) ≫ Tr := by
              simp only [Category.assoc]
              rw [ht]
              dsimp only [Tq]
              simp only [Iso.inv_hom_id_assoc])

/-- The diagonal exchange reaches the literal row zero of the corrected
precompletion of the walking cotensor. -/
def diagonalExchangeIso (W : Space) :
    diagonalFunctor.obj (walkingMappingResolution W) ≅
      (OrdinarySegalVerticalPrecompletion.precompletion (cotensor E₁ W)).obj zero := by
  change diagonalFunctor.obj (walkingMappingResolution W) ≅
    diagonalFunctor.obj (iteratedZeroResolution W)
  exact diagonalFunctor.mapIso (outerExchangeIso W)

#print axioms zeroIso_natural
#print axioms targetIso_natural
#print axioms outerExchangeIso
#print axioms diagonalExchangeIso

end

end DaggerModels.PartII.OrdinaryWalkingPrecompletionExchange
