import DaggerModelsPartII.CharacteristicQuotient
import DaggerModelsPartII.PathOrbitCells
import DaggerModelsPartII.ChainPathCoverage
import DaggerModelsPartII.ReversalOuterFaceSubobject
import DaggerModelsPartII.CellBoundaryGeometry

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial DaggerModels
open DaggerModelsPartII.DaggerSimplexIndex

namespace DaggerModels.PartII.LengthStageAttaching

open PathOrbitCells CharacteristicComposite CharacteristicInterior
open CharacteristicQuotient CharacteristicOuterBoundary
open FreeDaggerPathChains DaggerNerveLengthFiltration
open ChainPathCoverage ReversalOuterFaceSubobject
open ReversalOuterFaceAction ReversalRepresentableFixedPoints
open DiscreteBorelDiagram C2InvolutionActions

noncomputable section

def wordCharacteristic {m ℓ : ℕ} (w : Word m ℓ) :
    yoneda.obj (⟨ℓ⟩ : ReverseSimplex) ⟶
      (DaggerNativeOrdinaryDaggerNerveLift.daggerNerve
        (FreeDaggerSimplex m)).extension :=
  w.property ▸ characteristic w.val.hom

def wordStageCharacteristic {m ℓ : ℕ} (w : Word m ℓ) :
    yoneda.obj (⟨ℓ⟩ : ReverseSimplex) ⟶
      (lengthFiltration m ℓ).toFunctor :=
  w.property ▸ stageCharacteristic w.val.hom

theorem wordPal_arrow {m ℓ : ℕ} (w : Word m ℓ)
    (hw : Palindromic w) :
    Arrow.mk w.val.hom = daggerArrow (Arrow.mk w.val.hom) := by
  have h := congrArg Subtype.val hw
  change daggerArrow w.val = w.val at h
  simpa only [Arrow.mk_eq] using h.symm

def wordStageQuotient {m ℓ : ℕ} (w : Word m ℓ)
    (hw : Palindromic w) :
    strictOrbitDiagram
        (yoneda.obj (⟨ℓ⟩ : ReverseSimplex))
        (representableReversalIso ℓ)
        (representableReversal_involutive ℓ) ⟶
      discreteDiagram.obj (lengthFiltration m ℓ).toFunctor :=
  w.property ▸ stageCharacteristicQuotientMap w.val.hom (wordPal_arrow w hw)

def wordBoundaryCharacteristic {m ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (w : Word m ℓ) :
    (outerFaceSubpresheafAt ℓ (by omega : 1 ≤ ℓ)).toFunctor ⟶
      (lengthFiltration m (ℓ - 1)).toFunctor := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact boundaryCharacteristic p.hom (by omega)

def wordBoundaryQuotient {m ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (w : Word m ℓ) (hw : Palindromic w) :
    strictOrbitDiagram
        (outerFaceSubpresheafAt ℓ (by omega : 1 ≤ ℓ)).toFunctor
        (boundaryAction ℓ (by omega : 1 ≤ ℓ))
        (subsetAction_involutive
          (yoneda.obj (⟨ℓ⟩ : ReverseSimplex))
          (representableReversalIso ℓ)
          (representableReversal_involutive ℓ)
          (outerFaceSubpresheafAt ℓ (by omega : 1 ≤ ℓ))
          (outerFace_invariant ℓ (by omega : 1 ≤ ℓ))) ⟶
      discreteDiagram.obj (lengthFiltration m (ℓ - 1)).toFunctor := by
  cases w with
  | mk p hlen =>
    cases hlen
    exact boundaryCharacteristicQuotientMap p.hom (by omega)
      (wordPal_arrow ⟨p, rfl⟩ hw)

def evalZero : SSet.{0} ⥤ Type 0 :=
  (evaluation SimplexCategoryᵒᵖ (Type 0)).obj (op ⦋0⦌)

def representableOrbitPresheaf (ℓ : ℕ) :
    ReverseSimplexᵒᵖ ⥤ Type 0 :=
  strictOrbitDiagram
      (yoneda.obj (⟨ℓ⟩ : ReverseSimplex))
      (representableReversalIso ℓ)
      (representableReversal_involutive ℓ) ⋙ evalZero

def boundaryOrbitPresheaf (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ReverseSimplexᵒᵖ ⥤ Type 0 :=
  strictOrbitDiagram
      (outerFaceSubpresheafAt ℓ hℓ).toFunctor
      (boundaryAction ℓ hℓ)
      (subsetAction_involutive
        (yoneda.obj (⟨ℓ⟩ : ReverseSimplex))
        (representableReversalIso ℓ)
        (representableReversal_involutive ℓ)
        (outerFaceSubpresheafAt ℓ hℓ)
        (outerFace_invariant ℓ hℓ)) ⋙ evalZero

def indexedCells {C : Type*} [Category C]
    (R S : Type 0) (F G : C ⥤ Type 0) : C ⥤ Type 0 where
  obj c := (R × F.obj c) ⊕ (S × G.obj c)
  map {c d} f := fun x => match x with
    | Sum.inl (r, u) => Sum.inl (r, F.map f u)
    | Sum.inr (s, v) => Sum.inr (s, G.map f v)
  map_id c := by
    funext x
    rcases x with ⟨r, u⟩ | ⟨s, v⟩ <;> simp
  map_comp {a b c} f g := by
    funext x
    rcases x with ⟨r, u⟩ | ⟨s, v⟩ <;> simp

def indexedCellsMap {C : Type*} [Category C]
    {R S : Type 0} {F G F' G' : C ⥤ Type 0}
    (α : F ⟶ F') (β : G ⟶ G') :
    indexedCells R S F G ⟶ indexedCells R S F' G' where
  app c := fun x => match x with
    | Sum.inl (r, u) => Sum.inl (r, α.app c u)
    | Sum.inr (s, v) => Sum.inr (s, β.app c v)
  naturality c d f := by
    funext x
    rcases x with ⟨r, u⟩ | ⟨s, v⟩
    · exact congrArg (Sum.inl ∘ Prod.mk r) (congrFun (α.naturality f) u)
    · exact congrArg (Sum.inr ∘ Prod.mk s) (congrFun (β.naturality f) v)

def indexedCellsElim {C : Type*} [Category C]
    {R S : Type 0} {F G H : C ⥤ Type 0}
    (α : ∀ _ : R, F ⟶ H) (β : ∀ _ : S, G ⟶ H) :
    indexedCells R S F G ⟶ H where
  app c := fun x => match x with
    | Sum.inl (r, u) => (α r).app c u
    | Sum.inr (s, v) => (β s).app c v
  naturality c d f := by
    funext x
    rcases x with ⟨r, u⟩ | ⟨s, v⟩
    · exact congrFun ((α r).naturality f) u
    · exact congrFun ((β s).naturality f) v

def palStageTypeMap {m ℓ : ℕ} (w : Word m ℓ)
    (hw : Palindromic w) :
    representableOrbitPresheaf ℓ ⟶ (lengthFiltration m ℓ).toFunctor := by
  exact Functor.whiskerRight (wordStageQuotient w hw) evalZero

def palBoundaryTypeMap {m ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (w : Word m ℓ) (hw : Palindromic w) :
    boundaryOrbitPresheaf ℓ (by omega) ⟶
      (lengthFiltration m (ℓ - 1)).toFunctor := by
  exact Functor.whiskerRight (wordBoundaryQuotient hℓ w hw) evalZero

def boundaryOrbitTypeInclusion (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    boundaryOrbitPresheaf ℓ hℓ ⟶ representableOrbitPresheaf ℓ := by
  exact Functor.whiskerRight
    (subsetStrictOrbitInclusion
      (yoneda.obj (⟨ℓ⟩ : ReverseSimplex))
      (representableReversalIso ℓ)
      (representableReversal_involutive ℓ)
      (outerFaceSubpresheafAt ℓ hℓ)
      (outerFace_invariant ℓ hℓ)) evalZero

def cellPresheaf (m ℓ : ℕ) : ReverseSimplexᵒᵖ ⥤ Type 0 :=
  indexedCells (NonpalOrbit m ℓ) (PalOrbit m ℓ)
    (yoneda.obj (⟨ℓ⟩ : ReverseSimplex)) (representableOrbitPresheaf ℓ)

def boundaryPresheaf (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ReverseSimplexᵒᵖ ⥤ Type 0 :=
  indexedCells (NonpalOrbit m ℓ) (PalOrbit m ℓ)
    (outerFaceSubpresheafAt ℓ hℓ).toFunctor (boundaryOrbitPresheaf ℓ hℓ)

def boundaryToCell (m ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    boundaryPresheaf m ℓ hℓ ⟶ cellPresheaf m ℓ :=
  indexedCellsMap (outerFaceSubpresheafAt ℓ hℓ).ι
    (boundaryOrbitTypeInclusion ℓ hℓ)

def cellToStage (m ℓ : ℕ) :
    cellPresheaf m ℓ ⟶ (lengthFiltration m ℓ).toFunctor :=
  indexedCellsElim
    (fun r : NonpalOrbit m ℓ => wordStageCharacteristic (representative r.val))
    (fun s : PalOrbit m ℓ => palStageTypeMap (representative s.val) s.property)

def boundaryToPrevious (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    boundaryPresheaf m ℓ (by omega) ⟶
      (lengthFiltration m (ℓ - 1)).toFunctor :=
  indexedCellsElim
    (fun r : NonpalOrbit m ℓ => wordBoundaryCharacteristic hℓ (representative r.val))
    (fun s : PalOrbit m ℓ =>
      palBoundaryTypeMap hℓ (representative s.val) s.property)

def stageInclusion (m ℓ : ℕ) :
    (lengthFiltration m (ℓ - 1)).toFunctor ⟶
      (lengthFiltration m ℓ).toFunctor :=
  Subfunctor.homOfLe (lengthFiltration_mono m (Nat.sub_le ℓ 1))

private theorem pal_boundary_square_point {m ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (w : Word m ℓ) (hw : Palindromic w)
    (k : ReverseSimplexᵒᵖ) (q : (boundaryOrbitPresheaf ℓ (by omega)).obj k) :
    (stageInclusion m ℓ).app k ((palBoundaryTypeMap hℓ w hw).app k q) =
      (palStageTypeMap w hw).app k
        ((boundaryOrbitTypeInclusion ℓ (by omega)).app k q) := by
  cases w with
  | mk p hlen =>
    cases hlen
    induction q using Quotient.inductionOn with
    | _ φ =>
      apply Subtype.ext
      rfl

theorem boundary_square (m ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    boundaryToPrevious m ℓ hℓ ≫ stageInclusion m ℓ =
      boundaryToCell m ℓ (by omega) ≫ cellToStage m ℓ := by
  ext k x
  rcases x with ⟨r, φ⟩ | ⟨s, q⟩
  · change (stageInclusion m ℓ).app k
        ((wordBoundaryCharacteristic hℓ (representative r.val)).app k φ) =
      ((wordStageCharacteristic (representative r.val)).app k φ.val)
    cases hrep : representative r.val with
    | mk p hlen =>
      cases hlen
      exact congrFun (NatTrans.congr_app
        (boundaryCharacteristic_square p.hom (by omega)) k) φ
  · exact pal_boundary_square_point hℓ (representative s.val) s.property k q

end

end DaggerModels.PartII.LengthStageAttaching
