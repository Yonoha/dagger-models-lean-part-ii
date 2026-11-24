import DaggerModelsPartII.DiagramMappingSpace
import DaggerModelsPartII.IndexKanExtensions
import DaggerModelsPartII.ProjectiveKanDiagram
import Mathlib.CategoryTheory.Adjunction.Unique

/-! The representable product functor and evaluation. -/

set_option autoImplicit false

open CategoryTheory Opposite MonoidalCategory

universe u

namespace DaggerModels.PartII

variable {C : Type u} [SmallCategory C] (c : C)

/-- Product with the simplicial representable, viewed as a functor in the coefficient. -/
def representableTensor : SSet.{u} ⥤ (Cᵒᵖ ⥤ SSet.{u}) :=
  diagramTensor ((simplicialYoneda.{u, 0} C).obj c)

/-- The product has the expected degreewise vertices. -/
theorem representableTensor_obj_obj_obj (K : SSet.{u}) (d : C)
    (n : SimplexCategoryᵒᵖ) :
    (((representableTensor c).obj K).obj (op d)).obj n =
      (ULift.{u} (d ⟶ c) × K.obj n) := rfl

/-- Evaluation at the identity component of a transformation. -/
def representableTensorHomTo {K : SSet.{u}} {W : Cᵒᵖ ⥤ SSet.{u}}
    (η : (representableTensor c).obj K ⟶ W) : K ⟶ W.obj (op c) where
  app n x := (η.app (op c)).app n (ULift.up (𝟙 c), x)
  naturality {n m} g := by
    funext x
    have h := congrFun ((η.app (op c)).naturality g) (ULift.up (𝟙 c), x)
    simpa [representableTensor, diagramTensor, simplicialYoneda, discretePresheaf]
      using h

/-- Extend a coefficient map along every arrow into the representing object. -/
def representableTensorHomFrom {K : SSet.{u}} {W : Cᵒᵖ ⥤ SSet.{u}}
    (α : K ⟶ W.obj (op c)) : (representableTensor c).obj K ⟶ W where
  app d := {
    app n p := (W.map (p.1.down : d.unop ⟶ c).op).app n (α.app n p.2)
    naturality {n m} g := by
      funext p
      simp [representableTensor, diagramTensor, simplicialYoneda, discretePresheaf,
        ← FunctorToTypes.naturality]
  }
  naturality {d e} g := by
    apply NatTrans.ext
    funext n p
    simp [representableTensor, diagramTensor, simplicialYoneda, discretePresheaf,
      W.map_comp]

theorem representableTensorHomTo_from {K : SSet.{u}} {W : Cᵒᵖ ⥤ SSet.{u}}
    (α : K ⟶ W.obj (op c)) :
    representableTensorHomTo c (representableTensorHomFrom c α) = α := by
  apply NatTrans.ext
  funext n x
  simp [representableTensorHomTo, representableTensorHomFrom]

theorem representableTensorHomFrom_to {K : SSet.{u}} {W : Cᵒᵖ ⥤ SSet.{u}}
    (η : (representableTensor c).obj K ⟶ W) :
    representableTensorHomFrom c (representableTensorHomTo c η) = η := by
  apply NatTrans.ext
  funext d
  apply NatTrans.ext
  funext n p
  obtain ⟨⟨f⟩, x⟩ := p
  have h := congrFun (congrArg (fun φ ↦ φ.app n) (η.naturality f.op))
    (ULift.up (𝟙 c), x)
  simpa [representableTensorHomTo, representableTensorHomFrom,
    representableTensor, diagramTensor, simplicialYoneda, discretePresheaf,
    uliftYoneda, yoneda] using h.symm

/-- The enriched Yoneda bijection for a representable times a simplicial set. -/
def representableTensorHomEquiv (K : SSet.{u}) (W : Cᵒᵖ ⥤ SSet.{u}) :
    ((representableTensor c).obj K ⟶ W) ≃ (K ⟶ W.obj (op c)) where
  toFun := representableTensorHomTo c
  invFun := representableTensorHomFrom c
  left_inv := representableTensorHomFrom_to c
  right_inv := representableTensorHomTo_from c

/-- Product with the simplicial representable is left adjoint to evaluation. -/
noncomputable def representableTensorAdjunction :
    representableTensor c ⊣ (evaluation Cᵒᵖ SSet.{u}).obj (op c) := by
  apply Adjunction.mkOfHomEquiv
  refine {
    homEquiv := fun K W ↦ representableTensorHomEquiv c K W
    homEquiv_naturality_left_symm := ?_
    homEquiv_naturality_right := ?_ }
  · intro K' K W f α
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext n p
    simp [representableTensorHomEquiv, representableTensorHomFrom,
      representableTensor, diagramTensor]
  · intro K W W' η g
    apply NatTrans.ext
    funext n x
    rfl

/-- The representable product is naturally isomorphic to the free diagram. -/
noncomputable def representableTensorIsoFree :
    representableTensor c ≅ ProjectiveKanDiagram.free Cᵒᵖ (op c) :=
  (representableTensorAdjunction c).leftAdjointUniq
    (evaluationAdjunctionRight SSet.{u} (op c))

/-- The isomorphism is natural in the simplicial-set coefficient. -/
theorem representableTensorIsoFree_naturality {K L : SSet.{u}} (f : K ⟶ L) :
    (representableTensor c).map f ≫ (representableTensorIsoFree c).hom.app L =
      (representableTensorIsoFree c).hom.app K ≫
        (ProjectiveKanDiagram.free Cᵒᵖ (op c)).map f :=
  (representableTensorIsoFree c).hom.naturality f

/-- The same comparison identifies the literal boundary generators. -/
theorem representableTensorIsoFree_boundary (n : ℕ) :
    (representableTensor c).map (SSet.boundary n).ι ≫
        (representableTensorIsoFree c).hom.app _ =
      (representableTensorIsoFree c).hom.app _ ≫
        (ProjectiveKanDiagram.free Cᵒᵖ (op c)).map (SSet.boundary n).ι :=
  representableTensorIsoFree_naturality c (SSet.boundary n).ι

/-- The same comparison identifies the literal horn generators. -/
theorem representableTensorIsoFree_horn (n : ℕ) (i : Fin (n + 2)) :
    (representableTensor c).map (SSet.horn (n + 1) i).ι ≫
        (representableTensorIsoFree c).hom.app _ =
      (representableTensorIsoFree c).hom.app _ ≫
        (ProjectiveKanDiagram.free Cᵒᵖ (op c)).map (SSet.horn (n + 1) i).ι :=
  representableTensorIsoFree_naturality c (SSet.horn (n + 1) i).ι

end DaggerModels.PartII
