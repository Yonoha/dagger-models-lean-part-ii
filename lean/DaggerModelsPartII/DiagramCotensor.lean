import DaggerModelsPartII.ProjectiveSimplicialAxiom
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import DaggerModelsPartII.SegalLocalizers
import DaggerModelsPartII.DiagramMappingTensor

/-!
# The literal cotensor of reversal-indexed simplicial-set diagrams

The existing pointwise internal-Hom construction is specialized to the
reversal diagram category. Its parametrized adjunction supplies the tensor
and cotensor coherences in the simplicial-set variable. The resulting Hom
equivalence is compared with the literal simplicial mapping space.
-/

set_option autoImplicit false

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace DaggerModels.PartII.DiagramCotensor

open SegalLocalizers

noncomputable section

/-- The actual cotensor bifunctor, pointwise internal Hom in simplicial sets. -/
abbrev diagramCotensor :
    SSet.{0}ᵒᵖ ⥤ ReverseDaggerSpace.{0} ⥤ ReverseDaggerSpace.{0} :=
  ProjectiveKanDiagram.diagramCotensorSource ReverseSimplexᵒᵖ

/-- The existing diagram tensor regarded as a functor in the diagram variable. -/
abbrev diagramTensorLeft (K : SSet.{0}) :
    ReverseDaggerSpace.{0} ⥤ ReverseDaggerSpace.{0} :=
  (InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip.obj K

@[simp] theorem diagramCotensor_obj_obj (K : SSet.{0})
    (W : ReverseDaggerSpace.{0}) (c : ReverseSimplexᵒᵖ) :
    ((diagramCotensor.obj (op K)).obj W).obj c =
      (ihom K).obj (W.obj c) := rfl

@[simp] theorem diagramCotensor_map_app (K : SSet.{0})
    {W W' : ReverseDaggerSpace.{0}} (f : W ⟶ W')
    (c : ReverseSimplexᵒᵖ) :
    ((diagramCotensor.obj (op K)).map f).app c =
      (ihom K).map (f.app c) := rfl

@[simp] theorem diagramTensorLeft_obj (K : SSet.{0})
    (A : ReverseDaggerSpace.{0}) :
    (diagramTensorLeft K).obj A = (diagramTensor A).obj K := rfl

/-- A fixed simplicial set gives the actual tensor–cotensor adjunction. -/
def tensorCotensorAdjunction (K : SSet.{0}) :
    diagramTensorLeft K ⊣ diagramCotensor.obj (op K) :=
  (ProjectiveKanDiagram.diagramTensorCotensorAdjunction ReverseSimplexᵒᵖ).adj K

/-- Coherence in the simplicial-set parameter is inherited from the actual
parametrized adjunction, not chosen separately for each cotensor. -/
def parametrizedTensorCotensorAdjunction :
    (InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip ⊣₂
      diagramCotensor :=
  ProjectiveKanDiagram.diagramTensorCotensorAdjunction ReverseSimplexᵒᵖ

/-- A map into the cotensor is the same map represented by the literal
simplicial mapping space at the simplicial parameter. -/
def cotensorMappingHomEquiv (K : SSet.{0})
    (A W : ReverseDaggerSpace.{0}) :
    (A ⟶ (diagramCotensor.obj (op K)).obj W) ≃
      (K ⟶ diagramMappingSpace A W) :=
  ((tensorCotensorAdjunction K).homEquiv A W).symm.trans
    ((diagramTensorMappingAdjunction A).homEquiv K W)

/-- Symmetric associativity exchanges a fixed simplicial parameter with the
variable parameter of the diagram tensor. -/
def tensorParameterSwapIso (A : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    tensorLeft K ⋙ diagramTensor A ≅
      diagramTensor A ⋙ diagramTensorLeft K :=
  NatIso.ofComponents
    (fun L => NatIso.ofComponents
      (fun c => (whiskerLeftIso (A.obj c) (β_ K L)) ≪≫
        (α_ (A.obj c) L K).symm)
      (by
        intro c d f
        change (A.map f ▷ (K ⊗ L)) ≫
            (A.obj d ◁ (β_ K L).hom ≫ (α_ (A.obj d) L K).inv) =
          (A.obj c ◁ (β_ K L).hom ≫ (α_ (A.obj c) L K).inv) ≫
            ((A.map f ▷ L) ▷ K)
        simp only [← Category.assoc]
        rw [← whisker_exchange]
        simp only [Category.assoc, associator_inv_naturality_left]))
    (by
      intro L M f
      apply NatTrans.ext
      funext c
      change (A.obj c ◁ (K ◁ f)) ≫
          (A.obj c ◁ (β_ K M).hom ≫ (α_ (A.obj c) M K).inv) =
        (A.obj c ◁ (β_ K L).hom ≫ (α_ (A.obj c) L K).inv) ≫
          ((A.obj c ◁ f) ▷ K)
      simp only [← Category.assoc]
      rw [← whiskerLeft_comp, BraidedCategory.braiding_naturality_right,
        whiskerLeft_comp]
      simp only [Category.assoc, associator_inv_naturality_middle])

/-- Mapping into a pointwise cotensor is the internal Hom of the actual
diagram mapping space, naturally in the target diagram. -/
def diagramMappingCotensorIso (A : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    diagramCotensor.obj (op K) ⋙ diagramMappingTarget A ≅
      diagramMappingTarget A ⋙ ihom K :=
  (conjugateIsoEquiv
      ((diagramTensorMappingAdjunction A).comp (tensorCotensorAdjunction K))
      ((ihom.adjunction K).comp (diagramTensorMappingAdjunction A))
      (tensorParameterSwapIso A K))

/-- The internal-Hom law for the actual simplicial mapping space. -/
def mappingCotensorIso (A W : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    diagramMappingSpace A ((diagramCotensor.obj (op K)).obj W) ≅
      (ihom K).obj (diagramMappingSpace A W) :=
  (diagramMappingCotensorIso A K).app W

/-- The tensor parameter exchange is natural in the source diagram. -/
theorem tensorParameterSwapIso_natural {A B : ReverseDaggerSpace.{0}}
    (i : A ⟶ B) (K : SSet.{0}) :
    Functor.whiskerLeft (tensorLeft K)
        ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i) ≫
        (tensorParameterSwapIso B K).hom =
      (tensorParameterSwapIso A K).hom ≫
        Functor.whiskerRight
          ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i)
          (diagramTensorLeft K) := by
  apply NatTrans.ext
  funext L
  apply NatTrans.ext
  funext c
  change (i.app c ▷ (K ⊗ L)) ≫
      (B.obj c ◁ (β_ K L).hom ≫ (α_ (B.obj c) L K).inv) =
    (A.obj c ◁ (β_ K L).hom ≫ (α_ (A.obj c) L K).inv) ≫
      ((i.app c ▷ L) ▷ K)
  simp only [← Category.assoc]
  rw [← whisker_exchange]
  simp only [Category.assoc, associator_inv_naturality_left]

/-- The tensor parameter exchange is natural in the simplicial parameter. -/
theorem tensorParameterSwapIso_natural_K (A : ReverseDaggerSpace.{0})
    {K L : SSet.{0}} (j : K ⟶ L) :
    Functor.whiskerRight ((tensoringLeft SSet.{0}).map j) (diagramTensor A) ≫
        (tensorParameterSwapIso A L).hom =
      (tensorParameterSwapIso A K).hom ≫
        Functor.whiskerLeft (diagramTensor A)
          ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip.map j) := by
  apply NatTrans.ext
  funext T
  apply NatTrans.ext
  funext c
  change (A.obj c ◁ (j ▷ T)) ≫
      (A.obj c ◁ (β_ L T).hom ≫ (α_ (A.obj c) T L).inv) =
    (A.obj c ◁ (β_ K T).hom ≫ (α_ (A.obj c) T K).inv) ≫
      ((A.obj c ⊗ T) ◁ j)
  simp only [← Category.assoc]
  rw [← whiskerLeft_comp, BraidedCategory.braiding_naturality_left,
    whiskerLeft_comp]
  simp only [Category.assoc, associator_inv_naturality_right]

/-- The mapping-cotensor law commutes with precomposition in its source
diagram. -/
theorem mappingCotensorIso_precomp {A B : ReverseDaggerSpace.{0}}
    (i : A ⟶ B) (W : ReverseDaggerSpace.{0}) (K : SSet.{0}) :
    diagramMappingPrecomp i ((diagramCotensor.obj (op K)).obj W) ≫
        (mappingCotensorIso A W K).hom =
      (mappingCotensorIso B W K).hom ≫
        (ihom K).map (diagramMappingPrecomp i W) := by
  let adjLA := (diagramTensorMappingAdjunction A).comp (tensorCotensorAdjunction K)
  let adjLB := (diagramTensorMappingAdjunction B).comp (tensorCotensorAdjunction K)
  let adjFA := (ihom.adjunction K).comp (diagramTensorMappingAdjunction A)
  let adjFB := (ihom.adjunction K).comp (diagramTensorMappingAdjunction B)
  let α := Functor.whiskerRight
    ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i)
    (diagramTensorLeft K)
  let β := Functor.whiskerLeft (tensorLeft K)
    ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i)
  let θA := tensorParameterSwapIso A K
  let θB := tensorParameterSwapIso B K
  have hθ : β ≫ θB.hom = θA.hom ≫ α :=
    tensorParameterSwapIso_natural i K
  have hα : (conjugateEquiv adjLB adjLA) α =
      Functor.whiskerLeft (diagramCotensor.obj (op K))
        ((InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ).map i.op) := by
    exact (conjugateEquiv_whiskerRight
      (diagramTensorMappingAdjunction B) (diagramTensorMappingAdjunction A)
      (tensorCotensorAdjunction K)
      ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i)).trans
        (congrArg (fun τ => Functor.whiskerLeft (diagramCotensor.obj (op K)) τ)
          (InjectiveKanDiagram.conjugateDiagramTensorMap ReverseSimplexᵒᵖ i))
  have hβ : (conjugateEquiv adjFB adjFA) β =
      Functor.whiskerRight
        ((InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ).map i.op)
        (ihom K) := by
    exact (conjugateEquiv_whiskerLeft
      (diagramTensorMappingAdjunction B) (diagramTensorMappingAdjunction A)
      (ihom.adjunction K)
      ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).map i)).trans
        (congrArg (fun τ => Functor.whiskerRight τ (ihom K))
          (InjectiveKanDiagram.conjugateDiagramTensorMap ReverseSimplexᵒᵖ i))
  have hnat :
      Functor.whiskerLeft (diagramCotensor.obj (op K))
          ((InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ).map i.op) ≫
          (diagramMappingCotensorIso A K).hom =
        (diagramMappingCotensorIso B K).hom ≫
          Functor.whiskerRight
            ((InjectiveKanDiagram.diagramMappingSource ReverseSimplexᵒᵖ).map i.op)
            (ihom K) := by
    calc
      _ = (conjugateEquiv adjLB adjLA) α ≫
          (conjugateEquiv adjLA adjFA) θA.hom := by
        rw [hα]
        rfl
      _ = (conjugateEquiv adjLB adjFA) (θA.hom ≫ α) :=
        conjugateEquiv_comp adjLB adjLA adjFA α θA.hom
      _ = (conjugateEquiv adjLB adjFA) (β ≫ θB.hom) := by rw [hθ]
      _ = (conjugateEquiv adjLB adjFB) θB.hom ≫
          (conjugateEquiv adjFB adjFA) β :=
        (conjugateEquiv_comp adjLB adjFB adjFA θB.hom β).symm
      _ = _ := by
        rw [hβ]
        rfl
  exact congrArg (fun τ => τ.app W) hnat

/-- The cotensor's contravariant action in the simplicial parameter is the
mate of the tensor's covariant action under the parametrized adjunction. -/
theorem cotensorMap_conjugate {K L : SSet.{0}} (j : K ⟶ L) :
    conjugateEquiv (tensorCotensorAdjunction L) (tensorCotensorAdjunction K)
        ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip.map j) =
      diagramCotensor.map j.op := by
  apply NatTrans.ext
  funext W
  apply ((tensorCotensorAdjunction K).homEquiv _ W).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  apply ((tensorCotensorAdjunction K).homEquiv _ W).injective
  rw [Equiv.apply_symm_apply]
  have h := parametrizedTensorCotensorAdjunction.homEquiv_naturality_one j
    ((tensorCotensorAdjunction L).counit.app W)
  change ((tensorCotensorAdjunction K).homEquiv _ W) _ =
    ((tensorCotensorAdjunction L).homEquiv _ W)
      ((tensorCotensorAdjunction L).counit.app W) ≫
        (diagramCotensor.map j.op).app W at h
  simpa only [← Adjunction.homEquiv_symm_id,
    Equiv.apply_symm_apply, Category.id_comp] using h

/-- The mapping-cotensor law commutes with restriction of the simplicial
parameter. -/
theorem mappingCotensorIso_parameter (A W : ReverseDaggerSpace.{0})
    {K L : SSet.{0}} (j : K ⟶ L) :
    diagramMappingPostcomp A ((diagramCotensor.map j.op).app W) ≫
        (mappingCotensorIso A W K).hom =
      (mappingCotensorIso A W L).hom ≫
        (MonoidalClosed.pre j).app (diagramMappingSpace A W) := by
  let adjLK := (diagramTensorMappingAdjunction A).comp (tensorCotensorAdjunction K)
  let adjLL := (diagramTensorMappingAdjunction A).comp (tensorCotensorAdjunction L)
  let adjFK := (ihom.adjunction K).comp (diagramTensorMappingAdjunction A)
  let adjFL := (ihom.adjunction L).comp (diagramTensorMappingAdjunction A)
  let α := Functor.whiskerLeft (diagramTensor A)
    ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip.map j)
  let β := Functor.whiskerRight ((tensoringLeft SSet.{0}).map j) (diagramTensor A)
  let θK := tensorParameterSwapIso A K
  let θL := tensorParameterSwapIso A L
  have hθ : β ≫ θL.hom = θK.hom ≫ α :=
    tensorParameterSwapIso_natural_K A j
  have hα : (conjugateEquiv adjLL adjLK) α =
      Functor.whiskerRight (diagramCotensor.map j.op) (diagramMappingTarget A) := by
    exact (conjugateEquiv_whiskerLeft
      (tensorCotensorAdjunction L) (tensorCotensorAdjunction K)
      (diagramTensorMappingAdjunction A)
      ((InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ).flip.map j)).trans
        (congrArg (fun τ => Functor.whiskerRight τ (diagramMappingTarget A))
          (cotensorMap_conjugate j))
  have hβ : (conjugateEquiv adjFL adjFK) β =
      Functor.whiskerLeft (diagramMappingTarget A) (MonoidalClosed.pre j) := by
    exact conjugateEquiv_whiskerRight (ihom.adjunction L) (ihom.adjunction K)
      (diagramTensorMappingAdjunction A) ((tensoringLeft SSet.{0}).map j)
  have hnat :
      Functor.whiskerRight (diagramCotensor.map j.op) (diagramMappingTarget A) ≫
          (diagramMappingCotensorIso A K).hom =
        (diagramMappingCotensorIso A L).hom ≫
          Functor.whiskerLeft (diagramMappingTarget A) (MonoidalClosed.pre j) := by
    calc
      _ = (conjugateEquiv adjLL adjLK) α ≫
          (conjugateEquiv adjLK adjFK) θK.hom := by
        rw [hα]
        rfl
      _ = (conjugateEquiv adjLL adjFK) (θK.hom ≫ α) :=
        conjugateEquiv_comp adjLL adjLK adjFK α θK.hom
      _ = (conjugateEquiv adjLL adjFK) (β ≫ θL.hom) := by rw [hθ]
      _ = (conjugateEquiv adjLL adjFL) θL.hom ≫
          (conjugateEquiv adjFL adjFK) β :=
        (conjugateEquiv_comp adjLL adjFL adjFK θL.hom β).symm
      _ = _ := by
        rw [hβ]
        rfl
  exact congrArg (fun τ => τ.app W) hnat

end

end DaggerModels.PartII.DiagramCotensor
