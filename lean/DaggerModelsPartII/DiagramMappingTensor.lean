import DaggerModelsPartII.DiagramMappingPrecompFibration
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory MorphismProperty HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen
universe u
namespace DaggerModels.PartII.InjectiveKanDiagram
variable (C : Type u) [Category.{u} C]
noncomputable section

def diagramTensorAssocIso (A : C ⥤ SSet.{u}) (K : SSet.{u}) :
    diagramTensor ((diagramTensor A).obj K) ≅ tensorLeft K ⋙ diagramTensor A :=
  NatIso.ofComponents
    (fun L => NatIso.ofComponents
      (fun c => (α_ (A.obj c) K L))
      (by
        intro c d f
        exact associator_naturality_left (A.map f) K L))
    (by
      intro L M f
      apply NatTrans.ext
      funext c
      exact associator_naturality_right (A.obj c) K f)

/-- Exponential law for the diagram tensor, natural in the target diagram. -/
def diagramMappingTensorIso (A : C ⥤ SSet.{u}) (K : SSet.{u}) :
    diagramMappingTarget ((diagramTensor A).obj K) ≅
      diagramMappingTarget A ⋙ ihom K :=
  conjugateIsoEquiv
    (diagramTensorMappingAdjunction ((diagramTensor A).obj K))
    ((ihom.adjunction K).comp (diagramTensorMappingAdjunction A))
    (diagramTensorAssocIso C A K).symm

theorem diagramTensorAssocIso_natural {A B : C ⥤ SSet.{u}}
    (i : A ⟶ B) (K : SSet.{u}) :
    ((curriedDiagramTensor C).map (((curriedDiagramTensor C).map i).app K)) ≫
        (diagramTensorAssocIso C B K).hom =
      (diagramTensorAssocIso C A K).hom ≫
        Functor.whiskerLeft (tensorLeft K) ((curriedDiagramTensor C).map i) := by
  apply NatTrans.ext
  funext L
  apply NatTrans.ext
  funext c
  exact associator_naturality_left (i.app c) K L

theorem conjugateDiagramTensorMap {A B : C ⥤ SSet.{u}} (i : A ⟶ B) :
    conjugateEquiv (diagramTensorMappingAdjunction B)
      (diagramTensorMappingAdjunction A) ((curriedDiagramTensor C).map i) =
        (diagramMappingSource C).map i.op := by
  apply NatTrans.ext
  funext W
  apply ((diagramTensorMappingAdjunction A).homEquiv _ W).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [conjugateEquiv_counit]
  apply ((diagramTensorMappingAdjunction A).homEquiv _ W).injective
  rw [Equiv.apply_symm_apply]
  have h := (diagramParametrizedAdjunction C).homEquiv_naturality_one i
    ((diagramTensorMappingAdjunction B).counit.app W)
  change ((diagramTensorMappingAdjunction A).homEquiv _ W) _ =
    ((diagramTensorMappingAdjunction B).homEquiv _ W)
      ((diagramTensorMappingAdjunction B).counit.app W) ≫
        ((diagramMappingSource C).map i.op).app W at h
  simpa only [← Adjunction.homEquiv_symm_id,
    Equiv.apply_symm_apply, Category.id_comp] using h

theorem diagramMappingTensorIso_precomp {A B : C ⥤ SSet.{u}}
    (i : A ⟶ B) (K : SSet.{u}) (W : C ⥤ SSet.{u}) :
    diagramMappingPrecomp (((curriedDiagramTensor C).map i).app K) W ≫
      (diagramMappingTensorIso C A K).hom.app W =
      (diagramMappingTensorIso C B K).hom.app W ≫
        (ihom K).map (diagramMappingPrecomp i W) := by
  let adjLA := diagramTensorMappingAdjunction ((diagramTensor A).obj K)
  let adjLB := diagramTensorMappingAdjunction ((diagramTensor B).obj K)
  let adjFA := (ihom.adjunction K).comp (diagramTensorMappingAdjunction A)
  let adjFB := (ihom.adjunction K).comp (diagramTensorMappingAdjunction B)
  let α := (curriedDiagramTensor C).map (((curriedDiagramTensor C).map i).app K)
  let β := Functor.whiskerLeft (tensorLeft K) ((curriedDiagramTensor C).map i)
  let θA := diagramTensorAssocIso C A K
  let θB := diagramTensorAssocIso C B K
  have hα : α ≫ θB.hom = θA.hom ≫ β := diagramTensorAssocIso_natural C i K
  have hα' : β ≫ θB.inv = θA.inv ≫ α := by
    calc
      β ≫ θB.inv = θA.inv ≫ (θA.hom ≫ β) ≫ θB.inv := by simp [Category.assoc]
      _ = θA.inv ≫ (α ≫ θB.hom) ≫ θB.inv := by rw [hα]
      _ = θA.inv ≫ α := by simp [Category.assoc]
  have hTensorConj : (conjugateEquiv adjLB adjLA) α =
      (diagramMappingSource C).map (((curriedDiagramTensor C).map i).app K).op :=
    conjugateDiagramTensorMap C (((curriedDiagramTensor C).map i).app K)
  have hBaseConj :
      (conjugateEquiv (diagramTensorMappingAdjunction B)
        (diagramTensorMappingAdjunction A)) ((curriedDiagramTensor C).map i) =
          (diagramMappingSource C).map i.op := conjugateDiagramTensorMap C i
  have hWhisk : (conjugateEquiv adjFB adjFA) β =
      Functor.whiskerRight ((diagramMappingSource C).map i.op) (ihom K) :=
    (conjugateEquiv_whiskerLeft (diagramTensorMappingAdjunction B)
      (diagramTensorMappingAdjunction A) (ihom.adjunction K)
      ((curriedDiagramTensor C).map i)).trans
        (congrArg (fun τ => Functor.whiskerRight τ (ihom K)) hBaseConj)
  have hnat :
      (diagramMappingSource C).map (((curriedDiagramTensor C).map i).app K).op ≫
          (diagramMappingTensorIso C A K).hom =
        (diagramMappingTensorIso C B K).hom ≫
          Functor.whiskerRight ((diagramMappingSource C).map i.op) (ihom K) := by
    calc
      _ = (conjugateEquiv adjLB adjLA) α ≫
          (conjugateEquiv adjLA adjFA) θA.inv := by
        rw [hTensorConj]
        simp only [diagramMappingTensorIso, conjugateIsoEquiv_apply_hom,
          Iso.symm_hom]
        rfl
      _ = (conjugateEquiv adjLB adjFA) (θA.inv ≫ α) :=
        conjugateEquiv_comp adjLB adjLA adjFA α θA.inv
      _ = (conjugateEquiv adjLB adjFA) (β ≫ θB.inv) := by rw [hα']
      _ = (conjugateEquiv adjLB adjFB) θB.inv ≫
          (conjugateEquiv adjFB adjFA) β :=
        (conjugateEquiv_comp adjLB adjFB adjFA θB.inv β).symm
      _ = _ := by
        rw [hWhisk]
        simp only [diagramMappingTensorIso, conjugateIsoEquiv_apply_hom,
          Iso.symm_hom]
        rfl
  exact congrArg (fun τ => τ.app W) hnat

theorem diagramTensorAssocIso_natural_K (A : C ⥤ SSet.{u})
    {K L : SSet.{u}} (j : K ⟶ L) :
    ((curriedDiagramTensor C).map ((diagramTensor A).map j)) ≫
        (diagramTensorAssocIso C A L).hom =
      (diagramTensorAssocIso C A K).hom ≫
        Functor.whiskerRight ((tensoringLeft SSet.{u}).map j) (diagramTensor A) := by
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext c
  exact associator_naturality_middle (A.obj c) j X

theorem diagramMappingTensorIso_tensorMap (A : C ⥤ SSet.{u})
    {K L : SSet.{u}} (j : K ⟶ L) (W : C ⥤ SSet.{u}) :
    diagramMappingPrecomp ((diagramTensor A).map j) W ≫
      (diagramMappingTensorIso C A K).hom.app W =
      (diagramMappingTensorIso C A L).hom.app W ≫
        (MonoidalClosed.pre j).app (diagramMappingSpace A W) := by
  let adjLK := diagramTensorMappingAdjunction ((diagramTensor A).obj K)
  let adjLL := diagramTensorMappingAdjunction ((diagramTensor A).obj L)
  let adjFK := (ihom.adjunction K).comp (diagramTensorMappingAdjunction A)
  let adjFL := (ihom.adjunction L).comp (diagramTensorMappingAdjunction A)
  let α := (curriedDiagramTensor C).map ((diagramTensor A).map j)
  let β := Functor.whiskerRight ((tensoringLeft SSet.{u}).map j) (diagramTensor A)
  let θK := diagramTensorAssocIso C A K
  let θL := diagramTensorAssocIso C A L
  have hα : α ≫ θL.hom = θK.hom ≫ β := diagramTensorAssocIso_natural_K C A j
  have hα' : β ≫ θL.inv = θK.inv ≫ α := by
    calc
      β ≫ θL.inv = θK.inv ≫ (θK.hom ≫ β) ≫ θL.inv := by simp [Category.assoc]
      _ = θK.inv ≫ (α ≫ θL.hom) ≫ θL.inv := by rw [hα]
      _ = θK.inv ≫ α := by simp [Category.assoc]
  have hTensorConj : (conjugateEquiv adjLL adjLK) α =
      (diagramMappingSource C).map ((diagramTensor A).map j).op :=
    conjugateDiagramTensorMap C ((diagramTensor A).map j)
  have hWhisk : (conjugateEquiv adjFL adjFK) β =
      Functor.whiskerLeft (diagramMappingTarget A) (MonoidalClosed.pre j) := by
    exact (conjugateEquiv_whiskerRight (ihom.adjunction L)
      (ihom.adjunction K) (diagramTensorMappingAdjunction A)
      ((tensoringLeft SSet.{u}).map j))
  have hnat :
      (diagramMappingSource C).map ((diagramTensor A).map j).op ≫
          (diagramMappingTensorIso C A K).hom =
        (diagramMappingTensorIso C A L).hom ≫
          Functor.whiskerLeft (diagramMappingTarget A) (MonoidalClosed.pre j) := by
    calc
      _ = (conjugateEquiv adjLL adjLK) α ≫
          (conjugateEquiv adjLK adjFK) θK.inv := by
        rw [hTensorConj]
        simp only [diagramMappingTensorIso, conjugateIsoEquiv_apply_hom,
          Iso.symm_hom]
        rfl
      _ = (conjugateEquiv adjLL adjFK) (θK.inv ≫ α) :=
        conjugateEquiv_comp adjLL adjLK adjFK α θK.inv
      _ = (conjugateEquiv adjLL adjFK) (β ≫ θL.inv) := by rw [hα']
      _ = (conjugateEquiv adjLL adjFL) θL.inv ≫
          (conjugateEquiv adjFL adjFK) β :=
        (conjugateEquiv_comp adjLL adjFL adjFK θL.inv β).symm
      _ = _ := by
        rw [hWhisk]
        simp only [diagramMappingTensorIso, conjugateIsoEquiv_apply_hom,
          Iso.symm_hom]
        rfl
  exact congrArg (fun τ => τ.app W) hnat

end
end DaggerModels.PartII.InjectiveKanDiagram
