import DaggerModelsPartII.DiagramTensorMappingAdjunction
import DaggerModelsPartII.DiagramMappingPrecompFibration
import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
import Mathlib.CategoryTheory.Enriched.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic

/-!
# Native simplicial enrichment of simplicial-set diagrams

The end construction in Mathlib supplies enriched identities, composition,
associativity, unit laws, and compatibility with the ordinary natural
transformations of the diagram category.
-/

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory Opposite

namespace DaggerModels.PartII.DiagramSimplicialEnrichment

noncomputable section


variable (J : Type) [SmallCategory J]

private local instance sSetClosedEnrichment :
    EnrichedOrdinaryCategory SSet SSet.{0} :=
  MonoidalClosed.enrichedOrdinaryCategorySelf SSet

/-- The native simplicial-category structure on the diagram category. -/
def diagramSimplicialCategory :
    SimplicialCategory (J ⥤ SSet.{0}) := by
  letI : ∀ (A B : J ⥤ SSet.{0}),
      Enriched.FunctorCategory.HasEnrichedHom SSet A B := by
    intro A B
    infer_instance
  exact Enriched.FunctorCategory.enrichedOrdinaryCategory SSet SSet.{0} J

/-- A representability comparison between the native enriched Hom end and the
literal mapping simplicial set. -/
def mappingEquiv (A B : J ⥤ SSet.{0}) (K : SSet.{0}) :
    (K ⟶ Enriched.FunctorCategory.enrichedHom SSet A B) ≃
      (K ⟶ diagramMappingSpace A B) := by
  let h₁ := (Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv
    (W := K)
  let h₂ := (MonoidalClosed.FunctorCategory.homEquiv
    (F₁ := A) (F₂ := (Functor.const J).obj K) (F₃ := B)).symm
  let h₃ := (diagramTensorMappingAdjunction A).homEquiv K B
  exact h₁.trans (h₂.trans h₃)

private theorem mappingEquiv_naturality (A B : J ⥤ SSet.{0})
    {K L : SSet.{0}} (g : L ⟶ K)
    (h : K ⟶ Enriched.FunctorCategory.enrichedHom SSet A B) :
    mappingEquiv J A B L (g ≫ h) = g ≫ mappingEquiv J A B K h := by
  dsimp [mappingEquiv]
  convert_to ((diagramTensorMappingAdjunction A).homEquiv L B)
      (MonoidalClosed.FunctorCategory.homEquiv.symm
        ((Functor.const J).map g ≫
          (Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv h)) =
      g ≫ ((diagramTensorMappingAdjunction A).homEquiv K B)
        (MonoidalClosed.FunctorCategory.homEquiv.symm
          ((Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv h))
    using 1
  · rw [MonoidalClosed.FunctorCategory.homEquiv_naturality_two_symm]
    exact (diagramTensorMappingAdjunction A).homEquiv_naturality_left g _

/-- The native end-valued enriched Hom is canonically isomorphic to the
literal simplicial set of natural transformations from `A × Δ[n]` to `B`. -/
def mappingIso (A B : J ⥤ SSet.{0}) :
    Enriched.FunctorCategory.enrichedHom SSet A B ≅ diagramMappingSpace A B := by
  let E := Enriched.FunctorCategory.enrichedHom SSet A B
  let L := diagramMappingSpace A B
  let e := mappingEquiv J A B
  let hom : E ⟶ L := e E (𝟙 E)
  let inv : L ⟶ E := (e L).symm (𝟙 L)
  refine ⟨hom, inv, ?_, ?_⟩
  · apply (e E).injective
    have h := mappingEquiv_naturality J A B hom inv
    change e E (hom ≫ inv) = hom ≫ e L inv at h
    rw [Equiv.apply_symm_apply] at h
    simpa only [e, hom, Equiv.apply_symm_apply, Category.comp_id] using h
  · have h := mappingEquiv_naturality J A B inv (𝟙 E)
    change e L (inv ≫ 𝟙 E) = inv ≫ e E (𝟙 E) at h
    simpa only [Category.comp_id, e, inv, Equiv.apply_symm_apply, hom] using h.symm

/-- The comparison with the Hom of the chosen native simplicial enrichment. -/
def nativeMappingIso (A B : J ⥤ SSet.{0}) :
    (letI := diagramSimplicialCategory J;
      SimplicialCategory.sHom A B ≅ diagramMappingSpace A B) := by
  exact mappingIso J A B

private theorem eHomWhiskerLeft_projection
    (A : J ⥤ SSet.{0}) {B B' : J ⥤ SSet.{0}} (f : B ⟶ B') (j : J) :
    (letI := diagramSimplicialCategory J;
      eHomWhiskerLeft SSet A f ≫
        Enriched.FunctorCategory.enrichedHomπ SSet A B' j =
      Enriched.FunctorCategory.enrichedHomπ SSet A B j ≫
        (ihom (A.obj j)).map (f.app j)) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  dsimp [eHomWhiskerLeft]
  change (ρ_ _).inv ≫
      (Enriched.FunctorCategory.enrichedHom SSet A B ◁
        Enriched.FunctorCategory.homEquiv SSet f) ≫
      Enriched.FunctorCategory.enrichedComp SSet A B B' ≫
      Enriched.FunctorCategory.enrichedHomπ SSet A B' j = _
  simp only [Enriched.FunctorCategory.enrichedComp_π]
  rw [whiskerLeft_comp_tensorHom_assoc,
    Enriched.FunctorCategory.homEquiv_apply_π,
    rightUnitor_inv_comp_tensorHom_assoc]
  exact congrArg (Enriched.FunctorCategory.enrichedHomπ SSet A B j ≫ ·)
    (MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft
      SSet (A.obj j) (f.app j))

private theorem eHomWhiskerRight_projection
    {A A' : J ⥤ SSet.{0}} (f : A ⟶ A') (B : J ⥤ SSet.{0}) (j : J) :
    (letI := diagramSimplicialCategory J;
      eHomWhiskerRight SSet f B ≫
        Enriched.FunctorCategory.enrichedHomπ SSet A B j =
      Enriched.FunctorCategory.enrichedHomπ SSet A' B j ≫
        (MonoidalClosed.pre (f.app j)).app (B.obj j)) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  dsimp [eHomWhiskerRight]
  change (λ_ _).inv ≫
      (Enriched.FunctorCategory.homEquiv SSet f ▷
        Enriched.FunctorCategory.enrichedHom SSet A' B) ≫
      Enriched.FunctorCategory.enrichedComp SSet A A' B ≫
      Enriched.FunctorCategory.enrichedHomπ SSet A B j = _
  simp only [Enriched.FunctorCategory.enrichedComp_π]
  rw [whiskerRight_comp_tensorHom_assoc,
    Enriched.FunctorCategory.homEquiv_apply_π,
    leftUnitor_inv_comp_tensorHom_assoc]
  exact congrArg (Enriched.FunctorCategory.enrichedHomπ SSet A' B j ≫ ·)
    (MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight
      SSet (f.app j) (B.obj j))

private theorem nativeHom_equiv_symm_app
    (A B : J ⥤ SSet.{0}) (K : SSet.{0})
    (h : K ⟶ Enriched.FunctorCategory.enrichedHom SSet A B) (j : J) :
    ((MonoidalClosed.FunctorCategory.homEquiv
      (F₁ := A) (F₂ := (Functor.const J).obj K) (F₃ := B)).symm
      ((Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv h)).app j =
        MonoidalClosed.uncurry (h ≫ Enriched.FunctorCategory.enrichedHomπ SSet A B j) := by
  dsimp [MonoidalClosed.FunctorCategory.homEquiv, IsLimit.homEquiv]
  congr 1
  rw [Category.assoc]
  simp [Enriched.FunctorCategory.precompEnrichedHom,
    Enriched.FunctorCategory.precompEnrichedHom']

private theorem mappingEquiv_target_naturality
    (A : J ⥤ SSet.{0}) {B B' : J ⥤ SSet.{0}} (f : B ⟶ B')
    (K : SSet.{0})
    (h : K ⟶ Enriched.FunctorCategory.enrichedHom SSet A B) :
    mappingEquiv J A B' K (h ≫
      (letI := diagramSimplicialCategory J; eHomWhiskerLeft SSet A f)) =
      mappingEquiv J A B K h ≫ diagramMappingPostcomp A f := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  dsimp [mappingEquiv]
  have hpost : (diagramMappingTarget A).map f = diagramMappingPostcomp A f := rfl
  rw [← hpost]
  let q := (MonoidalClosed.FunctorCategory.homEquiv
    (F₁ := A) (F₂ := (Functor.const J).obj K) (F₃ := B)).symm
      ((Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv h)
  have hn := (diagramTensorMappingAdjunction A).homEquiv_naturality_right q f
  dsimp only [q] at hn
  calc
    _ = ((diagramTensorMappingAdjunction A).homEquiv K B') (q ≫ f) := by
      congr 1
      apply NatTrans.ext
      funext j
      calc
        _ = MonoidalClosed.uncurry ((h ≫ eHomWhiskerLeft SSet A f) ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A B' j) :=
          nativeHom_equiv_symm_app J A B' K (h ≫ eHomWhiskerLeft SSet A f) j
        _ = MonoidalClosed.uncurry ((h ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A B j) ≫
              (ihom (A.obj j)).map (f.app j)) := by
          simp only [Category.assoc, eHomWhiskerLeft_projection]
        _ = MonoidalClosed.uncurry (h ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A B j) ≫ f.app j :=
          MonoidalClosed.uncurry_natural_right _ _
        _ = (q ≫ f).app j := by
          rw [NatTrans.comp_app]
          exact congrArg (· ≫ f.app j) (nativeHom_equiv_symm_app J A B K h j).symm
    _ = _ := by simpa only [q] using hn

private theorem mappingEquiv_source_naturality
    {A A' : J ⥤ SSet.{0}} (f : A ⟶ A')
    (B : J ⥤ SSet.{0}) (K : SSet.{0})
    (h : K ⟶ Enriched.FunctorCategory.enrichedHom SSet A' B) :
    mappingEquiv J A B K (h ≫
      (letI := diagramSimplicialCategory J; eHomWhiskerRight SSet f B)) =
      mappingEquiv J A' B K h ≫ diagramMappingPrecomp f B := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  dsimp [mappingEquiv]
  let q := (MonoidalClosed.FunctorCategory.homEquiv
    (F₁ := A') (F₂ := (Functor.const J).obj K) (F₃ := B)).symm
      ((Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A' B).homEquiv h)
  have hn := (InjectiveKanDiagram.diagramParametrizedAdjunction J).homEquiv_naturality_one
    f q
  calc
    _ = (InjectiveKanDiagram.diagramParametrizedAdjunction J).homEquiv
        (((InjectiveKanDiagram.curriedDiagramTensor J).map f).app K ≫ q) := by
      congr 1
      apply NatTrans.ext
      funext j
      calc
        _ = MonoidalClosed.uncurry ((h ≫ eHomWhiskerRight SSet f B) ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A B j) :=
          nativeHom_equiv_symm_app J A B K (h ≫ eHomWhiskerRight SSet f B) j
        _ = MonoidalClosed.uncurry ((h ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A' B j) ≫
              (MonoidalClosed.pre (f.app j)).app (B.obj j)) := by
          simp only [Category.assoc, eHomWhiskerRight_projection]
        _ = (f.app j ▷ K) ≫ MonoidalClosed.uncurry
            (h ≫ Enriched.FunctorCategory.enrichedHomπ SSet A' B j) :=
          MonoidalClosed.uncurry_natural_left _ _
        _ = (((InjectiveKanDiagram.curriedDiagramTensor J).map f).app K ≫ q).app j := by
          rw [NatTrans.comp_app]
          change _ = (f.app j ▷ K) ≫ q.app j
          exact congrArg ((f.app j ▷ K) ≫ ·)
            (nativeHom_equiv_symm_app J A' B K h j).symm
    _ = _ := by simpa only [q] using hn

private theorem mappingIso_target_natural
    (A : J ⥤ SSet.{0}) {B B' : J ⥤ SSet.{0}} (f : B ⟶ B') :
    (letI := diagramSimplicialCategory J;
      eHomWhiskerLeft SSet A f ≫ (nativeMappingIso J A B').hom =
        (nativeMappingIso J A B).hom ≫ diagramMappingPostcomp A f) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  let m := eHomWhiskerLeft SSet A f
  have hK := mappingEquiv_naturality J A B' m
    (𝟙 (Enriched.FunctorCategory.enrichedHom SSet A B'))
  have hB := mappingEquiv_target_naturality J A f
    (Enriched.FunctorCategory.enrichedHom SSet A B)
    (𝟙 (Enriched.FunctorCategory.enrichedHom SSet A B))
  simpa only [nativeMappingIso, mappingIso, Category.id_comp, Category.comp_id] using
    hK.symm.trans hB

private theorem mappingIso_source_natural
    {A A' : J ⥤ SSet.{0}} (f : A ⟶ A') (B : J ⥤ SSet.{0}) :
    (letI := diagramSimplicialCategory J;
      eHomWhiskerRight SSet f B ≫ (nativeMappingIso J A B).hom =
        (nativeMappingIso J A' B).hom ≫ diagramMappingPrecomp f B) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  let m := eHomWhiskerRight SSet f B
  have hK := mappingEquiv_naturality J A B m
    (𝟙 (Enriched.FunctorCategory.enrichedHom SSet A B))
  have hA := mappingEquiv_source_naturality J f B
    (Enriched.FunctorCategory.enrichedHom SSet A' B)
    (𝟙 (Enriched.FunctorCategory.enrichedHom SSet A' B))
  simpa only [nativeMappingIso, mappingIso, Category.id_comp, Category.comp_id] using
    hK.symm.trans hA

/-- The chosen native simplicial Hom bifunctor is naturally isomorphic, in
both diagram variables, to the literal mapping-space bifunctor. -/
def homComparison :
    (letI := diagramSimplicialCategory J;
      SimplicialCategory.sHomFunctor (J ⥤ SSet.{0}) ≅
        InjectiveKanDiagram.diagramMappingSource J) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  let comp (A : (J ⥤ SSet.{0})ᵒᵖ) :
      (SimplicialCategory.sHomFunctor (J ⥤ SSet.{0})).obj A ≅
        (InjectiveKanDiagram.diagramMappingSource J).obj A :=
    NatIso.ofComponents (fun B => nativeMappingIso J A.unop B)
      (by intro B B' f; exact mappingIso_target_natural J A.unop f)
  refine NatIso.ofComponents comp (by
    intro A A' f
    apply NatTrans.ext
    funext B
    exact mappingIso_source_natural J f.unop B)

/-- Tensoring a diagram with the simplicial unit has the pointwise right
unitor as its canonical comparison. -/
def diagramTensorUnitIso (A : J ⥤ SSet.{0}) :
    (diagramTensor A).obj (𝟙_ SSet.{0}) ≅ A :=
  NatIso.ofComponents (fun j ↦ ρ_ (A.obj j)) (by
    intro j j' f
    exact rightUnitor_naturality (A.map f))

/-- The Hom comparison sends an ordinary natural transformation to its
canonical zero-simplex, using the specified tensor-unit comparison. -/
theorem homComparison_ordinary {A B : J ⥤ SSet.{0}} (f : A ⟶ B) :
    (letI := diagramSimplicialCategory J;
      eHomEquiv SSet f ≫ ((homComparison J).hom.app (op A)).app B =
        (diagramTensorMappingAdjunction A).homEquiv (𝟙_ SSet.{0}) B
          ((diagramTensorUnitIso J A).hom ≫ f)) := by
  letI : SimplicialCategory (J ⥤ SSet.{0}) := diagramSimplicialCategory J
  let E := Enriched.FunctorCategory.enrichedHom SSet A B
  have hn := mappingEquiv_naturality J A B (eHomEquiv SSet f) (𝟙 E)
  have hq : (MonoidalClosed.FunctorCategory.homEquiv
      (F₁ := A) (F₂ := (Functor.const J).obj (𝟙_ SSet.{0})) (F₃ := B)).symm
        ((Enriched.FunctorCategory.isLimitConeFunctorEnrichedHom SSet A B).homEquiv
          (eHomEquiv SSet f)) = (diagramTensorUnitIso J A).hom ≫ f := by
    apply NatTrans.ext
    funext j
    calc
      _ = MonoidalClosed.uncurry ((eHomEquiv SSet f) ≫
          Enriched.FunctorCategory.enrichedHomπ SSet A B j) :=
        nativeHom_equiv_symm_app J A B (𝟙_ SSet.{0}) (eHomEquiv SSet f) j
      _ = MonoidalClosed.uncurry (MonoidalClosed.curry' (f.app j)) := by
        change MonoidalClosed.uncurry
          ((Enriched.FunctorCategory.homEquiv SSet f) ≫
            Enriched.FunctorCategory.enrichedHomπ SSet A B j) = _
        rw [Enriched.FunctorCategory.homEquiv_apply_π]
        rfl
      _ = (ρ_ (A.obj j)).hom ≫ f.app j := by
        simp [MonoidalClosed.curry', MonoidalClosed.uncurry_curry]
      _ = ((diagramTensorUnitIso J A).hom ≫ f).app j := rfl
  simpa only [homComparison, nativeMappingIso, mappingIso, Category.id_comp,
    Category.comp_id] using hn.symm.trans (congrArg
      ((diagramTensorMappingAdjunction A).homEquiv (𝟙_ SSet.{0}) B) hq)

end

end DaggerModels.PartII.DiagramSimplicialEnrichment
