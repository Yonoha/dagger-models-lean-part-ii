import DaggerModelsPartII.OrderedSimplexEndpointFiber
import DaggerModelsPartII.ReversalDiscreteFreeColimits
import DaggerModelsPartII.JTNativeRowCoefficientOperators
import TopCatModelCategory.SSet.Boundary

/-! The three genuine free edges of a two-simplex boundary. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory
open DaggerModels

namespace DaggerModels.PartII.JTTriangleBoundaryLabel

open ReversalDiscreteFreeColimits
open OrderedSimplexEndpointFiber
open SegalLocalizers
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev F := discreteFree.{0}
private abbrev Rows (W : Source) :=
  JTRealizationDiagonal.ordinaryCurry.obj (JTReversalInput.ordinaryInput.obj W)

private instance discreteFree_preservesColimitOfShape (J : Type) [Category J] :
    PreservesColimitsOfShape J F := by
  letI : PreservesColimitsOfShape J freeDagger.{0} :=
    freeDaggerAdjunction.leftAdjoint_preservesColimits.preservesColimitsOfShape
  letI : PreservesColimitsOfShape J discreteDagger.{0} := by
    letI : PreservesColimitsOfShape J DaggerSSet.toPresheaf.{0} :=
      let h := daggerSSetEquivalencePresheaf.toAdjunction.leftAdjoint_preservesColimits
      h.preservesColimitsOfShape
    letI : PreservesColimitsOfShape J (SimplicialObject.const (Type 0)) :=
      (CategoryTheory.Limits.preservesColimits_const
        (D := SimplexCategoryᵒᵖ)).preservesColimitsOfShape
    letI : PreservesColimitsOfShape J
        ((Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
          (SimplicialObject.const (Type 0))) := inferInstance
    change PreservesColimitsOfShape J
      (DaggerSSet.toPresheaf.{0} ⋙
        (Functor.whiskeringRight ReverseSimplexᵒᵖ (Type 0) SSet.{0}).obj
          (SimplicialObject.const (Type 0)))
    infer_instance
  change PreservesColimitsOfShape J
    (freeDagger.{0} ⋙ discreteDagger.{0})
  infer_instance

private def boundaryFreeIsColimit :
    IsColimit (F.mapCocone
      ((SSet.boundary.multicoequalizerDiagram 2).multicofork.toLinearOrder.map
        SSet.Subcomplex.toPresheafFunctor)) := by
  letI : PreservesColimitsOfSize.{0, 0} F :=
    ⟨fun {J} _ ↦ discreteFree_preservesColimitOfShape J⟩
  exact isColimitOfPreserves F (SSet.boundary.isColimit 2)

private def tensorBy (k : SimplexCategory) : Source ⥤ Source :=
  (Functor.whiskeringRight ReverseSimplexᵒᵖ SSet.{0} SSet.{0}).obj
    (tensorRight (std.obj k))

private def boundaryTensorIsColimit (k : SimplexCategory) :
    IsColimit ((tensorBy k).mapCocone
      (F.mapCocone
        ((SSet.boundary.multicoequalizerDiagram 2).multicofork.toLinearOrder.map
          SSet.Subcomplex.toPresheafFunctor))) := by
  letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
  letI : PreservesColimitsOfSize.{0, 0} (tensorRight (std.obj k)) :=
    ⟨fun {J} _ ↦ by
      letI : PreservesColimitsOfShape J (tensorLeft (std.obj k)) := inferInstance
      exact preservesColimitsOfShape_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (std.obj k))⟩
  letI : PreservesColimitsOfSize.{0, 0} (tensorBy k) :=
    ⟨fun {J} _ ↦ CategoryTheory.whiskeringRight_preservesColimitsOfShape _⟩
  exact isColimitOfPreserves (tensorBy k) boundaryFreeIsColimit

private abbrev Face (j : Fin 3) : SSet.{0} :=
  (SSet.stdSimplex.face {j}ᶜ : SSet.{0})

private def faceLabel (W : Source) (k : SimplexCategory) (j : Fin 3)
    (e : std.obj k ⟶ row W ⦋1⦌) :
    (tensorBy k).obj (F.obj (Face j)) ⟶ W :=
  Functor.whiskerRight (F.map (SSet.stdSimplex.faceSingletonComplIso j).inv)
    (tensorRight (std.obj k)) ≫
    SSet.yonedaEquiv
      (e ≫ (freeSimplexRowIso W 1).inv)

private abbrev FacePair (j l : Fin 3) : SSet.{0} :=
  (SSet.stdSimplex.face {j, l}ᶜ : SSet.{0})

private def facePairMapLeft (j l : Fin 3) : FacePair j l ⟶ Face j :=
  SSet.Subcomplex.homOfLE (show SSet.stdSimplex.face {j, l}ᶜ ≤
    SSet.stdSimplex.face {j}ᶜ by
      simp [SSet.stdSimplex.face_le_face_iff])

private def facePairMapRight (j l : Fin 3) : FacePair j l ⟶ Face l :=
  SSet.Subcomplex.homOfLE (show SSet.stdSimplex.face {j, l}ᶜ ≤
    SSet.stdSimplex.face {l}ᶜ by
      simp [SSet.stdSimplex.face_le_face_iff])

/-- Three row-one labels with their literal pairwise vertex compatibilities. -/
structure BoundaryData (W : Source) (k : SimplexCategory) where
  edge : Fin 3 → (std.obj k ⟶ row W ⦋1⦌)
  compatible : ∀ (j l : Fin 3) (_ : j < l),
    Functor.whiskerRight (F.map (facePairMapLeft j l)) (tensorRight (std.obj k)) ≫
      faceLabel W k j (edge j) =
    Functor.whiskerRight (F.map (facePairMapRight j l)) (tensorRight (std.obj k)) ≫
      faceLabel W k l (edge l)

private def boundaryIndex (k : SimplexCategory) :
    MultispanIndex (.ofLinearOrder (Fin 3)) Source :=
  ((((SSet.boundary.multicoequalizerDiagram 2).multispanIndex.toLinearOrder).map
    SSet.Subcomplex.toPresheafFunctor).map F).map (tensorBy k)

private def boundaryCocone {W : Source} {k : SimplexCategory}
    (D : BoundaryData W k) : Multicofork (boundaryIndex k) :=
  Multicofork.ofπ _ W (fun j ↦ faceLabel W k j (D.edge j))
    (fun p ↦ D.compatible p.1.1 p.1.2 p.2)

private def boundaryIndexIsColimit (k : SimplexCategory) :
    IsColimit
      ((((SSet.boundary.multicoequalizerDiagram 2).multicofork.toLinearOrder.map
        SSet.Subcomplex.toPresheafFunctor).map F).map (tensorBy k)) := by
  letI : PreservesColimitsOfSize.{0, 0} (tensorBy k) := by
    letI : BraidedCategory SSet.{0} := .ofCartesianMonoidalCategory
    letI : PreservesColimitsOfSize.{0, 0} (tensorRight (std.obj k)) :=
      ⟨fun {J} _ ↦ by
        letI : PreservesColimitsOfShape J (tensorLeft (std.obj k)) := inferInstance
        exact preservesColimitsOfShape_of_natIso
          (BraidedCategory.tensorLeftIsoTensorRight (std.obj k))⟩
    exact ⟨fun {J} _ ↦ CategoryTheory.whiskeringRight_preservesColimitsOfShape _⟩
  have hfree : IsColimit
      ((SSet.boundary.multicoequalizerDiagram 2).multicofork.toLinearOrder.map
        SSet.Subcomplex.toPresheafFunctor |>.map F) :=
    (Multicofork.isColimitMapEquiv _ F) boundaryFreeIsColimit
  exact (Multicofork.isColimitMapEquiv _ (tensorBy k))
    (isColimitOfPreserves (tensorBy k) hfree)

private def boundaryNat {W : Source} {k : SimplexCategory}
    (D : BoundaryData W k) :
    (tensorBy k).obj (F.obj (SSet.boundary 2).toSSet) ⟶ W :=
  (boundaryIndexIsColimit k).desc (boundaryCocone D)

/-- Restriction of a boundary label to its `j`th free edge. -/
def facePrecomp (W : Source) (j : Fin 3) :
    diagramMappingSpace (F.obj (SSet.boundary 2).toSSet) W ⟶
      diagramMappingSpace (F.obj (Δ[1] : SSet.{0})) W :=
  diagramMappingPrecomp (F.map (SSet.boundary.ι j)) W

/-- The actual boundary coefficient assembled from its three compatible row edges. -/
def boundaryLabel {W : Source} {k : SimplexCategory} (D : BoundaryData W k) :
    std.obj k ⟶ diagramMappingSpace (F.obj (SSet.boundary 2).toSSet) W :=
  SSet.yonedaEquiv.symm (boundaryNat D)

private theorem boundaryNat_face {W : Source} {k : SimplexCategory}
    (D : BoundaryData W k) (j : Fin 3) :
    Functor.whiskerRight (F.map (SSet.boundary.faceι j))
      (tensorRight (std.obj k)) ≫ boundaryNat D =
    faceLabel W k j (D.edge j) := by
  exact (boundaryIndexIsColimit k).fac (boundaryCocone D) (.right j)

private theorem boundaryNat_edge {W : Source} {k : SimplexCategory}
    (D : BoundaryData W k) (j : Fin 3) :
    Functor.whiskerRight (F.map (SSet.boundary.ι j))
      (tensorRight (std.obj k)) ≫ boundaryNat D =
    SSet.yonedaEquiv (D.edge j ≫ (freeSimplexRowIso W 1).inv) := by
  have hι : SSet.boundary.ι j =
      (SSet.stdSimplex.faceSingletonComplIso j).hom ≫ SSet.boundary.faceι j := by
    rw [← cancel_epi (SSet.stdSimplex.faceSingletonComplIso j).inv]
    simp [SSet.boundary.faceSingletonComplIso_inv_ι]
  rw [hι, F.map_comp, Functor.whiskerRight_comp, Category.assoc,
    boundaryNat_face]
  simp only [faceLabel]
  rw [← Category.assoc, ← Functor.whiskerRight_comp, ← F.map_comp,
    Iso.hom_inv_id, F.map_id]
  simp

/-- Each of the three literal boundary facets recovers its input row edge. -/
theorem boundaryLabel_face {W : Source} {k : SimplexCategory}
    (D : BoundaryData W k) (j : Fin 3) :
    boundaryLabel D ≫ facePrecomp W j ≫ (freeSimplexRowIso W 1).hom =
      D.edge j := by
  have h : boundaryLabel D ≫ facePrecomp W j =
      D.edge j ≫ (freeSimplexRowIso W 1).inv := by
    apply SSet.yonedaEquiv.injective
    simpa [boundaryLabel, facePrecomp, diagramMappingPrecomp,
      SSet.yonedaEquiv_comp] using boundaryNat_edge D j
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Restricting a full triangle first to its boundary and then to a face
is its ordinary coface restriction. -/
theorem full_facePrecomp (W : Source) (j : Fin 3) :
    diagramMappingPrecomp (F.map (SSet.boundary 2).ι) W ≫ facePrecomp W j =
      diagramMappingPrecomp (F.map (SSet.stdSimplex.δ j)) W := by
  simp only [facePrecomp, ← diagramMappingPrecomp_comp,
    ← F.map_comp, SSet.boundary.ι_ι]

private theorem boundaryNat_ext {W : Source} {k : SimplexCategory}
    {f g : (tensorBy k).obj (F.obj (SSet.boundary 2).toSSet) ⟶ W}
    (h : ∀ j : Fin 3,
      Functor.whiskerRight (F.map (SSet.boundary.faceι j))
        (tensorRight (std.obj k)) ≫ f =
      Functor.whiskerRight (F.map (SSet.boundary.faceι j))
        (tensorRight (std.obj k)) ≫ g) : f = g := by
  apply Multicofork.IsColimit.hom_ext (boundaryIndexIsColimit k)
  exact h

private theorem yoneda_precomp {A B W : Source} {k : SimplexCategory}
    (f : A ⟶ B) (b : std.obj k ⟶ diagramMappingSpace B W) :
    Functor.whiskerRight f (tensorRight (std.obj k)) ≫ SSet.yonedaEquiv b =
      SSet.yonedaEquiv (b ≫ diagramMappingPrecomp f W) := by
  rfl

private theorem row_vertex_restrict (W : Source) {k : SimplexCategory}
    (a : ⦋0⦌ ⟶ ⦋1⦌) (e : std.obj k ⟶ row W ⦋1⦌) :
    e ≫ (freeSimplexRowIso W 1).inv ≫
      diagramMappingPrecomp (F.map (std.map a)) W =
    e ≫ (Rows W).map a.op ≫ (freeSimplexRowIso W 0).inv := by
  have h := JTNativeRowCoefficientOperators.freeSimplexRowIso_natural W a
  have h' := congrArg (fun f ↦ (freeSimplexRowIso W 1).inv ≫ f ≫
    (freeSimplexRowIso W 0).inv) h
  have h'' : (freeSimplexRowIso W 1).inv ≫
      diagramMappingPrecomp (F.map (std.map a)) W =
    (Rows W).map a.op ≫ (freeSimplexRowIso W 0).inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h'
  simpa only [Category.assoc] using
    congrArg (fun f ↦ e ≫ f) h''

private theorem faceLabel_pair_left (W : Source) {k : SimplexCategory}
    (j l : Fin 3) (hjl : j < l) (e : std.obj k ⟶ row W ⦋1⦌) :
    Functor.whiskerRight (F.map (SSet.stdSimplex.facePairComplIso j l hjl).hom)
      (tensorRight (std.obj k)) ≫
      Functor.whiskerRight (F.map (facePairMapLeft j l))
        (tensorRight (std.obj k)) ≫ faceLabel W k j e =
    SSet.yonedaEquiv
      (e ≫ (Rows W).map
        (SimplexCategory.δ (l.pred (Fin.ne_zero_of_lt hjl))).op ≫
          (freeSimplexRowIso W 0).inv) := by
  have hmap : (SSet.stdSimplex.facePairComplIso j l hjl).hom ≫
      facePairMapLeft j l ≫ (SSet.stdSimplex.faceSingletonComplIso j).inv =
      SSet.stdSimplex.δ (l.pred (Fin.ne_zero_of_lt hjl)) := by
    rw [show facePairMapLeft j l ≫
      (SSet.stdSimplex.faceSingletonComplIso j).inv =
      (SSet.stdSimplex.facePairComplIso j l hjl).inv ≫
        SSet.stdSimplex.δ (l.pred (Fin.ne_zero_of_lt hjl)) from by
          simpa only [facePairMapLeft] using
            SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_pred j l hjl]
    simp
  simp only [faceLabel]
  rw [← Category.assoc, ← Functor.whiskerRight_comp,
    ← Category.assoc, ← Functor.whiskerRight_comp, ← F.map_comp,
    ← F.map_comp, Category.assoc, hmap]
  change SSet.yonedaEquiv
      (e ≫ (freeSimplexRowIso W 1).inv ≫
        diagramMappingPrecomp
          (F.map (std.map (SimplexCategory.δ
            (l.pred (Fin.ne_zero_of_lt hjl))))) W) = _
  rw [row_vertex_restrict]
  rfl

private theorem faceLabel_pair_right (W : Source) {k : SimplexCategory}
    (j l : Fin 3) (hjl : j < l) (e : std.obj k ⟶ row W ⦋1⦌) :
    Functor.whiskerRight (F.map (SSet.stdSimplex.facePairComplIso j l hjl).hom)
      (tensorRight (std.obj k)) ≫
      Functor.whiskerRight (F.map (facePairMapRight j l))
        (tensorRight (std.obj k)) ≫ faceLabel W k l e =
    SSet.yonedaEquiv
      (e ≫ (Rows W).map
        (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjl))).op ≫
          (freeSimplexRowIso W 0).inv) := by
  have hmap : (SSet.stdSimplex.facePairComplIso j l hjl).hom ≫
      facePairMapRight j l ≫ (SSet.stdSimplex.faceSingletonComplIso l).inv =
      SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjl)) := by
    rw [show facePairMapRight j l ≫
      (SSet.stdSimplex.faceSingletonComplIso l).inv =
      (SSet.stdSimplex.facePairComplIso j l hjl).inv ≫
        SSet.stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjl)) from by
          simpa only [facePairMapRight] using
            SSet.stdSimplex.homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_δ_castPred
              j l hjl]
    simp
  simp only [faceLabel]
  rw [← Category.assoc, ← Functor.whiskerRight_comp,
    ← Category.assoc, ← Functor.whiskerRight_comp, ← F.map_comp,
    ← F.map_comp, Category.assoc, hmap]
  change SSet.yonedaEquiv
      (e ≫ (freeSimplexRowIso W 1).inv ≫
        diagramMappingPrecomp
          (F.map (std.map (SimplexCategory.δ
            (j.castPred (Fin.ne_last_of_lt hjl))))) W) = _
  rw [row_vertex_restrict]
  rfl

/-- Pairwise ordinary vertex equations suffice for the literal boundary gluing. -/
def BoundaryData.ofEndpoints (W : Source) (k : SimplexCategory)
    (edge : Fin 3 → (std.obj k ⟶ row W ⦋1⦌))
    (h : ∀ (j l : Fin 3) (hjl : j < l),
      edge j ≫ (Rows W).map
        (SimplexCategory.δ (l.pred (Fin.ne_zero_of_lt hjl))).op =
      edge l ≫ (Rows W).map
        (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjl))).op) :
    BoundaryData W k where
  edge := edge
  compatible := by
    intro j l hjl
    let q := Functor.whiskerRight
      (F.map (SSet.stdSimplex.facePairComplIso j l hjl).hom)
        (tensorRight (std.obj k))
    haveI : Epi q := inferInstance
    apply (cancel_epi q).mp
    rw [faceLabel_pair_left W j l hjl (edge j),
      faceLabel_pair_right W j l hjl (edge l)]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ SSet.yonedaEquiv
        (f ≫ (freeSimplexRowIso W 0).inv)) (h j l hjl)

/-- A horizontal boundary coefficient is determined by its three edge maps. -/
theorem boundaryLabel_ext {W : Source} {k : SimplexCategory}
    {b c : std.obj k ⟶ diagramMappingSpace (F.obj (SSet.boundary 2).toSSet) W}
    (h : ∀ j : Fin 3, b ≫ facePrecomp W j = c ≫ facePrecomp W j) :
    b = c := by
  apply SSet.yonedaEquiv.injective
  apply boundaryNat_ext
  intro j
  rw [yoneda_precomp, yoneda_precomp]
  congr 1
  have hj := congrArg
    (fun q ↦ q ≫ diagramMappingPrecomp
      (F.map (SSet.stdSimplex.faceSingletonComplIso j).inv) W) (h j)
  simpa only [facePrecomp, Category.assoc, ← diagramMappingPrecomp_comp,
    ← F.map_comp, SSet.boundary.faceSingletonComplIso_inv_ι] using hj

/-- Restriction to the three free edges detects a boundary map from any
simplicial set, including a full support subcomplex. -/
theorem boundaryLabel_ext_general {W : Source} {X : SSet.{0}}
    {f g : X ⟶ diagramMappingSpace (F.obj (SSet.boundary 2).toSSet) W}
    (h : ∀ j : Fin 3, f ≫ facePrecomp W j = g ≫ facePrecomp W j) :
    f = g := by
  apply NatTrans.ext
  funext n
  cases n with
  | op n =>
  funext x
  let sx : std.obj n ⟶ X := SSet.yonedaEquiv.symm x
  have hx : sx ≫ f = sx ≫ g := by
    apply boundaryLabel_ext
    intro j
    simpa only [Category.assoc] using
      congrArg (fun q ↦ sx ≫ q) (h j)
  have hy := congrArg SSet.yonedaEquiv hx
  have hsx : SSet.yonedaEquiv sx = x := Equiv.apply_symm_apply _ _
  simpa only [SSet.yonedaEquiv_comp, hsx] using hy

/-- The assembled boundary is natural when its three row edges are transported. -/
theorem boundaryLabel_natural {W : Source} {l k : SimplexCategory}
    (D : BoundaryData W k) (E : BoundaryData W l) (u : l ⟶ k)
    (h : ∀ j : Fin 3, E.edge j = std.map u ≫ D.edge j) :
    boundaryLabel E = std.map u ≫ boundaryLabel D := by
  apply boundaryLabel_ext
  intro j
  apply (cancel_mono (freeSimplexRowIso W 1).hom).mp
  calc
    (boundaryLabel E ≫ facePrecomp W j) ≫ (freeSimplexRowIso W 1).hom =
        E.edge j := by simpa only [Category.assoc] using boundaryLabel_face E j
    _ = std.map u ≫ D.edge j := h j
    _ = ((std.map u ≫ boundaryLabel D) ≫ facePrecomp W j) ≫
          (freeSimplexRowIso W 1).hom := by
            simpa only [Category.assoc] using
              congrArg (fun f ↦ std.map u ≫ f) (boundaryLabel_face D j).symm

end

end DaggerModels.PartII.JTTriangleBoundaryLabel
