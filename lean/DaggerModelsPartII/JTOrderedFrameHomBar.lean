import DaggerModelsPartII.BoundaryNecklaceComma
import DaggerModelsPartII.TotalElementsWeakComparison
import NativeSimplicialReplacementReindex
import NativeSimplicialReplacementWeightsChange

/-! The full rigidified ordered Hom evaluator for a cosimplicial frame. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial EnrichedCategory HomotopicalAlgebra DaggerModels
open scoped SSet.modelCategoryQuillen
open DaggerModels.OrdinaryRigidification
open DaggerModels.OrdinaryRigidification.RigidificationVertices
open DaggerModels.OriginalOrdinaryMovingHomColimits
open DaggerNativeSimplicialReplacement DaggerNativeSimplicialReplacementReindex
open DaggerNativeSimplicialReplacementWeightsChange

namespace DaggerModels.PartII.JTOrderedFrameHomBar

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

private def rigidified : Under B ⥤ SimplicialCat.{0, 0} :=
  Under.forget B ⋙ rigidification

private def first (U : Under B) : (rigidified.obj U).Obj :=
  vertexEquiv U.right (BoundaryNecklaceComma.first U)

private def last (U : Under B) : (rigidified.obj U).Obj :=
  vertexEquiv U.right (BoundaryNecklaceComma.last U)

private theorem first_map {U V : Under B} (f : U ⟶ V) :
    (rigidified.map f).obj (first U) = first V := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (vertexEquiv V.right)
  rw [BoundaryNecklaceComma.first_eq, BoundaryNecklaceComma.first_eq]
  exact congrFun (NatTrans.congr_app (Under.w f) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₀)

private theorem last_map {U V : Under B} (f : U ⟶ V) :
    (rigidified.map f).obj (last U) = last V := by
  refine (vertexEquiv_naturality _ _).trans ?_
  apply congrArg (vertexEquiv V.right)
  rw [BoundaryNecklaceComma.last_eq, BoundaryNecklaceComma.last_eq]
  exact congrFun (NatTrans.congr_app (Under.w f) (op ⦋0⦌))
    (SSet.yonedaEquiv SSet.boundary₁.ι₁)

/-- Rigidify a simplicial set and take the entire Hom between its two ordered vertices. -/
def orderedHom : Under B ⥤ SSet.{0} :=
  { obj U := (rigidified.obj U).enriched.Hom (first U) (last U)
    map f := castMap (rigidified.map f) _ _ _ _ (first_map f) (last_map f)
    map_id U := by
      rw [castMap_congr (rigidified.map_id U) _ _ _ _ (first_map _) (last_map _) rfl rfl]
      simp [castMap]
    map_comp f g := by
      exact (castMap_congr (rigidified.map_comp f g) _ _ _ _ (first_map _) (last_map _)
        ((congrArg (rigidified.map g).obj (first_map f)).trans (first_map g))
        ((congrArg (rigidified.map g).obj (last_map f)).trans (last_map g))).trans
        (castMap_comp (rigidified.map f) (rigidified.map g) _ _ _ _ _ _
          (first_map f) (last_map f) (first_map g) (last_map g)) }

/-- The action on the entire Hom is induced by the actual boundary map. -/
theorem orderedHom_map {U V : Under B} (f : U ⟶ V) :
    orderedHom.map f =
      castMap (rigidification.map f.right)
        (first U) (last U) (first V) (last V) (first_map f) (last_map f) := rfl

variable (F : SimplexCategory ⥤ Under B) (U : Under B)

/-- All simplices of the simplicial set of frame maps into the specified target. -/
abbrev Index := (EndpointMappingFiber.mapping (Z := U) F).Elementsᵒᵖ

/-- The actual cosimplicial degree of an indexed full map into the target. -/
def degree : Index F U ⥤ SimplexCategory :=
  (CategoryOfElements.π (EndpointMappingFiber.mapping (Z := U) F)).op ⋙
    unopUnop SimplexCategory

/-- The entire ordered Hom of the frame in the degree of each map. -/
def weights : Index F U ⥤ SSet.{0} := degree F U ⋙ F ⋙ orderedHom

/-- Apply the original map into the target as a map of ordered Homs. -/
def cocone : weights F U ⟶ (Functor.const (Index F U)).obj (orderedHom.obj U) where
  app i := orderedHom.map i.unop.2
  naturality {i j} f := by
    change orderedHom.map (F.map f.unop.1.unop) ≫ orderedHom.map j.unop.2 =
      orderedHom.map i.unop.2 ≫ 𝟙 _
    rw [Category.comp_id, ← orderedHom.map_comp]
    exact congrArg orderedHom.map f.unop.2

/-- The weighted replacement uses every ordered Hom simplex in every chain. -/
def bar : SSet.{0} := DaggerBisimplicialDiagonal.diag (replacement (weights F U))

/-- The exact diagonal evaluation on the whole ordered-Hom bar. -/
def evaluator : bar F U ⟶ orderedHom.obj U :=
  diagonalAugmentation (weights F U) (cocone F U)

variable {F} {G : SimplexCategory ⥤ Under B} (θ : F ⟶ G)

/-- Reindex by precomposition with the actual frame map. -/
def restrict : Index G U ⥤ Index F U :=
  (NatTrans.mapElements (EndpointMappingFiber.precomp (Z := U) θ)).op

theorem restrict_degree : restrict U θ ⋙ degree F U = degree G U := rfl

/-- Over the original source of the restriction, apply the frame map to every weight. -/
def change : restrict U θ ⋙ weights F U ⟶ weights G U :=
  Functor.whiskerLeft (degree G U) (Functor.whiskerRight θ orderedHom)

theorem cocone_square :
    change U θ ≫ cocone G U = Functor.whiskerLeft (restrict U θ) (cocone F U) := by
  apply NatTrans.ext
  funext i
  exact (orderedHom.map_comp (θ.app ((degree G U).obj i)) i.unop.2).symm

/-- The first comparison keeps the ordered Hom weight and changes the index. -/
def toRestrictedBar :
    DaggerBisimplicialDiagonal.diag
      (replacement (restrict U θ ⋙ weights F U)) ⟶ bar F U :=
  diagonalReindex (restrict U θ) (weights F U)

/-- The second comparison keeps the index and applies the frame map to the weight. -/
def toFrameBar :
    DaggerBisimplicialDiagonal.diag
      (replacement (restrict U θ ⋙ weights F U)) ⟶ bar G U :=
  diagonalChange (change U θ)

/-- Both whole-bar composites evaluate every full map by the same composition. -/
theorem evaluator_square :
    toRestrictedBar U θ ≫ evaluator F U = toFrameBar U θ ≫ evaluator G U := by
  unfold toRestrictedBar toFrameBar evaluator
  rw [DaggerNativeSimplicialReplacementReindex.augmentation_square,
    DaggerNativeSimplicialReplacementWeightsChange.augmentation_square, cocone_square]


open DaggerSSetGluing DaggerOriginalProductGadget

/-- With contractible weights and weak restriction, the two exact evaluations
are weak simultaneously. -/
theorem evaluator_weak_iff
    (hrestrict : WeakEquivalence (EndpointMappingFiber.precomp (Z := U) θ))
    (hF : ∀ k, GW (pointMap ((F ⋙ orderedHom).obj k)))
    (hG : ∀ k, GW (pointMap ((G ⋙ orderedHom).obj k))) :
    WeakEquivalence (evaluator F U) ↔ WeakEquivalence (evaluator G U) := by
  haveI : WeakEquivalence (toRestrictedBar U θ) :=
    (weakEquivalence_iff_GW _).mpr (diagonalReindex_GW _ _
      ((weakEquivalence_iff_GW _).mp
        ((TotalElementsWeakComparison.elementsOpposite_weak_iff _).mpr hrestrict))
      (fun i ↦ hF ((degree F U).obj i)))
  haveI : WeakEquivalence (toFrameBar U θ) :=
    (weakEquivalence_iff_GW _).mpr (diagonalChange_GW _
      (diagonalProjection_GW _ fun i ↦ hF ((degree G U).obj i))
      (diagonalProjection_GW _ fun i ↦ hG ((degree G U).obj i)))
  calc
    WeakEquivalence (evaluator F U) ↔ WeakEquivalence (toRestrictedBar U θ ≫ evaluator F U) :=
      (weakEquivalence_precomp_iff _ _).symm
    _ ↔ WeakEquivalence (toFrameBar U θ ≫ evaluator G U) := by rw [evaluator_square]
    _ ↔ WeakEquivalence (evaluator G U) := weakEquivalence_precomp_iff _ _

end

end DaggerModels.PartII.JTOrderedFrameHomBar
