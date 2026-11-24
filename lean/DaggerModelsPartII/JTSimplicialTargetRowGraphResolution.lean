import DaggerModelsPartII.JTRowGraphFaceResolution

/-! All actual simplices of a fixed raw target, with the exact coefficient
graphs over their raw image. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTSimplicialTargetRowGraphResolution

open OrdinaryJTRealization JTRowGraphResolution JTRowGraphFiber

noncomputable section

private abbrev std := SSet.stdSimplex.{0}

variable {W : BiPresheaf} {X : SSet.{0}} (q : X ⟶ realization.obj W)

/-- The actual raw value of a simplex of the native target. -/
abbrev value (P : X.Elements) : std.obj P.1.unop ⟶ realization.obj W :=
  SSet.yonedaEquiv.symm P.2 ≫ q

/-- Compose the literal target simplex with its actual horizontal operator. -/
theorem value_map {P Q : X.Elements} (a : P ⟶ Q) :
    std.map a.val.unop ≫ value q P = value q Q := by
  have h : std.map a.val.unop ≫ SSet.yonedaEquiv.symm P.2 = SSet.yonedaEquiv.symm Q.2 := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_map_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact a.property
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ q) h)

private def restrictAt {P Q : X.Elements} (a : P ⟶ Q) :
    Fiber (value q P) ⥤ Fiber (value q Q) :=
  (fixed (value q Q)).lift ((fixed (value q P)).ι ⋙ restrict W a.val.unop) (by
    intro G
    change (restrictGraph a.val.unop G.obj).value = value q Q
    rw [restrictGraph_value, G.property, value_map])

private theorem inclusion_cancel {D E : Type} [SmallCategory D] [SmallCategory E]
    (P : ObjectProperty E) {F G : D ⥤ P.FullSubcategory}
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  let e (x : D) : F.obj x = G.obj x :=
    ObjectProperty.FullSubcategory.ext (congrArg (fun K : D ⥤ E ↦ K.obj x) h)
  refine CategoryTheory.Functor.ext e ?_
  intro U V f
  apply P.ι.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

private theorem restrictAt_id (P : X.Elements) : restrictAt q (𝟙 P) = 𝟭 (Fiber (value q P)) := by
  apply inclusion_cancel
  change (fixed (value q P)).ι ⋙ restrict W (𝟙 P.1.unop) =
    (𝟭 (Fiber (value q P))) ⋙ (fixed (value q P)).ι
  rw [restrict_id, Functor.comp_id, Functor.id_comp]

private theorem restrictAt_comp {P Q R : X.Elements} (a : P ⟶ Q) (b : Q ⟶ R) :
    restrictAt q (a ≫ b) = restrictAt q a ⋙ restrictAt q b := by
  apply inclusion_cancel
  change (fixed (value q P)).ι ⋙ restrict W (b.val.unop ≫ a.val.unop) =
    ((fixed (value q P)).ι ⋙ restrict W a.val.unop) ⋙ restrict W b.val.unop
  rw [restrict_comp, Functor.assoc]

/-- Coefficient graphs of every target simplex and every exact raw horizontal restriction. -/
def diagram : X.Elements ⥤ Cat.{0, 0} where
  obj P := Cat.of (Fiber (value q P))ᵒᵖ
  map a := (restrictAt q a).op.toCatHom
  map_id P := by
    apply Cat.Hom.ext
    change (restrictAt q (𝟙 P)).op = 𝟭 _
    rw [restrictAt_id]
    rfl
  map_comp a b := by
    apply Cat.Hom.ext
    change (restrictAt q (a ≫ b)).op = (restrictAt q a).op ⋙ (restrictAt q b).op
    rw [restrictAt_comp]
    rfl

abbrev Resolution := Grothendieck (diagram q)

private theorem elements_point_GW (hX : GW (pointMap X)) : GW (pointMap (nerve X.Elements)) := by
  apply (SynchronizedSimplicialParameters.point_op_iff _).mp
  let a := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  letI : WeakEquivalence a := SimplicialResolutionFunctor.augmentation_weak X
  letI : WeakEquivalence e := SimplicialResolutionFunctor.elementsProjection_weak X
  letI : WeakEquivalence (pointMap X) := (weakEquivalence_iff_GW _).mpr hX
  apply (weakEquivalence_iff_GW _).mp
  change WeakEquivalence (pointMap (nerve X.Elementsᵒᵖ))
  apply (weakEquivalence_precomp_iff e _).mp
  rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (a ≫ pointMap X)]
  infer_instance

/-- Use just the vertices of the coefficient used by the entire graph. -/
def supportedObj (P : Resolution q) : Resolution q :=
  ⟨P.base, op ((supportAt (value q P.base)).obj P.fiber.unop)⟩

private def supportedMap {P Q : Resolution q} (f : P ⟶ Q) :
    supportedObj q P ⟶ supportedObj q Q :=
  ⟨f.base, Quiver.Hom.op ⟨JTRowGraphHorizontalSupport.supportedArrow f.base.val.unop
    f.fiber.unop.hom⟩⟩

/-- Over the same horizontal operator, a map into a supported graph is uniquely determined. -/
theorem supported_ext {P : Resolution q} (Q : Resolution q)
    {f g : P ⟶ supportedObj q Q} (h : f.base = g.base) : f = g := by
  apply Grothendieck.ext f g h
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  exact @JTRowGraphCategory.hom_ext_of_label_surjective W Q.base.1.unop
    (supportAt (value q Q.base) |>.obj Q.fiber.unop).obj _
    (JTRowGraphParameterSupport.source_vertex_surjective Q.fiber.unop.obj.parameter) _ _

/-- The support restriction is functorial, also for maps between different target beads. -/
def supported : Resolution q ⥤ Resolution q where
  obj := supportedObj q
  map := supportedMap q
  map_id Q := supported_ext q Q rfl
  map_comp {_ _ Q} _ _ := supported_ext q Q rfl

/-- The actual target and the full graph resolution have the same weak contractibility. -/
theorem point_GW (hX : GW (pointMap X)) : GW (pointMap (nerve (Resolution q))) := by
  let p := nerveMap (Grothendieck.forget (diagram q))
  letI : WeakEquivalence p := GrothendieckContractibleFibers.projection_weak _
    (fun P ↦ (SynchronizedSimplicialParameters.point_op_iff _).2 (JTRowGraphFiber.point_GW _))
  letI : WeakEquivalence (pointMap (nerve X.Elements)) :=
    (weakEquivalence_iff_GW _).mpr (elements_point_GW hX)
  apply (weakEquivalence_iff_GW _).mp
  rw [← pointIsTerminal.hom_ext (p ≫ pointMap (nerve X.Elements)) (pointMap _)]
  infer_instance

end
end DaggerModels.PartII.JTSimplicialTargetRowGraphResolution
