import DaggerModelsPartII.JTRowGraphHorizontalSupport
import DaggerModelsPartII.JTRowGraphFiber
import DaggerModelsPartII.GrothendieckContractibleFibers
import DaggerModelsPartII.SynchronizedSimplicialParameters
import NativeOverNerveWeakContractibility

/-!
# A weakly contractible resolution retaining all horizontal operators into one raw simplex

The base consists of all simplex operators into the fixed raw simplex, including
degeneracies. Coefficient arrows in each fiber are taken in the opposite direction
so that the induced mixed arrow goes from a smaller horizontal graph to the larger one.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra
open DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTRowGraphFaceResolution

open OrdinaryJTRealization JTRowGraphRelations JTRowGraphCategory
open JTRowGraphResolution JTRowGraphFiber JTRowGraphNormalForm

noncomputable section

private abbrev Δ (d : SimplexCategory) := SSet.stdSimplex.{0}.obj d

variable {W : BiPresheaf} {d : SimplexCategory}
variable (q : Δ d ⟶ realization.obj W)

/-- The exact raw value of a simplex operator into the fixed target. -/
abbrev value (p : Over d) : Δ p.left ⟶ realization.obj W := SSet.stdSimplex.map p.hom ≫ q

/-- Restriction commutes with the literal map to the original raw realization. -/
def restrictFiber {p p' : Over d} (a : p ⟶ p') :
    Fiber (value q p') ⥤ Fiber (value q p) :=
  (fixed (value q p)).lift ((fixed (value q p')).ι ⋙ restrict W a.left) (by
    intro G
    change (restrictGraph a.left G.obj).value = value q p
    rw [restrictGraph_value, G.property]
    change SSet.stdSimplex.map a.left ≫ SSet.stdSimplex.map p'.hom ≫ q =
      SSet.stdSimplex.map p.hom ≫ q
    rw [← Category.assoc, ← Functor.map_comp, Over.w])

private theorem inclusion_cancel {D E : Type} [SmallCategory D] [SmallCategory E]
    (P : ObjectProperty E) {F G : D ⥤ P.FullSubcategory}
    (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  let e (x : D) : F.obj x = G.obj x :=
    ObjectProperty.FullSubcategory.ext (congrArg (fun K : D ⥤ E ↦ K.obj x) h)
  refine CategoryTheory.Functor.ext e ?_
  intro X Y f
  apply P.ι.map_injective
  simp only [Functor.map_comp, eqToHom_map]
  exact Functor.congr_hom h f

theorem restrictFiber_id (p : Over d) : restrictFiber q (𝟙 p) = 𝟭 (Fiber (value q p)) := by
  apply inclusion_cancel
  change (fixed (value q p)).ι ⋙ restrict W (𝟙 p.left) =
    (𝟭 (Fiber (value q p))) ⋙ (fixed (value q p)).ι
  rw [restrict_id, Functor.comp_id, Functor.id_comp]

theorem restrictFiber_comp {p p' p'' : Over d} (a : p ⟶ p') (b : p' ⟶ p'') :
    restrictFiber q (a ≫ b) = restrictFiber q b ⋙ restrictFiber q a := by
  apply inclusion_cancel
  change (fixed (value q p'')).ι ⋙ restrict W (a.left ≫ b.left) =
    ((fixed (value q p'')).ι ⋙ restrict W b.left) ⋙ restrict W a.left
  rw [restrict_comp, Functor.assoc]

/-- The actual raw coefficient fibers over all the original horizontal operators. -/
def diagram : (Over d)ᵒᵖ ⥤ Cat.{0, 0} where
  obj p := Cat.of (Fiber (value q p.unop))ᵒᵖ
  map a := (restrictFiber q a.unop).op.toCatHom
  map_id p := by
    apply Cat.Hom.ext
    change (restrictFiber q (𝟙 p.unop)).op = 𝟭 _
    rw [restrictFiber_id]
    rfl
  map_comp a b := by
    apply Cat.Hom.ext
    change (restrictFiber q (b.unop ≫ a.unop)).op =
      (restrictFiber q a.unop).op ⋙ (restrictFiber q b.unop).op
    rw [restrictFiber_comp]
    rfl

abbrev Resolution := Grothendieck (diagram q)

/-- Every face retains the unchanged coefficient of the fixed raw simplex. -/
def centerRestriction (p : Over d) : Fiber (value q p) :=
  ⟨restrictGraph p.hom (center q).obj,
    (restrictGraph_value p.hom (center q).obj).trans
      (congrArg (fun a ↦ SSet.stdSimplex.map p.hom ≫ a) (center q).property)⟩

/-- The full resolution has the weak nerve type of the literal horizontal slice. -/
theorem forget_weak : WeakEquivalence (nerveMap (Grothendieck.forget (diagram q))) :=
  GrothendieckContractibleFibers.projection_weak _
    (fun p ↦ (SynchronizedSimplicialParameters.point_op_iff _).2
      (JTRowGraphFiber.point_GW (value q p.unop)))

/-- All raw graph representatives on all faces of the fixed simplex lie in
one weakly contractible category. -/
theorem point_GW : GW (pointMap (nerve (Resolution q))) := by
  let f := nerveMap (Grothendieck.forget (diagram q))
  letI : WeakEquivalence f := forget_weak q
  letI : WeakEquivalence (pointMap (nerve (Over d)ᵒᵖ)) :=
    (weakEquivalence_iff_GW _).mpr ((SynchronizedSimplicialParameters.point_op_iff _).2
      (DaggerNativeOverNerveWeakContractibility.point_GW d))
  have h : f ≫ pointMap (nerve (Over d)ᵒᵖ) = pointMap (nerve (Resolution q)) :=
    pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

/-- Keep precisely the labels used by the parameter of each original row graph. -/
def supportedObj (P : Resolution q) : Resolution q :=
  ⟨P.base, op ((supportAt (value q P.base.unop)).obj P.fiber.unop)⟩

private def supportedHom {P P' : Resolution q} (a : P ⟶ P') :
    supportedObj q P ⟶ supportedObj q P' :=
  ⟨a.base, Quiver.Hom.op ⟨JTRowGraphHorizontalSupport.supportedArrow a.base.unop.left
      a.fiber.unop.hom⟩⟩

/-- Over the same horizontal operator, maps into a supported object are determined
by the whole supported parameter. -/
theorem supported_ext {T : Resolution q} (P' : Resolution q)
    {a b : T ⟶ supportedObj q P'} (h : a.base = b.base) : a = b := by
  apply Grothendieck.ext a b h
  apply Quiver.Hom.unop_inj
  apply InducedCategory.hom_ext
  exact @hom_ext_of_label_surjective W P'.base.unop.left
    (support P'.fiber.unop.obj) (restrictGraph b.base.unop.left T.fiber.unop.obj)
    (JTRowGraphParameterSupport.source_vertex_surjective P'.fiber.unop.obj.parameter) _ _

/-- Simultaneous support restriction is a functor on the whole face resolution. -/
def supported : Resolution q ⥤ Resolution q where
  obj := supportedObj q
  map := supportedHom q
  map_id P := supported_ext q P rfl
  map_comp {_ _ P''} _ _ := supported_ext q P'' rfl

/-- The original raw graphs compare to their actual supports over the same horizontal faces. -/
def toSupported : 𝟭 (Resolution q) ⟶ supported q where
  app P := ⟨𝟙 P.base, eqToHom (by simp) ≫
    Quiver.Hom.op ((inclusionAt (value q P.base.unop)).app P.fiber.unop)⟩
  naturality {P P'} a := supported_ext q P' (by
    change a.base ≫ 𝟙 P'.base = 𝟙 P.base ≫ a.base
    simp)

/-- The full subcategory whose graphs actually use every coefficient vertex. -/
def usesAllVertices : ObjectProperty (Resolution q) :=
  fun P ↦ Function.Surjective (JTRowGraphParameterSupport.label P.fiber.unop.obj.parameter)

/-- The support functor lands in the full subcategory of supported graphs. -/
def toFullSupport : Resolution q ⥤ (usesAllVertices q).FullSubcategory :=
  (usesAllVertices q).lift (supported q)
    (fun P ↦ JTRowGraphParameterSupport.source_vertex_surjective P.fiber.unop.obj.parameter)

/-- The inclusion of supported graphs has the same weak type as the whole exact resolution. -/
theorem fullSupport_inclusion_weak :
    WeakEquivalence (nerveMap (usesAllVertices q).ι) := by
  let F := (usesAllVertices q).ι
  let G := toFullSupport q
  let s : 𝟭 _ ⟶ F ⋙ G :=
    { app P := ObjectProperty.homMk ((toSupported q).app P.obj)
      naturality _ _ a := ObjectProperty.hom_ext _ ((toSupported q).naturality a.hom) }
  apply (weakEquivalence_iff_GW _).mpr
  exact DaggerNerveHomotopy.nerveMap_geometricW F G
    (.symm _ _ (.rel _ _ ⟨s⟩)) (.symm _ _ (.rel _ _ ⟨toSupported q⟩))

theorem fullSupport_point_GW : GW (pointMap (nerve (usesAllVertices q).FullSubcategory)) := by
  let f := nerveMap (usesAllVertices q).ι
  letI : WeakEquivalence f := fullSupport_inclusion_weak q
  letI : WeakEquivalence (pointMap (nerve (Resolution q))) :=
    (weakEquivalence_iff_GW _).mpr (point_GW q)
  have h : f ≫ pointMap (nerve (Resolution q)) =
      pointMap (nerve (usesAllVertices q).FullSubcategory) := pointIsTerminal.hom_ext _ _
  rw [← h]
  exact (weakEquivalence_iff_GW _).mp inferInstance

end

end DaggerModels.PartII.JTRowGraphFaceResolution
