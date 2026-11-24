import DaggerModelsPartII.DecoratedCylinderNecklacePresentation
import DaggerModelsPartII.JTCommaGraphPredecessor
import TopCatModelCategory.SSet.Contractible

/-!
# One fixed homotopy cylinder maps to the same actual target comma

The original
`NecklaceCode.Hom` consists of all endpoint-preserving simplicial-set maps.
Thus every map from an internal necklace to a cylinder can be augmented to
a native morphism into the cylinder's original necklace code.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace
open DaggerModels.PartII.JTNecklaceEndpointCylinder
open DaggerModels.PartII.DecoratedCylinderNecklacePresentation
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTHomotopyTargetComma

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev R (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev v (W : Source) (x : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)) :=
  JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex W x
private abbrev U (T : NecklaceCode) : Under JTXiEndpointCollapse.boundary :=
  (under T).obj ⦋1⦌
private abbrev Fiber (T : NecklaceCode) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder (U T)
private abbrev FiberAt (T : NecklaceCode) (n : SimplexCategory) :=
  CostructuredArrow BoundaryNecklaceComma.necklaceUnder ((under T).obj n)
private abbrev aug := NecklaceCylinderAugmentation.augmentation

variable (W : Source)
  (x y : (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌))
  (i : DecoratedNecklaceHomDiagram.Index W x y)
  (Q : NecklacesOver (R W) (v W x) (v W y))
  (T : NecklaceCode) (c : T ⟶ Q.code)

/- The homotopy map is a map under the original ordered boundary. -/
variable (h : U T ⟶ (underDiagram W x y).obj i)

/- Both paths to the raw realization are the very same complete map. -/
variable (heq : h.right ≫ ((underCocone W x y).app i).right =
  aug T ⦋1⦌ ≫ c.map ≫ Q.map)

/-- Include the whole source fiber in the fixed decorated fiber. -/
def toPresentation : Fiber T ⥤ Presentation W x y :=
  CostructuredArrow.map h ⋙
    Grothendieck.ι (BoundaryNecklaceComma.fiberDiagram (underDiagram W x y)) i

private theorem eqToHom_left {A : Under JTXiEndpointCollapse.boundary}
    {P P' : CostructuredArrow BoundaryNecklaceComma.necklaceUnder A}
    (h : P = P') : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  cases h
  rfl

private theorem toPresentation_map_code {P P' : Fiber T} (f : P ⟶ P') :
    ((toPresentation W x y i T h).map f).fiber.left = f.left := by
  let P₀ := (CostructuredArrow.map h).obj P
  have hi : (CostructuredArrow.map ((underDiagram W x y).map (𝟙 i))).obj P₀ = P₀ := by
    rw [(underDiagram W x y).map_id i]
    exact CostructuredArrow.map_id
  change (eqToHom hi ≫ (CostructuredArrow.map h).map f).left = f.left
  rw [CostructuredArrow.comp_left, eqToHom_left]
  change 𝟙 _ ≫ f.left = f.left
  exact Category.id_comp _

private theorem augmentation_boundary (P : Fiber T) :
    endpointInclusion P.left ≫ (P.hom.right ≫ aug T ⦋1⦌) =
      endpointInclusion T := by
  rw [← Category.assoc]
  have hp : endpointInclusion P.left ≫ P.hom.right =
      (boundary T).app ⦋1⦌ := Under.w P.hom
  rw [hp, NecklaceCylinderAugmentation.augmentation_boundary]

private theorem augmentation_endpoints (P : Fiber T) :
    ((P.hom.right ≫ aug T ⦋1⦌).app (op ⦋0⦌) P.left.first,
      (P.hom.right ≫ aug T ⦋1⦌).app (op ⦋0⦌) P.left.last) =
      (T.first, T.last) := by
  have hp := augmentation_boundary T P
  dsimp only [endpointInclusion] at hp
  rw [JTGeneralOrderedFiberWeak.orderedBoundary_natural] at hp
  exact (JTEndpointObjects.boundaryHomEquiv _).symm.injective hp

/-- The full internal map augmented to the original native code. -/
def augmentationCode (P : Fiber T) : P.left ⟶ T where
  map := P.hom.right ≫ aug T ⦋1⦌
  first := congrArg Prod.fst (augmentation_endpoints T P)
  last := congrArg Prod.snd (augmentation_endpoints T P)

/-- The target-comma arrow uses the supplied native collapse `c`. -/
def toQArrow (P : Fiber T) :
    (DecoratedCylinderNecklacePresentation.toTarget W x y).obj
        ((toPresentation W x y i T h).obj P) ⟶ Q where
  hom := augmentationCode T P ≫ c
  w := by
    change ((P.hom.right ≫ aug T ⦋1⦌) ≫ c.map) ≫ Q.map =
      (P.hom.right ≫ h.right) ≫ ((underCocone W x y).app i).right
    calc
      ((P.hom.right ≫ aug T ⦋1⦌) ≫ c.map) ≫ Q.map =
          P.hom.right ≫ (aug T ⦋1⦌ ≫ c.map ≫ Q.map) := by
            simp only [Category.assoc]
      _ = P.hom.right ≫
          (h.right ≫ ((underCocone W x y).app i).right) := by rw [heq]
      _ = (P.hom.right ≫ h.right) ≫
          ((underCocone W x y).app i).right := by
            simp only [Category.assoc]

/-- The full source fiber maps into the actual comma over the SAME `Q`. -/
def toComma : Fiber T ⥤
    CostructuredArrow (DecoratedCylinderNecklacePresentation.toTarget W x y) Q :=
  (toPresentation W x y i T h).toCostructuredArrow
    (DecoratedCylinderNecklacePresentation.toTarget W x y) Q
    (toQArrow W x y i Q T c h heq) (by
      intro P P' f
      apply NecklacesOver.Hom.ext
      change ((DecoratedCylinderNecklacePresentation.toTarget W x y).map
        ((toPresentation W x y i T h).map f)).hom ≫
          (augmentationCode T P' ≫ c) = augmentationCode T P ≫ c
      rw [toTarget_map_hom, toPresentation_map_code]
      apply NecklaceCode.Hom.ext
      have hp := congrArg (fun q ↦ q.right) (CostructuredArrow.w f)
      change f.left.map ≫ P'.hom.right = P.hom.right at hp
      change f.left.map ≫ ((P'.hom.right ≫ aug T ⦋1⦌) ≫ c.map) =
        (P.hom.right ≫ aug T ⦋1⦌) ≫ c.map
      simp only [← Category.assoc, hp])

/-- The actual comma functor retains the exact fixed decorated label. -/
theorem toComma_obj_base (P : Fiber T) :
    ((toComma W x y i Q T c h heq).obj P).left.base = i := rfl

/-- Every native source operator remains the native operator of the comma arrow. -/
theorem toComma_map_code {P P' : Fiber T} (f : P ⟶ P') :
    ((toComma W x y i Q T c h heq).map f).left.fiber.left = f.left :=
  toPresentation_map_code W x y i T h f

/-- The original cylinder Hom is weakly contractible for any native code. -/
private theorem cylinderHom_point_GW (T : NecklaceCode) (k : SimplexCategory) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.cylinderHom T k)) := by
  have hl : WeakEquivalence (NecklaceCylinderHomSpan.leftMap T k) :=
    NecklaceCylinderHomSpan.leftMap_weak T k
  have hs : WeakEquivalence
      (DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.necklaceHom T)) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr
      (DecoratedNecklaceHomBar.necklaceHom_point_GW T)
  have he : NecklaceCylinderHomSpan.leftMap T k ≫
      DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.necklaceHom T) =
      DaggerOriginalProductGadget.pointMap (NecklaceCylinderHomSpan.cylinderHom T k) :=
    DaggerOriginalProductGadget.pointIsTerminal.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← he]
  infer_instance

/-- The unrestricted source comma fiber has contractible nerve in every degree. -/
theorem fiber_point_GW_at (T : NecklaceCode) (n : SimplexCategory) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap
        (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder
          ((under T).obj n)))) := by
  have hf : BoundaryNecklaceComma.first ((under T).obj n) =
      NecklaceCylinderHomSpan.firstVertex T n := by
    rw [BoundaryNecklaceComma.first_eq]
    rfl
  have hl : BoundaryNecklaceComma.last ((under T).obj n) =
      NecklaceCylinderHomSpan.lastVertex T n := by
    rw [BoundaryNecklaceComma.last_eq]
    rfl
  have hn : DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap
        (nerve (NecklacesOver ((under T).obj n).right
          (BoundaryNecklaceComma.first ((under T).obj n))
          (BoundaryNecklaceComma.last ((under T).obj n))))) := by
    rw [hf, hl]
    exact DaggerActualNecklaceConeGadgetComparison.necklace_point_GW_of_original_hom
      ((value T).obj n)
      (NecklaceCylinderHomSpan.firstVertex T n)
      (NecklaceCylinderHomSpan.lastVertex T n)
      (cylinderHom_point_GW T n)
  have he : WeakEquivalence
      (nerveMap (BoundaryNecklaceComma.equivalence ((under T).obj n)).functor) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  have hp : WeakEquivalence
      (DaggerOriginalProductGadget.pointMap
        (nerve (NecklacesOver ((under T).obj n).right
          (BoundaryNecklaceComma.first ((under T).obj n))
          (BoundaryNecklaceComma.last ((under T).obj n))))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr hn
  have hpoint : nerveMap (BoundaryNecklaceComma.equivalence ((under T).obj n)).functor ≫
      DaggerOriginalProductGadget.pointMap
        (nerve (NecklacesOver ((under T).obj n).right
          (BoundaryNecklaceComma.first ((under T).obj n))
          (BoundaryNecklaceComma.last ((under T).obj n)))) =
      DaggerOriginalProductGadget.pointMap
        (nerve (CostructuredArrow BoundaryNecklaceComma.necklaceUnder
          ((under T).obj n))) :=
    DaggerOriginalProductGadget.pointIsTerminal.hom_ext _ _
  apply (DaggerSSetGluing.weakEquivalence_iff_GW _).mp
  rw [← hpoint]
  infer_instance

/-- The unrestricted degree-one source comma fiber has contractible nerve. -/
theorem fiber_point_GW (T : NecklaceCode) :
    DaggerSSetGluing.GW
      (DaggerOriginalProductGadget.pointMap (nerve (Fiber T))) :=
  fiber_point_GW_at T ⦋1⦌

/-- A Kan weak map induces a bijection on the actual unreplaced `π₀`. -/
private theorem bijective_mapπ₀_of_weak {A B : SSet.{0}} (f : A ⟶ B)
    (hf : weakEquivalences SSet.{0} f) : Function.Bijective (SSet.mapπ₀ f) := by
  let G := SSet.toTop.{0} ⋙ TopCat.toSSet
  have hG : WeakEquivalence (G.map f) :=
    (TopCat.weakEquivalence_toSSet_map_iff _).mpr
      ((SSet.modelCategoryQuillen.weakEquivalence_iff _).mp
        ((weakEquivalence_iff _).mpr hf))
  have hmap := ((SSet.weakEquivalence_iff_kanComplexW _).mp hG).bijective_mapπ₀
  have hA := SSet.bijective_mapπ₀_sSetTopAdj_unit_app A
  have hB := SSet.bijective_mapπ₀_sSetTopAdj_unit_app B
  apply (Function.Bijective.of_comp_iff' hB _).mp
  have hcomp : SSet.mapπ₀ (sSetTopAdj.unit.app B) ∘ SSet.mapπ₀ f =
      SSet.mapπ₀ (G.map f) ∘ SSet.mapπ₀ (sSetTopAdj.unit.app A) := by
    funext z
    change SSet.mapπ₀ _ (SSet.mapπ₀ _ z) =
      SSet.mapπ₀ _ (SSet.mapπ₀ _ z)
    rw [← SSet.mapπ₀_comp_apply, ← SSet.mapπ₀_comp_apply]
    exact congrArg (fun q ↦ SSet.mapπ₀ q z) (sSetTopAdj.unit.naturality f)
  rw [hcomp]
  exact hmap.comp hA

/-- A simplex edge of the nerve supplies an actual forward category arrow. -/
private theorem edge_to_zigzag {C : Type} [Category C]
    {a b : (nerve C).obj (op ⦋0⦌)}
    (e : SSet.π₀Rel (X := nerve C) a b) :
    Relation.EqvGen (fun P Q : C ↦ Nonempty (P ⟶ Q))
      (CategoryTheory.nerveEquiv a) (CategoryTheory.nerveEquiv b) := by
  obtain ⟨edge, first, last⟩ := e
  exact Relation.EqvGen.rel _ _
    ⟨CategoryTheory.nerve.homEquiv (SSet.Edge.mk edge first last)⟩

/-- Contractibility gives an actual finite zigzag in every source-fiber degree. -/
theorem source_zigzag_at (T : NecklaceCode) (n : SimplexCategory)
    (P P' : FiberAt T n) :
    Relation.EqvGen (fun A B : FiberAt T n ↦ Nonempty (A ⟶ B)) P P' := by
  have hw : WeakEquivalence
      (DaggerOriginalProductGadget.pointMap (nerve (FiberAt T n))) :=
    (DaggerSSetGluing.weakEquivalence_iff_GW _).mpr (fiber_point_GW_at T n)
  let e := DaggerOriginalProductGadget.pointIsTerminal.uniqueUpToIso
    SSet.stdSimplex.isTerminalObj₀
  have hm : weakEquivalences SSet.{0}
      (DaggerOriginalProductGadget.pointMap (nerve (FiberAt T n)) ≫ e.hom) :=
    mem_weakEquivalences _
  have hi := (bijective_mapπ₀_of_weak _ hm).1
  letI : Subsingleton (SSet.π₀ (nerve (FiberAt T n))) := hi.subsingleton
  have hπ : SSet.π₀.mk (X := nerve (FiberAt T n)) (ComposableArrows.mk₀ P) =
      SSet.π₀.mk (X := nerve (FiberAt T n)) (ComposableArrows.mk₀ P') :=
    Subsingleton.elim _ _
  have hz := (SSet.π₀.mk_eq_mk_iff (X := nerve (FiberAt T n))
    (ComposableArrows.mk₀ P) (ComposableArrows.mk₀ P')).mp hπ
  have htransfer : ∀ {a b : (nerve (FiberAt T n)).obj (op ⦋0⦌)},
      Relation.EqvGen (SSet.π₀Rel (X := nerve (FiberAt T n))) a b →
      Relation.EqvGen (fun A B : FiberAt T n ↦ Nonempty (A ⟶ B))
        (CategoryTheory.nerveEquiv a) (CategoryTheory.nerveEquiv b) := by
    intro a b hab
    induction hab with
    | rel a b e => exact edge_to_zigzag e
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  simpa [CategoryTheory.nerveEquiv] using htransfer hz

/-- Contractibility gives an actual finite zigzag of degree-one source-fiber morphisms. -/
theorem source_zigzag (T : NecklaceCode) (P P' : Fiber T) :
    Relation.EqvGen (fun A B : Fiber T ↦ Nonempty (A ⟶ B)) P P' :=
  source_zigzag_at T ⦋1⦌ P P'

/-- Both resulting target-comma objects are joined by the image zigzag. -/
theorem target_zigzag (P P' : Fiber T) :
    Relation.EqvGen
      (fun A B : CostructuredArrow
          (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ↦
        Nonempty (A ⟶ B))
      ((toComma W x y i Q T c h heq).obj P)
      ((toComma W x y i Q T c h heq).obj P') := by
  induction source_zigzag T P P' with
  | rel A B f =>
      exact Relation.EqvGen.rel _ _
        ⟨(toComma W x y i Q T c h heq).map f.some⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'

end

end DaggerModels.PartII.JTHomotopyTargetComma
