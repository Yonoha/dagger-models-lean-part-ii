import DaggerModelsPartII.NecklaceCylinderJointDiagram
import ChosenNecklacesOver
import Mathlib.CategoryTheory.Comma.StructuredArrow.Functor
import Mathlib.CategoryTheory.Grothendieck

/-!
# The original necklaces over a boundary object are its actual comma category

Use the existing Mathlib comma functor for strict functoriality under every
boundary-preserving map. The equivalence keeps each original necklace code,
its entire map, all native morphisms and both ordered endpoint equations.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.BoundaryNecklaceComma

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary
private abbrev NCode := NecklaceCode

/-- The SAME native necklace functor under the original ordered boundary. -/
def necklaceUnder : NCode ⥤ Under B where
  obj T := Under.mk (JTNecklaceEndpointCylinder.endpointInclusion T)
  map f := Under.homMk f.map (JTNecklaceEndpointCylinder.endpointInclusion_natural f)
  map_id _ := by apply Under.UnderMorphism.ext; rfl
  map_comp _ _ := by apply Under.UnderMorphism.ext; rfl

/-- All original endpoint-preserving necklaces, in Mathlib's actual comma functor. -/
def diagram : Under B ⥤ Cat.{0,0} := CostructuredArrow.functor necklaceUnder

def first (U : Under B) : U.right.obj (op ⦋0⦌) :=
  (JTEndpointObjects.boundaryHomEquiv U.right U.hom).1

def last (U : Under B) : U.right.obj (op ⦋0⦌) :=
  (JTEndpointObjects.boundaryHomEquiv U.right U.hom).2

theorem first_eq (U : Under B) :
    first U = U.hom.app (op ⦋0⦌) (SSet.yonedaEquiv SSet.boundary₁.ι₀) :=
  SSet.yonedaEquiv_comp _ _

theorem last_eq (U : Under B) :
    last U = U.hom.app (op ⦋0⦌) (SSet.yonedaEquiv SSet.boundary₁.ι₁) :=
  SSet.yonedaEquiv_comp _ _

private theorem boundary_eta (U : Under B) :
    JTConeMappingPresentation.orderedBoundary U.right (first U) (last U) = U.hom :=
  (JTEndpointObjects.boundaryHomEquiv U.right).symm_apply_apply U.hom

private theorem boundary_pair {T : NCode} {U : Under B}
    (f : necklaceUnder.obj T ⟶ U) :
    (f.right.app (op ⦋0⦌) T.first, f.right.app (op ⦋0⦌) T.last) =
      (first U, last U) := by
  have h := congrArg (JTEndpointObjects.boundaryHomEquiv U.right) (Under.w f)
  change JTEndpointObjects.boundaryHomEquiv U.right
    (JTNecklaceEndpointCylinder.endpointInclusion T ≫ f.right) = _ at h
  rw [JTNecklaceEndpointCylinder.endpointInclusion,
    JTGeneralOrderedFiberWeak.orderedBoundary_natural] at h
  simpa only [JTConeMappingPresentation.orderedBoundary, Equiv.apply_symm_apply] using h

/-- Keep the actual comma map and both original ordered endpoints. -/
def toNative (U : Under B) :
    CostructuredArrow necklaceUnder U ⥤ NecklacesOver U.right (first U) (last U) where
  obj P := ⟨P.left, P.hom.right, congrArg Prod.fst (boundary_pair P.hom),
    congrArg Prod.snd (boundary_pair P.hom)⟩
  map f := ⟨f.left, congrArg (fun h ↦ h.right) (CostructuredArrow.w f)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Repack the SAME complete necklace map as an actual map under the boundary. -/
def fromNative (U : Under B) :
    NecklacesOver U.right (first U) (last U) ⥤ CostructuredArrow necklaceUnder U where
  obj P := CostructuredArrow.mk (Under.homMk P.map (by
    change JTNecklaceEndpointCylinder.endpointInclusion P.code ≫ P.map = U.hom
    rw [JTNecklaceEndpointCylinder.endpointInclusion,
      JTGeneralOrderedFiberWeak.orderedBoundary_natural, P.first, P.last]
    exact boundary_eta U))
  map f := CostructuredArrow.homMk f.hom (by
    apply Under.UnderMorphism.ext
    exact f.w)
  map_id _ := by apply CostructuredArrow.hom_ext; rfl
  map_comp _ _ := by apply CostructuredArrow.hom_ext; rfl

/-- A full actual category equivalence, without replacing a necklace or its map. -/
def equivalence (U : Under B) :
    CostructuredArrow necklaceUnder U ≌ NecklacesOver U.right (first U) (last U) where
  functor := toNative U
  inverse := fromNative U
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- At a specified original endpoint pair, retain the literal native map and code. -/
def toNativeAt (X : SSet.{0}) (a b : X.obj (op ⦋0⦌)) :
    CostructuredArrow necklaceUnder (JTConeMappingPresentation.targetUnder X a b) ⥤
      NecklacesOver X a b where
  obj P := ⟨P.left, P.hom.right,
    (congrArg Prod.fst (boundary_pair P.hom)).trans
      (congrArg Prod.fst ((JTEndpointObjects.boundaryHomEquiv X).apply_symm_apply (a, b))),
    (congrArg Prod.snd (boundary_pair P.hom)).trans
      (congrArg Prod.snd ((JTEndpointObjects.boundaryHomEquiv X).apply_symm_apply (a, b)))⟩
  map f := ⟨f.left, congrArg (fun h ↦ h.right) (CostructuredArrow.w f)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

variable {J : Type} [SmallCategory J]

/-- The actual category diagram of ALL original necklaces in each boundary object. -/
def fiberDiagram (F : J ⥤ Under B) : J ⥤ Cat.{0,0} := F ⋙ diagram

/-- The full parameter-aware presentation, with original fiber necklaces. -/
abbrev Presentation (F : J ⥤ Under B) := Grothendieck (fiberDiagram F)

private theorem eqToHom_left {U : Under B} {P Q : CostructuredArrow necklaceUnder U}
    (h : P = Q) : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  cases h
  rfl

/-- Remember the SAME original internal necklace and every native operator. -/
def sourceCode (F : J ⥤ Under B) : Presentation F ⥤ NCode where
  obj P := P.fiber.left
  map f := f.fiber.left
  map_id P := by
    have hi : (CostructuredArrow.map (F.map (𝟙 P.base))).obj P.fiber = P.fiber := by
      rw [F.map_id]
      exact CostructuredArrow.map_id
    change (eqToHom hi).left = 𝟙 P.fiber.left
    rw [eqToHom_left]
    rfl
  map_comp {X Y Z} f g := by
    have hc : (CostructuredArrow.map (F.map (f.base ≫ g.base))).obj X.fiber =
        (CostructuredArrow.map (F.map g.base)).obj
          ((CostructuredArrow.map (F.map f.base)).obj X.fiber) := by
      rw [F.map_comp]
      rfl
    change (eqToHom hc ≫ (CostructuredArrow.map (F.map g.base)).map f.fiber ≫
      g.fiber).left = f.fiber.left ≫ g.fiber.left
    simp only [CostructuredArrow.comp_left]
    rw [eqToHom_left (U := F.obj Z.base)]
    change 𝟙 _ ≫ (f.fiber.left ≫ g.fiber.left) = f.fiber.left ≫ g.fiber.left
    rw [Category.id_comp]

/-- The actual internal necklace maps naturally into its full original boundary object. -/
def evaluation (F : J ⥤ Under B) :
    sourceCode F ⋙ necklaceUnder ⟶ Grothendieck.forget (fiberDiagram F) ⋙ F where
  app P := P.fiber.hom
  naturality {_ _} f := CostructuredArrow.w f.fiber

/-- Postcompose every full original necklace by the SAME boundary-preserving cocone. -/
def toTarget (F : J ⥤ Under B) {U : Under B}
    (ρ : F ⟶ (Functor.const J).obj U) :
    Presentation F ⥤ CostructuredArrow necklaceUnder U :=
  (sourceCode F).toCostructuredArrow necklaceUnder U (fun P ↦ P.fiber.hom ≫ ρ.app P.base)
    (by
      intro P Q f
      change necklaceUnder.map f.fiber.left ≫ (Q.fiber.hom ≫ ρ.app Q.base) =
        P.fiber.hom ≫ ρ.app P.base
      rw [← Category.assoc, CostructuredArrow.w f.fiber]
      change (P.fiber.hom ≫ F.map f.base) ≫ ρ.app Q.base = P.fiber.hom ≫ ρ.app P.base
      rw [Category.assoc]
      have h := ρ.naturality f.base
      change F.map f.base ≫ ρ.app Q.base = ρ.app P.base ≫ 𝟙 U at h
      exact congrArg (fun q ↦ P.fiber.hom ≫ q) (h.trans (Category.comp_id _)))

/-- The target object keeps the SAME original necklace and complete composite map. -/
theorem toTarget_obj (F : J ⥤ Under B) {U : Under B}
    (ρ : F ⟶ (Functor.const J).obj U) (P : Presentation F) :
    (toTarget F ρ).obj P = CostructuredArrow.mk (P.fiber.hom ≫ ρ.app P.base) := by
  rfl

/-- Every actual original internal necklace operator is retained by the target functor. -/
theorem toTarget_map_left (F : J ⥤ Under B) {U : Under B}
    (ρ : F ⟶ (Functor.const J).obj U) {P Q : Presentation F} (f : P ⟶ Q) :
    ((toTarget F ρ).map f).left = f.fiber.left := rfl

end

end DaggerModels.PartII.BoundaryNecklaceComma
