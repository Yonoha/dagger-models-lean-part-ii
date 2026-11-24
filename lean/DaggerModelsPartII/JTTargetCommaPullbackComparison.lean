import DaggerModelsPartII.JTTargetCommaPullbackDiagram

/-!
# The fixed-target comma as the Grothendieck construction of pullback fibers
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTTargetCommaPullback

open DecoratedCylinderNecklacePresentation (underDiagram underCocone toTarget)
open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev B := JTXiEndpointCollapse.boundary

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

local notation "D" => underDiagram W x y
local notation "ρ" => underCocone W x y
local notation "C" => CostructuredArrow (toTarget W x y) Q
local notation "I" => DecoratedNecklaceHomDiagram.Index W x y

local notation "E" => diagram W x y Q
local notation "q" => targetMap W x y Q

/-- The Grothendieck construction using the fixed-target pullback diagram. -/
abbrev Presentation := BoundaryNecklaceComma.Presentation E

local notation "G" => Presentation W x y Q

private theorem eqToHom_left {U : Under B} {P P' : CostructuredArrow necklaceUnder U}
    (h : P = P') : (eqToHom h).left = eqToHom (congrArg Comma.left h) := by
  cases h
  rfl

/-- A decorated arrow is determined by its base operator and its native code map. -/
theorem operator_ext {J : Type} [SmallCategory J] {F : J ⥤ Under B} {P P' : BoundaryNecklaceComma.Presentation F}
    {f g : P ⟶ P'} (hb : f.base = g.base) (hc : f.fiber.left = g.fiber.left) : f = g := by
  apply Grothendieck.ext f g hb
  apply CostructuredArrow.hom_ext
  rw [CostructuredArrow.comp_left, eqToHom_left]
  change 𝟙 _ ≫ f.fiber.left = g.fiber.left
  rw [Category.id_comp, hc]

section Assemble

variable {J K : Type} [SmallCategory J] [SmallCategory K]
variable (F : J ⥤ Under B) (base : K ⥤ J) (code : K ⥤ NecklaceCode)
variable (maps : code ⋙ necklaceUnder ⟶ base ⋙ F)

private def assembleObj (P : K) : BoundaryNecklaceComma.Presentation F :=
  ⟨base.obj P, CostructuredArrow.mk (maps.app P)⟩

private def assembleHom {P P' : K} (f : P ⟶ P') :
    assembleObj F base code maps P ⟶ assembleObj F base code maps P' :=
  ⟨base.map f, CostructuredArrow.homMk (code.map f) (maps.naturality f)⟩

/-- Assemble the original decorated and native operators into a functor of presentations. -/
def assemble : K ⥤ BoundaryNecklaceComma.Presentation F where
  obj := assembleObj F base code maps
  map := assembleHom F base code maps
  map_id P := operator_ext (base.map_id P)
    ((code.map_id P).trans ((sourceCode F).map_id (assembleObj F base code maps P)).symm)
  map_comp f g := operator_ext (base.map_comp f g)
    ((code.map_comp f g).trans
      ((sourceCode F).map_comp (assembleHom F base code maps f)
        (assembleHom F base code maps g)).symm)

end Assemble

private abbrev projection := CostructuredArrow.proj (toTarget W x y) Q

private abbrev baseOf := projection W x y Q ⋙ DecoratedCylinderNecklacePresentation.projection W x y

private abbrev codeOf := projection W x y Q ⋙ sourceCode D

private def pairedMaps : codeOf W x y Q ⋙ necklaceUnder ⟶ baseOf W x y Q ⋙ E where
  app := lift W x y Q
  naturality {_ _} f := lift_naturality W x y Q f

/-- Pair each entire cylinder map with the specified comparison to the fixed target. -/
def toPullback : C ⥤ G :=
  assemble E (baseOf W x y Q) (codeOf W x y Q) (pairedMaps W x y Q)

/-- The comparison leaves the original decorated operator and native arrow in place. -/
theorem toPullback_map_operators {P P' : C} (f : P ⟶ P') :
    ((toPullback W x y Q).map f).base = f.left.base ∧
    ((toPullback W x y Q).map f).fiber.left = f.left.fiber.left :=
  ⟨rfl, rfl⟩

end

end DaggerModels.PartII.JTTargetCommaPullback
