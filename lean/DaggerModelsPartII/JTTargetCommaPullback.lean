import DaggerModelsPartII.JTTargetCommaPullbackComparison

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

local notation "G" => Presentation W x y Q

private theorem necklaceUnder_map_injective {T U : NecklaceCode}
    {f g : T ⟶ U} (h : necklaceUnder.map f = necklaceUnder.map g) : f = g :=
  NecklaceCode.Hom.ext (congrArg (fun k ↦ k.right) h)

/-- Read a map between native necklaces under their ordered boundary as a native operator. -/
def nativeArrow {T U : NecklaceCode} (f : necklaceUnder.obj T ⟶ necklaceUnder.obj U) :
    T ⟶ U :=
  let h : (f.right.app (op ⦋0⦌) T.first, f.right.app (op ⦋0⦌) T.last) =
      (U.first, U.last) := by
    have hw := Under.w f
    change JTNecklaceEndpointCylinder.endpointInclusion T ≫ f.right =
      JTNecklaceEndpointCylinder.endpointInclusion U at hw
    rw [JTNecklaceEndpointCylinder.endpointInclusion,
      JTGeneralOrderedFiberWeak.orderedBoundary_natural] at hw
    exact (JTEndpointObjects.boundaryHomEquiv _).symm.injective hw
  ⟨f.right, congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The recovered operator gives the original map under the ordered boundary. -/
theorem map_nativeArrow {T U : NecklaceCode}
    (f : necklaceUnder.obj T ⟶ necklaceUnder.obj U) :
    necklaceUnder.map (nativeArrow f) = f :=
  Under.UnderMorphism.ext rfl

/-- Project an entire pullback map to the original cylinder and to the fixed target. -/
def fromObj (P : G) : C := by
  let A : DecoratedCylinderNecklacePresentation.Presentation W x y :=
    ⟨P.base, CostructuredArrow.mk (P.fiber.hom ≫ fst W x y Q P.base)⟩
  refine CostructuredArrow.mk (Y := A) ⟨nativeArrow (P.fiber.hom ≫ snd W x y Q P.base), ?_⟩
  have h : (P.fiber.hom ≫ snd W x y Q P.base) ≫ q =
      (P.fiber.hom ≫ fst W x y Q P.base) ≫ (ρ).app P.base := by
    simp only [Category.assoc, condition W x y Q P.base]
  exact congrArg (fun m ↦ m.right) h

private def fromHom {P P' : C}
    (f : (toPullback W x y Q).obj P ⟶ (toPullback W x y Q).obj P') : P ⟶ P' := by
  have w : necklaceUnder.map f.fiber.left ≫ lift W x y Q P' =
      (lift W x y Q P) ≫ (E).map f.base := CostructuredArrow.w f.fiber
  refine CostructuredArrow.homMk ⟨f.base, CostructuredArrow.homMk f.fiber.left ?_⟩ ?_
  · change necklaceUnder.map f.fiber.left ≫ P'.left.fiber.hom =
      P.left.fiber.hom ≫ (D).map f.base
    calc
      _ = necklaceUnder.map f.fiber.left ≫
          (lift W x y Q P' ≫ fst W x y Q P'.left.base) :=
        congrArg (fun m ↦ necklaceUnder.map f.fiber.left ≫ m)
          (lift_fst W x y Q P').symm
      _ = lift W x y Q P ≫ ((E).map f.base ≫ fst W x y Q P'.left.base) := by
        rw [← Category.assoc, w, Category.assoc]
      _ = lift W x y Q P ≫ (fst W x y Q P.left.base ≫ (D).map f.base) :=
        congrArg (fun m ↦ lift W x y Q P ≫ m) (map_fst W x y Q f.base)
      _ = _ := lift_fst_assoc W x y Q P ((D).map f.base)
  · apply NecklacesOver.Hom.ext
    apply necklaceUnder_map_injective
    change necklaceUnder.map (f.fiber.left ≫ P'.hom.hom) = necklaceUnder.map P.hom.hom
    calc
      _ = necklaceUnder.map f.fiber.left ≫
          (lift W x y Q P' ≫ snd W x y Q P'.left.base) := by
        rw [necklaceUnder.map_comp, lift_snd]
      _ = lift W x y Q P ≫ ((E).map f.base ≫ snd W x y Q P'.left.base) := by
        rw [← Category.assoc, w, Category.assoc]
      _ = lift W x y Q P ≫ snd W x y Q P.left.base :=
        congrArg (fun m ↦ lift W x y Q P ≫ m) (map_snd W x y Q f.base)
      _ = _ := lift_snd W x y Q P

private theorem pair_fromObj (P : G) : (toPullback W x y Q).obj (fromObj W x y Q P) = P := by
  have h : lift W x y Q (fromObj W x y Q P) = P.fiber.hom := by
    apply pullback.hom_ext (f := (ρ).app P.base) (g := q)
    · change lift W x y Q (fromObj W x y Q P) ≫ fst W x y Q P.base =
        P.fiber.hom ≫ fst W x y Q P.base
      exact lift_fst W x y Q (fromObj W x y Q P)
    · change lift W x y Q (fromObj W x y Q P) ≫ snd W x y Q P.base =
        P.fiber.hom ≫ snd W x y Q P.base
      exact (lift_snd W x y Q (fromObj W x y Q P)).trans
        (map_nativeArrow (P.fiber.hom ≫ snd W x y Q P.base))
  exact congrArg (fun m ↦ ⟨P.base, CostructuredArrow.mk m⟩ : _ → G) h

private theorem comparison_faithful : (toPullback W x y Q).Faithful where
  map_injective := by
    intro P P' f g h
    apply CostructuredArrow.hom_ext
    refine operator_ext ?_ ?_
    · exact congrArg (fun k ↦ k.base) h
    · exact congrArg (fun k ↦ (sourceCode E).map k) h

private theorem comparison_full : (toPullback W x y Q).Full where
  map_surjective := by
    intro P P' f
    refine ⟨fromHom W x y Q f, operator_ext ?_ ?_⟩
    · rfl
    · rfl

instance : (toPullback W x y Q).IsEquivalence where
  faithful := comparison_faithful W x y Q
  full := comparison_full W x y Q
  essSurj := Functor.essSurj_of_surj (F := toPullback W x y Q)
    (fun P ↦ ⟨fromObj W x y Q P, pair_fromObj W x y Q P⟩)

/-- The actual target comma is the total category of necklaces over these pullbacks. -/
def equivalence : C ≌ G := (toPullback W x y Q).asEquivalence

end

end DaggerModels.PartII.JTTargetCommaPullback
