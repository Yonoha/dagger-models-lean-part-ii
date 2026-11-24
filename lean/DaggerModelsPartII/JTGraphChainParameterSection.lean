import DaggerModelsPartII.JTGraphArrowParameterDiagram
import DaggerModelsPartII.JTGraphChainArrowIndex
import DaggerModelsPartII.JTGraphInterpolatedChainOver

/-! The original finite-chain comparisons give compatible exact graph parameters. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphChainParameterSection

open JTGraphFactoredPresentation (TargetComma)
open JTProjectiveOrderedFiberComparison (row)
open JTGraphCylinderSimplexSpan (Simplices firstVertex)
open JTGraphSimplexLastVertex (lastVertex lastVertex_weak)
open JTGraphChainArrowIndex (chainIndex)
open JTGraphInterpolatedChainOver
open JTGraphLiftTransport JTGraphLiftRestriction
open DaggerNativeSimplicialReplacementCells (first initialArrow)
open DaggerNativeDualTheoremACells (last lastArrow)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

private abbrev C := TargetComma Q

/-- The entire time space of graph lifts over the original composite of each chain. -/
abbrev diagram := chainIndex (C Q) ⋙ JTGraphArrowParameterDiagram.diagram Q

/-- The category containing all time choices, with the two actual operators. -/
abbrev ChainParameters :=
  Grothendieck (diagram Q ⋙ SimplicialResolutionFunctor.elementsOpposite)

private abbrev fibers := diagram Q ⋙ SimplicialResolutionFunctor.elementsOpposite

/-- Forgetting the exact choices is weak on the full original chain index. -/
theorem projection_weak : WeakEquivalence (nerveMap (Grothendieck.forget (fibers Q))) :=
  GrothendieckContractibleFibers.projection_weak _
    (fun P ↦ JTGraphArrowParameterDiagram.timeSimplices_point_GW Q ((chainIndex (C Q)).obj P))

private abbrev chosenLifts {n : SimplexCategory} (F : Fin (n.len + 1) ⥤ C Q) :=
  fun i ↦ (identityLift (F.obj i)).val

private theorem chosenLifts_collapse {n : SimplexCategory}
    (F : Fin (n.len + 1) ⥤ C Q) (i : Fin (n.len + 1)) :
    (chosenLifts Q F i).collapse = 𝟙 _ := (identityLift (F.obj i)).property

private def chosen (P : Simplices (C Q)) : ((diagram Q).obj P).obj P.unop.fst :=
  fun i ↦ ⟨chainFamily P.unop.snd (chosenLifts Q P.unop.snd) i,
    chainFamily_collapse P.unop.snd (chosenLifts Q P.unop.snd)
      (chosenLifts_collapse Q P.unop.snd) i⟩

set_option maxHeartbeats 750000 in
private theorem chosen_reindex {P P' : Simplices (C Q)} (f : P ⟶ P') :
    ((diagram Q).obj P').map f.unop.val (chosen Q P') =
      ((diagram Q).map f).app P.unop.fst (chosen Q P) := by
  obtain ⟨f, rfl⟩ : ∃ g : P'.unop ⟶ P.unop, g.op = f := ⟨f.unop, rfl⟩
  rcases P with ⟨⟨p, u⟩⟩
  rcases P' with ⟨⟨q, v⟩⟩
  rcases f with ⟨j, h⟩
  change q ⟶ p at j
  change (nerve (C Q)).map j v = u at h
  subst u
  funext i
  apply Subtype.ext
  let H := chosenLifts Q v
  let hH := chosenLifts_collapse Q v
  let a := initialArrow j v
  let b := lastArrow j v
  let small := (nerve (C Q)).map j v
  change chainFamily v H (j.unop.toOrderHom i) =
    restrict ((chainFamily small (chosenLifts Q small) i).transport
      ((eqToHom _ ≫ b) : last small ⟶ last v).left)
      (((a ≫ eqToHom _) : first v ⟶ first small).left.fiber.left)
  simp only [eqToHom_refl, Category.id_comp]
  let L := CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)
  have ha : (a ≫ 𝟙 _).left.fiber.left = a.left.fiber.left :=
    congrArg L.map (Category.comp_id a)
  rw [ha, ← chainFamily_reindex v H j.unop i]
  calc
    _ = (restrict (chainFamily small (chosenLifts Q small) i) a.left.fiber.left).transport
        b.left := rfl
    _ = _ := JTGraphTransportRestriction.transport_restrict _ a.left.fiber.left b

private def sectionObj (P : Simplices (C Q)) : ChainParameters Q :=
  ⟨P, op ⟨P.unop.fst, chosen Q P⟩⟩

private def sectionMap {P P' : Simplices (C Q)} (f : P ⟶ P') :
    sectionObj Q P ⟶ sectionObj Q P' :=
  ⟨f, (CategoryOfElements.homMk (F := (diagram Q).obj P') _ _ f.unop.val
    (chosen_reindex Q f)).op⟩

private theorem eqToHom_time {X : SSet.{0}} {a b : X.Elementsᵒᵖ} (h : a = b) :
    (eqToHom h).unop.val = eqToHom (congrArg (fun P ↦ P.unop.fst) h.symm) := by
  cases h
  rfl

private theorem comp_time {X : SSet.{0}} {a b d : X.Elementsᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    (f ≫ g).unop.val = g.unop.val ≫ f.unop.val := rfl

private theorem sectionMap_id (P : Simplices (C Q)) :
    sectionMap Q (𝟙 P) = 𝟙 (sectionObj Q P) := by
  refine Grothendieck.ext _ _ rfl ?_
  rw [eqToHom_refl, Category.id_comp]
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  rw [Grothendieck.id_fiber, eqToHom_time]
  rfl

set_option maxHeartbeats 800000 in
private theorem sectionMap_comp {P P' P'' : Simplices (C Q)} (f : P ⟶ P') (g : P' ⟶ P'') :
    sectionMap Q (f ≫ g) = sectionMap Q f ≫ sectionMap Q g := by
  refine Grothendieck.ext _ _ rfl ?_
  rw [eqToHom_refl, Category.id_comp]
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  have hp : ((fibers Q).map (f ≫ g)).toFunctor.obj (sectionObj Q P).fiber =
      ((fibers Q).map g).toFunctor.obj
        (((fibers Q).map f).toFunctor.obj (sectionObj Q P).fiber) := by
    rw [(fibers Q).map_comp]
    rfl
  change g.unop.val ≫ f.unop.val = (eqToHom hp ≫
    ((fibers Q).map g).toFunctor.map (sectionMap Q f).fiber ≫ (sectionMap Q g).fiber).unop.val
  rw [comp_time, comp_time, eqToHom_time]
  change g.unop.val ≫ f.unop.val = (g.unop.val ≫ f.unop.val) ≫ 𝟙 _
  exact (Category.comp_id _).symm

/-- Each original chain gives a coherent exact family using its original
first and last vertices and its chosen identity graph lifts. -/
def chosenSection : Simplices (C Q) ⥤ ChainParameters Q where
  obj := sectionObj Q
  map := sectionMap Q
  map_id := sectionMap_id Q
  map_comp := sectionMap_comp Q

/-- The section retains the original chain and every original operator. -/
theorem section_forget : chosenSection Q ⋙ Grothendieck.forget (fibers Q) = 𝟭 _ :=
  rfl

/-- The coherent choice of chain parameters induces a weak equivalence. -/
theorem chosenSection_weak : WeakEquivalence (nerveMap (chosenSection Q)) := by
  let p := Grothendieck.forget (fibers Q)
  have : WeakEquivalence (nerveMap p) := projection_weak Q
  apply (weakEquivalence_postcomp_iff _ (nerveMap p)).mp
  change WeakEquivalence (nerveFunctor.map (chosenSection Q ⋙ p).toCatHom)
  rw [section_forget]
  change WeakEquivalence (nerveFunctor.map (𝟙 (Cat.of (Simplices (C Q)))))
  rw [nerveFunctor.map_id]
  infer_instance


/-- The full parameter resolution projects to the actual last comma object. -/
def toOriginal : ChainParameters Q ⥤ C Q :=
  Grothendieck.forget (fibers Q) ⋙ lastVertex (C Q)

/-- This comparison has the weak homotopy type of the original fixed-target comma. -/
theorem toOriginal_weak : WeakEquivalence (nerveMap (toOriginal Q)) := by
  have : WeakEquivalence (nerveMap (Grothendieck.forget (fibers Q))) := projection_weak Q
  have : WeakEquivalence (nerveMap (lastVertex (C Q))) := lastVertex_weak (C Q)
  change WeakEquivalence (nerveMap (Grothendieck.forget (fibers Q)) ≫ nerveMap (lastVertex (C Q)))
  infer_instance

end

end DaggerModels.PartII.JTGraphChainParameterSection
