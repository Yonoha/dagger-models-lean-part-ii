import DaggerModelsPartII.JTGraphVariableTimeIndex
import DaggerModelsPartII.JTGraphTransportRestriction

/-! Original comma arrows transport the full variable-source time index. -/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTGraphVariableTimeTransport

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphVariableTimeIndex JTGraphLiftTransport JTGraphLiftRestriction
open JTGraphParameterTimeResolution (Lifts)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {U V : TargetComma Q} (a : U ⟶ V)

private abbrev post := Over.map a.left.fiber.left
private abbrev total (U : TargetComma Q) := GrothendieckTotalElements.totalDiagram (timeDiagram U)

private def transportLift {P : NativeSlice U} (D : Lifts U P.hom) :
    Lifts V ((post a).obj P).hom :=
  ⟨D.val.transport a.left, congrArg (· ≫ a.left.fiber.left) D.property⟩

private def transportObj (P : (total U).Elements) : (total V).Elements :=
  ⟨((post a).op.obj P.fst.1, P.fst.2), fun i ↦ transportLift a (P.snd i)⟩

private theorem transport_natural {P P' : (total U).Elements} (f : P ⟶ P') :
    (total V).map ((post a).op.map f.val.1, f.val.2) (transportObj a P).snd =
      (transportObj a P').snd := by
  funext i
  apply Subtype.ext
  let j := f.val.2.unop.toOrderHom
  let g := f.val.1.unop.left
  change restrict ((P.snd (j i)).val.transport a.left) g = (P'.snd i).val.transport a.left
  rw [← JTGraphTransportRestriction.transport_restrict _ _ a]
  have h : restrict (P.snd (j i)).val g = (P'.snd i).val :=
    (family_map U f.op i).symm
  exact congrArg (fun D ↦ D.transport a.left) h

private def totalTransport : (total U).Elements ⥤ (total V).Elements where
  obj := transportObj a
  map f := ⟨((post a).op.map f.val.1, f.val.2), transport_natural a f⟩
  map_id P := by
    apply Subtype.ext
    apply Prod.ext
    · exact (post a).op.map_id P.fst.1
    · rfl
  map_comp f g := by
    apply Subtype.ext
    apply Prod.ext
    · exact (post a).op.map_comp f.val.1 g.val.1
    · rfl

/-- Original target transport changes only the target and graph parameters. -/
def transport : Index U ⥤ Index V := (totalTransport a).op

/-- The original native collapse is postcomposed with the actual native arrow. -/
theorem transport_toNative : transport a ⋙ toNative V = toNative U ⋙ post a := rfl

/-- The native source necklace and the time operators are both retained. -/
theorem transport_joint : transport a ⋙ joint V = joint U := rfl

theorem transport_family (P : Index U) (i : Fin (((degree U).obj P).len + 1)) :
    family V ((transport a).obj P) i = (family U P i).transport a.left := rfl

private theorem family_heq_of_values {I A B : Type*} (p : A → B) {s t : B}
    (x : I → {a : A // p a = s}) (y : I → {a : A // p a = t})
    (h : s = t) (hval : ∀ i, (x i).val = (y i).val) : HEq x y := by
  subst t
  exact heq_of_eq (funext fun i ↦ Subtype.ext (hval i))

private theorem elements_functor_ext {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ Type} {L M : D ⥤ F.Elements}
    (hobj : ∀ X, L.obj X = M.obj X)
    (hπ : L ⋙ CategoryOfElements.π F = M ⋙ CategoryOfElements.π F) :
    L = M := by
  refine CategoryTheory.Functor.ext hobj ?_
  intro X Y f
  let π := CategoryOfElements.π F
  apply CategoryOfElements.ext F
  change π.map (L.map f) =
    π.map (eqToHom (hobj X) ≫ M.map f ≫ eqToHom (hobj Y).symm)
  rw [π.map_comp, π.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hπ f

private abbrev sourceCode : TargetComma Q ⥤ NecklaceCode :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

variable {Z : TargetComma Q} (b : V ⟶ Z)

set_option maxHeartbeats 400000 in
private theorem post_comp : post (a ≫ b) = post a ⋙ post b := by
  have h := (sourceCode (Q := Q)).map_comp a b
  change (a ≫ b).left.fiber.left = a.left.fiber.left ≫ b.left.fiber.left at h
  exact (congrArg Over.map h).trans (Over.mapComp_eq _ _)

private theorem total_base_comp :
    totalTransport (a ≫ b) ⋙ CategoryOfElements.π (total Z) =
      (totalTransport a ⋙ totalTransport b) ⋙ CategoryOfElements.π (total Z) := by
  let S := SimplexCategoryᵒᵖ
  change CategoryOfElements.π (total U) ⋙ (post (a ≫ b)).op.prod (𝟭 S) =
    CategoryOfElements.π (total U) ⋙ (post a).op.prod (𝟭 S) ⋙ (post b).op.prod (𝟭 S)
  rw [post_comp a b]
  rfl

set_option maxHeartbeats 400000 in
private theorem total_obj_comp (P : (total U).Elements) :
    (totalTransport (a ≫ b)).obj P = (totalTransport a ⋙ totalTransport b).obj P := by
  apply Sigma.ext
  · exact Functor.congr_obj (total_base_comp a b) P
  · let f := P.fst.1.unop.hom
    have hn := (sourceCode (Q := Q)).map_comp a b
    change (a ≫ b).left.fiber.left = a.left.fiber.left ≫ b.left.fiber.left at hn
    have hc : f ≫ (a ≫ b).left.fiber.left =
        (f ≫ a.left.fiber.left) ≫ b.left.fiber.left :=
      (congrArg (f ≫ ·) hn).trans (Category.assoc _ _ _).symm
    exact family_heq_of_values GraphLift.collapse
      ((totalTransport (a ≫ b)).obj P).snd
      ((totalTransport a ⋙ totalTransport b).obj P).snd hc
      (fun i ↦ (GraphLift.transport_comp (P.snd i).val a.left b.left).symm)


set_option maxHeartbeats 400000 in
private theorem post_id (U : TargetComma Q) : post (𝟙 U) = 𝟭 (NativeSlice U) := by
  exact (congrArg Over.map ((sourceCode (Q := Q)).map_id U)).trans (Over.mapId_eq _)

private theorem total_base_id (U : TargetComma Q) :
    totalTransport (𝟙 U) ⋙ CategoryOfElements.π (total U) =
      𝟭 ((total U).Elements) ⋙ CategoryOfElements.π (total U) := by
  let S := SimplexCategoryᵒᵖ
  change CategoryOfElements.π (total U) ⋙ (post (𝟙 U)).op.prod (𝟭 S) =
    CategoryOfElements.π (total U)
  exact congrArg (fun F : NativeSlice U ⥤ NativeSlice U ↦
    CategoryOfElements.π (total U) ⋙ F.op.prod (𝟭 S)) (post_id U)

set_option maxHeartbeats 400000 in
private theorem total_obj_id (U : TargetComma Q) (P : (total U).Elements) :
    (totalTransport (𝟙 U)).obj P = (𝟭 ((total U).Elements)).obj P := by
  apply Sigma.ext
  · exact Functor.congr_obj (total_base_id U) P
  · let f := P.fst.1.unop.hom
    have hn := (sourceCode (Q := Q)).map_id U
    have hc : f ≫ (sourceCode (Q := Q)).map (𝟙 U) = f :=
      (congrArg (f ≫ ·) hn).trans (Category.comp_id _)
    exact family_heq_of_values GraphLift.collapse
      ((totalTransport (𝟙 U)).obj P).snd P.snd hc
      (fun i ↦ GraphLift.transport_id (P.snd i).val)

/-- The original identity arrow acts by the identity on the exact time index. -/
theorem transport_id (U : TargetComma Q) : transport (𝟙 U) = 𝟭 (Index U) :=
  congrArg Functor.op (elements_functor_ext (total_obj_id U) (total_base_id U))

/-- Transport of all exact parameters respects composition of original target arrows. -/
theorem transport_comp : transport (a ≫ b) = transport a ⋙ transport b :=
  congrArg Functor.op (elements_functor_ext (total_obj_comp a b) (total_base_comp a b))

/-- Transport of the full cylinder resolution preserves every internal necklace. -/
def transportResolution : Resolution U ⥤ Resolution V :=
  Grothendieck.pre (joint V ⋙ JTGraphCylinderFiberDiagram.diagram) (transport a)

private def preOver {I K : Type} [SmallCategory I] [SmallCategory K]
    (D₀ : I ⥤ Cat.{0, 0}) (D : K ⥤ Cat.{0, 0}) (F : I ⥤ K) (e : D₀ = F ⋙ D) :
    Grothendieck D₀ ⥤ Grothendieck D := by
  subst D₀
  exact Grothendieck.pre D F

private theorem preOver_congr {I K : Type} [SmallCategory I] [SmallCategory K]
    (D₀ : I ⥤ Cat.{0, 0}) (D : K ⥤ Cat.{0, 0}) {F F' : I ⥤ K}
    (h : F = F') (e : D₀ = F ⋙ D) (e' : D₀ = F' ⋙ D) :
    preOver D₀ D F e = preOver D₀ D F' e' := by
  subst F'
  rfl

private theorem preOver_comp {I J K : Type} [SmallCategory I] [SmallCategory J]
    [SmallCategory K] (D₀ : I ⥤ Cat.{0, 0}) (D₁ : J ⥤ Cat.{0, 0})
    (D : K ⥤ Cat.{0, 0}) (F : I ⥤ J) (G : J ⥤ K)
    (e₀ : D₀ = F ⋙ D₁) (e₁ : D₁ = G ⋙ D) (e : D₀ = (F ⋙ G) ⋙ D) :
    preOver D₀ D (F ⋙ G) e = preOver D₀ D₁ F e₀ ⋙ preOver D₁ D G e₁ := by
  subst D₁
  subst D₀
  exact Grothendieck.pre_comp D G F

private theorem preOver_id {I : Type} [SmallCategory I] (D : I ⥤ Cat.{0, 0})
    (e : D = 𝟭 I ⋙ D) : preOver D D (𝟭 I) e = 𝟭 (Grothendieck D) :=
  Grothendieck.pre_id D

private abbrev cylinderDiagram (U : TargetComma Q) :=
  joint U ⋙ JTGraphCylinderFiberDiagram.diagram

set_option maxHeartbeats 650000 in
/-- The identity transport keeps every native source, time, and internal necklace. -/
theorem transportResolution_id (U : TargetComma Q) :
    transportResolution (𝟙 U) = 𝟭 (Resolution U) := by
  let D := cylinderDiagram U
  let G := transport (𝟙 U)
  let h : D = G ⋙ D := (congrArg (· ⋙ JTGraphCylinderFiberDiagram.diagram)
    (transport_joint (𝟙 U))).symm
  have h' : transportResolution (𝟙 U) = preOver D D G h := by
    have hp : h = rfl := Subsingleton.elim _ _
    rw [hp]
    rfl
  refine h'.trans ?_
  exact (preOver_congr D D (transport_id U) h (Functor.id_comp D).symm).trans
    (preOver_id D (Functor.id_comp D).symm)

set_option maxHeartbeats 180000 in
/-- Transport of the entire resolution respects composition, including all internal necklaces. -/
theorem transportResolution_comp : transportResolution (a ≫ b) =
    transportResolution a ⋙ transportResolution b :=
  (preOver_congr (cylinderDiagram U) (cylinderDiagram Z) (transport_comp a b) rfl rfl).trans
    (preOver_comp (cylinderDiagram U) (cylinderDiagram V) (cylinderDiagram Z)
      (transport a) (transport b) rfl rfl rfl)

/-- All original variable-source resolutions form a diagram under postcomposition. -/
def resolutionDiagram (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)) :
    TargetComma Q ⥤ Cat.{0, 0} where
  obj U := Cat.of (Resolution U)
  map f := (transportResolution f).toCatHom
  map_id U := by
    apply Cat.Hom.ext
    exact transportResolution_id U
  map_comp f g := by
    apply Cat.Hom.ext
    exact transportResolution_comp f g

/-- Original transport is a Kan weak map of the simultaneous resolutions. -/
theorem transportResolution_weak : WeakEquivalence (nerveMap (transportResolution a)) := by
  let p := pointMap (nerve (Resolution V))
  haveI : WeakEquivalence p := (weakEquivalence_iff_GW _).mpr (resolution_point_GW V)
  apply (weakEquivalence_postcomp_iff (nerveMap (transportResolution a)) p).mp
  rw [pointIsTerminal.hom_ext (nerveMap (transportResolution a) ≫ p) (pointMap _)]
  exact (weakEquivalence_iff_GW _).mpr (resolution_point_GW U)

end
end DaggerModels.PartII.JTGraphVariableTimeTransport
