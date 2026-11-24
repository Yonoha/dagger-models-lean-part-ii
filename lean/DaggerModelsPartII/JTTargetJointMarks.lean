import ChosenNecklaceTargetJoints
import DaggerModelsPartII.DecoratedCylinderNecklacePresentation
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Joint marks for arbitrary native targets

A mark chooses one source vertex over each joint of the target. All such
choices form a poset, with transport along every actual over-target arrow.
For each object there are choices consisting entirely of source joints.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra DaggerModels
open DaggerChosenRigidificationNecklace DaggerSSetGluing DaggerOriginalProductGadget
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTTargetJointMarks

open NecklaceCode
open DaggerNerveHomotopy
open DaggerOriginalFlagFlankification (nerveDiscreteIso)

noncomputable section

/-- The actual joints of the fixed native target. -/
abbrev Joint (U : NecklaceCode) := {j : Fin (U.len + 1) // j ∈ U.joints}

/-- Simultaneous marks on the full native map, ordered coordinatewise. -/
@[ext]
structure Marks {T U : NecklaceCode} (f : Hom.{0} T U) where
  vertex : ∀ j : Joint U, {v : Fin (T.len + 1) // orderMap f.map v = j.val}

instance {T U : NecklaceCode} {f : Hom.{0} T U} :
    CoeFun (Marks f) (fun _ ↦ ∀ j : Joint U, {v : Fin (T.len + 1) // orderMap f.map v = j.val}) :=
  ⟨Marks.vertex⟩

instance {T U : NecklaceCode} {f : Hom.{0} T U} : Preorder (Marks f) :=
  Preorder.lift Marks.vertex

/-- Marks at distinct ordered target joints are strictly ordered in the source. -/
theorem marks_ordered {T U : NecklaceCode} {f : Hom.{0} T U} (m : Marks f)
    {j k : Joint U} (h : j.val < k.val) : (m j).val < (m k).val := by
  by_contra! h'
  have hm := (orderMap f.map).monotone h'
  rw [(m k).property, (m j).property] at hm
  exact (not_le_of_gt h) hm

/-- Each original over-target map admits marks that are all actual source joints. -/
theorem exists_joint_marks {T U : NecklaceCode} (f : Hom.{0} T U) :
    ∃ m : Marks f, ∀ j, (m j).val ∈ T.joints := by
  classical
  have h (j : Joint U) : ∃ v ∈ T.joints, orderMap f.map v = j.val :=
    Finset.mem_image.mp (joints_subset_image f j.property)
  choose v hv hw using h
  exact ⟨⟨fun j ↦ ⟨v j, hw j⟩⟩, hv⟩

private def choices {T U : NecklaceCode} (f : Hom.{0} T U) (j : Joint U) :
    Finset (Fin (T.len + 1)) :=
  Finset.univ.filter (fun v ↦ orderMap f.map v = j.val)

private theorem choices_nonempty {T U : NecklaceCode} (f : Hom.{0} T U) (j : Joint U) :
    (choices f j).Nonempty := by
  obtain ⟨m, _⟩ := exists_joint_marks f
  exact ⟨(m j).val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (m j).property⟩⟩

/-- The greatest source vertex over each target joint. -/
def greatest {T U : NecklaceCode} (f : Hom.{0} T U) : Marks f :=
  ⟨fun j ↦ ⟨(choices f j).max' (choices_nonempty f j),
    (Finset.mem_filter.mp ((choices f j).max'_mem (choices_nonempty f j))).2⟩⟩

theorem le_greatest {T U : NecklaceCode} {f : Hom.{0} T U} (m : Marks f) :
    m ≤ greatest f :=
  fun j ↦ (choices f j).le_max' (m j).val
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (m j).property⟩)

/-- The least source vertex over each target joint. -/
def least {T U : NecklaceCode} (f : Hom.{0} T U) : Marks f :=
  ⟨fun j ↦ ⟨(choices f j).min' (choices_nonempty f j),
    (Finset.mem_filter.mp ((choices f j).min'_mem (choices_nonempty f j))).2⟩⟩

/-- The preimage of the upper interval starting at a target joint. -/
theorem least_le_iff {T U : NecklaceCode} (f : Hom.{0} T U) (j : Joint U)
    (v : Fin (T.len + 1)) :
    (least f j).val ≤ v ↔ j.val ≤ orderMap f.map v := by
  constructor
  · intro h
    simpa only [(least f j).property] using (orderMap f.map).monotone h
  · intro h
    by_contra! hv
    have hm := (orderMap f.map).monotone hv.le
    rw [(least f j).property] at hm
    have hmem : v ∈ choices f j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm hm h⟩
    exact (not_le_of_gt hv) ((choices f j).min'_le v hmem)

/-- The preimage of the lower interval ending at a target joint. -/
theorem le_greatest_iff {T U : NecklaceCode} (f : Hom.{0} T U) (j : Joint U)
    (v : Fin (T.len + 1)) :
    v ≤ (greatest f j).val ↔ orderMap f.map v ≤ j.val := by
  constructor
  · intro h
    simpa only [(greatest f j).property] using (orderMap f.map).monotone h
  · intro h
    by_contra! hv
    have hm := (orderMap f.map).monotone hv.le
    rw [(greatest f j).property] at hm
    have hmem : v ∈ choices f j :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_antisymm h hm⟩
    exact (not_le_of_gt hv) ((choices f j).le_max' v hmem)

/-- The choice category has a terminal object for every original native map. -/
def greatestIsTerminal {T U : NecklaceCode} (f : Hom.{0} T U) :
    IsTerminal (greatest f) :=
  IsTerminal.ofUniqueHom (fun m ↦ homOfLE (le_greatest m)) (fun _ _ ↦ Subsingleton.elim _ _)

private def transport {T T' U : NecklaceCode} {f : T ⟶ U} {f' : T' ⟶ U}
    (g : T ⟶ T') (h : g ≫ f' = f) (m : Marks f) : Marks f' :=
  ⟨fun j ↦ ⟨orderMap g.map (m j).val, by
    rw [← orderMap_comp_apply g.map f'.map]
    exact (congrArg (fun k : T ⟶ U ↦ orderMap k.map (m j).val) h).trans (m j).property⟩⟩

private theorem transport_monotone {T T' U : NecklaceCode} {f : T ⟶ U} {f' : T' ⟶ U}
    (g : T ⟶ T') (h : g ≫ f' = f) : Monotone (transport g h) :=
  fun _ _ hm j ↦ (orderMap g.map).monotone (hm j)

private theorem transport_id {T U : NecklaceCode} {f : T ⟶ U}
    (h : 𝟙 T ≫ f = f) (m : Marks f) : transport (𝟙 T) h m = m := by
  apply Marks.ext
  funext j
  apply Subtype.ext
  change (T.verticesEquiv (T.verticesEquiv.symm (ULift.up (m j).val))).down = (m j).val
  rw [T.verticesEquiv.apply_symm_apply]

private theorem transport_comp {T T' T'' U : NecklaceCode}
    {f : T ⟶ U} {f' : T' ⟶ U} {f'' : T'' ⟶ U}
    (g : T ⟶ T') (g' : T' ⟶ T'') (h : g ≫ f' = f) (h' : g' ≫ f'' = f')
    (h'' : (g ≫ g') ≫ f'' = f) (m : Marks f) :
    transport (g ≫ g') h'' m = transport g' h' (transport g h m) := by
  apply Marks.ext
  funext j
  apply Subtype.ext
  exact orderMap_comp_apply g.map g'.map (m j).val

private theorem preorder_functor_ext {A B : Type} [SmallCategory A] [Preorder B]
    {F G : A ⥤ B} (h : ∀ a, F.obj a = G.obj a) : F = G := by
  refine CategoryTheory.Functor.ext h ?_
  intros
  apply Subsingleton.elim

/-- Choices of all target-joint marks vary along arbitrary native over-target arrows. -/
def nativeDiagram (U : NecklaceCode) : Over U ⥤ Cat.{0,0} where
  obj P := Cat.of (Marks P.hom)
  map g := (transport_monotone g.left (Over.w g)).functor.toCatHom
  map_id P := by
    apply Cat.Hom.ext
    refine preorder_functor_ext (A := Marks P.hom) (B := Marks P.hom) ?_
    exact transport_id (Over.w (𝟙 P))
  map_comp {P _ P''} f g := by
    apply Cat.Hom.ext
    refine preorder_functor_ext (A := Marks P.hom) (B := Marks P''.hom) ?_
    exact transport_comp f.left g.left (Over.w f) (Over.w g) (Over.w (f ≫ g))

/-- Each full mark fiber has weakly contractible nerve. -/
theorem marks_point_GW {T U : NecklaceCode} (f : Hom.{0} T U) :
    GW (pointMap (nerve (Marks f))) := by
  let F : Marks f ⥤ Discrete PUnit := (Functor.const _).obj (Discrete.mk PUnit.unit)
  let G : Discrete PUnit ⥤ Marks f := (Functor.const _).obj (greatest f)
  let η : 𝟭 (Marks f) ⟶ F ⋙ G :=
    { app := (greatestIsTerminal f).from
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  let ε : G ⋙ F ⟶ 𝟭 (Discrete PUnit) :=
    { app := fun _ ↦ eqToHom (Subsingleton.elim _ _)
      naturality := fun {_ _} _ ↦ Subsingleton.elim _ _ }
  have : WeakEquivalence (nerveMap F) :=
    (weakEquivalence_iff_GW _).mpr
      (nerveMap_geometricW F G
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨η⟩))
        (Relation.EqvGen.rel _ _ ⟨ε⟩))
  have h : nerveMap F ≫ (nerveDiscreteIso PUnit).hom =
      pointMap (nerve (Marks f)) := pointIsTerminal.hom_ext _ _
  apply (weakEquivalence_iff_GW _).mp
  rw [← h]
  infer_instance

open DecoratedCylinderNecklacePresentation (underDiagram toTarget)

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable (W : Source) (x y : Vertex W)
variable (Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y))

local notation "C" => CostructuredArrow (toTarget W x y) Q

private abbrev sourceProjection : C ⥤ NecklaceCode :=
  CostructuredArrow.proj (toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (underDiagram W x y)

private def toNativeOver : C ⥤ Over Q.code :=
  Over.lift (sourceProjection W x y Q)
    { app := fun P ↦ P.hom.hom
      naturality := by
        intro P P' f
        change f.left.fiber.left ≫ P'.hom.hom = P.hom.hom ≫ 𝟙 Q.code
        rw [Category.comp_id]
        exact congrArg (fun g : (toTarget W x y).obj P.left ⟶ Q ↦ g.hom)
          (CostructuredArrow.w f) }

/-- Extract the full original native map over the fixed target necklace. -/
abbrev nativeOver : C ⥤ Over Q.code :=
  toNativeOver W x y Q

/-- All simultaneous choices over the original fixed-target comma. -/
def diagram : C ⥤ Cat.{0,0} :=
  toNativeOver W x y Q ⋙ nativeDiagram Q.code

/-- Each fiber of the joint-mark diagram on the actual comma has weakly contractible nerve. -/
theorem diagram_point_GW (P : C) :
    GW (pointMap (nerve ((diagram W x y Q).obj P))) :=
  marks_point_GW P.hom.hom

/-- There is at most one arrow between two choices in a fixed fiber. -/
theorem diagram_thin (P : C) : Quiver.IsThin ((diagram W x y Q).obj P) := by
  change Quiver.IsThin (Marks P.hom.hom)
  infer_instance

/-- The actual fixed-target comma retains its weak homotopy type after adding all joint marks. -/
theorem projection_weak :
    WeakEquivalence (nerveMap (Grothendieck.forget (diagram W x y Q))) :=
  GrothendieckContractibleFibers.projection_weak (diagram W x y Q)
    (diagram_point_GW W x y Q)

end

end DaggerModels.PartII.JTTargetJointMarks
