import DaggerModelsPartII.JTGraphMultiBeadIdentityLift
import DaggerModelsPartII.JTHomElementsTargetWeak
import DaggerModelsPartII.JTGraphParameterRelative
import DaggerModelsPartII.JTGraphCylinderSpanProjection
import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Exact unreduced lifts of the full internal traversal

The native coordinate is its actual augmented map. Time choices move by
native precomposition and original cylinder postcomposition.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace
open DaggerSSetGluing DaggerOriginalProductGadget HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace DaggerModels.PartII.JTInternalTraversalLifts

open JTNecklaceEndpointCylinder
open NecklaceCylinderAugmentation (augmentation augmentation_native_natural augmentation_parameter_natural)
open NecklaceCylinderJointDiagram (cylinderUnder)

noncomputable section

private abbrev J := GroupoidSimplex.parameter

/-- All exact time maps for one entire reduced traversal, with its native
coordinate determined by the original augmentation. -/
abbrev Lift {X : SSet.{0}} {T : NecklaceCode} {k : SimplexCategory} (g : X ⟶ (value T).obj k) :=
  {s : X ⟶ J.obj k // lift (g ≫ augmentation T k) s ≫ (cylinder T).app k = g}

/-- The actual traversal into the unreduced prism, including its entire time map. -/
def intoPrism {X : SSet.{0}} {T : NecklaceCode} {k : SimplexCategory}
    {g : X ⟶ (value T).obj k} (s : Lift g) : X ⟶ T.toSSet ⊗ J.obj k :=
  lift (g ≫ augmentation T k) s.val

theorem intoPrism_cylinder {X : SSet.{0}} {T : NecklaceCode} {k : SimplexCategory}
    {g : X ⟶ (value T).obj k} (s : Lift g) :
    intoPrism s ≫ (cylinder T).app k = g := s.property

/-- Every entire native necklace admits an exact lift, with all shared
joint coordinates already identified. -/
theorem nonempty_of_necklace {S T : NecklaceCode} {k : SimplexCategory}
    (g : S.toSSet ⟶ (value T).obj k) : Nonempty (Lift g) := by
  let P : NecklacesOver ((value T).obj k)
      (g.app (op ⦋0⦌) S.first) (g.app (op ⦋0⦌) S.last) :=
    ⟨S, g, rfl, rfl⟩
  obtain ⟨s, hs⟩ := JTGraphMultiBeadIdentityLift.exists_parameter P
  exact ⟨⟨s, hs⟩⟩

private abbrev joint {T T' : NecklaceCode} {k k' : SimplexCategory}
    (f : T ⟶ T') (j : k ⟶ k') : (value T).obj k ⟶ (value T').obj k' :=
  (cylinderUnder.map (show (T, k) ⟶ (T', k') from (f, j))).right

private theorem joint_cylinder {T T' : NecklaceCode} {k k' : SimplexCategory}
    (f : T ⟶ T') (j : k ⟶ k') :
    (cylinder T).app k ≫ joint f j =
      (f.map ⊗ₘ J.map j) ≫ (cylinder T').app k' := by
  change (cylinder T).app k ≫ (nativeMap f k ≫ (value T').map j) = _
  rw [← Category.assoc, nativeMap_cylinder, Category.assoc, ← (cylinder T').naturality j]
  change (f.map ⊗ₘ 𝟙 (J.obj k)) ≫
    (𝟙 T'.toSSet ⊗ₘ J.map j) ≫ (cylinder T').app k' = _
  rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]

private theorem joint_augmentation {T T' : NecklaceCode} {k k' : SimplexCategory}
    (f : T ⟶ T') (j : k ⟶ k') :
    joint f j ≫ augmentation T' k' = augmentation T k ≫ f.map :=
  NecklaceCylinderJointDiagram.augmentation.naturality
    (show (T, k) ⟶ (T', k') from (f, j))

private theorem pastePrisms {X Y T T' K K' V V' : SSet.{0}}
    (a : X ⟶ Y) (b : Y ⟶ T) (s : Y ⟶ K) (f : T ⟶ T') (j : K ⟶ K')
    (c : T ⊗ K ⟶ V) (c' : T' ⊗ K' ⟶ V') (d : V ⟶ V')
    (g : Y ⟶ V) (hg : lift b s ≫ c = g)
    (hd : c ≫ d = (f ⊗ₘ j) ≫ c') :
    lift (a ≫ b ≫ f) (a ≫ s ≫ j) ≫ c' = a ≫ g ≫ d := by
  have hl : (a ≫ lift b s) ≫ (f ⊗ₘ j) = lift (a ≫ b ≫ f) (a ≫ s ≫ j) := by
    rw [Category.assoc, lift_map, comp_lift]
  rw [← hl, Category.assoc, Category.assoc, ← hd, ← Category.assoc (lift b s), hg]

/-- A full lift can be transported under both actual operators at once. -/
def mapLift {X Y : SSet.{0}} {T T' : NecklaceCode} {k k' : SimplexCategory}
    {g : Y ⟶ (value T).obj k} {g' : X ⟶ (value T').obj k'}
    (a : X ⟶ Y) (f : T ⟶ T') (j : k ⟶ k')
    (h : g' = a ≫ g ≫ joint f j) (s : Lift g) : Lift g' := by
  refine ⟨a ≫ s.val ≫ J.map j, ?_⟩
  have hb : g' ≫ augmentation T' k' = a ≫ (g ≫ augmentation T k) ≫ f.map := by
    rw [h, Category.assoc, Category.assoc, joint_augmentation]
    simp only [Category.assoc]
  rw [hb]
  exact (pastePrisms a (g ≫ augmentation T k) s.val f.map (J.map j) ((cylinder T).app k)
    ((cylinder T').app k') (joint f j) g s.property (joint_cylinder f j)).trans h.symm

theorem mapLift_prism {X Y : SSet.{0}} {T T' : NecklaceCode} {k k' : SimplexCategory}
    {g : Y ⟶ (value T).obj k} {g' : X ⟶ (value T').obj k'}
    (a : X ⟶ Y) (f : T ⟶ T') (j : k ⟶ k')
    (h : g' = a ≫ g ≫ joint f j) (s : Lift g) :
    intoPrism (mapLift a f j h s) = a ≫ intoPrism s ≫ (f.map ⊗ₘ J.map j) := by
  have hb : g' ≫ augmentation T' k' = a ≫ (g ≫ augmentation T k) ≫ f.map := by
    rw [h, Category.assoc, Category.assoc, joint_augmentation]
    simp only [Category.assoc]
  change lift (g' ≫ augmentation T' k') (a ≫ s.val ≫ J.map j) = _
  rw [hb, intoPrism, lift_map, comp_lift]

section Presentation

private theorem pasteEvaluation {D : Type} [SmallCategory D] {E : Type*} [Category* E]
    {F G : D ⥤ E} (t : F ⟶ G) {B A C D₀ : D}
    (u : B ⟶ A) (a : A ⟶ C) (v : C ⟶ D₀) (b : B ⟶ D₀) (h : u ≫ a ≫ v = b) :
    t.app B ≫ G.map b = F.map u ≫ (t.app A ≫ G.map a) ≫ G.map v := by
  rw [← h, Functor.map_comp, Functor.map_comp, ← Category.assoc (t.app B), ← t.naturality]
  simp only [Category.assoc]

variable {A : Type} [SmallCategory A]
variable (N : A ⥤ NecklaceCode) (time : A ⥤ SimplexCategory)

/-- The actual reduced time cylinders retain both original operators. -/
abbrev cylinders := (N.prod' time) ⋙ cylinderUnder

abbrev Presentation := BoundaryNecklaceComma.Presentation (cylinders N time)

/-- Choose a whole original internal necklace at the source of an actual
presentation arrow, and use the target cylinder for all its coordinates. -/
abbrev ArrowIndex := (Functor.hom (Presentation N time)).Elements

private abbrev native := BoundaryNecklaceComma.sourceCode (cylinders N time)
private abbrev base := Grothendieck.forget (BoundaryNecklaceComma.fiberDiagram (cylinders N time))
private abbrev atTarget (a : ArrowIndex N time) := a.fst.2.base

/-- Traverse an entire source necklace in the actual reduced target cylinder. -/
def traversal (a : ArrowIndex N time) :
    ((native N time).obj a.fst.1.unop).toSSet ⟶ ((value (N.obj (atTarget N time a))).obj
      (time.obj (atTarget N time a))) :=
  (a.fst.1.unop.fiber.hom ≫ (cylinders N time).map a.snd.base).right

private theorem traversal_map {a b : ArrowIndex N time} (f : a ⟶ b) :
    traversal N time b = ((native N time).map f.val.1.unop).map ≫ traversal N time a ≫
      joint (N.map f.val.2.base) (time.map f.val.2.base) := by
  exact congrArg (fun g ↦ g.right) (pasteEvaluation
    (BoundaryNecklaceComma.evaluation (cylinders N time))
    f.val.1.unop a.snd f.val.2 b.snd f.property)

private abbrev ambient : ArrowIndex N time ⥤ Type :=
  CategoryOfElements.π (Functor.hom (Presentation N time)) ⋙
    (((native N time) ⋙ NecklaceCode.simplicialFunctor).op.prod
      ((base N time) ⋙ time ⋙ J)) ⋙ Functor.hom SSet.{0}

/-- Exact unreduced time lifts form a subfunctor of the mixed mapping diagram. -/
def liftSubfunctor : Subfunctor (ambient N time) where
  obj a := fun s ↦ lift (traversal N time a ≫ augmentation _ _) s ≫
    (cylinder _).app _ = traversal N time a
  map f _ hs :=
    (mapLift (((native N time).map f.val.1.unop).map) (N.map f.val.2.base)
      (time.map f.val.2.base) (traversal_map N time f) ⟨_, hs⟩).property

abbrev lifts := (liftSubfunctor N time).toFunctor

/-- The exact prism traversal uses both operators of every original factorization. -/
theorem prism_map {a b : ArrowIndex N time} (f : a ⟶ b)
    (s : (lifts N time).obj a) :
    intoPrism ((lifts N time).map f s) =
      ((native N time).map f.val.1.unop).map ≫ intoPrism s ≫
        ((N.map f.val.2.base).map ⊗ₘ J.map (time.map f.val.2.base)) :=
  mapLift_prism _ _ _ (traversal_map N time f) s

/-- Full-necklace lifts exist for every actual presentation arrow. -/
theorem lifts_nonempty (a : ArrowIndex N time) : Nonempty ((lifts N time).obj a) :=
  nonempty_of_necklace (traversal N time a)

open DaggerOriginalCodiscreteNerveInjective (codiscreteNerve)
open JTGraphParameterInterpolation (interpolateBy coord_interpolateBy)

/-- Retain all finite time families of exact lifts, over all original factorizations. -/
abbrev spaces := lifts N time ⋙ codiscreteNerve

private abbrev choices (a : ArrowIndex N time) := (spaces N time).obj a
private abbrev sourceSet (a : ArrowIndex N time) := ((native N time).obj a.fst.1.unop).toSSet

private abbrev atVertex (a : ArrowIndex N time) (v : (choices N time a).obj (op ⦋0⦌)) :
    (lifts N time).obj a := (v.obj 0).as

/-- The universal interpolated lift, including all original shared joints. -/
def universalTime (a : ArrowIndex N time) :
    sourceSet N time a ⊗ choices N time a ⟶ J.obj (time.obj (atTarget N time a)) :=
  interpolateBy (fun v ↦ (atVertex N time a v).val)

/-- A whole time family simultaneously lifts the entire original traversal. -/
def universalPrism (a : ArrowIndex N time) :
    sourceSet N time a ⊗ choices N time a ⟶
      (N.obj (atTarget N time a)).toSSet ⊗ J.obj (time.obj (atTarget N time a)) :=
  lift (fst _ _ ≫ traversal N time a ≫ augmentation _ _) (universalTime N time a)

theorem universalPrism_cylinder (a : ArrowIndex N time) :
    universalPrism N time a ≫ (cylinder (N.obj (atTarget N time a))).app
        (time.obj (atTarget N time a)) =
      fst _ _ ≫ traversal N time a := by
  let s := (lifts_nonempty N time a).some
  let g := traversal N time a
  unfold universalPrism
  refine JTGraphParameterFiber.fiber_of_coordinates _ _ (g ≫ augmentation _ _)
    (fun v ↦ (atVertex N time a v).val) s.val g (fun v ↦ (atVertex N time a v).property)
    s.property (universalTime N time a) ?_
  intro q z i
  exact ⟨(choices N time a).map (SimplexCategory.const ⦋0⦌ q.unop i).op z.2,
    coord_interpolateBy _ q z i⟩

private theorem interpolateBy_mixed {X X' Y Y' : SSet.{0}} {k k' : SimplexCategory}
    (u : X' ⟶ X) (v : Y ⟶ Y') (j : k ⟶ k')
    (s : Y.obj (op ⦋0⦌) → (X ⟶ J.obj k))
    (t : Y'.obj (op ⦋0⦌) → (X' ⟶ J.obj k'))
    (h : ∀ y, u ≫ s y ≫ J.map j = t (v.app (op ⦋0⦌) y)) :
    (u ▷ Y) ≫ interpolateBy s ≫ J.map j = (X' ◁ v) ≫ interpolateBy t := by
  apply JTCodiscreteParameterPairing.hom_ext
  intro q z i
  let w := (SimplexCategory.const ⦋0⦌ q.unop i).op
  change JTCodiscreteParameterPairing.coord k' q ((J.map j).app q ((interpolateBy s).app q (u.app q z.1, z.2))) i =
    JTCodiscreteParameterPairing.coord k' q ((interpolateBy t).app q (z.1, v.app q z.2)) i
  rw [JTCodiscreteParameterPairing.coord_map, coord_interpolateBy, coord_interpolateBy]
  change j.toOrderHom
      (JTCodiscreteParameterPairing.coord k q ((s (Y.map w z.2)).app q (u.app q z.1)) i) =
    JTCodiscreteParameterPairing.coord k' q ((t (Y'.map w (v.app q z.2))).app q z.1) i
  rw [← JTCodiscreteParameterPairing.coord_map]
  have hv : Y'.map w (v.app q z.2) = v.app (op ⦋0⦌) (Y.map w z.2) :=
    (congrFun (v.naturality w) z.2).symm
  rw [hv]
  exact congrArg (fun e ↦ JTCodiscreteParameterPairing.coord k' q (e.app q z.1) i)
    (h (Y.map w z.2))

/-- The universal time family respects the mixed operators on the entire
unreduced traversal and all its time lifts. -/
theorem universalTime_map {a b : ArrowIndex N time} (f : a ⟶ b) :
    ((((native N time).map f.val.1.unop).map) ▷ choices N time a) ≫
        universalTime N time a ≫ J.map (time.map f.val.2.base) =
      (sourceSet N time b ◁ (spaces N time).map f) ≫ universalTime N time b := by
  apply interpolateBy_mixed
  intro y
  rfl

/-- The whole lifted prism commutes with every mixed factorization arrow. -/
theorem universalPrism_map {a b : ArrowIndex N time} (f : a ⟶ b) :
    ((((native N time).map f.val.1.unop).map) ▷ choices N time a) ≫
        universalPrism N time a ≫ ((N.map f.val.2.base).map ⊗ₘ J.map (time.map f.val.2.base)) =
      (sourceSet N time b ◁ (spaces N time).map f) ≫ universalPrism N time b := by
  have hh := traversal_map N time f
  have hz := joint_augmentation (N.map f.val.2.base) (time.map f.val.2.base)
  have h :
      traversal N time b ≫ augmentation (N.obj (atTarget N time b)) (time.obj (atTarget N time b)) =
        ((native N time).map f.val.1.unop).map ≫ traversal N time a ≫
          augmentation (N.obj (atTarget N time a)) (time.obj (atTarget N time a)) ≫
          (N.map f.val.2.base).map := by
    rw [hh, Category.assoc, Category.assoc, hz]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [universalPrism, Category.assoc, tensorHom_fst, lift_fst, lift_fst_assoc,
      whiskerRight_fst_assoc, whiskerLeft_fst_assoc, h]
  · simpa only [universalPrism, Category.assoc, tensorHom_snd, lift_snd_assoc] using
      universalTime_map N time f

/-- All exact lift families over an arrow form a trivially fibrant time space. -/
theorem spaces_toPoint_trivialFibration (a : ArrowIndex N time) :
    trivialFibrations SSet.{0} (pointMap ((spaces N time).obj a)) := by
  letI := lifts_nonempty N time a
  exact DaggerOriginalCodiscreteNerveInjective.toTerminal_trivialFibration _ pointIsTerminal

abbrev TimePresentation :=
  Grothendieck (spaces N time ⋙ SimplicialResolutionFunctor.elementsOpposite)

private theorem choiceElements_point_GW (a : ArrowIndex N time) :
    GW (pointMap (nerve (choices N time a).Elementsᵒᵖ)) := by
  let X := choices N time a
  let r := SimplicialResolutionFunctor.augmentation.app X
  let e := SimplicialResolutionFunctor.elementsProjection.app X
  letI := SimplicialResolutionFunctor.augmentation_weak X
  letI := SimplicialResolutionFunctor.elementsProjection_weak X
  letI := ((mem_trivialFibrations_iff _).mp (spaces_toPoint_trivialFibration N time a)).2
  apply (weakEquivalence_iff_GW _).mp
  apply (weakEquivalence_precomp_iff e _).mp
  rw [pointIsTerminal.hom_ext (e ≫ pointMap (nerve X.Elementsᵒᵖ)) (r ≫ pointMap X)]
  infer_instance

/-- Adding all exact time families is a weak cover of the original factorization category. -/
theorem timeProjection_weak :
    WeakEquivalence (nerveMap
      (Grothendieck.forget (spaces N time ⋙ SimplicialResolutionFunctor.elementsOpposite))) :=
  GrothendieckContractibleFibers.projection_weak _ (choiceElements_point_GW N time)

private abbrev sourceProjection : ArrowIndex N time ⥤ (Presentation N time)ᵒᵖ :=
  CategoryOfElements.π (Functor.hom (Presentation N time)) ⋙ CategoryTheory.Prod.fst _ _

/-- Forget the lift and retain its entire original source necklace. -/
def sourceFromTime : (TimePresentation N time)ᵒᵖ ⥤ Presentation N time :=
  (Grothendieck.forget (spaces N time ⋙ SimplicialResolutionFunctor.elementsOpposite) ⋙
    sourceProjection N time).op ⋙ unopUnop _

theorem sourceFromTime_weak : WeakEquivalence (nerveMap (sourceFromTime N time)) := by
  haveI := timeProjection_weak N time
  haveI := JTGraphCylinderSpanProjection.homElements_source_weak (Presentation N time)
  let p := Grothendieck.forget (spaces N time ⋙ SimplicialResolutionFunctor.elementsOpposite) ⋙
    sourceProjection N time
  have h : WeakEquivalence (nerveMap p) := by
    change WeakEquivalence (nerveMap (Grothendieck.forget _) ≫ nerveMap (sourceProjection N time))
    infer_instance
  haveI : WeakEquivalence (nerveMap p.op) := (TotalElementsWeakComparison.nerveMap_op_iff _).mpr h
  haveI : WeakEquivalence (nerveMap (unopUnop (Presentation N time))) :=
    DaggerNativeGroupoidCompletionNerveBaseCases.nerveMap_weak_of_equivalence _
  change WeakEquivalence (nerveMap p.op ≫ nerveMap (unopUnop (Presentation N time)))
  infer_instance

/-- The other projection keeps the actual target cylinder of the original arrow. -/
abbrev targetFromTime : TimePresentation N time ⥤ Presentation N time :=
  Grothendieck.forget (spaces N time ⋙ SimplicialResolutionFunctor.elementsOpposite) ⋙
    CategoryOfElements.π (Functor.hom (Presentation N time)) ⋙ CategoryTheory.Prod.snd _ _

theorem targetFromTime_weak : WeakEquivalence (nerveMap (targetFromTime N time)) := by
  haveI := timeProjection_weak N time
  haveI := JTHomElementsTargetWeak.homElements_target_weak (Presentation N time)
  change WeakEquivalence (nerveMap (Grothendieck.forget _) ≫ nerveMap
    (CategoryOfElements.π (Functor.hom (Presentation N time)) ⋙ CategoryTheory.Prod.snd _ _))
  infer_instance

end Presentation

end

end DaggerModels.PartII.JTInternalTraversalLifts
