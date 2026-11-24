import DaggerModelsPartII.JTRealizationBoxCalibration
import DaggerModelsPartII.OrderedNecklaceLabelDiagram
import DaggerModelsPartII.DiagramMappingSpace

/-!
# Realizing a strict decorated label on an arbitrary simplex

The original free-dagger unit sends the ordinary simplex coordinate of a
strict diagram label into its discrete free dagger diagram. The existing
ordinary JT external-box isomorphism then realizes the full label as a map
`X × J[k] ⟶ R(W)`, natural in `X`, `k`, and `W`. In particular, `X` may be
an arbitrary native necklace. This does not construct a flag-bar comparison
or establish weakness of the original chosen-fiber map.
-/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open DaggerModels
open DaggerModels.PartII.ReversalDiscreteFreeColimits
open DaggerModels.PartII.JTReversalInput
open DaggerModels.PartII.OrdinaryJTRealization
open DaggerModels.PartII.JTRealizationBox
open DaggerModels.PartII.JTRealizationGenerators

namespace DaggerModels.PartII.JTNecklaceLabelRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev F := discreteFree.{0}
private abbrev Box := boxStandard
private abbrev Input := ordinaryInput
private abbrev R (W : Source) := realization.obj (Input.obj W)

/-- The original free-dagger unit, constant in the inner simplicial degree,
places a box label inside the actual ordinary bisimplicial input. -/
def freeUnitBox (X : SSet.{0}) (k : SimplexCategory) :
    Box.obj (X, k) ⟶
      Input.obj ((diagramTensor (F.obj X)).obj (SSet.stdSimplex.obj k)) where
  app p z := ((freeDaggerAdjunction.unit.app X).app (op p.unop.1) z.1, z.2)
  naturality {p q} f := by
    funext z
    have hu := congrFun
      ((freeDaggerAdjunction.unit.app X).naturality f.unop.1.op) z.1
    have hu' : ((freeDaggerAdjunction.unit.app X).app (op q.unop.1))
        (X.map f.unop.1.op z.1) =
      (freeDagger.obj X).extension.map
        (ReverseSimplex.inclusion.map f.unop.1).op
          ((freeDaggerAdjunction.unit.app X).app (op p.unop.1) z.1) := by
      simpa only [DaggerSSet.extension_inclusion] using hu
    simp only [boxStandard, boxFunctor, pullFirst, pullSecond,
      firstProjection, secondProjection, SimplicialObject.const,
      ordinaryInput, discreteFree, SegalLocalizers.discreteDagger,
      diagramTensor]
    change (((freeDaggerAdjunction.unit.app X).app (op q.unop.1))
        (X.map f.unop.1.op z.1),
        (SSet.stdSimplex.obj k).map f.unop.2.op z.2) =
      ((freeDagger.obj X).extension.map
          (ReverseSimplex.inclusion.map f.unop.1).op
            ((freeDaggerAdjunction.unit.app X).app (op p.unop.1) z.1),
        (SSet.stdSimplex.obj k).map f.unop.2.op z.2)
    exact congrArg
      (fun a ↦ (a, (SSet.stdSimplex.obj k).map f.unop.2.op z.2)) hu'

/-- A strict `k`-simplex label gives a map of the actual two-index JT inputs. -/
def labelBox (X : SSet.{0}) (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    Box.obj (X, k) ⟶ Input.obj W :=
  freeUnitBox X k ≫ Input.map η

/-- The realized decorated label uses the already existing arbitrary-`X`
external-box isomorphism; no represented-only replacement is selected. -/
def realizedLabel (X : SSet.{0}) (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    X ⊗ GroupoidSimplex.parameter.obj k ⟶ R W :=
  (realizationBoxIso.app (X, k)).inv ≫ realization.map (labelBox X W k η)

/-- The free-unit box respects a map of ordinary simplicial sets. -/
theorem freeUnitBox_natural_X {X Y : SSet.{0}} (f : X ⟶ Y)
    (k : SimplexCategory) :
    Box.map (f, 𝟙 k) ≫ freeUnitBox Y k =
      freeUnitBox X k ≫
        Input.map (Functor.whiskerRight (F.map f)
          (tensorRight (SSet.stdSimplex.obj k))) := by
  apply NatTrans.ext
  funext p z
  simp [freeUnitBox, boxStandard, boxFunctor, pullFirst, pullSecond,
    firstProjection, secondProjection, ordinaryInput, discreteFree,
    SegalLocalizers.discreteDagger, diagramTensor,
    DaggerSSet.toPresheaf, DaggerSSet.extensionHom]
  have hu := congrFun
    (NatTrans.congr_app (freeDaggerAdjunction.unit.naturality f) (op p.unop.1)) z.1
  change ((freeDaggerAdjunction.unit.app Y).app (op p.unop.1))
      (f.app (op p.unop.1) z.1) =
    (freeDagger.map f).hom.app (op ⦋p.unop.1.len⦌)
      ((freeDaggerAdjunction.unit.app X).app (op p.unop.1) z.1) at hu
  exact congrArg (fun a ↦ (a, z.2)) hu

/-- The free-unit box respects every inner simplex operator. -/
theorem freeUnitBox_natural_k (X : SSet.{0}) {k l : SimplexCategory}
    (g : k ⟶ l) :
    Box.map (𝟙 X, g) ≫ freeUnitBox X l =
      freeUnitBox X k ≫
        Input.map ((diagramTensor (F.obj X)).map (SSet.stdSimplex.map g)) := by
  apply NatTrans.ext
  funext p z
  rfl

/-- Realized labels commute with all native maps of the ordinary first input. -/
theorem realizedLabel_natural_X {X Y : SSet.{0}} (f : X ⟶ Y)
    (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj Y) W).obj (op k)) :
    (f ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        realizedLabel Y W k η =
      realizedLabel X W k
        (Functor.whiskerRight (F.map f)
          (tensorRight (SSet.stdSimplex.obj k)) ≫ η) := by
  have hn := realizationBoxIso.inv.naturality
    (show (X, k) ⟶ (Y, k) from (f, 𝟙 k))
  have hn' : (f ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
      (realizationBoxIso.app (Y, k)).inv =
    (realizationBoxIso.app (X, k)).inv ≫ realization.map (Box.map (f, 𝟙 k)) := by
    simpa [Functor.comp_map, Functor.prod_map] using hn
  calc
    _ = ((realizationBoxIso.app (X, k)).inv ≫
          realization.map (Box.map (f, 𝟙 k))) ≫
            realization.map (labelBox Y W k η) := by
              dsimp only [realizedLabel]
              rw [← Category.assoc, hn']
    _ = (realizationBoxIso.app (X, k)).inv ≫
          realization.map (labelBox X W k
            (Functor.whiskerRight (F.map f)
              (tensorRight (SSet.stdSimplex.obj k)) ≫ η)) := by
      rw [Category.assoc, ← realization.map_comp]
      exact congrArg (fun h ↦ (realizationBoxIso.app (X, k)).inv ≫
        realization.map h) (by
          dsimp only [labelBox]
          rw [← Category.assoc, freeUnitBox_natural_X]
          simp only [Category.assoc, ← Functor.map_comp])

/-- Realized labels commute with every inner simplex operator. -/
theorem realizedLabel_natural_k (X : SSet.{0}) (W : Source)
    {k l : SimplexCategory} (g : k ⟶ l)
    (η : (diagramMappingSpace (F.obj X) W).obj (op l)) :
    (𝟙 X ⊗ₘ GroupoidSimplex.parameter.map g) ≫
        realizedLabel X W l η =
      realizedLabel X W k
        ((diagramTensor (F.obj X)).map (SSet.stdSimplex.map g) ≫ η) := by
  have hn := realizationBoxIso.inv.naturality
    (show (X, k) ⟶ (X, l) from (𝟙 X, g))
  have hn' : (𝟙 X ⊗ₘ GroupoidSimplex.parameter.map g) ≫
      (realizationBoxIso.app (X, l)).inv =
    (realizationBoxIso.app (X, k)).inv ≫ realization.map (Box.map (𝟙 X, g)) := by
    simpa [Functor.comp_map, Functor.prod_map] using hn
  calc
    _ = ((realizationBoxIso.app (X, k)).inv ≫
          realization.map (Box.map (𝟙 X, g))) ≫
            realization.map (labelBox X W l η) := by
              dsimp only [realizedLabel]
              rw [← Category.assoc, hn']
    _ = (realizationBoxIso.app (X, k)).inv ≫
          realization.map (labelBox X W k
            ((diagramTensor (F.obj X)).map (SSet.stdSimplex.map g) ≫ η)) := by
      rw [Category.assoc, ← realization.map_comp]
      exact congrArg (fun h ↦ (realizationBoxIso.app (X, k)).inv ≫
        realization.map h) (by
          dsimp only [labelBox]
          rw [← Category.assoc, freeUnitBox_natural_k]
          simp only [Category.assoc, ← Functor.map_comp])

/-- Realized labels are natural in the original reversal target. -/
theorem realizedLabel_natural_W (X : SSet.{0}) {W V : Source}
    (h : W ⟶ V) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k)) :
    realizedLabel X W k η ≫ realization.map (Input.map h) =
      realizedLabel X V k (η ≫ h) := by
  simp only [realizedLabel, labelBox, Category.assoc, ← Functor.map_comp]

/-- Every actual box coend generator maps to the corresponding generator
of the original ordinary JT realization, with no chosen representative. -/
theorem realizedLabel_generator (X : SSet.{0}) (W : Source)
    (k m l : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k))
    (a : X.obj (op m))
    (β : (SSet.stdSimplex.obj k).obj (op l)) :
    JTRealizationGenerators.generator (Box.obj (X, k)) (m, l) (a, β) ≫
        realization.map (labelBox X W k η) =
      JTRealizationGenerators.generator (Input.obj W) (m, l)
        ((labelBox X W k η).app (op (m, l)) (a, β)) :=
  JTRealizationGenerators.generator_naturality (labelBox X W k η) (m, l) (a, β)

/-- The box coefficient is the literal strict label evaluated at the image of
the original free-dagger unit and the given inner simplex. -/
theorem labelBox_apply (X : SSet.{0}) (W : Source)
    (k m l : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k))
    (a : X.obj (op m))
    (β : (SSet.stdSimplex.obj k).obj (op l)) :
    (labelBox X W k η).app (op (m, l)) (a, β) =
      (η.app (op (ReverseSimplex.inclusion.obj m))).app (op l)
        ((freeDaggerAdjunction.unit.app X).app (op m) a, β) := rfl

/-- The actual realized-label map, including the inverse box isomorphism,
has the specified coend-generator value at every pair of simplex indices. -/
theorem realizedLabel_generator_formula (X : SSet.{0}) (W : Source)
    (k m l : SimplexCategory)
    (η : (diagramMappingSpace (F.obj X) W).obj (op k))
    (a : X.obj (op m))
    (β : (SSet.stdSimplex.obj k).obj (op l)) :
    (SSet.yonedaEquiv.symm a ⊗ₘ
        GroupoidSimplex.parameter.map (SSet.stdSimplex.objEquiv β)) ≫
      realizedLabel X W k η =
    JTRealizationGenerators.generator (Input.obj W) (m, l)
      ((η.app (op (ReverseSimplex.inclusion.obj m))).app (op l)
        ((freeDaggerAdjunction.unit.app X).app (op m) a, β)) := by
  have hbox := JTRealizationBoxCalibration.realizationBoxIso_generator X k m l a β
  calc
    _ = JTRealizationGenerators.generator (Box.obj (X, k)) (m, l) (a, β) ≫
          realization.map (labelBox X W k η) := by
            rw [← hbox, realizedLabel]
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = JTRealizationGenerators.generator (Input.obj W) (m, l)
          ((labelBox X W k η).app (op (m, l)) (a, β)) :=
      realizedLabel_generator X W k m l η a β
    _ = _ := by rw [labelBox_apply]

/-- The arbitrary first-input construction specializes without an altered
operator class to every native necklace. -/
def realizedNecklaceLabel
    (T : DaggerChosenRigidificationNecklace.NecklaceCode)
    (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj T.toSSet) W).obj (op k)) :
    T.toSSet ⊗ GroupoidSimplex.parameter.obj k ⟶ R W :=
  realizedLabel T.toSSet W k η

/-- The specialization retains every native necklace operator, including
collapsed-bead maps, through its underlying ordinary simplicial map. -/
theorem realizedNecklaceLabel_natural
    {T U : DaggerChosenRigidificationNecklace.NecklaceCode}
    (f : T ⟶ U) (W : Source) (k : SimplexCategory)
    (η : (diagramMappingSpace (F.obj U.toSSet) W).obj (op k)) :
    (f.map ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) ≫
        realizedNecklaceLabel U W k η =
      realizedNecklaceLabel T W k
        (Functor.whiskerRight (F.map f.map)
          (tensorRight (SSet.stdSimplex.obj k)) ≫ η) :=
  realizedLabel_natural_X f.map W k η

end
end DaggerModels.PartII.JTNecklaceLabelRealization
