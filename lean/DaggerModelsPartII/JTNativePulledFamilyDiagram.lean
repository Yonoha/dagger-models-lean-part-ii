import DaggerModelsPartII.JTNativePulledCutComparison

/-!
All native restrictions of one actual decorated graph form a strict family.
`JTNativePulledCutComparison.labelMap` supplies the decorated arrow and `raw`
supplies the exact original-target raw equation; the ordered-label projection
is faithful, so the restriction maps satisfy strict functor laws. The ambient
code is not required to map to the target except through the given `c`.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

open CategoryTheory Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativePulledFamilyDiagram

open JTProjectiveOrderedFiberComparison (row)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTParametrizedTargetFamilies (Family codes)
open JTParametrizedTargetLiftTransport (graph)
open DecoratedCylinderNecklacePresentation (underCocone)
open NecklaceCylinderAugmentation (augmentation)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev J := GroupoidSimplex.parameter
private abbrev Index (W : Source) (x y : Vertex W) :=
  DecoratedNecklaceHomDiagram.Index W x y
private abbrev pr (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (boundaryPoint W x y)

variable {W : Source} {x y : Vertex W}
variable (i : Index W x y)
private instance : (pr W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private abbrev T := ((pr W x y).obj i).1
private abbrev k := ((pr W x y).obj i).2

/-- Every object is an original native restriction into the same ambient code. -/
def labels : Over (T i) ⥤ Index W x y where
  obj f := JTNativePulledCutComparison.label i f.hom
  map {f f'} g := JTNativePulledCutComparison.labelMap i f.hom f'.hom g.left (Over.w g)
  map_id f := by
    apply (pr W x y).map_injective
    change (𝟙 f.left, 𝟙 (k i)) = (𝟙 f.left, 𝟙 (k i))
    rfl
  map_comp {f f' f''} g g' := by
    apply (pr W x y).map_injective
    change (g.left ≫ g'.left, 𝟙 (k i)) =
      (g.left ≫ g'.left, 𝟙 (k i) ≫ 𝟙 (k i))
    rw [Category.id_comp]

/-- The native and coefficient components of every decorated arrow are exact. -/
theorem labels_projection {f f' : Over (T i)} (g : f ⟶ f') :
    (pr W x y).map ((labels i).map g) = (g.left, 𝟙 (k i)) := rfl

/-- The complete old time degree is constant along all native restrictions. -/
def time (n : SimplexCategory) : Over (T i) ⥤ SimplexCategory :=
  (Functor.const (Over (T i))).obj n

variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable (n : SimplexCategory) (c : T i ⟶ Q.code)
variable (p : (T i).toSSet ⊗ J.obj n ⟶ J.obj (k i))
variable (hr : (graph (i := i) p).right ≫ ((underCocone W x y).app i).right =
  augmentation (T i) n ≫ c.map ≫ Q.map)

/-- The actual native collapse on every restricted code. -/
def collapse : codes (labels i) ⟶ (Functor.const (Over (T i))).obj Q.code where
  app f := f.hom ≫ c
  naturality {f f'} g := by
    change (g.left ≫ f'.hom) ≫ c = (f.hom ≫ c) ≫ 𝟙 Q.code
    rw [Over.w g, Category.comp_id]

/-- The original full product parameter, pulled back only in the native direction. -/
abbrev parameter (f : Over (T i)) :
    f.left.toSSet ⊗ J.obj n ⟶ J.obj (k i) :=
  JTNativePulledCutComparison.parameter i n p f.hom

/-- The strict family covers every native restriction, including composites. -/
def family : Family Q (labels i) (time i n) where
  collapse := collapse i c
  parameter := parameter i n p
  parameter_map := by
    intro f f' g
    change (g.left.map ⊗ₘ J.map (𝟙 n)) ≫
      ((f'.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) =
      ((f.hom.map ⊗ₘ 𝟙 (J.obj n)) ≫ p) ≫ J.map (𝟙 (k i))
    rw [J.map_id, J.map_id, Category.comp_id, ← Category.assoc,
      tensorHom_comp_tensorHom, Category.id_comp]
    exact congrArg (fun u : f.left.toSSet ⟶ (T i).toSSet ↦
      (u ⊗ₘ 𝟙 (J.obj n)) ≫ p)
      (congrArg (fun u : f.left ⟶ T i ↦ u.map) (Over.w g))
  raw := by
    intro f
    exact JTNativePulledCutComparison.raw i n c p hr f.hom

/-- Each family object has the original complete native target map. -/
theorem family_collapse (f : Over (T i)) :
    (family i n c p hr).collapse.app f = f.hom ≫ c := rfl

/-- Every diagram of restrictions inherits the same strict full family. -/
def precomp {B : Type} [SmallCategory B] (D : B ⥤ Over (T i)) :
    Family Q (D ⋙ labels i) (D ⋙ time i n) :=
  (family i n c p hr).precomp D

end
end DaggerModels.PartII.JTNativePulledFamilyDiagram
