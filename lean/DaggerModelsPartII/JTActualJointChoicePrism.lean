import DaggerModelsPartII.JTActualJointChoiceCover
import DaggerModelsPartII.JTJointRelativeEdgePrism

/-!
# Full relative edge maps on the actual choice cover

All higher choices give maps on the entire coefficient-time product. Both the
original exact cut arrows and arbitrary simplicial operators are retained.
-/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTActualJointChoicePrism

open JTParametrizedTargetFamilies (Family)
open JTTargetJointMarks (Joint)
open JTExactlyMarkedSourceDiagram (Index supports degrees incl endpointRows supported_endpoint)
open JTActualJointChoiceCover (endingSpaces startingSpaces spaces Cover projection)
open JTJointRelativeEdgePrism
open JTProjectiveOrderedFiberComparison (row)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev std := SSet.stdSimplex.{0}

variable {A : Type} [SmallCategory A] {W : Source} {x y : Vertex W}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}
variable {L : A ⥤ DecoratedNecklaceHomDiagram.Index W x y} {time : A ⥤ SimplexCategory}
variable (F : Family Q L time) (j : Joint Q.code)

private abbrev z := JTParametrizedBeadGraph.jointCoefficient (Q := Q) j

/-- Keep the complete ending-edge simplex at every cut. -/
def endingProjection : spaces F j ⟶ endingSpaces F j where
  app a := fst ((endingSpaces F j).obj a) ((startingSpaces F j).obj a)
  naturality _ _ f :=
    tensorHom_fst ((endingSpaces F j).map f) ((startingSpaces F j).map f)

/-- Keep the complete starting-edge simplex at every cut. -/
def startingProjection : spaces F j ⟶ startingSpaces F j where
  app a := snd ((endingSpaces F j).obj a) ((startingSpaces F j).obj a)
  naturality _ _ f :=
    tensorHom_snd ((endingSpaces F j).map f) ((startingSpaces F j).map f)

variable (a : Index F j) (n : SimplexCategory)

private abbrev endingSimplex (v : ((spaces F j).obj (op a)).obj (op n)) :=
  ((endingProjection F j).app (op a)).app (op n) v
private abbrev startingSimplex (v : ((spaces F j).obj (op a)).obj (op n)) :=
  ((startingProjection F j).app (op a)).app (op n) v

/-- The entire ending-edge map of an arbitrary higher paired choice. -/
def endingMap (v : ((spaces F j).obj (op a)).obj (op n)) :
    std.obj ((degrees F j).obj a) ⊗ std.obj n ⟶ row W ⦋1⦌ :=
  leftMap W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) a n (endingSimplex F j a n v)

/-- The entire starting-edge map of the same higher paired choice. -/
def startingMap (v : ((spaces F j).obj (op a)).obj (op n)) :
    std.obj ((degrees F j).obj a) ⊗ std.obj n ⟶ row W ⦋1⦌ :=
  rightMap W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) a n (startingSimplex F j a n v)

section Mixed

variable {a n} {b : Index F j} (f : a ⟶ b) {m : SimplexCategory} (u : n ⟶ m)
variable (v : ((spaces F j).obj (op b)).obj (op m))

private theorem endingSimplex_restrict :
    endingSimplex F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
    ((endingSpaces F j).obj (op a)).map u.op
      (((endingSpaces F j).map f.op).app _ (endingSimplex F j b m v)) := by
  have ht := congrFun (((endingProjection F j).app (op a)).naturality u.op)
    (((spaces F j).map f.op).app _ v)
  have hb := congrFun (NatTrans.congr_app ((endingProjection F j).naturality f.op) (op m)) v
  change endingSimplex F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
    ((endingSpaces F j).obj (op a)).map u.op
      (endingSimplex F j a m (((spaces F j).map f.op).app _ v)) at ht
  exact ht.trans (congrArg (((endingSpaces F j).obj (op a)).map u.op) hb)

private theorem startingSimplex_restrict :
    startingSimplex F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
    ((startingSpaces F j).obj (op a)).map u.op
      (((startingSpaces F j).map f.op).app _ (startingSimplex F j b m v)) := by
  have ht := congrFun (((startingProjection F j).app (op a)).naturality u.op)
    (((spaces F j).map f.op).app _ v)
  have hb := congrFun (NatTrans.congr_app ((startingProjection F j).naturality f.op) (op m)) v
  change startingSimplex F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
    ((startingSpaces F j).obj (op a)).map u.op
      (startingSimplex F j a m (((spaces F j).map f.op).app _ v)) at ht
  exact ht.trans (congrArg (((startingSpaces F j).obj (op a)).map u.op) hb)

/-- Both the old coefficient operator and every simplex operator act on the
whole ending-edge map by literal precomposition. -/
theorem endingMap_restrict :
    endingMap F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
      (std.map ((degrees F j).map f) ⊗ₘ std.map u) ≫ endingMap F j b m v := by
  unfold endingMap
  rw [endingSimplex_restrict]
  exact leftMap_restrict W (supports F j) (degrees F j) (incl F j)
    (endpointRows F j) (z j) (supported_endpoint F j) f u _

/-- The same mixed formula holds for the complete starting-edge map. -/
theorem startingMap_restrict :
    startingMap F j a n
      (((spaces F j).obj (op a)).map u.op (((spaces F j).map f.op).app _ v)) =
      (std.map ((degrees F j).map f) ⊗ₘ std.map u) ≫ startingMap F j b m v := by
  unfold startingMap
  rw [startingSimplex_restrict]
  exact rightMap_restrict W (supports F j) (degrees F j) (incl F j)
    (endpointRows F j) (z j) (supported_endpoint F j) f u _

end Mixed

/-- The original coefficient degree on the entire higher choice cover. -/
abbrev coefficient : Cover F j ⥤ SimplexCategory := projection F j ⋙ degrees F j

/-- Every ordinary simplex degree and operator of the full choice cover. -/
abbrev choiceTime : Cover F j ⥤ SimplexCategory :=
  SynchronizedSimplicialParameters.time (spaces F j)

/-- The coefficient-time products over all higher choices. -/
abbrev prisms :=
  (((coefficient F j) ⋙ std).prod' ((choiceTime F j) ⋙ std)) ⋙
    MonoidalCategory.tensor SSet.{0}

private theorem choice_restrict {c d : Cover F j} (g : c ⟶ d) :
    c.unop.2 =
      ((spaces F j).obj (op ((projection F j).obj c))).map
        ((choiceTime F j).map g).op
        (((spaces F j).map ((projection F j).map g).op).app
          (op ((choiceTime F j).obj d)) d.unop.2) :=
  g.unop.property.symm

/-- All higher ending-edge maps form one natural transformation on the full cover. -/
def ending : prisms F j ⟶ (Functor.const (Cover F j)).obj (row W ⦋1⦌) where
  app c := endingMap F j ((projection F j).obj c) ((choiceTime F j).obj c) c.unop.2
  naturality c d g := by
    change (std.map ((coefficient F j).map g) ⊗ₘ std.map ((choiceTime F j).map g)) ≫
      endingMap F j ((projection F j).obj d) ((choiceTime F j).obj d) d.unop.2 =
        endingMap F j ((projection F j).obj c) ((choiceTime F j).obj c) c.unop.2 ≫ 𝟙 _
    rw [Category.comp_id, choice_restrict F j g]
    exact (endingMap_restrict F j ((projection F j).map g) ((choiceTime F j).map g)
      d.unop.2).symm

/-- All higher starting-edge maps form a natural transformation on the same cover. -/
def starting : prisms F j ⟶ (Functor.const (Cover F j)).obj (row W ⦋1⦌) where
  app c := startingMap F j ((projection F j).obj c) ((choiceTime F j).obj c) c.unop.2
  naturality c d g := by
    change (std.map ((coefficient F j).map g) ⊗ₘ std.map ((choiceTime F j).map g)) ≫
      startingMap F j ((projection F j).obj d) ((choiceTime F j).obj d) d.unop.2 =
        startingMap F j ((projection F j).obj c) ((choiceTime F j).obj c) c.unop.2 ≫ 𝟙 _
    rw [Category.comp_id, choice_restrict F j g]
    exact (startingMap_restrict F j ((projection F j).map g) ((choiceTime F j).map g)
      d.unop.2).symm

section RelativeFaces

variable (c : Cover F j)

private abbrev a₀ := (projection F j).obj c
private abbrev n₀ := (choiceTime F j).obj c

/-- The entire ending-edge prism is the identity on the actual used face. -/
theorem ending_face :
    (std.map ((incl F j).app (a₀ F j c)) ▷ std.obj (n₀ F j c)) ≫
        (ending F j).app c =
      fst (std.obj ((supports F j).obj (a₀ F j c))) (std.obj (n₀ F j c)) ≫
        JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  leftMap_face W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) (a₀ F j c) (n₀ F j c) _

/-- The starting-edge prism has the same stationary relative identity face. -/
theorem starting_face :
    (std.map ((incl F j).app (a₀ F j c)) ▷ std.obj (n₀ F j c)) ≫
        (starting F j).app c =
      fst (std.obj ((supports F j).obj (a₀ F j c))) (std.obj (n₀ F j c)) ≫
        JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  rightMap_face W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) (a₀ F j c) (n₀ F j c) _

/-- The two ordered endpoints of every complete ending-edge prism. -/
theorem ending_endpoints :
    (ending F j).app c ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      fst (std.obj ((coefficient F j).obj c)) (std.obj (n₀ F j c)) ≫
        JTJointEndpointRelativeLift.boundaryPair W ((endpointRows F j).app (a₀ F j c))
          (z j) :=
  leftMap_endpoints W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) (a₀ F j c) (n₀ F j c) _

/-- The reversed ordered endpoints of every complete starting-edge prism. -/
theorem starting_endpoints :
    (starting F j).app c ≫ JTProjectiveOrderedFiberComparison.endpointArrow W =
      fst (std.obj ((coefficient F j).obj c)) (std.obj (n₀ F j c)) ≫
        JTJointEndpointRelativeLift.reverseBoundaryPair W
          ((endpointRows F j).app (a₀ F j c)) (z j) :=
  rightMap_endpoints W (supports F j) (degrees F j) (incl F j) (endpointRows F j) (z j)
    (supported_endpoint F j) (a₀ F j c) (n₀ F j c) _

private theorem chain_face {s k n d e : SimplexCategory}
    (u : s ⟶ k) (α : d ⟶ k) (β : d ⟶ n) (v : e ⟶ d) (b : e ⟶ s)
    (h : v ≫ α = b ≫ u) (E : std.obj k ⊗ std.obj n ⟶ row W ⦋1⦌)
    (hE : (std.map u ▷ std.obj n) ≫ E =
      fst (std.obj s) (std.obj n) ≫ JTJointEndpointRelativeLift.identityOnFace W (z j)) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ E =
      JTJointEndpointRelativeLift.identityOnFace W (z j) := by
  have hp : std.map v ≫ lift (std.map α) (std.map β) =
      lift (std.map b) (std.map (v ≫ β)) ≫ (std.map u ▷ std.obj n) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerRight_fst, lift_fst, lift_fst_assoc,
        ← std.map_comp, h]
    · simp only [Category.assoc, lift_snd, whiskerRight_snd, ← std.map_comp]
  rw [← Category.assoc, hp, Category.assoc, hE, ← Category.assoc, lift_fst]
  exact JTJointEndpointRelativeLift.identityOnFace_natural W (z j) b

variable {d e : SimplexCategory}
variable (α : d ⟶ (coefficient F j).obj c) (β : d ⟶ (choiceTime F j).obj c)
variable (v : e ⟶ d) (b : e ⟶ (supports F j).obj (a₀ F j c))

/-- Restricting a higher ending choice to an ordered chain preserves every
relative face that factors through the original used support. -/
theorem ending_chain_face (h : v ≫ α = b ≫ (incl F j).app (a₀ F j c)) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ (ending F j).app c =
      JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  chain_face j _ α β v b h _ (ending_face F j c)

/-- The same relative face is preserved by the starting choice on that chain. -/
theorem starting_chain_face (h : v ≫ α = b ≫ (incl F j).app (a₀ F j c)) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ (starting F j).app c =
      JTJointEndpointRelativeLift.identityOnFace W (z j) :=
  chain_face j _ α β v b h _ (starting_face F j c)

/-- The ending-edge chain has precisely the old coefficient pulled back by α. -/
theorem ending_chain_endpoints :
    (lift (std.map α) (std.map β) ≫ (ending F j).app c) ≫
        JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointEndpointRelativeLift.boundaryPair W
        (std.map α ≫ (endpointRows F j).app (a₀ F j c)) (z j) := by
  rw [Category.assoc, ending_endpoints, ← Category.assoc, lift_fst,
    JTJointEndpointRelativeLift.boundaryPair_natural]

/-- The starting-edge chain has the same pulled-back coefficient on the right. -/
theorem starting_chain_endpoints :
    (lift (std.map α) (std.map β) ≫ (starting F j).app c) ≫
        JTProjectiveOrderedFiberComparison.endpointArrow W =
      JTJointEndpointRelativeLift.reverseBoundaryPair W
        (std.map α ≫ (endpointRows F j).app (a₀ F j c)) (z j) := by
  rw [Category.assoc, starting_endpoints, ← Category.assoc, lift_fst,
    JTJointEndpointRelativeLift.reverseBoundaryPair_natural]

end RelativeFaces

end
end DaggerModels.PartII.JTActualJointChoicePrism
