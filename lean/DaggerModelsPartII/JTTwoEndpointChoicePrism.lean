import DaggerModelsPartII.JTTwoEndpointChoiceCover
import DaggerModelsPartII.JTActualJointChoiceChainGraph

/-! Complete coefficient-time maps for different front and back endpoint rows. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory

namespace DaggerModels.PartII.JTTwoEndpointChoicePrism

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTJointRelativeEdgePrism (rightMap leftMap rightMap_restrict leftMap_restrict)
open JTTwoEndpointChoiceCover

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem project_restrict {I : Type} [SmallCategory I]
    {X Y : Iᵒᵖ ⥤ SSet.{0}} (p : X ⟶ Y) {a b : I} (f : a ⟶ b)
    {n m : SimplexCategory} (u : n ⟶ m) (v : (X.obj (op b)).obj (op m)) :
    (p.app (op a)).app (op n)
        ((X.obj (op a)).map u.op ((X.map f.op).app (op m) v)) =
      (Y.obj (op a)).map u.op
        ((Y.map f.op).app (op m) ((p.app (op b)).app (op m) v)) := by
  have ht := congrFun ((p.app (op a)).naturality u.op) ((X.map f.op).app (op m) v)
  have hb := congrFun (NatTrans.congr_app (p.naturality f.op) (op m)) v
  exact ht.trans (congrArg ((Y.obj (op a)).map u.op) hb)

variable {I : Type} [SmallCategory I] (W : Source)
variable (s k : I ⥤ SimplexCategory) (u : s ⟶ k)
variable (f₀ f₁ : k ⋙ std ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (z : (row W ⦋0⦌).obj (op ⦋0⦌))
variable (h₀ : ∀ i, std.map (u.app i) ≫ f₀.app i =
  term (std.obj (s.obj i)) ≫ vertexPoint W z)
variable (h₁ : ∀ i, std.map (u.app i) ≫ f₁.app i =
  term (std.obj (s.obj i)) ≫ vertexPoint W z)

private abbrev X := spaces W s k u f₀ f₁ z h₀ h₁
private abbrev C := Cover W s k u f₀ f₁ z h₀ h₁
private abbrev P := projection W s k u f₀ f₁ z h₀ h₁
private abbrev K := coefficient W s k u f₀ f₁ z h₀ h₁
private abbrev N := choiceTime W s k u f₀ f₁ z h₀ h₁

/-- The higher front edge includes every coefficient and every choice-time simplex. -/
def frontMap (a : I) (n : SimplexCategory) (v : ((X W s k u f₀ f₁ z h₀ h₁).obj
    (op a)).obj (op n)) : std.obj (k.obj a) ⊗ std.obj n ⟶ row W ⦋1⦌ :=
  rightMap W s k u f₀ z h₀ a n
    (((frontProjection W s k u f₀ f₁ z h₀ h₁).app (op a)).app (op n) v)

/-- The higher back edge is taken at the other original endpoint row. -/
def backMap (a : I) (n : SimplexCategory) (v : ((X W s k u f₀ f₁ z h₀ h₁).obj
    (op a)).obj (op n)) : std.obj (k.obj a) ⊗ std.obj n ⟶ row W ⦋1⦌ :=
  leftMap W s k u f₁ z h₁ a n
    (((backProjection W s k u f₀ f₁ z h₀ h₁).app (op a)).app (op n) v)

/-- The first edge respects all original arrows and all higher simplex operators. -/
theorem frontMap_restrict {a b : I} (f : a ⟶ b) {n m : SimplexCategory} (v : n ⟶ m)
    (c : ((X W s k u f₀ f₁ z h₀ h₁).obj (op b)).obj (op m)) :
    frontMap W s k u f₀ f₁ z h₀ h₁ a n
      (((X W s k u f₀ f₁ z h₀ h₁).obj (op a)).map v.op
        (((X W s k u f₀ f₁ z h₀ h₁).map f.op).app (op m) c)) =
      (std.map (k.map f) ⊗ₘ std.map v) ≫ frontMap W s k u f₀ f₁ z h₀ h₁ b m c := by
  unfold frontMap
  rw [project_restrict]
  exact rightMap_restrict W s k u f₀ z h₀ f v _

/-- The same mixed naturality holds for the other endpoint edge. -/
theorem backMap_restrict {a b : I} (f : a ⟶ b) {n m : SimplexCategory} (v : n ⟶ m)
    (c : ((X W s k u f₀ f₁ z h₀ h₁).obj (op b)).obj (op m)) :
    backMap W s k u f₀ f₁ z h₀ h₁ a n
      (((X W s k u f₀ f₁ z h₀ h₁).obj (op a)).map v.op
        (((X W s k u f₀ f₁ z h₀ h₁).map f.op).app (op m) c)) =
      (std.map (k.map f) ⊗ₘ std.map v) ≫ backMap W s k u f₀ f₁ z h₀ h₁ b m c := by
  unfold backMap
  rw [project_restrict]
  exact leftMap_restrict W s k u f₁ z h₁ f v _

/-- Full coefficient-choice-time products over all paired higher choices. -/
abbrev prisms := JTActualJointChoiceChainGraph.prism (K W s k u f₀ f₁ z h₀ h₁)
  (N W s k u f₀ f₁ z h₀ h₁)

private theorem choice_restrict {a b : C W s k u f₀ f₁ z h₀ h₁} (v : a ⟶ b) :
    a.unop.2 = ((X W s k u f₀ f₁ z h₀ h₁).obj (op ((P W s k u f₀ f₁ z h₀ h₁).obj a))).map
      ((N W s k u f₀ f₁ z h₀ h₁).map v).op
      (((X W s k u f₀ f₁ z h₀ h₁).map ((P W s k u f₀ f₁ z h₀ h₁).map v).op).app
        (op ((N W s k u f₀ f₁ z h₀ h₁).obj b)) b.unop.2) := v.unop.property.symm

/-- A single natural front map on the entire full choice cover. -/
def front : prisms W s k u f₀ f₁ z h₀ h₁ ⟶
    (Functor.const (C W s k u f₀ f₁ z h₀ h₁)).obj (row W ⦋1⦌) where
  app a := frontMap W s k u f₀ f₁ z h₀ h₁ ((P W s k u f₀ f₁ z h₀ h₁).obj a)
    ((N W s k u f₀ f₁ z h₀ h₁).obj a) a.unop.2
  naturality a b v := by
    change (std.map ((K W s k u f₀ f₁ z h₀ h₁).map v) ⊗ₘ
        std.map ((N W s k u f₀ f₁ z h₀ h₁).map v)) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, choice_restrict W s k u f₀ f₁ z h₀ h₁ v]
    exact (frontMap_restrict W s k u f₀ f₁ z h₀ h₁
      ((P W s k u f₀ f₁ z h₀ h₁).map v) ((N W s k u f₀ f₁ z h₀ h₁).map v) b.unop.2).symm

/-- A single natural back map on that identical full choice cover. -/
def back : prisms W s k u f₀ f₁ z h₀ h₁ ⟶
    (Functor.const (C W s k u f₀ f₁ z h₀ h₁)).obj (row W ⦋1⦌) where
  app a := backMap W s k u f₀ f₁ z h₀ h₁ ((P W s k u f₀ f₁ z h₀ h₁).obj a)
    ((N W s k u f₀ f₁ z h₀ h₁).obj a) a.unop.2
  naturality a b v := by
    change (std.map ((K W s k u f₀ f₁ z h₀ h₁).map v) ⊗ₘ
        std.map ((N W s k u f₀ f₁ z h₀ h₁).map v)) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id, choice_restrict W s k u f₀ f₁ z h₀ h₁ v]
    exact (backMap_restrict W s k u f₀ f₁ z h₀ h₁
      ((P W s k u f₀ f₁ z h₀ h₁).map v) ((N W s k u f₀ f₁ z h₀ h₁).map v) b.unop.2).symm


variable (c : C W s k u f₀ f₁ z h₀ h₁)
private abbrev a₀ := (P W s k u f₀ f₁ z h₀ h₁).obj c
private abbrev n₀ := (N W s k u f₀ f₁ z h₀ h₁).obj c

/-- The full front prism is stationary on the original complete support. -/
theorem front_face :
    (std.map (u.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) ▷
        std.obj (n₀ W s k u f₀ f₁ z h₀ h₁ c)) ≫ (front W s k u f₀ f₁ z h₀ h₁).app c =
      fst _ _ ≫ JTJointEndpointRelativeLift.identityOnFace W z :=
  JTJointRelativeEdgePrism.rightMap_face W s k u f₀ z h₀ _ _ _

/-- The full back prism is stationary on that SAME complete support. -/
theorem back_face :
    (std.map (u.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) ▷
        std.obj (n₀ W s k u f₀ f₁ z h₀ h₁ c)) ≫ (back W s k u f₀ f₁ z h₀ h₁).app c =
      fst _ _ ≫ JTJointEndpointRelativeLift.identityOnFace W z :=
  JTJointRelativeEdgePrism.leftMap_face W s k u f₁ z h₁ _ _ _

/-- The front edge has the original first row as its variable last endpoint. -/
theorem front_endpoints : (front W s k u f₀ f₁ z h₀ h₁).app c ≫ endpointArrow W =
    fst _ _ ≫ JTJointEndpointRelativeLift.reverseBoundaryPair W
      (f₀.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) z :=
  JTJointRelativeEdgePrism.rightMap_endpoints W s k u f₀ z h₀ _ _ _

/-- The back edge has the original last row as its variable first endpoint. -/
theorem back_endpoints : (back W s k u f₀ f₁ z h₀ h₁).app c ≫ endpointArrow W =
    fst _ _ ≫ JTJointEndpointRelativeLift.boundaryPair W
      (f₁.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) z :=
  JTJointRelativeEdgePrism.leftMap_endpoints W s k u f₁ z h₁ _ _ _

private theorem chain_face {a b n d e : SimplexCategory}
    (i : a ⟶ b) (α : d ⟶ b) (β : d ⟶ n) (v : e ⟶ d) (q : e ⟶ a)
    (h : v ≫ α = q ≫ i) (E : std.obj b ⊗ std.obj n ⟶ row W ⦋1⦌)
    (hE : (std.map i ▷ std.obj n) ≫ E =
      fst (std.obj a) (std.obj n) ≫ JTJointEndpointRelativeLift.identityOnFace W z) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ E =
      JTJointEndpointRelativeLift.identityOnFace W z := by
  have hp : std.map v ≫ lift (std.map α) (std.map β) =
      lift (std.map q) (std.map (v ≫ β)) ≫ (std.map i ▷ std.obj n) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, whiskerRight_fst, lift_fst, lift_fst_assoc,
        ← std.map_comp, h]
    · simp only [Category.assoc, lift_snd, whiskerRight_snd, ← std.map_comp]
  rw [← Category.assoc, hp, Category.assoc, hE, ← Category.assoc, lift_fst]
  exact JTJointEndpointRelativeLift.identityOnFace_natural W z q

variable {d e : SimplexCategory}
variable (α : d ⟶ (K W s k u f₀ f₁ z h₀ h₁).obj c)
variable (β : d ⟶ n₀ W s k u f₀ f₁ z h₀ h₁ c)
variable (v : e ⟶ d) (q : e ⟶ s.obj (a₀ W s k u f₀ f₁ z h₀ h₁ c))

/-- Every chain face factoring through the original support keeps the front identity. -/
theorem front_chain_face (h : v ≫ α = q ≫ u.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ (front W s k u f₀ f₁ z h₀ h₁).app c =
      JTJointEndpointRelativeLift.identityOnFace W z :=
  chain_face W z _ α β v q h _ (front_face W s k u f₀ f₁ z h₀ h₁ c)

/-- The back identity has the identical support factorization criterion. -/
theorem back_chain_face (h : v ≫ α = q ≫ u.app (a₀ W s k u f₀ f₁ z h₀ h₁ c)) :
    std.map v ≫ lift (std.map α) (std.map β) ≫ (back W s k u f₀ f₁ z h₀ h₁).app c =
      JTJointEndpointRelativeLift.identityOnFace W z :=
  chain_face W z _ α β v q h _ (back_face W s k u f₀ f₁ z h₀ h₁ c)

end
end DaggerModels.PartII.JTTwoEndpointChoicePrism
