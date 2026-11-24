import DaggerModelsPartII.BorelDiagramFreeCells
import DaggerModelsPartII.DiagramMappingPrecompFibration
import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
import Mathlib.CategoryTheory.Action.Monoidal

/-!
# Equivariant mapping spaces of simplicial-set diagrams

For a C₂-action `V` on a simplicial-set diagram and a plain diagram `W`, the
diagram mapping space from `V.V` to `W` carries the conjugate C₂-action by
precomposition with `V.ρ g⁻¹`. The strict orbit of the diagonal tensor of
`V` with a constant equivariant simplicial parameter is left adjoint to this
mapping action. The adjunction is parametrized in `V`, and forgetting its
relative mapping corner gives the ordinary diagram mapping corner.
-/

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory
open DaggerOriginalDaggerRealizationC2Action
universe u

namespace DaggerModels.PartII.EquivariantDiagramMapping

noncomputable section

variable (C : Type u) [Category.{u} C]

/-- The diagram mapping space with action by precomposition with inverse
group elements. -/
def mappingAction (V : Action (C ⥤ SSet.{u}) C2.{u}) (W : C ⥤ SSet.{u}) :
    Action SSet.{u} C2.{u} where
  V := diagramMappingSpace V.V W
  ρ := {
    toFun g := diagramMappingPrecomp (V.ρ g⁻¹) W
    map_one' := by
      simp only [inv_one, Action.ρ_one]
      apply NatTrans.ext
      funext n η
      apply NatTrans.ext
      funext c
      exact Category.id_comp _
    map_mul' := by
      intro g h
      rw [mul_inv_rev, map_mul, End.mul_def]
      rfl }

/-- A simplicial action viewed as a constant action diagram. -/
def constantActionDiagram :
    Action SSet.{u} C2.{u} ⥤ Action (C ⥤ SSet.{u}) C2.{u} :=
  (Functor.const C).mapAction C2.{u}

/-- The strict orbit of the diagonal tensor with an equivariant parameter. -/
def orbitTensor (V : Action (C ⥤ SSet.{u}) C2.{u}) :
    Action SSet.{u} C2.{u} ⥤ (C ⥤ SSet.{u}) :=
  constantActionDiagram C ⋙ tensorLeft V ⋙
    ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u}

/-- Functoriality of the conjugate mapping action in its plain diagram target. -/
def mappingActionFunctor (V : Action (C ⥤ SSet.{u}) C2.{u}) :
    (C ⥤ SSet.{u}) ⥤ Action SSet.{u} C2.{u} where
  obj W := mappingAction C V W
  map {W X} f := {
    hom := diagramMappingPostcomp V.V f
    comm g := by
      apply NatTrans.ext
      funext n η
      rfl }
  map_id W := by
    apply Action.hom_ext
    apply NatTrans.ext
    funext n η
    simp [diagramMappingPostcomp]
  map_comp f g := by
    apply Action.hom_ext
    apply NatTrans.ext
    funext n η
    rfl

private theorem tensorAction_rho
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) (g : C2.{u}) :
    (V ⊗ (constantActionDiagram C).obj K).ρ g =
      Functor.whiskerRight (V.ρ g) (tensorRight K.V) ≫
        (diagramTensor V.V).map (K.ρ g) := by
  apply NatTrans.ext
  funext c
  apply NatTrans.ext
  funext n x
  rfl

private theorem twist_eq_iff_invariant
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) (W : C ⥤ SSet.{u})
    (f : (V ⊗ (constantActionDiagram C).obj K).V ⟶ W)
    (g : C2.{u}) :
    (diagramTensor V.V).map (K.ρ g) ≫ f =
        Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V) ≫ f ↔
      (V ⊗ (constantActionDiagram C).obj K).ρ g ≫ f = f := by
  let A := Functor.whiskerRight (V.ρ g) (tensorRight K.V)
  let Ainv := Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V)
  let B := (diagramTensor V.V).map (K.ρ g)
  have hAAinv : A ≫ Ainv = 𝟙 _ := by
    change Functor.whiskerRight (V.ρ g) (tensorRight K.V) ≫
      Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V) = 𝟙 _
    rw [← Functor.whiskerRight_comp]
    have h : V.ρ g ≫ V.ρ g⁻¹ = 𝟙 V.V := (V.ρAut g).hom_inv_id
    rw [h]
    exact Functor.whiskerRight_id _
  have hAinvA : Ainv ≫ A = 𝟙 _ := by
    change Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V) ≫
      Functor.whiskerRight (V.ρ g) (tensorRight K.V) = 𝟙 _
    rw [← Functor.whiskerRight_comp]
    have h : V.ρ g⁻¹ ≫ V.ρ g = 𝟙 V.V := (V.ρAut g).inv_hom_id
    rw [h]
    exact Functor.whiskerRight_id _
  rw [tensorAction_rho C V K g]
  change B ≫ f = Ainv ≫ f ↔ A ≫ B ≫ f = f
  constructor
  · intro h
    calc
      A ≫ B ≫ f = A ≫ (B ≫ f) := rfl
      _ = A ≫ (Ainv ≫ f) := by rw [h]
      _ = f := by rw [← Category.assoc, hAAinv, Category.id_comp]
  · intro h
    calc
      B ≫ f = (Ainv ≫ A) ≫ (B ≫ f) := by rw [hAinvA, Category.id_comp]
      _ = Ainv ≫ f := by rw [Category.assoc, h]

private theorem transpose_comm_iff_invariant
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) (W : C ⥤ SSet.{u})
    (f : (V ⊗ (constantActionDiagram C).obj K).V ⟶ W)
    (g : C2.{u}) :
    K.ρ g ≫ (diagramTensorMappingAdjunction V.V).homEquiv K.V W f =
        (diagramTensorMappingAdjunction V.V).homEquiv K.V W f ≫
          (mappingAction C V W).ρ g ↔
      (V ⊗ (constantActionDiagram C).obj K).ρ g ≫ f = f := by
  let adj := InjectiveKanDiagram.diagramParametrizedAdjunction C
  have hK := adj.homEquiv_naturality_two (K.ρ g) f
  have hV := adj.homEquiv_naturality_one (V.ρ g⁻¹) f
  constructor
  · intro h
    apply (twist_eq_iff_invariant C V K W f g).mp
    apply adj.homEquiv.injective
    calc
      adj.homEquiv ((diagramTensor V.V).map (K.ρ g) ≫ f) =
          K.ρ g ≫ adj.homEquiv f := hK
      _ = adj.homEquiv f ≫ (mappingAction C V W).ρ g := h
      _ = adj.homEquiv
          (Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V) ≫ f) := hV.symm
  · intro h
    have ht := (twist_eq_iff_invariant C V K W f g).mpr h
    calc
      K.ρ g ≫ (diagramTensorMappingAdjunction V.V).homEquiv K.V W f =
          adj.homEquiv ((diagramTensor V.V).map (K.ρ g) ≫ f) := hK.symm
      _ = adj.homEquiv
          (Functor.whiskerRight (V.ρ g⁻¹) (tensorRight K.V) ≫ f) := by rw [ht]
      _ = (diagramTensorMappingAdjunction V.V).homEquiv K.V W f ≫
          (mappingAction C V W).ρ g := hV

/-- Equivariant transposition of a tensor map with a trivial target action. -/
def actionTensorHomEquiv
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) (W : C ⥤ SSet.{u}) :
    (V ⊗ (constantActionDiagram C).obj K ⟶ Action.trivial C2.{u} W) ≃
      (K ⟶ mappingAction C V W) where
  toFun f := {
    hom := (diagramTensorMappingAdjunction V.V).homEquiv K.V W f.hom
    comm g := by
      apply (transpose_comm_iff_invariant C V K W f.hom g).mpr
      simpa using f.comm g }
  invFun t := {
    hom := ((diagramTensorMappingAdjunction V.V).homEquiv K.V W).symm t.hom
    comm g := by
      apply (transpose_comm_iff_invariant C V K W
        (((diagramTensorMappingAdjunction V.V).homEquiv K.V W).symm t.hom) g).mp
      simpa only [Equiv.apply_symm_apply] using t.comm g }
  left_inv f := by
    apply Action.hom_ext
    exact Equiv.symm_apply_apply _ _
  right_inv t := by
    apply Action.hom_ext
    exact Equiv.apply_symm_apply _ _

/-- Orbit adjunction followed by equivariant tensor transposition. -/
def orbitTensorHomEquiv
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) (W : C ⥤ SSet.{u}) :
    ((orbitTensor C V).obj K ⟶ W) ≃
      (K ⟶ mappingAction C V W) :=
  ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
    (V ⊗ (constantActionDiagram C).obj K) W).trans
      (actionTensorHomEquiv C V K W)

private theorem actionTensorHomEquiv_natural_parameter
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    {K L : Action SSet.{u} C2.{u}} (i : K ⟶ L) (W : C ⥤ SSet.{u})
    (f : V ⊗ (constantActionDiagram C).obj L ⟶ Action.trivial C2.{u} W) :
    actionTensorHomEquiv C V K W
        ((tensorLeft V).map ((constantActionDiagram C).map i) ≫ f) =
      i ≫ actionTensorHomEquiv C V L W f := by
  apply Action.hom_ext
  exact (diagramTensorMappingAdjunction V.V).homEquiv_naturality_left i.hom f.hom

private theorem actionTensorHomEquiv_natural_target
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) {W X : C ⥤ SSet.{u}}
    (f : V ⊗ (constantActionDiagram C).obj K ⟶ Action.trivial C2.{u} W)
    (j : W ⟶ X) :
    actionTensorHomEquiv C V K X
        (f ≫ (ActionStrictOrbits.trivial (C ⥤ SSet.{u}) C2.{u}).map j) =
      actionTensorHomEquiv C V K W f ≫ (mappingActionFunctor C V).map j := by
  apply Action.hom_ext
  exact (diagramTensorMappingAdjunction V.V).homEquiv_naturality_right f.hom j

private theorem orbitTensorHomEquiv_natural_parameter
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    {K L : Action SSet.{u} C2.{u}} (i : K ⟶ L)
    (W : C ⥤ SSet.{u}) (f : (orbitTensor C V).obj L ⟶ W) :
    orbitTensorHomEquiv C V K W ((orbitTensor C V).map i ≫ f) =
      i ≫ orbitTensorHomEquiv C V L W f := by
  unfold orbitTensorHomEquiv
  simp only [Equiv.trans_apply]
  have hOrbit :
      ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
        (V ⊗ (constantActionDiagram C).obj K) W) ((orbitTensor C V).map i ≫ f) =
      (tensorLeft V).map ((constantActionDiagram C).map i) ≫
        ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
          (V ⊗ (constantActionDiagram C).obj L) W) f :=
    (ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv_naturality_left
      ((tensorLeft V).map ((constantActionDiagram C).map i)) f
  exact (congrArg (actionTensorHomEquiv C V K W) hOrbit).trans
    (actionTensorHomEquiv_natural_parameter C V i W _)

private theorem orbitTensorHomEquiv_natural_target
    (V : Action (C ⥤ SSet.{u}) C2.{u})
    (K : Action SSet.{u} C2.{u}) {W X : C ⥤ SSet.{u}}
    (f : (orbitTensor C V).obj K ⟶ W) (j : W ⟶ X) :
    orbitTensorHomEquiv C V K X (f ≫ j) =
      orbitTensorHomEquiv C V K W f ≫ (mappingActionFunctor C V).map j := by
  unfold orbitTensorHomEquiv
  simp only [Equiv.trans_apply]
  have hOrbit :
      ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
        (V ⊗ (constantActionDiagram C).obj K) X) (f ≫ j) =
      ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
        (V ⊗ (constantActionDiagram C).obj K) W) f ≫
        (ActionStrictOrbits.trivial (C ⥤ SSet.{u}) C2.{u}).map j :=
    (ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv_naturality_right
      f j
  exact (congrArg (actionTensorHomEquiv C V K X) hOrbit).trans
    (actionTensorHomEquiv_natural_target C V K _ j)

/-- Orbiting the tensor with an equivariant simplicial parameter is left
adjoint to the diagram mapping space with its conjugate action. -/
def orbitTensorAdjunction (V : Action (C ⥤ SSet.{u}) C2.{u}) :
    orbitTensor C V ⊣ mappingActionFunctor C V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun K W => orbitTensorHomEquiv C V K W
      homEquiv_naturality_left_symm := by
        intro K L W i q
        apply (orbitTensorHomEquiv C V K W).injective
        calc
          (orbitTensorHomEquiv C V K W)
              ((orbitTensorHomEquiv C V K W).symm (i ≫ q)) = i ≫ q :=
            Equiv.apply_symm_apply _ _
          _ = (orbitTensorHomEquiv C V K W)
              ((orbitTensor C V).map i ≫
                (orbitTensorHomEquiv C V L W).symm q) := by
            rw [orbitTensorHomEquiv_natural_parameter C V i W,
              Equiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro K W X f j
        exact orbitTensorHomEquiv_natural_target C V K f j }

/-- The diagonal tensor before strict orbits, functorial in the action diagram. -/
def tensorConstantBifunctor :
    Action (C ⥤ SSet.{u}) C2.{u} ⥤ Action SSet.{u} C2.{u} ⥤
      Action (C ⥤ SSet.{u}) C2.{u} :=
  (curriedTensor (Action (C ⥤ SSet.{u}) C2.{u})) ⋙
    (Functor.whiskeringLeft _ _ _).obj (constantActionDiagram C)

/-- The orbit tensor is covariantly functorial in the action diagram. -/
def orbitTensorBifunctor :
    Action (C ⥤ SSet.{u}) C2.{u} ⥤ Action SSet.{u} C2.{u} ⥤
      (C ⥤ SSet.{u}) :=
  tensorConstantBifunctor C ⋙
    (Functor.whiskeringRight _ _ _).obj
      (ActionStrictOrbits.orbit (C ⥤ SSet.{u}) C2.{u})

/-- Precomposition by an equivariant diagram map is equivariant on mapping spaces. -/
private theorem diagramMappingPrecomp_comp
    {A B D : C ⥤ SSet.{u}} (i : A ⟶ B) (j : B ⟶ D)
    (X : C ⥤ SSet.{u}) :
    diagramMappingPrecomp (i ≫ j) X =
      diagramMappingPrecomp j X ≫ diagramMappingPrecomp i X := by
  apply NatTrans.ext
  funext n η
  apply NatTrans.ext
  funext c
  rfl

def mappingActionPrecomp {V W : Action (C ⥤ SSet.{u}) C2.{u}}
    (φ : V ⟶ W) (X : C ⥤ SSet.{u}) :
    mappingAction C W X ⟶ mappingAction C V X where
  hom := diagramMappingPrecomp φ.hom X
  comm g := by
    change diagramMappingPrecomp (W.ρ g⁻¹) X ≫
        diagramMappingPrecomp φ.hom X =
      diagramMappingPrecomp φ.hom X ≫
        diagramMappingPrecomp (V.ρ g⁻¹) X
    rw [← diagramMappingPrecomp_comp C φ.hom (W.ρ g⁻¹) X,
      ← diagramMappingPrecomp_comp C (V.ρ g⁻¹) φ.hom X]
    rw [φ.comm g⁻¹]

/-- The conjugate mapping action is contravariant in the action diagram. -/
def mappingActionBifunctor :
    (Action (C ⥤ SSet.{u}) C2.{u})ᵒᵖ ⥤
      (C ⥤ SSet.{u}) ⥤ Action SSet.{u} C2.{u} where
  obj V := mappingActionFunctor C V.unop
  map {V W} φ := {
    app X := mappingActionPrecomp C φ.unop X
    naturality X Y j := by
      apply Action.hom_ext
      apply NatTrans.ext
      funext n η
      rfl }
  map_id V := by
    apply NatTrans.ext
    funext X
    apply Action.hom_ext
    apply NatTrans.ext
    funext n η
    rfl
  map_comp φ ψ := by
    apply NatTrans.ext
    funext X
    apply Action.hom_ext
    apply NatTrans.ext
    funext n η
    rfl

private theorem orbitTensorHomEquiv_natural_action
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (K : Action SSet.{u} C2.{u}) (X : C ⥤ SSet.{u})
    (f : ((orbitTensorBifunctor C).obj W).obj K ⟶ X) :
    orbitTensorHomEquiv C V K X
        (((orbitTensorBifunctor C).map φ).app K ≫ f) =
      orbitTensorHomEquiv C W K X f ≫
        ((mappingActionBifunctor C).map φ.op).app X := by
  unfold orbitTensorHomEquiv
  simp only [Equiv.trans_apply]
  have hOrbit :
      ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
        (V ⊗ (constantActionDiagram C).obj K) X)
          (((orbitTensorBifunctor C).map φ).app K ≫ f) =
      (φ ⊗ₘ 𝟙 ((constantActionDiagram C).obj K)) ≫
        ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
          (W ⊗ (constantActionDiagram C).obj K) X) f :=
    (ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv_naturality_left
      (φ ⊗ₘ 𝟙 ((constantActionDiagram C).obj K)) f
  calc
    (actionTensorHomEquiv C V K X)
        (((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
          (V ⊗ (constantActionDiagram C).obj K) X)
            (((orbitTensorBifunctor C).map φ).app K ≫ f)) =
      (actionTensorHomEquiv C V K X)
        ((φ ⊗ₘ 𝟙 ((constantActionDiagram C).obj K)) ≫
          ((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
            (W ⊗ (constantActionDiagram C).obj K) X) f) :=
      congrArg (actionTensorHomEquiv C V K X) hOrbit
    _ = (actionTensorHomEquiv C W K X)
          (((ActionStrictOrbits.orbitAdjunction (C ⥤ SSet.{u}) C2.{u}).homEquiv
            (W ⊗ (constantActionDiagram C).obj K) X) f) ≫
          ((mappingActionBifunctor C).map φ.op).app X := by
      apply Action.hom_ext
      exact (InjectiveKanDiagram.diagramParametrizedAdjunction C).homEquiv_naturality_one
        φ.hom _

/-- The orbit tensor and conjugate mapping action form a parametrized adjunction. -/
def orbitTensorParametrizedAdjunction :
    orbitTensorBifunctor C ⊣₂ mappingActionBifunctor C :=
  ParametrizedAdjunction.mk'
    (fun V => orbitTensorAdjunction C V)
    (by
      intro V W φ K X f
      exact orbitTensorHomEquiv_natural_action C φ K X f)

/-- Forgetting the equivariant relative mapping square gives the ordinary
diagram mapping pullback square. -/
def underlyingMappingCorner
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (r : (mappingActionBifunctor C).PullbackObjObj φ p) :
    (InjectiveKanDiagram.diagramMappingSource C).PullbackObjObj φ.hom p where
  pt := r.pt.V
  fst := r.fst.hom
  snd := r.snd.hom
  isPullback := r.isPullback.map
    (Action.forget SSet.{u} C2.{u})

/-- The equivariant mapping corner has exactly the ordinary underlying
mapping-corner projection. -/
theorem underlyingMappingCorner_π
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    {X Y : C ⥤ SSet.{u}} (p : X ⟶ Y)
    (r : (mappingActionBifunctor C).PullbackObjObj φ p) :
    (underlyingMappingCorner C φ p r).π = r.π.hom := by
  apply (underlyingMappingCorner C φ p r).isPullback.hom_ext
  · exact (Functor.PullbackObjObj.π_fst _).trans
      (congrArg Action.Hom.hom r.π_fst).symm
  · exact (Functor.PullbackObjObj.π_snd _).trans
      (congrArg Action.Hom.hom r.π_snd).symm

/-- On a native free simplicial parameter the orbit tensor is the ordinary
diagram tensor. -/
def orbitTensorFreeCellIso
    (V : Action (C ⥤ SSet.{u}) C2.{u}) (K : SSet.{u}) :
    ((orbitTensorBifunctor C).obj V).obj
      (DaggerOriginalSimplicialActionFreeGenerators.free.obj K) ≅
      (diagramTensor V.V).obj K :=
  BorelDiagramFreeCells.orbitFreeCellIso C V K

/-- The free-cell comparison identifies equivariant attaching arrows with
the ordinary diagram-tensor arrows. -/
theorem orbitTensorFreeCellIso_natural_action
    {V W : Action (C ⥤ SSet.{u}) C2.{u}} (φ : V ⟶ W)
    (K : SSet.{u}) :
    ((orbitTensorBifunctor C).map φ).app
        (DaggerOriginalSimplicialActionFreeGenerators.free.obj K) ≫
      (orbitTensorFreeCellIso C W K).hom =
    (orbitTensorFreeCellIso C V K).hom ≫
      Functor.whiskerRight φ.hom (tensorRight K) :=
  BorelDiagramFreeCells.orbitFreeCellIso_natural_action C φ K

/-- The free-cell comparison respects every simplicial map, including a
boundary inclusion. -/
theorem orbitTensorFreeCellIso_natural_cell
    (V : Action (C ⥤ SSet.{u}) C2.{u}) {K L : SSet.{u}}
    (f : K ⟶ L) :
    ((orbitTensorBifunctor C).obj V).map
        (DaggerOriginalSimplicialActionFreeGenerators.free.map f) ≫
      (orbitTensorFreeCellIso C V L).hom =
    (orbitTensorFreeCellIso C V K).hom ≫ (diagramTensor V.V).map f :=
  BorelDiagramFreeCells.orbitFreeCellIso_natural_cell C V f

end

end DaggerModels.PartII.EquivariantDiagramMapping
