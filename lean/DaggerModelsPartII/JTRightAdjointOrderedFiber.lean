import DaggerModelsPartII.JTRightAdjointNativeRow
import DaggerModelsPartII.JTRightAdjointForwardNormalization
import DaggerModelsPartII.JTUnderlyingOrderedFibers
import DaggerModelsPartII.EndpointMappingFiber

/-!
# Original right-adjoint ordered endpoint fibers

The original dagger and ordinary JT right adjoints retain their literal
rows and ordered endpoint arrows. Their categorical fibers are compared to
the checked endpoint-span presentations before applying the original right
comparison. All constructions use the fixed value-zero adjunctions.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTRightAdjointOrderedFiber

open DaggerJTAdjunction JTRightAdjointNativeRow
open JTOrderedFrameMate JTXiEndpointCollapse
open JTUnderlyingOrderedFibers
open OrdinaryJTRealization JTXiEndpointCollapseBoundary

noncomputable section

private local instance : HasColimits DaggerSSet.{0} := daggerSSetHasColimits

/-- A literal row of the original dagger JT right adjoint. -/
def daggerRow (X : DaggerSSet.{0}) (m : ReverseSimplex) : SSet.{0} :=
  (daggerNerve.obj X).obj (op m)

/-- Remove only the native universe lift from a literal dagger-nerve row. -/
def daggerRowHomIso (X : DaggerSSet.{0}) (m : ReverseSimplex) :
    daggerRow X m ≅ EndpointMappingFiber.mapping (Z := X) (verticalFrame m) :=
  NatIso.ofComponents
    (fun k ↦ (show
      ULift (frame.obj (m, k.unop) ⟶ X) ≃
        ((verticalFrame m).obj k.unop ⟶ X) from
      { toFun := ULift.down
        invFun := ULift.up
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }).toIso)
    (by
      intro k l θ
      ext f
      change frame.map
        (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)) ≫ f.down =
        (verticalFrame m).map θ.unop ≫ f.down
      rfl)

/-- The original outer-one endpoint arrow is induced by the two actual
reversal-simplex vertex operators, in their specified order. -/
def daggerEndpointArrow (X : DaggerSSet.{0}) :
    daggerRow X oneIndex ⟶
      daggerRow X JTZeroObjects.zeroIndex ⨯
        daggerRow X JTZeroObjects.zeroIndex :=
  prod.lift ((daggerNerve.obj X).map (vertex 0).op)
    ((daggerNerve.obj X).map (vertex 1).op)

private theorem daggerEndpointArrow_fst (X : DaggerSSet.{0}) :
    daggerEndpointArrow X ≫ prod.fst =
      (daggerNerve.obj X).map (vertex 0).op :=
  prod.lift_fst _ _

private theorem daggerEndpointArrow_snd (X : DaggerSSet.{0}) :
    daggerEndpointArrow X ≫ prod.snd =
      (daggerNerve.obj X).map (vertex 1).op :=
  prod.lift_snd _ _

/-- The prescribed constant endpoint in the original degree-zero dagger
row, expressed through its actual augmentation and free-dagger boundary. -/
def daggerVertexPoint (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    (Δ[0] : SSet.{0}) ⟶ daggerRow X JTZeroObjects.zeroIndex where
  app k _ := ULift.up
    ((endpointCollapse i).app k.unop ≫ daggerBoundary X x y)
  naturality {k l} θ := by
    funext z
    have h := (endpointCollapse i).naturality θ.unop
    change frame0.map θ.unop ≫ (endpointCollapse i).app k.unop =
      (endpointCollapse i).app l.unop at h
    change ULift.up ((endpointCollapse i).app l.unop ≫
      daggerBoundary X x y) =
        ULift.up (frame0.map θ.unop ≫
          ((endpointCollapse i).app k.unop ≫ daggerBoundary X x y))
    exact congrArg ULift.up
      ((congrArg (fun t ↦ t ≫ daggerBoundary X x y) h).symm.trans
        (Category.assoc _ _ _))

/-- The actual ordered pair of constant endpoint simplices in the product
of the two original degree-zero rows. -/
def daggerEndpointPoint (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      daggerRow X JTZeroObjects.zeroIndex ⨯
        daggerRow X JTZeroObjects.zeroIndex :=
  prod.lift (daggerVertexPoint X x y 0) (daggerVertexPoint X x y 1)

private theorem daggerEndpointPoint_fst (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerEndpointPoint X x y ≫ prod.fst =
      daggerVertexPoint X x y 0 := prod.lift_fst _ _

private theorem daggerEndpointPoint_snd (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerEndpointPoint X x y ≫ prod.snd =
      daggerVertexPoint X x y 1 := prod.lift_snd _ _

/-- The categorical strict fiber of the **original** dagger JT right
adjoint's ordered endpoint arrow. -/
def daggerOrderedFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (daggerEndpointArrow X) (daggerEndpointPoint X x y)

/-- The two endpoint equations written pointwise in the *original* dagger
right-adjoint row. -/
private def daggerRowSpan (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} where
  obj k := {f : frame1.obj k.unop ⟶ X // ∀ i : Fin 2,
    (frameEndpoint i).app k.unop ≫ f =
      (endpointCollapse i).app k.unop ≫ daggerBoundary X x y}
  map {k l} θ f := ⟨frame1.map θ.unop ≫ f.val, by
    intro i
    have hf := (frameEndpoint i).naturality θ.unop
    have ha := (endpointCollapse i).naturality θ.unop
    calc
      (frameEndpoint i).app l.unop ≫ (frame1.map θ.unop ≫ f.val) =
          frame0.map θ.unop ≫ ((frameEndpoint i).app k.unop ≫ f.val) := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ t ≫ f.val) hf.symm
      _ = frame0.map θ.unop ≫
          ((endpointCollapse i).app k.unop ≫ daggerBoundary X x y) := by
            rw [f.property i]
      _ = (endpointCollapse i).app l.unop ≫ daggerBoundary X x y := by
            simpa only [Functor.const_obj_map, Category.comp_id,
              Category.assoc] using
                congrArg (fun t ↦ t ≫ daggerBoundary X x y) ha⟩
  map_id k := by
    funext f
    apply Subtype.ext
    simp
  map_comp θ ψ := by
    funext f
    apply Subtype.ext
    simp [Functor.map_comp, Category.assoc]

private theorem rawFaces_inl (k : SimplexCategory) :
    (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k ≫ rawFaces.app k =
      (frameEndpoint 0).app k :=
  NatTrans.congr_app (coprod.inl_desc (frameEndpoint 0) (frameEndpoint 1)) k

private theorem rawFaces_inr (k : SimplexCategory) :
    (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k ≫ rawFaces.app k =
      (frameEndpoint 1).app k :=
  NatTrans.congr_app (coprod.inr_desc (frameEndpoint 0) (frameEndpoint 1)) k

private theorem rawEndpoints_inl (k : SimplexCategory) :
    (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k ≫ rawEndpoints.app k =
      (endpointCollapse 0).app k :=
  NatTrans.congr_app (coprod.inl_desc (endpointCollapse 0) (endpointCollapse 1)) k

private theorem rawEndpoints_inr (k : SimplexCategory) :
    (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k ≫ rawEndpoints.app k =
      (endpointCollapse 1).app k :=
  NatTrans.congr_app (coprod.inr_desc (endpointCollapse 0) (endpointCollapse 1)) k

/-- The evaluated functor-category coproduct is controlled by its two
actual evaluated coprojections. -/
private theorem evaluatedCoprod_hom_ext (k : SimplexCategory)
    {Z : DaggerSSet.{0}}
    {f g : (frame0 ⨿ frame0).obj k ⟶ Z}
    (h₀ : (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k ≫ f =
      (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k ≫ g)
    (h₁ : (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k ≫ f =
      (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k ≫ g) : f = g := by
  let E := (evaluation SimplexCategory DaggerSSet.{0}).obj k
  letI : IsIso (coprodComparison E frame0 frame0) := inferInstance
  apply (cancel_epi (coprodComparison E frame0 frame0)).1
  apply coprod.hom_ext
  · simpa only [coprodComparison_inl_assoc] using h₀
  · simpa only [coprodComparison_inr_assoc] using h₁

/-- The pointwise row equations are precisely the accepted raw face-span
equation. This equivalence retains the actual functor-category coproduct. -/
private def daggerRowSpanRawIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerRowSpan X x y ≅ daggerOrderedSpanSSet X x y :=
  NatIso.ofComponents (fun k ↦ (show
    (daggerRowSpan X x y).obj k ≃
      (daggerOrderedSpanSSet X x y).obj k from
    { toFun := fun f ↦ ⟨f.val, by
        apply evaluatedCoprod_hom_ext k.unop
        · rw [← Category.assoc, rawFaces_inl, ← Category.assoc,
            rawEndpoints_inl]
          exact f.property 0
        · rw [← Category.assoc, rawFaces_inr, ← Category.assoc,
            rawEndpoints_inr]
          exact f.property 1⟩
      invFun := fun f ↦ ⟨f.val, by
        intro i
        fin_cases i
        · have h := congrArg
            (fun t ↦ (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫ t)
            f.property
          change (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫
            (rawFaces.app k.unop ≫ f.val) =
            (coprod.inl : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫
              (rawEndpoints.app k.unop ≫ daggerBoundary X x y) at h
          rw [← Category.assoc, rawFaces_inl,
            ← Category.assoc, rawEndpoints_inl] at h
          simpa only using h
        · have h := congrArg
            (fun t ↦ (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫ t)
            f.property
          change (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫
            (rawFaces.app k.unop ≫ f.val) =
            (coprod.inr : frame0 ⟶ frame0 ⨿ frame0).app k.unop ≫
              (rawEndpoints.app k.unop ≫ daggerBoundary X x y) at h
          rw [← Category.assoc, rawFaces_inr,
            ← Category.assoc, rawEndpoints_inr] at h
          simpa only using h⟩
      left_inv := fun f ↦ Subtype.ext rfl
      right_inv := fun f ↦ Subtype.ext rfl }).toIso)
    (by intro k l θ; funext f; apply Subtype.ext; rfl)

/-- Restrict a pointwise ordered dagger frame map to the literal original
right-adjoint row, retaining its native universe lift. -/
private def daggerRowSpanRestriction (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerRowSpan X x y ⟶ daggerRow X oneIndex where
  app _ f := ULift.up f.val
  naturality {k l} θ := by
    funext f
    rfl

private theorem daggerRowSpan_square (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerRowSpanRestriction X x y ≫ daggerEndpointArrow X =
      SSet.stdSimplex.objZeroIsTerminal.from (daggerRowSpan X x y) ≫
        daggerEndpointPoint X x y := by
  apply prod.hom_ext
  · rw [Category.assoc, daggerEndpointArrow_fst,
      Category.assoc, daggerEndpointPoint_fst]
    apply NatTrans.ext
    funext k f
    change ULift.up ((frameEndpoint 0).app k.unop ≫ f.val) =
      ULift.up ((endpointCollapse 0).app k.unop ≫ daggerBoundary X x y)
    exact congrArg ULift.up (f.property 0)
  · rw [Category.assoc, daggerEndpointArrow_snd,
      Category.assoc, daggerEndpointPoint_snd]
    apply NatTrans.ext
    funext k f
    change ULift.up ((frameEndpoint 1).app k.unop ≫ f.val) =
      ULift.up ((endpointCollapse 1).app k.unop ≫ daggerBoundary X x y)
    exact congrArg ULift.up (f.property 1)

private theorem daggerCone_condition (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌))
    (s : PullbackCone (daggerEndpointArrow X) (daggerEndpointPoint X x y))
    (k : SimplexCategoryᵒᵖ) (z : s.pt.obj k) :
    ∀ i : Fin 2,
      (frameEndpoint i).app k.unop ≫ (s.fst.app k z).down =
        (endpointCollapse i).app k.unop ≫ daggerBoundary X x y := by
  intro i
  fin_cases i
  · have h₀ := congrFun (NatTrans.congr_app
      (congrArg (fun t ↦ t ≫
        (prod.fst : daggerRow X JTZeroObjects.zeroIndex ⨯
          daggerRow X JTZeroObjects.zeroIndex ⟶ _)) s.condition) k) z
    dsimp only at h₀
    rw [Category.assoc, daggerEndpointArrow_fst,
      Category.assoc, daggerEndpointPoint_fst] at h₀
    change ULift.up ((frameEndpoint 0).app k.unop ≫
      (s.fst.app k z).down) =
        ULift.up ((endpointCollapse 0).app k.unop ≫ daggerBoundary X x y) at h₀
    exact congrArg ULift.down h₀
  · have h₁ := congrFun (NatTrans.congr_app
      (congrArg (fun t ↦ t ≫
        (prod.snd : daggerRow X JTZeroObjects.zeroIndex ⨯
          daggerRow X JTZeroObjects.zeroIndex ⟶ _)) s.condition) k) z
    dsimp only at h₁
    rw [Category.assoc, daggerEndpointArrow_snd,
      Category.assoc, daggerEndpointPoint_snd] at h₁
    change ULift.up ((frameEndpoint 1).app k.unop ≫
      (s.fst.app k z).down) =
        ULift.up ((endpointCollapse 1).app k.unop ≫ daggerBoundary X x y) at h₁
    exact congrArg ULift.down h₁

/-- The literal original product-row endpoint arrow has the pointwise
ordered span as its categorical strict fiber. -/
private theorem daggerRowSpan_isPullback (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    IsPullback (daggerRowSpanRestriction X x y)
      (SSet.stdSimplex.objZeroIsTerminal.from (daggerRowSpan X x y))
      (daggerEndpointArrow X) (daggerEndpointPoint X x y) where
  w := daggerRowSpan_square X x y
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ {
      app k z := ⟨(s.fst.app k z).down, daggerCone_condition X x y s k z⟩
      naturality {k l} θ := by
        funext z
        apply Subtype.ext
        have h := congrFun (s.fst.naturality θ) z
        change (s.fst.app l ((s.pt.map θ) z)).down =
          frame1.map θ.unop ≫ (s.fst.app k z).down
        exact congrArg ULift.down h })
    (fun _ ↦ by ext k z; rfl)
    (fun _ ↦ SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _)
    (fun s t ht _ ↦ by
      apply NatTrans.ext
      funext k z
      apply Subtype.ext
      exact congrArg ULift.down (congrFun (NatTrans.congr_app ht k) z))⟩

/-- The categorical fiber of the original dagger-nerve endpoint arrow is
the accepted endpoint-span simplicial set, without changing the point. -/
def daggerOrderedFiberIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerOrderedFiber X x y ≅ daggerOrderedSpanSSet X x y :=
  (daggerRowSpan_isPullback X x y).isoPullback.symm ≪≫
    daggerRowSpanRawIso X x y

/-- Hold the horizontal index fixed in the *original* two-index ordinary
right adjoint; no alternate Hom presheaf is used. -/
def ordinaryRow (S : SSet.{0}) (m : SimplexCategory) : SSet.{0} where
  obj k := (nerve.obj S).obj (op (m, k.unop))
  map {k l} θ := (nerve.obj S).map
    (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))
  map_id k := by
    simpa only using (nerve.obj S).map_id (op (m, k.unop))
  map_comp := by
    intro k l n θ ψ
    change (nerve.obj S).map
      (op (show (m, n.unop) ⟶ (m, k.unop) from
        (𝟙 m, ψ.unop ≫ θ.unop))) =
      (nerve.obj S).map
        (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop))) ≫
      (nerve.obj S).map
        (op (show (m, n.unop) ⟶ (m, l.unop) from (𝟙 m, ψ.unop)))
    rw [← Functor.map_comp]
    rfl

/-- The original ordinary right-adjoint row is the native lifted Hom from
the actual two-variable JT parameter. -/
def ordinaryRowHomIso (S : SSet.{0}) (m : SimplexCategory) :
    ordinaryRow S m ≅
      EndpointMappingFiber.mapping (Z := S)
        (CategoryTheory.Prod.sectR m SimplexCategory ⋙ tFunctor) :=
  NatIso.ofComponents
    (fun k ↦ (show
      ULift (tFunctor.obj (m, k.unop) ⟶ S) ≃
        ((CategoryTheory.Prod.sectR m SimplexCategory ⋙ tFunctor).obj k.unop ⟶ S) from
      { toFun := ULift.down
        invFun := ULift.up
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }).toIso)
    (by intro k l θ; ext f; rfl)

/-- The original ordinary right-adjoint endpoint operator. -/
def ordinaryRowEndpoint (S : SSet.{0})
    (i : Fin 2) : ordinaryRow S ⦋1⦌ ⟶ ordinaryRow S ⦋0⦌ where
  app k := (nerve.obj S).map
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (ordinaryEndpoint i, 𝟙 k.unop)))
  naturality {k l} θ := by
    funext f
    change ((nerve.obj S).map
      (op (show (⦋1⦌, l.unop) ⟶ (⦋1⦌, k.unop) from
        (𝟙 ⦋1⦌, θ.unop))) ≫
      (nerve.obj S).map
        (op (show (⦋0⦌, l.unop) ⟶ (⦋1⦌, l.unop) from
          (ordinaryEndpoint i, 𝟙 l.unop)))) f =
      ((nerve.obj S).map
        (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
          (ordinaryEndpoint i, 𝟙 k.unop))) ≫
        (nerve.obj S).map
          (op (show (⦋0⦌, l.unop) ⟶ (⦋0⦌, k.unop) from
            (𝟙 ⦋0⦌, θ.unop)))) f
    rw [← (nerve.obj S).map_comp, ← (nerve.obj S).map_comp]
    rfl

/-- The two original ordinary endpoint operators, in order. -/
def ordinaryEndpointArrow (S : SSet.{0}) :
    ordinaryRow S ⦋1⦌ ⟶
      ordinaryRow S ⦋0⦌ ⨯ ordinaryRow S ⦋0⦌ :=
  prod.lift (ordinaryRowEndpoint S 0) (ordinaryRowEndpoint S 1)

private theorem ordinaryEndpointArrow_fst (S : SSet.{0}) :
    ordinaryEndpointArrow S ≫ prod.fst = ordinaryRowEndpoint S 0 :=
  prod.lift_fst _ _

private theorem ordinaryEndpointArrow_snd (S : SSet.{0}) :
    ordinaryEndpointArrow S ≫ prod.snd = ordinaryRowEndpoint S 1 :=
  prod.lift_snd _ _

/-- The actual ordinary endpoint coface on the whole parameter cylinder. -/
private def ordinaryCoface (i : Fin 2) : zeroCylinder ⟶ intervalCylinder :=
  Functor.whiskerRight
    (NatTrans.prod'
      ((Functor.const SimplexCategory).map
        (SSet.stdSimplex.map (ordinaryEndpoint i)))
      (𝟙 GroupoidSimplex.parameter))
    (MonoidalCategory.tensor SSet.{0})

private theorem ordinaryRowEndpoint_app (S : SSet.{0}) (i : Fin 2)
    (k : SimplexCategory) (f : (ordinaryRow S ⦋1⦌).obj (op k)) :
    (ordinaryRowEndpoint S i).app (op k) f =
      ULift.up ((ordinaryCoface i).app k ≫ f.down) := by
  change ULift.up
      ((SSet.stdSimplex.map (ordinaryEndpoint i) ⊗ₘ
        GroupoidSimplex.parameter.map (𝟙 k)) ≫ f.down) = _
  rw [GroupoidSimplex.parameter.map_id]
  rfl

/-- The chosen vertex is constant along the full groupoid parameter. -/
private def ordinaryZeroPointDiagram (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    zeroCylinder ⟶
      (Functor.const SimplexCategory).obj X.toSSet where
  app k := CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
      (GroupoidSimplex.parameter.obj k) ≫
        JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary X x y
  naturality {k l} θ := by
    change (𝟙 (Δ[0] : SSet.{0}) ⊗ₘ GroupoidSimplex.parameter.map θ) ≫
      (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj l) ≫
          JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary X x y) =
      (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj k) ≫
          JTEndpointObjects.boundaryVertexMap i ≫ ordinaryBoundary X x y) ≫ 𝟙 _
    rw [Category.comp_id]
    have h := CartesianMonoidalCategory.tensorHom_fst
      (𝟙 (Δ[0] : SSet.{0})) (GroupoidSimplex.parameter.map θ)
    simpa only [Category.assoc, Category.id_comp] using
      congrArg (fun t ↦ t ≫ JTEndpointObjects.boundaryVertexMap i ≫
        ordinaryBoundary X x y) h

/-- The constant selected vertex in the original ordinary degree-zero row.
The projection discards the full groupoid parameter `J[k]`. -/
def ordinaryVertexPoint (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    (Δ[0] : SSet.{0}) ⟶ ordinaryRow X.toSSet ⦋0⦌ where
  app k _ := ULift.up ((ordinaryZeroPointDiagram X x y i).app k.unop)
  naturality {k l} θ := by
    funext z
    have h := (ordinaryZeroPointDiagram X x y i).naturality θ.unop
    change (ordinaryZeroPointDiagram X x y i).app l.unop =
      zeroCylinder.map θ.unop ≫
        (ordinaryZeroPointDiagram X x y i).app k.unop at h
    change ULift.up ((ordinaryZeroPointDiagram X x y i).app l.unop) =
      ULift.up (zeroCylinder.map θ.unop ≫
        (ordinaryZeroPointDiagram X x y i).app k.unop)
    exact congrArg ULift.up h

/-- The original ordinary right-adjoint ordered point. -/
def ordinaryEndpointPoint (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      ordinaryRow X.toSSet ⦋0⦌ ⨯ ordinaryRow X.toSSet ⦋0⦌ :=
  prod.lift (ordinaryVertexPoint X x y 0) (ordinaryVertexPoint X x y 1)

private theorem ordinaryEndpointPoint_fst (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint X x y ≫ prod.fst =
      ordinaryVertexPoint X x y 0 := prod.lift_fst _ _

private theorem ordinaryEndpointPoint_snd (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryEndpointPoint X x y ≫ prod.snd =
      ordinaryVertexPoint X x y 1 := prod.lift_snd _ _

/-- The categorical strict fiber of the **original** ordinary JT right
adjoint's ordered endpoint arrow at the corresponding constant vertices. -/
def ordinaryOrderedFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} :=
  pullback (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y)

private def ordinaryRowSpan (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : SSet.{0} where
  obj k := {f : intervalCylinder.obj k.unop ⟶ X.toSSet // ∀ i : Fin 2,
    (ordinaryCoface i).app k.unop ≫ f =
      (ordinaryZeroPointDiagram X x y i).app k.unop}
  map {k l} θ f := ⟨intervalCylinder.map θ.unop ≫ f.val, by
    intro i
    have hf := (ordinaryCoface i).naturality θ.unop
    have hp := (ordinaryZeroPointDiagram X x y i).naturality θ.unop
    calc
      (ordinaryCoface i).app l.unop ≫
          (intervalCylinder.map θ.unop ≫ f.val) =
        zeroCylinder.map θ.unop ≫
          ((ordinaryCoface i).app k.unop ≫ f.val) := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ t ≫ f.val) hf.symm
      _ = zeroCylinder.map θ.unop ≫
          (ordinaryZeroPointDiagram X x y i).app k.unop := by
            rw [f.property i]
      _ = (ordinaryZeroPointDiagram X x y i).app l.unop := by
            simpa only [Functor.const_obj_map, Category.comp_id] using hp⟩
  map_id k := by funext f; apply Subtype.ext; simp
  map_comp θ ψ := by funext f; apply Subtype.ext; simp [Functor.map_comp, Category.assoc]

private def ordinaryRowSpanRestriction (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryRowSpan X x y ⟶ ordinaryRow X.toSSet ⦋1⦌ where
  app _ f := ULift.up f.val
  naturality {k l} θ := by
    funext f
    change ULift.up (intervalCylinder.map θ.unop ≫ f.val) =
      ULift.up ((CategoryTheory.Prod.sectR ⦋1⦌ SimplexCategory ⋙ tFunctor).map
        θ.unop ≫ f.val)
    change ULift.up ((𝟙 (Δ[1] : SSet.{0}) ⊗ₘ
      GroupoidSimplex.parameter.map θ.unop) ≫ f.val) =
      ULift.up ((SSet.stdSimplex.map (𝟙 (⦋1⦌ : SimplexCategory)) ⊗ₘ
        GroupoidSimplex.parameter.map θ.unop) ≫ f.val)
    exact congrArg
      (fun h : (Δ[1] : SSet.{0}) ⟶ Δ[1] ↦
        ULift.up ((h ⊗ₘ GroupoidSimplex.parameter.map θ.unop) ≫ f.val))
      (SSet.stdSimplex.map_id ⦋1⦌).symm

private theorem ordinaryRowSpan_square (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryRowSpanRestriction X x y ≫ ordinaryEndpointArrow X.toSSet =
      SSet.stdSimplex.objZeroIsTerminal.from (ordinaryRowSpan X x y) ≫
        ordinaryEndpointPoint X x y := by
  apply prod.hom_ext
  · rw [Category.assoc, ordinaryEndpointArrow_fst,
      Category.assoc, ordinaryEndpointPoint_fst]
    apply NatTrans.ext
    funext k f
    change (ordinaryRowEndpoint X.toSSet 0).app (op k.unop)
        (ULift.up f.val) =
      ULift.up ((ordinaryZeroPointDiagram X x y 0).app k.unop)
    rw [ordinaryRowEndpoint_app]
    exact congrArg ULift.up (f.property 0)
  · rw [Category.assoc, ordinaryEndpointArrow_snd,
      Category.assoc, ordinaryEndpointPoint_snd]
    apply NatTrans.ext
    funext k f
    change (ordinaryRowEndpoint X.toSSet 1).app (op k.unop)
        (ULift.up f.val) =
      ULift.up ((ordinaryZeroPointDiagram X x y 1).app k.unop)
    rw [ordinaryRowEndpoint_app]
    exact congrArg ULift.up (f.property 1)

private theorem ordinaryCone_condition (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌))
    (s : PullbackCone (ordinaryEndpointArrow X.toSSet)
      (ordinaryEndpointPoint X x y))
    (k : SimplexCategoryᵒᵖ) (z : s.pt.obj k) :
    ∀ i : Fin 2,
      (ordinaryCoface i).app k.unop ≫ (s.fst.app k z).down =
        (ordinaryZeroPointDiagram X x y i).app k.unop := by
  intro i
  fin_cases i
  · have h₀ := congrFun (NatTrans.congr_app
      (congrArg (fun t ↦ t ≫
        (prod.fst : ordinaryRow X.toSSet ⦋0⦌ ⨯
          ordinaryRow X.toSSet ⦋0⦌ ⟶ _)) s.condition) k) z
    dsimp only at h₀
    rw [Category.assoc, ordinaryEndpointArrow_fst,
      Category.assoc, ordinaryEndpointPoint_fst] at h₀
    change (ordinaryRowEndpoint X.toSSet 0).app (op k.unop)
        (s.fst.app k z) =
      ULift.up ((ordinaryZeroPointDiagram X x y 0).app k.unop) at h₀
    rw [ordinaryRowEndpoint_app] at h₀
    exact congrArg ULift.down h₀
  · have h₁ := congrFun (NatTrans.congr_app
      (congrArg (fun t ↦ t ≫
        (prod.snd : ordinaryRow X.toSSet ⦋0⦌ ⨯
          ordinaryRow X.toSSet ⦋0⦌ ⟶ _)) s.condition) k) z
    dsimp only at h₁
    rw [Category.assoc, ordinaryEndpointArrow_snd,
      Category.assoc, ordinaryEndpointPoint_snd] at h₁
    change (ordinaryRowEndpoint X.toSSet 1).app (op k.unop)
        (s.fst.app k z) =
      ULift.up ((ordinaryZeroPointDiagram X x y 1).app k.unop) at h₁
    rw [ordinaryRowEndpoint_app] at h₁
    exact congrArg ULift.down h₁

private theorem ordinaryRowSpan_isPullback (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    IsPullback (ordinaryRowSpanRestriction X x y)
      (SSet.stdSimplex.objZeroIsTerminal.from (ordinaryRowSpan X x y))
      (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y) where
  w := ordinaryRowSpan_square X x y
  isLimit' := ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ {
      app k z := ⟨(s.fst.app k z).down, ordinaryCone_condition X x y s k z⟩
      naturality {k l} θ := by
        funext z
        apply Subtype.ext
        have h := congrFun (s.fst.naturality θ) z
        change (s.fst.app l ((s.pt.map θ) z)).down =
          intervalCylinder.map θ.unop ≫ (s.fst.app k z).down
        have hm : intervalCylinder.map θ.unop =
            (CategoryTheory.Prod.sectR ⦋1⦌ SimplexCategory ⋙ tFunctor).map
              θ.unop := by
          change 𝟙 (Δ[1] : SSet.{0}) ⊗ₘ
              GroupoidSimplex.parameter.map θ.unop =
            SSet.stdSimplex.map (𝟙 (⦋1⦌ : SimplexCategory)) ⊗ₘ
              GroupoidSimplex.parameter.map θ.unop
          exact congrArg
            (fun h : (Δ[1] : SSet.{0}) ⟶ Δ[1] ↦
              h ⊗ₘ GroupoidSimplex.parameter.map θ.unop)
            (SSet.stdSimplex.map_id ⦋1⦌).symm
        rw [hm]
        exact congrArg ULift.down h })
    (fun _ ↦ by ext k z; rfl)
    (fun _ ↦ SSet.stdSimplex.objZeroIsTerminal.hom_ext _ _)
    (fun s t ht _ ↦ by
      apply NatTrans.ext
      funext k z
      apply Subtype.ext
      exact congrArg ULift.down (congrFun (NatTrans.congr_app ht k) z))⟩

private def orderedBoundaryVertex (i : Fin 2) :
    (Δ[0] : SSet.{0}) ⟶ boundary :=
  if i = 0 then SSet.boundary₁.ι₀ else SSet.boundary₁.ι₁

private theorem orderedBoundaryVertex_eq (i : Fin 2) :
    orderedBoundaryVertex i = JTEndpointObjects.boundaryVertexMap i := by
  fin_cases i
  · change SSet.boundary₁.ι₀ = JTEndpointObjects.boundaryVertexMap 0
    apply (cancel_mono (SSet.boundary 1).ι).mp
    apply SSet.yonedaEquiv.injective
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    simp only [SSet.yonedaEquiv_comp,
      JTEndpointObjects.boundaryVertexMap, Equiv.apply_symm_apply]
    rfl
  · change SSet.boundary₁.ι₁ = JTEndpointObjects.boundaryVertexMap 1
    apply (cancel_mono (SSet.boundary 1).ι).mp
    apply SSet.yonedaEquiv.injective
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    simp only [SSet.yonedaEquiv_comp,
      JTEndpointObjects.boundaryVertexMap, Equiv.apply_symm_apply]
    rfl

private theorem orderedBoundaryVertex_interval (i : Fin 2) :
    orderedBoundaryVertex i ≫ (SSet.boundary 1).ι =
      SSet.stdSimplex.map (ordinaryEndpoint i) := by
  fin_cases i
  · change SSet.boundary₁.ι₀ ≫ (SSet.boundary 1).ι =
      SSet.stdSimplex.map (ordinaryEndpoint 0)
    rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
    apply SSet.yonedaEquiv.injective
    rfl
  · change SSet.boundary₁.ι₁ ≫ (SSet.boundary 1).ι =
      SSet.stdSimplex.map (ordinaryEndpoint 1)
    rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
    apply SSet.yonedaEquiv.injective
    rfl

private theorem ordinaryCoface_boundary (i : Fin 2) (k : SimplexCategory) :
    (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
      cylinderInclusion.app k = (ordinaryCoface i).app k := by
  change (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
    ((SSet.boundary 1).ι ⊗ₘ 𝟙 (GroupoidSimplex.parameter.obj k)) = _
  rw [MonoidalCategory.tensorHom_id,
    ← MonoidalCategory.comp_whiskerRight,
    orderedBoundaryVertex_interval]
  rfl

private theorem ordinaryPoint_boundary (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2)
    (k : SimplexCategory) :
    (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
      cylinderProjection.app k ≫ ordinaryBoundary X x y =
        (ordinaryZeroPointDiagram X x y i).app k := by
  have h := CartesianMonoidalCategory.whiskerRight_fst
    (orderedBoundaryVertex i) (GroupoidSimplex.parameter.obj k)
  change (orderedBoundaryVertex i ▷ GroupoidSimplex.parameter.obj k) ≫
    CartesianMonoidalCategory.fst boundary (GroupoidSimplex.parameter.obj k) ≫
      ordinaryBoundary X x y = _
  rw [orderedBoundaryVertex_eq i]
  rw [orderedBoundaryVertex_eq i] at h
  simpa only [ordinaryZeroPointDiagram, Category.assoc] using
    congrArg (fun t ↦ t ≫ ordinaryBoundary X x y) h

/-- The original ordinary row's two constant-vertex equations are
equivalent to the accepted literal boundary-cylinder equation. -/
private def ordinaryRowSpanOrdinaryIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryRowSpan X x y ≅ ordinaryOrderedSpanSSet X x y :=
  NatIso.ofComponents (fun k ↦ (show
    (ordinaryRowSpan X x y).obj k ≃
      (ordinaryOrderedSpanSSet X x y).obj k from
    { toFun := fun f ↦ ⟨f.val, by
        apply SSet.boundary₁.hom_ext_rightTensor
          (X := GroupoidSimplex.parameter.obj k.unop)
        · change (orderedBoundaryVertex 0 ▷ GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderInclusion.app k.unop ≫ f.val) =
            (orderedBoundaryVertex 0 ▷ GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderProjection.app k.unop ≫ ordinaryBoundary X x y)
          rw [← Category.assoc, ordinaryCoface_boundary]
          rw [ordinaryPoint_boundary]
          exact f.property 0
        · change (orderedBoundaryVertex 1 ▷ GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderInclusion.app k.unop ≫ f.val) =
            (orderedBoundaryVertex 1 ▷ GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderProjection.app k.unop ≫ ordinaryBoundary X x y)
          rw [← Category.assoc, ordinaryCoface_boundary]
          rw [ordinaryPoint_boundary]
          exact f.property 1⟩
      invFun := fun f ↦ ⟨f.val, by
        intro i
        have h := congrArg
          (fun t ↦ (orderedBoundaryVertex i ▷
            GroupoidSimplex.parameter.obj k.unop) ≫ t) f.property
        change (orderedBoundaryVertex i ▷
            GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderInclusion.app k.unop ≫ f.val) =
          (orderedBoundaryVertex i ▷
            GroupoidSimplex.parameter.obj k.unop) ≫
              (cylinderProjection.app k.unop ≫ ordinaryBoundary X x y) at h
        rw [← Category.assoc, ordinaryCoface_boundary,
          ordinaryPoint_boundary] at h
        exact h⟩
      left_inv := fun f ↦ Subtype.ext rfl
      right_inv := fun f ↦ Subtype.ext rfl }).toIso)
    (by intro k l θ; funext f; apply Subtype.ext; rfl)

/-- The categorical fiber of the original ordinary right adjoint is
the literal ordered boundary-cylinder mapping simplicial set. -/
def ordinaryOrderedFiberIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    ordinaryOrderedFiber X x y ≅ ordinaryOrderedSpanSSet X x y :=
  (ordinaryRowSpan_isPullback X x y).isoPullback.symm ≪≫
    ordinaryRowSpanOrdinaryIso X x y

/-- Restriction of the actual right-adjoint comparison to one literal
horizontal row. -/
def comparisonRow (X : DaggerSSet.{0}) (m : SimplexCategory) :
    daggerRow X (ReverseSimplex.inclusion.obj m) ⟶
      ordinaryRow X.toSSet m where
  app k := (JTUnderlyingRightComparison.comparison.app X).app (op (m, k.unop))
  naturality {k l} θ := by
    have h := (JTUnderlyingRightComparison.comparison.app X).naturality
      (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))
    simpa [daggerRow, ordinaryRow, JTReversalInput.ordinaryInput] using h

/-- The literal comparison on a row is precomposition by the first copy
of the represented dagger frame. -/
private theorem comparisonRow_forward (X : DaggerSSet.{0})
    (m k : SimplexCategory)
    (f : frame.obj (ReverseSimplex.inclusion.obj m, k) ⟶ X) :
    (((comparisonRow X m).app (op k)) (ULift.up f)).down =
      forwardPair.app (m, k) ≫ f.hom := by
  change (((JTUnderlyingRightComparison.comparison.app X).app (op (m, k)))
    (ULift.up f)).down = _
  simpa only [daggerGeneratorEquiv_eq_native] using
    JTRightAdjointForwardNormalization.comparison_on_represented_forward X m k f

/-- At the two chosen constant vertices, the actual right comparison
preserves the specified ordered point. -/
private theorem comparisonRow_vertex (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (i : Fin 2) :
    daggerVertexPoint X x y i ≫ comparisonRow X ⦋0⦌ =
      ordinaryVertexPoint X x y i := by
  apply NatTrans.ext
  funext k z
  have h := comparisonRow_forward X ⦋0⦌ k.unop
    ((endpointCollapse i).app k.unop ≫ daggerBoundary X x y)
  have hz : forwardPair.app (⦋0⦌, k.unop) = forwardFrame0.app k.unop := rfl
  rw [hz] at h
  have hp := JTXiEndpointCollapseBoundary.projectionEndpointSquare i k.unop
  have hb := daggerBoundary_transpose X x y
  rw [Adjunction.homEquiv_unit] at hb
  change freeDaggerAdjunction.unit.app boundary ≫
    (daggerBoundary X x y).hom = ordinaryBoundary X x y at hb
  change ULift.up (((comparisonRow X ⦋0⦌).app k)
      (ULift.up ((endpointCollapse i).app k.unop ≫ daggerBoundary X x y))).down =
    ULift.up ((ordinaryZeroPointDiagram X x y i).app k.unop)
  apply congrArg ULift.up
  rw [h]
  change forwardFrame0.app k.unop ≫
    (DaggerSSet.forget.map ((endpointCollapse i).app k.unop) ≫
      (daggerBoundary X x y).hom) = _
  rw [← Category.assoc, ← hp]
  simp only [Category.assoc]
  rw [hb]
  exact ordinaryPoint_boundary X x y i k.unop

/-- Naturality of the original right comparison at a specified ordered
outer endpoint. -/
private theorem comparisonRow_endpoint_i (X : DaggerSSet.{0})
    (i : Fin 2) :
    (daggerNerve.obj X).map (vertex i).op ≫ comparisonRow X ⦋0⦌ =
      comparisonRow X ⦋1⦌ ≫ ordinaryRowEndpoint X.toSSet i := by
  apply NatTrans.ext
  funext k f
  have h := (JTUnderlyingRightComparison.comparison.app X).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (ordinaryEndpoint i, 𝟙 k.unop)))
  simpa [comparisonRow, ordinaryRowEndpoint,
    JTReversalInput.ordinaryInput, vertex,
    JTXiEndpointCollapseBoundary.ordinaryEndpoint] using congrFun h f

/-- The two endpoint operators form a commutative arrow square for the
actual original right-adjoint comparison. -/
private theorem comparisonRow_endpoint (X : DaggerSSet.{0}) :
    daggerEndpointArrow X ≫
        prod.map (comparisonRow X ⦋0⦌) (comparisonRow X ⦋0⦌) =
      comparisonRow X ⦋1⦌ ≫ ordinaryEndpointArrow X.toSSet := by
  apply prod.hom_ext
  · simpa only [daggerEndpointArrow, ordinaryEndpointArrow,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        comparisonRow_endpoint_i X 0
  · simpa only [daggerEndpointArrow, ordinaryEndpointArrow,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        comparisonRow_endpoint_i X 1

/-- The actual comparison carries the chosen ordered dagger point to the
chosen ordered ordinary point. -/
private theorem comparisonEndpointPoint (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerEndpointPoint X x y ≫
        prod.map (comparisonRow X ⦋0⦌) (comparisonRow X ⦋0⦌) =
      ordinaryEndpointPoint X x y := by
  apply prod.hom_ext
  · simpa only [daggerEndpointPoint, ordinaryEndpointPoint,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        comparisonRow_vertex X x y 0
  · simpa only [daggerEndpointPoint, ordinaryEndpointPoint,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        comparisonRow_vertex X x y 1

/-- The induced arrow between categorical fibers of the two **original**
JT right adjoints. Its definition uses the original right mate and literal
ordered points, before either span isomorphism is applied. -/
def comparisonFiber (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    daggerOrderedFiber X x y ⟶ ordinaryOrderedFiber X x y :=
  pullback.map (daggerEndpointArrow X) (daggerEndpointPoint X x y)
    (ordinaryEndpointArrow X.toSSet) (ordinaryEndpointPoint X x y)
    (comparisonRow X ⦋1⦌) (𝟙 (Δ[0] : SSet.{0}))
    (prod.map (comparisonRow X ⦋0⦌) (comparisonRow X ⦋0⦌))
    (comparisonRow_endpoint X) (by
      simpa only [Category.id_comp] using comparisonEndpointPoint X x y)

/-- The first projection of the induced categorical fiber map is exactly
the original right comparison on the outer-one row. -/
theorem comparisonFiber_fst (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    comparisonFiber X x y ≫
        pullback.fst (ordinaryEndpointArrow X.toSSet)
          (ordinaryEndpointPoint X x y) =
      pullback.fst (daggerEndpointArrow X) (daggerEndpointPoint X x y) ≫
        comparisonRow X ⦋1⦌ := by
  simp only [comparisonFiber, pullback.map, pullback.lift_fst]

/-- The second projection remains the literal constant endpoint simplex. -/
theorem comparisonFiber_snd (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    comparisonFiber X x y ≫
        pullback.snd (ordinaryEndpointArrow X.toSSet)
          (ordinaryEndpointPoint X x y) =
      pullback.snd (daggerEndpointArrow X) (daggerEndpointPoint X x y) := by
  simp only [comparisonFiber, pullback.map, pullback.lift_snd,
    Category.comp_id]

private theorem daggerFiberIso_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (z : (daggerOrderedFiber X x y).obj (op k)) :
    ((daggerOrderedFiberIso X x y).hom.app (op k) z).val =
      ((pullback.fst (daggerEndpointArrow X)
        (daggerEndpointPoint X x y)).app (op k) z).down := by
  have h := congrFun
    (NatTrans.congr_app
      (daggerRowSpan_isPullback X x y).isoPullback_inv_fst (op k)) z
  change ULift.up
    (((daggerRowSpan_isPullback X x y).isoPullback.inv.app (op k) z).val) =
      (pullback.fst (daggerEndpointArrow X)
        (daggerEndpointPoint X x y)).app (op k) z at h
  change (((daggerRowSpan_isPullback X x y).isoPullback.inv.app (op k) z).val) = _
  exact congrArg ULift.down h

private theorem ordinaryFiberIso_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (z : (ordinaryOrderedFiber X x y).obj (op k)) :
    ((ordinaryOrderedFiberIso X x y).hom.app (op k) z).val =
      ((pullback.fst (ordinaryEndpointArrow X.toSSet)
        (ordinaryEndpointPoint X x y)).app (op k) z).down := by
  have h := congrFun
    (NatTrans.congr_app
      (ordinaryRowSpan_isPullback X x y).isoPullback_inv_fst (op k)) z
  change ULift.up
    (((ordinaryRowSpan_isPullback X x y).isoPullback.inv.app (op k) z).val) =
      (pullback.fst (ordinaryEndpointArrow X.toSSet)
        (ordinaryEndpointPoint X x y)).app (op k) z at h
  change (((ordinaryRowSpan_isPullback X x y).isoPullback.inv.app (op k) z).val) = _
  exact congrArg ULift.down h

/-- On the two categorical fibers, the map induced by the original right
comparison is exactly the verified first-copy restriction. -/
theorem comparisonFiber_span (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) :
    comparisonFiber X x y ≫ (ordinaryOrderedFiberIso X x y).hom =
      (daggerOrderedFiberIso X x y).hom ≫
        (orderedSpanSSetIso X x y).hom := by
  apply NatTrans.ext
  funext k z
  apply Subtype.ext
  change ((ordinaryOrderedFiberIso X x y).hom.app k
      ((comparisonFiber X x y).app k z)).val =
    (orderedSpanEquiv X x y k.unop
      ((daggerOrderedFiberIso X x y).hom.app k z)).val
  rw [orderedSpanEquiv_val]
  rw [daggerFiberIso_val, ordinaryFiberIso_val]
  have hf := (congrFun (NatTrans.congr_app
    (comparisonFiber_fst X x y) k) z).symm
  change ((comparisonRow X ⦋1⦌).app k)
      ((pullback.fst (daggerEndpointArrow X)
        (daggerEndpointPoint X x y)).app k z) =
    (pullback.fst (ordinaryEndpointArrow X.toSSet)
      (ordinaryEndpointPoint X x y)).app k
        ((comparisonFiber X x y).app k z) at hf
  have hn := comparisonRow_forward X ⦋1⦌ k.unop
    (((pullback.fst (daggerEndpointArrow X)
      (daggerEndpointPoint X x y)).app k z).down)
  symm
  change forwardFrame.app k.unop ≫
      (((pullback.fst (daggerEndpointArrow X)
        (daggerEndpointPoint X x y)).app k z).down).hom =
    ((pullback.fst (ordinaryEndpointArrow X.toSSet)
      (ordinaryEndpointPoint X x y)).app k
        ((comparisonFiber X x y).app k z)).down
  rw [← hf]
  exact hn.symm

/-- The actual original right-comparison map on the specified ordered
categorical fibers is an isomorphism, with no fibrancy hypothesis. -/
theorem comparisonFiber_isIso (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) : IsIso (comparisonFiber X x y) := by
  let e := daggerOrderedFiberIso X x y ≪≫ orderedSpanSSetIso X x y ≪≫
    (ordinaryOrderedFiberIso X x y).symm
  have he : comparisonFiber X x y = e.hom := by
    apply (cancel_mono (ordinaryOrderedFiberIso X x y).hom).1
    rw [comparisonFiber_span]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he]
  infer_instance


/-- The original ordinary categorical fiber presentation retains the actual
outer-one row projection on every simplex. -/
theorem ordinaryOrderedFiberIso_hom_val (X : DaggerSSet.{0})
    (x y : X.toSSet.obj (op ⦋0⦌)) (k : SimplexCategory)
    (z : (ordinaryOrderedFiber X x y).obj (op k)) :
    ((ordinaryOrderedFiberIso X x y).hom.app (op k) z).val =
      ((pullback.fst (ordinaryEndpointArrow X.toSSet)
        (ordinaryEndpointPoint X x y)).app (op k) z).down :=
  ordinaryFiberIso_val X x y k z

end

end DaggerModels.PartII.JTRightAdjointOrderedFiber
