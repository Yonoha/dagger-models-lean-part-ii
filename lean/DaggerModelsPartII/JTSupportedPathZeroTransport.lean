import DaggerModelsPartII.JTEndpointReducedPullbackCover

/-! A pullback comparison after reindexing its diagram. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

open CategoryTheory Limits

namespace DaggerModels.PartII.JTSupportedPathZeroTransport

noncomputable section

variable {I K : Type} [SmallCategory I] [SmallCategory K]
variable (F : K ⥤ I) {A X Y : I ⥤ SSet.{0}}
variable (π : Y ⟶ X) (d : A ⟶ X)
variable {Z : K ⥤ SSet.{0}} (q : Z ⟶ F ⋙ Y) (v : Z ⟶ F ⋙ A)
variable (h : q ≫ Functor.whiskerLeft F π = v ≫ Functor.whiskerLeft F d)

/-- Map a compatible object of the reindexed span into its full old pullback. -/
def lift : Z ⟶ F ⋙ pullback π d where
  app p := ((IsPullback.of_hasPullback π d).map
    ((CategoryTheory.evaluation I SSet.{0}).obj (F.obj p))).lift
      (q.app p) (v.app p) (NatTrans.congr_app h p)
  naturality {p p'} f := by
    let sq := (IsPullback.of_hasPullback π d).map
      ((CategoryTheory.evaluation I SSet.{0}).obj (F.obj p'))
    let sq₀ := (IsPullback.of_hasPullback π d).map
      ((CategoryTheory.evaluation I SSet.{0}).obj (F.obj p))
    apply sq.hom_ext
    · have hp : sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
          (pullback.fst π d).app (F.obj p) = q.app p := sq₀.lift_fst _ _ _
      calc
        _ = Z.map f ≫ q.app p' := by
          rw [Category.assoc]
          exact congrArg (Z.map f ≫ ·) (sq.lift_fst _ _ _)
        _ = q.app p ≫ Y.map (F.map f) := q.naturality f
        _ = (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback.fst π d).app (F.obj p)) ≫ Y.map (F.map f) :=
            congrArg (· ≫ Y.map (F.map f)) hp.symm
        _ = _ := by
          change (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback.fst π d).app (F.obj p)) ≫ Y.map (F.map f) =
            (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback π d).map (F.map f)) ≫
                (pullback.fst π d).app (F.obj p')
          rw [Category.assoc, ← (pullback.fst π d).naturality (F.map f)]
          exact (Category.assoc _ _ _).symm
    · have hp : sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
          (pullback.snd π d).app (F.obj p) = v.app p := sq₀.lift_snd _ _ _
      calc
        _ = Z.map f ≫ v.app p' := by
          rw [Category.assoc]
          exact congrArg (Z.map f ≫ ·) (sq.lift_snd _ _ _)
        _ = v.app p ≫ A.map (F.map f) := v.naturality f
        _ = (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback.snd π d).app (F.obj p)) ≫ A.map (F.map f) :=
            congrArg (· ≫ A.map (F.map f)) hp.symm
        _ = _ := by
          change (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback.snd π d).app (F.obj p)) ≫ A.map (F.map f) =
            (sq₀.lift (q.app p) (v.app p) (NatTrans.congr_app h p) ≫
              (pullback π d).map (F.map f)) ≫
                (pullback.snd π d).app (F.obj p')
          rw [Category.assoc, ← (pullback.snd π d).naturality (F.map f)]
          exact (Category.assoc _ _ _).symm


theorem lift_fst : lift F π d q v h ≫ Functor.whiskerLeft F (pullback.fst π d) = q := by
  apply NatTrans.ext
  funext p
  exact ((IsPullback.of_hasPullback π d).map
    ((CategoryTheory.evaluation I SSet.{0}).obj (F.obj p))).lift_fst _ _ _

theorem lift_snd : lift F π d q v h ≫ Functor.whiskerLeft F (pullback.snd π d) = v := by
  apply NatTrans.ext
  funext p
  exact ((IsPullback.of_hasPullback π d).map
    ((CategoryTheory.evaluation I SSet.{0}).obj (F.obj p))).lift_snd _ _ _

section Pushout

variable {A' X' B' P Q : K ⥤ SSet.{0}}
variable (u : A' ⟶ X') (e : A' ⟶ B')
variable (l : X' ⟶ P) (r : B' ⟶ P)
variable (sq : ∀ p : K, IsPushout (u.app p) (e.app p) (l.app p) (r.app p))
variable (a : X' ⟶ Q) (b : B' ⟶ Q) (hab : u ≫ a = e ≫ b)

/-- Descend a natural cocone through a pointwise pushout after reindexing. -/
def pushoutDesc : P ⟶ Q where
  app p := (sq p).desc (a.app p) (b.app p) (NatTrans.congr_app hab p)
  naturality {p p'} f := by
    apply (sq p).hom_ext
    · calc
        l.app p ≫ (P.map f ≫ (sq p').desc (a.app p') (b.app p')
            (NatTrans.congr_app hab p')) =
          (X'.map f ≫ l.app p') ≫ (sq p').desc (a.app p') (b.app p')
            (NatTrans.congr_app hab p') := by rw [← Category.assoc, l.naturality f]
        _ = X'.map f ≫ a.app p' := by rw [Category.assoc, (sq p').inl_desc]
        _ = a.app p ≫ Q.map f := a.naturality f
        _ = (l.app p ≫ (sq p).desc (a.app p) (b.app p)
            (NatTrans.congr_app hab p)) ≫ Q.map f := by
          rw [(sq p).inl_desc]
    · calc
        r.app p ≫ (P.map f ≫ (sq p').desc (a.app p') (b.app p')
            (NatTrans.congr_app hab p')) =
          (B'.map f ≫ r.app p') ≫ (sq p').desc (a.app p') (b.app p')
            (NatTrans.congr_app hab p') := by rw [← Category.assoc, r.naturality f]
        _ = B'.map f ≫ b.app p' := by rw [Category.assoc, (sq p').inr_desc]
        _ = b.app p ≫ Q.map f := b.naturality f
        _ = (r.app p ≫ (sq p).desc (a.app p) (b.app p)
            (NatTrans.congr_app hab p)) ≫ Q.map f := by
          rw [(sq p).inr_desc]

theorem pushoutDesc_inl : l ≫ pushoutDesc u e l r sq a b hab = a := by
  apply NatTrans.ext
  funext p
  exact (sq p).inl_desc _ _ _

theorem pushoutDesc_inr : r ≫ pushoutDesc u e l r sq a b hab = b := by
  apply NatTrans.ext
  funext p
  exact (sq p).inr_desc _ _ _

end Pushout

end
end DaggerModels.PartII.JTSupportedPathZeroTransport
