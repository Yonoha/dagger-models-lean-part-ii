import DaggerModelsPartII.DaggerJTAdjunction
import DaggerModelsPartII.RepresentableTensorAdjunction
import DaggerModelsPartII.DiagramPushoutProduct

/-!
# Represented frames of the dagger JT realization

The product Yoneda presheaf on the reversal and ordinary simplex indices
corresponds to the actual representable diagram tensored with the ordinary
simplex. Applying the already constructed dagger realization gives the
manuscript's represented dagger frame.
-/

set_option autoImplicit false

open CategoryTheory Opposite MonoidalCategory DaggerModels

namespace DaggerModels.PartII.DaggerJTRepresentedFrames

open SegalLocalizers DaggerJTAdjunction DaggerJTRealization

noncomputable section

/-- The Yoneda represented pair transported to the two-direction source. -/
def representedPair : DaggerIndex ⥤ ReverseDaggerSpace.{0} :=
  uliftYoneda.{0} ⋙ sourceEquivalence.inverse

/-- The literal representable tensor, functorial in both indices. -/
def representedTensorPair : DaggerIndex ⥤ ReverseDaggerSpace.{0} :=
  ((simplicialYoneda.{0, 0} ReverseSimplex).prod SSet.stdSimplex.{0}) ⋙
    Functor.uncurry.obj
      (InjectiveKanDiagram.curriedDiagramTensor ReverseSimplexᵒᵖ)

@[simp] theorem representedTensorPair_obj (m : ReverseSimplex)
    (k : SimplexCategory) :
    representedTensorPair.obj (m, k) =
      (representableTensor m).obj (SSet.stdSimplex.obj k) := rfl

/-- On each bidegree, distribute the universe lift over the pair of
representable coordinates and identify the vertical Hom with a simplex. -/
def representedPointEquiv (m : ReverseSimplex) (k : SimplexCategory)
    (d : ReverseSimplex) (n : SimplexCategory) :
    ((representedPair.obj (m, k)).obj (op d)).obj (op n) ≃
      ((representedTensorPair.obj (m, k)).obj (op d)).obj (op n) where
  toFun x :=
    (ULift.up x.down.1, SSet.stdSimplex.objEquiv.symm x.down.2)
  invFun x :=
    ULift.up (x.1.down, SSet.stdSimplex.objEquiv x.2)
  left_inv x := by
    cases x with
    | up x =>
      cases x
      simp only [Equiv.apply_symm_apply]
  right_inv x := by
    rcases x with ⟨⟨f⟩, y⟩
    simp only [Equiv.symm_apply_apply]

/-- The represented product and the literal representable tensor agree as
two-direction simplicial presheaves. -/
def representedPairIso (m : ReverseSimplex) (k : SimplexCategory) :
    representedPair.obj (m, k) ≅ representedTensorPair.obj (m, k) :=
  NatIso.ofComponents
    (fun d => NatIso.ofComponents
      (fun n => (representedPointEquiv m k d.unop n.unop).toIso)
      (by
        intro n n' f
        ext x
        rfl))
    (by
      intro d d' f
      apply NatTrans.ext
      funext n x
      rcases x with ⟨⟨u, v⟩⟩
      simp [representedPair, representedTensorPair, representedPointEquiv,
        sourceEquivalence, InjectiveKanDiagram.curriedDiagramTensor,
        diagramTensor, tensorRight, simplicialYoneda, discretePresheaf, uliftYoneda])

/-- The comparison is jointly natural in the horizontal and vertical
representing simplices. -/
def representedPairNatIso : representedPair ≅ representedTensorPair :=
  NatIso.ofComponents (fun p => representedPairIso p.1 p.2) (by
    intro p q f
    apply NatTrans.ext
    funext d
    apply NatTrans.ext
    funext n x
    rfl)

/-- Apply the actual dagger realization to the represented-pair comparison. -/
def daggerFrameNatIso :
    representedPair ⋙ daggerRealization ≅
      representedTensorPair ⋙ daggerRealization :=
  Functor.isoWhiskerRight representedPairNatIso daggerRealization

/-- The adjunction's frame is naturally the dagger realization of
`yoneda_rev[m] × Δ[k]`, in both indices. -/
def frameRepresentation :
    frame ≅ representedTensorPair ⋙ daggerRealization :=
  (Functor.associator _ _ _).symm ≪≫ daggerFrameNatIso

end

end DaggerModels.PartII.DaggerJTRepresentedFrames
