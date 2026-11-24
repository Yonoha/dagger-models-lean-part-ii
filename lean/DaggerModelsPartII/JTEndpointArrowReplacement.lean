import DaggerModelsPartII.ProjectiveArrowInitial
import DaggerModelsPartII.JTEndpointCofibrancy
import DaggerModelsPartII.JTEndpointMateUnder
import DaggerModelsPartII.ReedyZeroFixedFactorization

/-!
# The two-stage zero-fixed replacement of the actual ordered arrow comparison

The first stage replaces the Gamma endpoint arrow as a Reedy cofibrant
cosimplicial arrow while preserving its actual degree-zero arrow. The second
stage factors the original Gamma-to-Xi comparison through that replacement.
The projective Arrow weak factorization system uses the actual pushout corner.
The actual degree-zero projective-cofibration input is proved from the free
boundary and ordered inclusion, calibrated by the zero-arrow isomorphism.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open DaggerModels

namespace DaggerModels.PartII.JTEndpointArrowReplacement

open JTEndpointHom JTEndpointMateUnder JTRelativeReedyFrame
open JTActualCosimplicialFrame ProjectiveArrowFactorization

noncomputable section

private local instance : ModelCategory Coefficient :=
  DaggerActualRigidificationQuillen.modelG.{0}
private local instance : HasLimits Coefficient := daggerSimplicialCatHasLimits
private local instance : HasColimits Coefficient := daggerSimplicialCatHasColimits

/-- A natural transformation is its literal diagram of commuting arrows. -/
def arrowsOf {S T : SimplexCategory ⥤ Coefficient} (u : S ⟶ T) :
    SimplexCategory ⥤ Arrow Coefficient where
  obj k := Arrow.mk (u.app k)
  map {j k} θ := Arrow.homMk (S.map θ) (T.map θ) (u.naturality θ)
  map_id k := by
    apply Arrow.hom_ext
    · exact S.map_id k
    · exact T.map_id k
  map_comp {i j k} θ ψ := by
    apply Arrow.hom_ext
    · exact S.map_comp θ ψ
    · exact T.map_comp θ ψ

/-- A commuting square of natural transformations is a map of their arrow diagrams. -/
def arrowsOfMap {S T S' T' : SimplexCategory ⥤ Coefficient}
    (u : S ⟶ T) (u' : S' ⟶ T')
    (a : S ⟶ S') (b : T ⟶ T') (h : u ≫ b = a ≫ u') :
    arrowsOf u ⟶ arrowsOf u' where
  app k := Arrow.homMk (a.app k) (b.app k) (by
    exact (congrArg (fun t ↦ t.app k) h).symm)
  naturality {j k} θ := by
    apply Arrow.hom_ext
    · exact a.naturality θ
    · exact b.naturality θ

/-- The manuscript's actual Gamma endpoint arrow, before collapse. -/
def G : SimplexCategory ⥤ Arrow Coefficient :=
  arrowsOf (endpointFaces Gamma)

/-- The manuscript's actual represented Xi endpoint arrow, before collapse. -/
def X : SimplexCategory ⥤ Arrow Coefficient :=
  arrowsOf (endpointFaces XiCurried)

/-- The literal Gamma-to-Xi arrow comparison with both ordered endpoint faces. -/
def lambda : G ⟶ X :=
  arrowsOfMap (endpointFaces Gamma) (endpointFaces XiCurried)
    comparisonSource comparisonOne comparison_faces

/-- The degree-zero arrow frozen by both stages is the actual Xi arrow. -/
def zeroArrow : Arrow Coefficient :=
  Arrow.mk ((endpointFaces XiCurried).app ⦋0⦌)

/-- No auxiliary boundary object is substituted for the literal zero arrow. -/
theorem X_obj_zero : X.obj ⦋0⦌ = zeroArrow := rfl

/-- The source zero arrow is the same actual arrow, using the fixed Gamma zero degree. -/
theorem G_obj_zero : G.obj ⦋0⦌ = zeroArrow := by
  rfl

/-- The literal Gamma-to-Xi arrow comparison is the identity on the
actual degree-zero endpoint arrow. -/
theorem lambda_zero : lambda.app ⦋0⦌ = 𝟙 zeroArrow := by
  apply Arrow.hom_ext
  · change coprod.map ((comparison.app ⦋0⦌).app JTZeroObjects.zeroIndex)
      ((comparison.app ⦋0⦌).app JTZeroObjects.zeroIndex) = 𝟙 _
    rw [JTRelativeReedyFrame.comparison_zero]
    change coprod.map (𝟙 _) (𝟙 _) = 𝟙 _
    exact coprod.map_id_id
  · change (comparison.app ⦋0⦌).app JTOrderedFrameMate.oneIndex = 𝟙 _
    rw [JTRelativeReedyFrame.comparison_zero]
    rfl

/-- The actual zero endpoint arrow is projectively cofibrant by the
original free boundary and its calibrated ordered inclusion. -/
theorem zeroArrow_projectiveCof :
    projectiveArrowCofibrations (initial.to zeroArrow) :=
  (ProjectiveArrowInitial.projective_initial_iff zeroArrow).2
    ⟨JTEndpointCofibrancy.source_zero_isCofibrant,
      JTEndpointCofibrancy.zeroFace_isCofibration⟩

/-- The opposite classes of the checked first projective Arrow WFS. -/
def leftClass : MorphismProperty (Arrow Coefficient)ᵒᵖ :=
  (pointwiseArrowTrivialFibrations (C := Coefficient)).op

def rightClass : MorphismProperty (Arrow Coefficient)ᵒᵖ :=
  (projectiveArrowCofibrations (C := Coefficient)).op

private local instance : HasFactorization leftClass rightClass := by
  dsimp only [leftClass, rightClass]
  infer_instance

private local instance : leftClass.IsStableUnderRetracts := by
  dsimp only [leftClass]
  infer_instance

private local instance : rightClass.IsStableUnderRetracts := by
  dsimp only [rightClass]
  infer_instance

/-- The opposite of the checked walking-arrow projective WFS. -/
private theorem arrowWfsOp : IsWeakFactorizationSystem leftClass rightClass := by
  letI := projectiveArrowWfs (C := Coefficient)
  apply IsWeakFactorizationSystem.mk' _ _
  intro A B U V i p hi hp
  exact (hasLiftingProperty_of_wfs p.unop i.unop hp hi).op

private local instance : IsWeakFactorizationSystem leftClass rightClass := arrowWfsOp

private local instance : leftClass.RespectsIso := inferInstance
private local instance : rightClass.RespectsIso := inferInstance

private local instance : leftClass.ContainsIdentities := by
  rw [← llp_eq_of_wfs leftClass rightClass]
  infer_instance

/-- Relative latching membership in the opposite trivial-fibration class
gives membership at each actual cosimplicial degree. -/
private theorem leftClass_component
    {U V : SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ} (f : U ⟶ V)
    (hf : reedyLatchingProperty leftClass f) (n : ℕ) :
    leftClass (f.app (op ⦋n⦌)) := by
  letI : leftClass.IsStableUnderCobaseChange := by
    rw [← llp_eq_of_wfs leftClass rightClass]
    infer_instance
  letI : leftClass.IsMultiplicative := by
    rw [← llp_eq_of_wfs leftClass rightClass]
    infer_instance
  have hm : leftClass ((latchingFunctor n).map f) := by
    rw [← llp_eq_of_wfs leftClass rightClass]
    apply latchingFunctor_map_llp
    intro m _
    rw [llp_eq_of_wfs leftClass rightClass]
    exact hf m
  rw [← inl_comp_relativeLatchingMap f n]
  exact leftClass.comp_mem _ _ (leftClass.pushout_inl _ _ hm) (hf n)

/-- The first opposite factorization is fixed at the literal degree-zero arrow. -/
def firstInput : G.op ⟶
    (⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)) :=
  terminal.from G.op

/-- The first zero-fixed input has the right-class premise at the actual
zero endpoint arrow, without identifying all dagger objects as cofibrant. -/
theorem firstInput_zero_rightClass :
    rightClass (firstInput.app (op ⦋0⦌)) := by
  let A : Arrow Coefficient :=
    ((⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)).obj (op ⦋0⦌)).unop
  have hT : IsTerminal
      ((⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)).obj (op ⦋0⦌)) :=
    terminalIsTerminal.isTerminalObj
      ((evaluation SimplexCategoryᵒᵖ (Arrow Coefficient)ᵒᵖ).obj (op ⦋0⦌)) _
  have hA : IsInitial A := initialUnopOfTerminal hT
  change projectiveArrowCofibrations ((firstInput.app (op ⦋0⦌)).unop)
  apply ProjectiveArrowInitial.projective_of_isInitial A _ hA
  · change IsCofibrant zeroArrow.left
    exact JTEndpointCofibrancy.source_zero_isCofibrant
  · change Cofibration zeroArrow.hom
    exact JTEndpointCofibrancy.zeroFace_isCofibration

def QGop : SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ :=
  zeroFixedReedyMid firstInput leftClass rightClass

def firstLeft : G.op ⟶ QGop :=
  zeroFixedReedyLeft firstInput leftClass rightClass

def firstRight : QGop ⟶
    (⊤_ (SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ)) :=
  zeroFixedReedyRight firstInput leftClass rightClass

/-- Factor the original comparison after the first opposite left factor. -/
def secondInput : X.op ⟶ QGop :=
  NatTrans.op lambda ≫ firstLeft

/-- The second zero-fixed input is the identity on the original zero arrow. -/
theorem secondInput_zero :
    secondInput.app (op ⦋0⦌) = 𝟙 (X.op.obj (op ⦋0⦌)) := by
  change (lambda.app ⦋0⦌).op ≫
    (zeroFixedReedyLeft firstInput leftClass rightClass).app (op ⦋0⦌) = 𝟙 _
  rw [lambda_zero, zeroFixedReedyLeft_app_zero]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

/-- The second zero-fixed input also satisfies the actual right-class
premise, now by identity membership rather than extra cofibrancy. -/
theorem secondInput_zero_rightClass :
    rightClass (secondInput.app (op ⦋0⦌)) := by
  rw [secondInput_zero, ← rlp_eq_of_wfs leftClass rightClass]
  exact (leftClass.rlp).id_mem _

def QXop : SimplexCategoryᵒᵖ ⥤ (Arrow Coefficient)ᵒᵖ :=
  zeroFixedReedyMid secondInput leftClass rightClass

def secondLeft : X.op ⟶ QXop :=
  zeroFixedReedyLeft secondInput leftClass rightClass

def secondRight : QXop ⟶ QGop :=
  zeroFixedReedyRight secondInput leftClass rightClass

/-- The first replacement map has relative latching maps in the opposite
pointwise trivial-fibration class. -/
theorem firstLeft_relative (n : ℕ) :
    leftClass (relativeLatchingMap n firstLeft) :=
  zeroFixedReedyLeft_relative_mem_of_id firstInput leftClass rightClass n

/-- The first terminal projection has actual projective relative matching
maps, including the zero map justified by the original ordered inclusion. -/
theorem firstRight_relative (n : ℕ) :
    rightClass (relativeMatchingMap n firstRight) :=
  zeroFixedReedyRight_relative_mem firstInput leftClass rightClass
    firstInput_zero_rightClass n

/-- The second replacement map has relative latching maps in the same class. -/
theorem secondLeft_relative (n : ℕ) :
    leftClass (relativeLatchingMap n secondLeft) :=
  zeroFixedReedyLeft_relative_mem_of_id secondInput leftClass rightClass n

/-- The comparison of the two replacements has actual projective relative
matching maps, with its zero component supplied by the identity. -/
theorem secondRight_relative (n : ℕ) :
    rightClass (relativeMatchingMap n secondRight) :=
  zeroFixedReedyRight_relative_mem secondInput leftClass rightClass
    secondInput_zero_rightClass n

/-- The composite to the terminal opposite arrow diagram has relative
matching maps in the opposite of the projective Arrow cofibration class.
Thus it witnesses original Reedy cofibrancy of the second replacement. -/
theorem QX_terminal_relativeMatching :
    reedyMatchingProperty rightClass (secondRight ≫ firstRight) := by
  letI : IsWeakFactorizationSystem (reedyLatchingProperty leftClass)
      (reedyMatchingProperty rightClass) :=
    reedyRelativeWeakFactorizationSystem leftClass rightClass
  letI : (reedyMatchingProperty rightClass).IsMultiplicative := by
    rw [← rlp_eq_of_wfs (reedyLatchingProperty leftClass)
      (reedyMatchingProperty rightClass)]
    infer_instance
  exact (reedyMatchingProperty rightClass).comp_mem _ _
    secondRight_relative firstRight_relative

/-- The two actual replacement arrows and their literal comparison. -/
def QG : SimplexCategory ⥤ Arrow Coefficient := QGop.unop
def QX : SimplexCategory ⥤ Arrow Coefficient := QXop.unop

def qG : QG ⟶ G :=
  NatTrans.unop firstLeft ≫ (Functor.opUnopIso G).hom

def qX : QX ⟶ X :=
  NatTrans.unop secondLeft ≫ (Functor.opUnopIso X).hom

def Qlambda : QG ⟶ QX := NatTrans.unop secondRight

/-- The replacement comparison is the actual two-stage factorization of
the original Gamma-to-Xi endpoint comparison. -/
theorem Qlambda_square : Qlambda ≫ qX = qG ≫ lambda := by
  apply NatTrans.ext
  funext n
  have h := congrArg (fun t : X.op ⟶ QGop ↦ (t.app (op n)).unop)
    (zeroFixedReedy_fac secondInput leftClass rightClass)
  change (secondRight.app (op n)).unop ≫ (secondLeft.app (op n)).unop =
    (firstLeft.app (op n)).unop ≫ lambda.app n
  simpa only [secondInput, NatTrans.comp_app, unop_comp,
    NatTrans.op_app, Quiver.Hom.unop_op] using h

/-- Every degree of the first replacement map is a pointwise original
trivial fibration of ordered arrows. -/
theorem qG_pointwiseTF (n : ℕ) :
    pointwiseArrowTrivialFibrations (qG.app ⦋n⦌) := by
  have h := leftClass_component firstLeft firstLeft_relative n
  change pointwiseArrowTrivialFibrations (firstLeft.app (op ⦋n⦌)).unop at h
  change pointwiseArrowTrivialFibrations
    ((firstLeft.app (op ⦋n⦌)).unop ≫ 𝟙 _)
  simpa only [Category.comp_id] using h

/-- Every degree of the second replacement map is a pointwise original
trivial fibration of ordered arrows. -/
theorem qX_pointwiseTF (n : ℕ) :
    pointwiseArrowTrivialFibrations (qX.app ⦋n⦌) := by
  have h := leftClass_component secondLeft secondLeft_relative n
  change pointwiseArrowTrivialFibrations (secondLeft.app (op ⦋n⦌)).unop at h
  change pointwiseArrowTrivialFibrations
    ((secondLeft.app (op ⦋n⦌)).unop ≫ 𝟙 _)
  simpa only [Category.comp_id] using h

/-- Both source and target components of each first replacement map are
weak equivalences in the original dagger Bergner model. -/
theorem qG_pointwiseWeak (n : ℕ) :
    weakEquivalences Coefficient (qG.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (qG.app ⦋n⦌).right := by
  exact ⟨(qG_pointwiseTF n).1.2, (qG_pointwiseTF n).2.2⟩

/-- Both source and target components of each second replacement map are
weak equivalences in the original dagger Bergner model. -/
theorem qX_pointwiseWeak (n : ℕ) :
    weakEquivalences Coefficient (qX.app ⦋n⦌).left ∧
      weakEquivalences Coefficient (qX.app ⦋n⦌).right := by
  exact ⟨(qX_pointwiseTF n).1.2, (qX_pointwiseTF n).2.2⟩

/-- The first replacement remains literally fixed at degree zero. -/
theorem QGop_zero : QGop.obj (op ⦋0⦌) = G.op.obj (op ⦋0⦌) :=
  zeroFixedReedyMid_obj_zero firstInput leftClass rightClass

/-- The second replacement remains literally fixed at degree zero. -/
theorem QXop_zero : QXop.obj (op ⦋0⦌) = X.op.obj (op ⦋0⦌) :=
  zeroFixedReedyMid_obj_zero secondInput leftClass rightClass

/-- The first replacement map is literally the identity in degree zero. -/
theorem qG_zero : qG.app ⦋0⦌ = 𝟙 zeroArrow := by
  change (firstLeft.app (op ⦋0⦌)).unop ≫ 𝟙 _ = 𝟙 _
  rw [show firstLeft.app (op ⦋0⦌) = 𝟙 _ from
    zeroFixedReedyLeft_app_zero firstInput leftClass rightClass]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

/-- The second replacement map is literally the identity in degree zero. -/
theorem qX_zero : qX.app ⦋0⦌ = 𝟙 zeroArrow := by
  change (secondLeft.app (op ⦋0⦌)).unop ≫ 𝟙 _ = 𝟙 _
  rw [show secondLeft.app (op ⦋0⦌) = 𝟙 _ from
    zeroFixedReedyLeft_app_zero secondInput leftClass rightClass]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  exact Category.id_comp _

end

end DaggerModels.PartII.JTEndpointArrowReplacement
