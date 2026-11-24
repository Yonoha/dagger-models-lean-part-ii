import DaggerModelsPartII.ReedySeededProperties

/-!
# A Reedy factorization fixed at degree zero

The first stage is the restriction of the source diagram, with identity left
factor and the original map as right factor. The previously constructed seeded
Reedy factorization supplies every higher degree.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C]
  [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y)
  (P Q : MorphismProperty C) [HasFactorization P Q]

/-- Start the factorization with the original source in degree zero. -/
def zeroFixedReedySeed : ReedyFactorizationBelow f 1 where
  mid := lowerDiagram 1 X
  left := 𝟙 _
  right := CategoryTheory.Functor.whiskerLeft (belowDegree 1).ι f
  fac := Category.id_comp _

/-- The middle diagram of the degree-zero-fixed factorization. -/
def zeroFixedReedyMid : SimplexCategoryᵒᵖ ⥤ C :=
  seededReedyMid f P Q (zeroFixedReedySeed f)

/-- The left map is the identity at degree zero. -/
def zeroFixedReedyLeft : X ⟶ zeroFixedReedyMid f P Q :=
  seededReedyLeft f P Q (zeroFixedReedySeed f)

/-- The right map restricts to the original map at degree zero. -/
def zeroFixedReedyRight : zeroFixedReedyMid f P Q ⟶ Y :=
  seededReedyRight f P Q (zeroFixedReedySeed f)

/-- The middle object at degree zero is definitionally the source object. -/
theorem zeroFixedReedyMid_obj_zero :
    (zeroFixedReedyMid f P Q).obj (op ⦋0⦌) = X.obj (op ⦋0⦌) := rfl

/-- The left map at degree zero is literally the identity. -/
theorem zeroFixedReedyLeft_app_zero :
    (zeroFixedReedyLeft f P Q).app (op ⦋0⦌) = 𝟙 (X.obj (op ⦋0⦌)) := rfl

/-- The right map at degree zero is literally the original component. -/
theorem zeroFixedReedyRight_app_zero :
    (zeroFixedReedyRight f P Q).app (op ⦋0⦌) = f.app (op ⦋0⦌) := rfl

/-- The two maps factor the original map in every degree. -/
theorem zeroFixedReedy_fac :
    zeroFixedReedyLeft f P Q ≫ zeroFixedReedyRight f P Q = f :=
  seededReedy_fac f P Q (zeroFixedReedySeed f)

/-- The left relative latching maps lie in `P` when its identity map does. -/
theorem zeroFixedReedyLeft_relative_mem [P.RespectsIso]
    (hzero : P (𝟙 (X.obj (op ⦋0⦌)))) (n : ℕ) :
    P (relativeLatchingMap n (zeroFixedReedyLeft f P Q)) :=
  seededReedyLeft_relative_mem f P Q (zeroFixedReedySeed f)
    (by change P (𝟙 (X.obj (op ⦋0⦌))); exact hzero) n

/-- The right relative matching maps lie in `Q` when the original zero map does. -/
theorem zeroFixedReedyRight_relative_mem [Q.RespectsIso]
    (hzero : Q (f.app (op ⦋0⦌))) (n : ℕ) :
    Q (relativeMatchingMap n (zeroFixedReedyRight f P Q)) :=
  seededReedyRight_relative_mem f P Q (zeroFixedReedySeed f)
    (by change Q (f.app (op ⦋0⦌)); exact hzero) n

/-- For a left class containing identities, only the right factor needs a
degree-zero hypothesis. -/
theorem zeroFixedReedyLeft_relative_mem_of_id
    [P.RespectsIso] [P.ContainsIdentities] (n : ℕ) :
    P (relativeLatchingMap n (zeroFixedReedyLeft f P Q)) :=
  zeroFixedReedyLeft_relative_mem f P Q (P.id_mem _) n

end

end DaggerModels.PartII
