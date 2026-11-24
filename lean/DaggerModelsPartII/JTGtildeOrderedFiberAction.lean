import DaggerModelsPartII.JTChosenOrdinaryAdjoint
import DaggerModelsPartII.JTRightAdjointOrderedFiber
import DaggerModelsPartII.JTRealizationDiagonal
import DaggerModelsPartII.JTParameterZero
import DaggerModelsPartII.ChosenHomotopyFiberFunctor

/-!
# The literal chosen ordinary JT map on pointed endpoint arrows

The source arrow uses the two original outer cofaces of the ordinary
restriction of the chosen projective input.  The target arrow is the
original ordinary JT right-adjoint arrow of the chosen free-inner target.
The map of arrows is induced by the actual ordinary transpose `gTilde`.
Its chosen-fiber action is defined at the literal image of the source point.
No weak-equivalence assertion is made here.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels

namespace DaggerModels.PartII.JTGtildeOrderedFiberAction

open JTChosenOrdinaryAdjoint JTStrictificationMaps JTStrictificationCoefficients
open JTReversalInput JTRealizationDiagonal JTRightAdjointOrderedFiber
open JTXiEndpointCollapseBoundary OrdinaryJTRealization

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}

/-- The actual two-index ordinary input of the chosen projective resolution. -/
def chosenOrdinaryInput (W : Source) : BiPresheaf :=
  ordinaryInput.obj (Qproj.obj W)

/-- On every represented pair, the transpose evaluates the actual
realization generator followed by the chosen free-inner map. -/
theorem gTilde_generator (W : Source)
    (p : OrdinaryJTRealization.Index)
    (w : (chosenOrdinaryInput W).obj (op p)) :
    (gTilde W).app (op p) w =
      ULift.up
        (JTRealizationGenerators.generator (chosenOrdinaryInput W) p w ≫
          DaggerSSet.forget.map (chosenG W)) := by
  simpa only [gTilde, chosenOrdinaryInput,
    JTRealizationGenerators.generator, realizationNerveAdjunction,
    realization, realizationUnit] using
      (Presheaf.uliftYonedaAdjunction_homEquiv_app
        (L := realization) (α := realizationUnit)
        (f := DaggerSSet.forget.map (chosenG W)) (z := w))

/-- A literal horizontal row of that input. -/
def sourceRow (W : Source) (m : SimplexCategory) : SSet.{0} :=
  (ordinaryCurry.obj (chosenOrdinaryInput W)).obj (op m)

/-- The original first-index coface of the chosen input. -/
def sourceEndpoint (W : Source) (i : Fin 2) :
    sourceRow W ⦋1⦌ ⟶ sourceRow W ⦋0⦌ :=
  (ordinaryCurry.obj (chosenOrdinaryInput W)).map (ordinaryEndpoint i).op

/-- The two literal source cofaces, in their original zero--one order. -/
def sourceEndpointArrow (W : Source) :
    sourceRow W ⦋1⦌ ⟶ sourceRow W ⦋0⦌ ⨯ sourceRow W ⦋0⦌ :=
  prod.lift (sourceEndpoint W 0) (sourceEndpoint W 1)

/-- The actual chosen ordinary transpose, restricted to a horizontal row. -/
def gRow (W : Source) (m : SimplexCategory) :
    sourceRow W m ⟶ ordinaryRow (chosenT W).toSSet m where
  app k := (gTilde W).app (op (m, k.unop))
  naturality {k l} θ := by
    exact (gTilde W).naturality
      (op (show (m, l.unop) ⟶ (m, k.unop) from (𝟙 m, θ.unop)))

/-- Naturality of `gTilde` at the literal outer coface. -/
theorem gRow_endpoint (W : Source) (i : Fin 2) :
    sourceEndpoint W i ≫ gRow W ⦋0⦌ =
      gRow W ⦋1⦌ ≫ ordinaryRowEndpoint (chosenT W).toSSet i := by
  apply NatTrans.ext
  funext k z
  exact congrFun ((gTilde W).naturality
    (op (show (⦋0⦌, k.unop) ⟶ (⦋1⦌, k.unop) from
      (ordinaryEndpoint i, 𝟙 k.unop)))) z

/-- The map on the ordered product of the literal outer-zero rows. -/
def gBase (W : Source) :
    sourceRow W ⦋0⦌ ⨯ sourceRow W ⦋0⦌ ⟶
      ordinaryRow (chosenT W).toSSet ⦋0⦌ ⨯
        ordinaryRow (chosenT W).toSSet ⦋0⦌ :=
  prod.map (gRow W ⦋0⦌) (gRow W ⦋0⦌)

/-- The actual natural-transformation square of the two endpoint arrows. -/
theorem gArrow_square (W : Source) :
    sourceEndpointArrow W ≫ gBase W =
      gRow W ⦋1⦌ ≫ ordinaryEndpointArrow (chosenT W).toSSet := by
  apply prod.hom_ext
  · simpa only [sourceEndpointArrow, gBase, ordinaryEndpointArrow,
      prod.lift_fst, prod.lift_fst_assoc, prod.map_fst, Category.assoc] using
        gRow_endpoint W 0
  · simpa only [sourceEndpointArrow, gBase, ordinaryEndpointArrow,
      prod.lift_snd, prod.lift_snd_assoc, prod.map_snd, Category.assoc] using
        gRow_endpoint W 1

/-- A chosen degree-(0,0) element determines a point in the literal source
outer-zero row by the ordinary simplicial Yoneda equivalence. -/
def sourceVertexPoint (W : Source)
    (x : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶ sourceRow W ⦋0⦌ :=
  SSet.yonedaEquiv.symm x

/-- The specified ordered pair of degree-(0,0) input vertices. -/
def sourcePoint (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      sourceRow W ⦋0⦌ ⨯ sourceRow W ⦋0⦌ :=
  prod.lift (sourceVertexPoint W x) (sourceVertexPoint W y)

/-- The canonical inverse to the first projection at the actual zero
groupoid parameter. This choice is fixed by `parameterZeroIso`. -/
def zeroTensorVertex :
    (Δ[0] : SSet.{0}) ⟶
      ((Δ[0] : SSet.{0}) ⊗ GroupoidSimplex.parameter.obj ⦋0⦌) :=
  CartesianMonoidalCategory.lift (𝟙 (Δ[0] : SSet.{0}))
    JTParameterZero.parameterZeroIso.inv

/-- The zero-parameter section really inverts the first projection. -/
theorem fst_zeroTensorVertex :
    CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫ zeroTensorVertex =
      𝟙 ((Δ[0] : SSet.{0}) ⊗
        GroupoidSimplex.parameter.obj ⦋0⦌) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, zeroTensorVertex,
      CartesianMonoidalCategory.lift_fst, Category.comp_id, Category.id_comp]
  · exact JTParameterZero.parameterZeroIsTerminal.hom_ext _ _

/-- Read the actual vertex of the chosen target represented by a
degree-(0,0) element of its original ordinary right-adjoint row. -/
def targetVertex (W : Source)
    (z : (ordinaryRow (chosenT W).toSSet ⦋0⦌).obj (op ⦋0⦌)) :
    (chosenT W).toSSet.obj (op ⦋0⦌) :=
  let f : ((Δ[0] : SSet.{0}) ⊗
      GroupoidSimplex.parameter.obj ⦋0⦌) ⟶ (chosenT W).toSSet := z.down
  SSet.yonedaEquiv (zeroTensorVertex ≫ f)

/-- The selected target vertex reconstructs the represented zero-row
simplex through the *actual* terminal groupoid parameter. -/
theorem targetVertex_spec (W : Source)
    (z : (ordinaryRow (chosenT W).toSSet ⦋0⦌).obj (op ⦋0⦌)) :
    CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫
        SSet.yonedaEquiv.symm (targetVertex W z) = z.down := by
  rw [show SSet.yonedaEquiv.symm (targetVertex W z) =
      zeroTensorVertex ≫ z.down from
        SSet.yonedaEquiv.symm_apply_apply _]
  rw [← Category.assoc, fst_zeroTensorVertex, Category.id_comp]

/-- The two *actual* chosen-target vertices of the image of the source
degree-(0,0) ordered pair. -/
def targetVertices (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (chosenT W).toSSet.obj (op ⦋0⦌) ×
      (chosenT W).toSSet.obj (op ⦋0⦌) :=
  (targetVertex W ((gRow W ⦋0⦌).app (op ⦋0⦌) x),
    targetVertex W ((gRow W ⦋0⦌).app (op ⦋0⦌) y))

private theorem boundaryVertexMap_zero :
    JTEndpointObjects.boundaryVertexMap 0 = SSet.boundary₁.ι₀ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₀_ι, SSet.stdSimplex.δ_one]
  simp only [SSet.yonedaEquiv_comp, JTEndpointObjects.boundaryVertexMap,
    Equiv.apply_symm_apply]
  rfl

private theorem boundaryVertexMap_one :
    JTEndpointObjects.boundaryVertexMap 1 = SSet.boundary₁.ι₁ := by
  apply (cancel_mono (SSet.boundary 1).ι).mp
  apply SSet.yonedaEquiv.injective
  rw [SSet.boundary₁.ι₁_ι, SSet.stdSimplex.δ_zero]
  simp only [SSet.yonedaEquiv_comp, JTEndpointObjects.boundaryVertexMap,
    Equiv.apply_symm_apply]
  rfl

private theorem targetBoundaryVertex (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) (i : Fin 2) :
    JTEndpointObjects.boundaryVertexMap i ≫
        JTUnderlyingOrderedFibers.ordinaryBoundary (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 =
      SSet.yonedaEquiv.symm
        (if i = 0 then (targetVertices W x y).1
          else (targetVertices W x y).2) := by
  fin_cases i
  · change JTEndpointObjects.boundaryVertexMap 0 ≫
        JTUnderlyingOrderedFibers.ordinaryBoundary (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 =
        SSet.yonedaEquiv.symm (targetVertices W x y).1
    rw [boundaryVertexMap_zero]
    exact SSet.boundary₁.ι₀_desc _ _
  · change JTEndpointObjects.boundaryVertexMap 1 ≫
        JTUnderlyingOrderedFibers.ordinaryBoundary (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 =
        SSet.yonedaEquiv.symm (targetVertices W x y).2
    rw [boundaryVertexMap_one]
    exact SSet.boundary₁.ι₁_desc _ _

/-- The literal image of the source point under the actual base map. -/
def imagePoint (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    (Δ[0] : SSet.{0}) ⟶
      ordinaryRow (chosenT W).toSSet ⦋0⦌ ⨯
        ordinaryRow (chosenT W).toSSet ⦋0⦌ :=
  sourcePoint W x y ≫ gBase W

/-- The image point is the **original** constant point at the two actual
chosen-target vertices. This is the missing degree-zero normalization that
prevents an unrelated choice of target base point. -/
theorem imagePoint_eq_ordinaryEndpointPoint (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    imagePoint W x y =
      ordinaryEndpointPoint (chosenT W)
        (targetVertices W x y).1 (targetVertices W x y).2 := by
  apply prod.hom_ext
  · rw [show imagePoint W x y ≫ prod.fst =
        sourceVertexPoint W x ≫ gRow W ⦋0⦌ from by
          dsimp only [imagePoint, sourcePoint, gBase]
          rw [Category.assoc, prod.map_fst, ← Category.assoc,
            prod.lift_fst]]
    rw [show ordinaryEndpointPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 ≫ prod.fst =
        ordinaryVertexPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 0 from
            prod.lift_fst _ _]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, sourceVertexPoint,
      Equiv.apply_symm_apply]
    change (gRow W ⦋0⦌).app (op ⦋0⦌) x =
      ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫
          JTEndpointObjects.boundaryVertexMap 0 ≫
            JTUnderlyingOrderedFibers.ordinaryBoundary (chosenT W)
              (targetVertices W x y).1 (targetVertices W x y).2)
    rw [targetBoundaryVertex W x y 0]
    exact congrArg ULift.up
      (targetVertex_spec W ((gRow W ⦋0⦌).app (op ⦋0⦌) x)).symm
  · rw [show imagePoint W x y ≫ prod.snd =
        sourceVertexPoint W y ≫ gRow W ⦋0⦌ from by
          dsimp only [imagePoint, sourcePoint, gBase]
          rw [Category.assoc, prod.map_snd, ← Category.assoc,
            prod.lift_snd]]
    rw [show ordinaryEndpointPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 ≫ prod.snd =
        ordinaryVertexPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2 1 from
            prod.lift_snd _ _]
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, sourceVertexPoint,
      Equiv.apply_symm_apply]
    change (gRow W ⦋0⦌).app (op ⦋0⦌) y =
      ULift.up (CartesianMonoidalCategory.fst (Δ[0] : SSet.{0})
        (GroupoidSimplex.parameter.obj ⦋0⦌) ≫
          JTEndpointObjects.boundaryVertexMap 1 ≫
            JTUnderlyingOrderedFibers.ordinaryBoundary (chosenT W)
              (targetVertices W x y).1 (targetVertices W x y).2)
    rw [targetBoundaryVertex W x y 1]
    exact congrArg ULift.up
      (targetVertex_spec W ((gRow W ⦋0⦌).app (op ⦋0⦌) y)).symm

/-- The literal `gTilde W` action on chosen homotopy fibers. Its target
point is the actual image point; the original-vertex normalization is
recorded as a separate theorem below. -/
def chosenFiberMapAtImagePoint (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    ChosenHomotopyFiberComparison.chosenFiber
        (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      ChosenHomotopyFiberComparison.chosenFiber
        (ordinaryEndpointArrow (chosenT W).toSSet)
        (imagePoint W x y) :=
  ChosenHomotopyFiberFunctor.chosenMap
    (sourceEndpointArrow W)
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (sourcePoint W x y) (imagePoint W x y) rfl

/-- The chosen homotopy-fiber action of the literal `gTilde W` square,
now over the original constant point at its actual two target vertices. -/
def chosenFiberMap (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    ChosenHomotopyFiberComparison.chosenFiber
        (sourceEndpointArrow W) (sourcePoint W x y) ⟶
      ChosenHomotopyFiberComparison.chosenFiber
        (ordinaryEndpointArrow (chosenT W).toSSet)
        (ordinaryEndpointPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2) :=
  ChosenHomotopyFiberFunctor.chosenMap
    (sourceEndpointArrow W)
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (sourcePoint W x y)
    (ordinaryEndpointPoint (chosenT W)
      (targetVertices W x y).1 (targetVertices W x y).2)
    (imagePoint_eq_ordinaryEndpointPoint W x y)

/-- The chosen map restricts to the actual strict-fiber action of the
same row square before passage to Kan localization. -/
theorem inclusion_chosenFiberMap (W : Source)
    (x y : (sourceRow W ⦋0⦌).obj (op ⦋0⦌)) :
    ChosenHomotopyFiberTriangle.inclusion
        (sourceEndpointArrow W) (sourcePoint W x y) ≫
          chosenFiberMap W x y =
      DaggerNativeSSetFibrationSquareFibreWeak.fibreMap
        (sourceEndpointArrow W)
        (ordinaryEndpointArrow (chosenT W).toSSet)
        (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
        (sourcePoint W x y)
        (ordinaryEndpointPoint (chosenT W)
          (targetVertices W x y).1 (targetVertices W x y).2)
        (imagePoint_eq_ordinaryEndpointPoint W x y) ≫
          ChosenHomotopyFiberTriangle.inclusion
            (ordinaryEndpointArrow (chosenT W).toSSet)
            (ordinaryEndpointPoint (chosenT W)
              (targetVertices W x y).1 (targetVertices W x y).2) := by
  exact ChosenHomotopyFiberFunctor.inclusion_chosenMap
    (sourceEndpointArrow W)
    (ordinaryEndpointArrow (chosenT W).toSSet)
    (gRow W ⦋1⦌) (gBase W) (gArrow_square W)
    (sourcePoint W x y)
    (ordinaryEndpointPoint (chosenT W)
      (targetVertices W x y).1 (targetVertices W x y).2)
    (imagePoint_eq_ordinaryEndpointPoint W x y)

end

end DaggerModels.PartII.JTGtildeOrderedFiberAction
