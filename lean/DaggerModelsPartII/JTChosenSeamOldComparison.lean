import DaggerModelsPartII.JTChosenSeamChainDiagram

/-! Compare the chosen collapsed seam with the literal old surrounding label. -/

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTChosenSeamOldComparison

open JTProjectiveOrderedFiberComparison (row vertexPoint endpointArrow)
open JTJointSubcomplexRelativeLift (boundaryPair reverseBoundaryPair identityOnU)
open TripleBeadEndpointLabel (labels)
open ReversalDiscreteFreeColimits (discreteFree)
open JTThreePieceLabelOperators (Data index indexMap indexMap_projection)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) := (row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev std := SSet.stdSimplex.{0}
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from
private abbrev pre (W : Source) {X Y : SSet.{0}} (u : X ⟶ Y) :=
  diagramMappingPrecomp (discreteFree.map u) W

variable {I : Type} [SmallCategory I] (W : Source) (z : Vertex W)
variable (U : I ⥤ SSet.{0}) (K : I ⥤ SimplexCategory)
private abbrev Domain := K ⋙ std
variable (incl : U ⟶ Domain K)
variable (f : Domain K ⟶ (Functor.const I).obj (row W ⦋0⦌))
variable (e s : Domain K ⟶ (Functor.const I).obj (row W ⦋1⦌))
variable (he : ∀ a : I, e.app a ≫ endpointArrow W = boundaryPair W (f.app a) z)
variable (hs : ∀ a : I, s.app a ≫ endpointArrow W =
  reverseBoundaryPair W (f.app a) z)
variable (hfU : ∀ a : I, incl.app a ≫ f.app a =
  term (U.obj a) ≫ vertexPoint W z)
variable (heU : ∀ a : I, incl.app a ≫ e.app a = identityOnU W z)
variable (hsU : ∀ a : I, incl.app a ≫ s.app a = identityOnU W z)
variable {x y : Vertex W} {P R : I ⥤ NecklaceCode}
variable (O : JTChosenSeamChainDiagram.Surroundings W K f P R x y)

private abbrev C := JTChosenSeamChainDiagram.Index W z U K incl f e s he hs hfU heU hsU
private abbrev base := JTChosenSeamChainDiagram.toOriginal W z U K incl f e s he hs hfU heU hsU
private abbrev degree := JTChosenSeamChainDiagram.ordinals W z U K incl f e s he hs hfU heU hsU
private abbrev alpha := JTChosenSeamChainDiagram.toOld W z U K incl f e s he hs hfU heU hsU
private abbrev chosen := JTChosenSeamChainDiagram.seamFamily
  W z U K incl f e s he hs hfU heU hsU O
private abbrev collapsed := JTWhiskeredSeamDiagram.collapsedFamily
  (chosen W z U K incl f e s he hs hfU heU hsU O)

private abbrev proj (W : Source) (x y : Vertex W) :=
  OrderedLabelElements.projection W (OrderedNecklaceVertexPoints.boundaryPoint W x y)

private instance : (proj W x y).Faithful := by
  change ((CategoryOfElements.π _).leftOp).Faithful
  infer_instance

private theorem pre_id (T : NecklaceCode) :
    pre W ((𝟙 T : T ⟶ T).map) = 𝟙 (labels W T) := by
  change diagramMappingPrecomp (discreteFree.map (𝟙 T.toSSet)) W = 𝟙 _
  rw [discreteFree.map_id]
  exact diagramMappingPrecomp_id _ W

/-- The literal old three-piece coefficient on the ORIGINAL index and degree. -/
def oldData (a : I) : Data W (P.obj a) (single 0) (R.obj a) (K.obj a) x y where
  left := O.left a
  middle := f.app a ≫ JTNativeRowLabel.labelFromRow W 0
  right := O.right a
  left_join := O.left_join a
  right_join := O.right_join a
  first := O.first a
  last := O.last a

/-- Genuine original-index decorated labels, before adding any seam filler. -/
def oldFamily : JTWhiskeredSeamDiagram.Family
    (W := W) (x := x) (y := y) (single 0) P R K where
  data := oldData W K f O
  left_nat g := O.left_nat g
  middle_nat := by
    intro a b g
    have h := congrArg (fun t ↦ t ≫ JTNativeRowLabel.labelFromRow W 0)
      (f.naturality g).symm
    simpa only [Category.assoc, Category.comp_id] using h
  right_nat g := O.right_nat g

variable (p : C W z U K incl f e s he hs hfU heU hsU)

/-- The collapsed chosen label restricts to the literal old coefficient
along the exact old-degree projection, with identity native operators. -/
def component :
    index ((collapsed W z U K incl f e s he hs hfU heU hsU O).data p) ⟶
      index (oldData W K f O ((base W z U K incl f e s he hs hfU heU hsU).obj p)) := by
  let a := (base W z U K incl f e s he hs hfU heU hsU).obj p
  let v := (alpha W z U K incl f e s he hs hfU heU hsU).app p
  apply indexMap
    ((collapsed W z U K incl f e s he hs hfU heU hsU O).data p)
    (oldData W K f O a) (𝟙 (P.obj a)) (𝟙 (single 0)) (𝟙 (R.obj a)) v
  · change std.map v ≫ O.left a =
      std.map v ≫ O.left a ≫
        pre W ((𝟙 (P.obj a) : P.obj a ⟶ P.obj a).map)
    rw [pre_id, Category.comp_id]
  · change (std.map v ≫ f.app a) ≫ JTNativeRowLabel.labelFromRow W 0 =
      std.map v ≫ (f.app a ≫ JTNativeRowLabel.labelFromRow W 0) ≫
        pre W ((𝟙 (single 0) : single 0 ⟶ single 0).map)
    rw [pre_id]
    simpa only [Category.assoc] using
      (Category.comp_id ((std.map v ≫ f.app a) ≫
        JTNativeRowLabel.labelFromRow W 0)).symm
  · change std.map v ≫ O.right a =
      std.map v ≫ O.right a ≫
        pre W ((𝟙 (R.obj a) : R.obj a ⟶ R.obj a).map)
    rw [pre_id, Category.comp_id]

theorem component_projection :
    (proj W x y).map (component W z U K incl f e s he hs hfU heU hsU O p) =
      (𝟙 (wedge (P.obj ((base W z U K incl f e s he hs hfU heU hsU).obj p))
        (wedge (single 0)
          (R.obj ((base W z U K incl f e s he hs hfU heU hsU).obj p)))),
        (alpha W z U K incl f e s he hs hfU heU hsU).app p) := by
  let a := (base W z U K incl f e s he hs hfU heU hsU).obj p
  let v := (alpha W z U K incl f e s he hs hfU heU hsU).app p
  have h : (proj W x y).map
      (component W z U K incl f e s he hs hfU heU hsU O p) =
      (wedgeMap (𝟙 (P.obj a)) (wedgeMap (𝟙 (single 0)) (𝟙 (R.obj a))), v) := by
    rfl
  rw [h]
  exact congrArg (fun q : wedge (P.obj a) (wedge (single 0) (R.obj a)) ⟶
      wedge (P.obj a) (wedge (single 0) (R.obj a)) ↦ (q, v))
    ((congrArg (wedgeMap (𝟙 (P.obj a)))
      (wedgeMap_id (T := single 0) (U := R.obj a))).trans
      (wedgeMap_id (T := P.obj a) (U := wedge (single 0) (R.obj a))))

/-- The literal old label is recovered by a NATURAL decorated comparison,
with all higher choices and the complete common chain still present. -/
def comparison :
    (collapsed W z U K incl f e s he hs hfU heU hsU O).labels ⟶
      base W z U K incl f e s he hs hfU heU hsU ⋙
        (oldFamily W K f O).labels where
  app p := component W z U K incl f e s he hs hfU heU hsU O p
  naturality {p q} g := by
    apply (proj W x y).map_injective
    simp only [Functor.map_comp]
    change (proj W x y).map
        ((collapsed W z U K incl f e s he hs hfU heU hsU O).arrow g) ≫
          (proj W x y).map (component W z U K incl f e s he hs hfU heU hsU O q) =
      (proj W x y).map (component W z U K incl f e s he hs hfU heU hsU O p) ≫
        (proj W x y).map
          ((oldFamily W K f O).arrow
            ((base W z U K incl f e s he hs hfU heU hsU).map g))
    rw [JTWhiskeredSeamDiagram.Family.arrow_projection,
      JTWhiskeredSeamDiagram.Family.arrow_projection,
      component_projection, component_projection]
    apply Prod.ext
    · let u := wedgeMap
        (P.map ((base W z U K incl f e s he hs hfU heU hsU).map g))
        (wedgeMap (𝟙 (single 0))
          (R.map ((base W z U K incl f e s he hs hfU heU hsU).map g)))
      let Tp := wedge (P.obj ((base W z U K incl f e s he hs hfU heU hsU).obj p))
        (wedge (single 0)
          (R.obj ((base W z U K incl f e s he hs hfU heU hsU).obj p)))
      let Tq := wedge (P.obj ((base W z U K incl f e s he hs hfU heU hsU).obj q))
        (wedge (single 0)
          (R.obj ((base W z U K incl f e s he hs hfU heU hsU).obj q)))
      change Hom.comp u (𝟙 Tq) = Hom.comp (𝟙 Tp) u
      exact (Hom.ext (Category.comp_id u.map)).trans
        (Hom.ext (Category.id_comp u.map)).symm
    · change (degree W z U K incl f e s he hs hfU heU hsU).map g ≫
          (alpha W z U K incl f e s he hs hfU heU hsU).app q =
        (alpha W z U K incl f e s he hs hfU heU hsU).app p ≫
          K.map ((base W z U K incl f e s he hs hfU heU hsU).map g)
      exact (alpha W z U K incl f e s he hs hfU heU hsU).naturality g

private abbrev sourceCoefficients := JTThreePieceLabelOperators.coefficients
  ((collapsed W z U K incl f e s he hs hfU heU hsU O).data p)
private abbrev targetCoefficients := JTThreePieceLabelOperators.coefficients
  (oldData W K f O ((base W z U K incl f e s he hs hfU heU hsU).obj p))

/-- The actual decorated comparison restricts the WHOLE three-piece
coefficient along the unchanged old degree, with identity native code. -/
theorem component_coefficient :
    JTComposedPrismLabels.coefficient
        (sourceCoefficients W z U K incl f e s he hs hfU heU hsU O p) =
      std.map ((alpha W z U K incl f e s he hs hfU heU hsU).app p) ≫
        JTComposedPrismLabels.coefficient
          (targetCoefficients W z U K incl f e s he hs hfU heU hsU O p) := by
  let Cs := sourceCoefficients W z U K incl f e s he hs hfU heU hsU O p
  let Ct := targetCoefficients W z U K incl f e s he hs hfU heU hsU O p
  let a := (base W z U K incl f e s he hs hfU heU hsU).obj p
  let v := (alpha W z U K incl f e s he hs hfU heU hsU).app p
  let T := wedge (P.obj a) (wedge (single 0) (R.obj a))
  have h := JTOrderedLabelWedge.coefficient_of_indexHom
    (JTComposedPrismLabels.orderedPoint Cs)
    (JTComposedPrismLabels.orderedPoint Ct) (𝟙 T) v
    (component W z U K incl f e s he hs hfU heU hsU O p)
    (component_projection W z U K incl f e s he hs hfU heU hsU O p)
  have hCs : JTOrderedLabelBinaryGlue.coefficient W x y T
      ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
      (JTComposedPrismLabels.orderedPoint Cs) =
        JTComposedPrismLabels.coefficient Cs := by
    rw [JTOrderedLabelBinaryGlue.coefficient,
      JTComposedPrismLabels.orderedPoint_coefficient]
    exact Equiv.symm_apply_apply _ _
  have hCt : JTOrderedLabelBinaryGlue.coefficient W x y T (K.obj a)
      (JTComposedPrismLabels.orderedPoint Ct) =
        JTComposedPrismLabels.coefficient Ct := by
    rw [JTOrderedLabelBinaryGlue.coefficient,
      JTComposedPrismLabels.orderedPoint_coefficient]
    exact Equiv.symm_apply_apply _ _
  change JTOrderedLabelBinaryGlue.coefficient W x y T
      ((degree W z U K incl f e s he hs hfU heU hsU).obj p)
      (JTComposedPrismLabels.orderedPoint Cs) =
    std.map v ≫ JTOrderedLabelBinaryGlue.coefficient W x y T (K.obj a)
      (JTComposedPrismLabels.orderedPoint Ct) ≫
        pre W ((𝟙 T : T ⟶ T).map) at h
  rw [hCs, hCt, pre_id, Category.comp_id] at h
  exact h

end
end DaggerModels.PartII.JTChosenSeamOldComparison
