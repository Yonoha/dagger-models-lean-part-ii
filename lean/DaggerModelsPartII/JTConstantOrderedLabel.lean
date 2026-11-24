import DaggerModelsPartII.JTPointNativeLifts
import DaggerModelsPartII.JTOrderedLabelBinaryGlue

/-!
# Constant ordered labels from an original zero vertex
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTConstantOrderedLabel

open ReversalDiscreteFreeColimits OrderedNecklaceLabelDiagram OrderedNecklaceVertexPoints
open TripleBeadEndpointLabel (labels)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev F := discreteFree.{0}
private abbrev K (k : SimplexCategory) := SSet.stdSimplex.{0}.obj k
private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

/-- The label obtained by collapsing the native necklace and the parameter to zero. -/
def constantCoefficient (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) : K k ⟶ labels W T :=
  term (K k) ≫ zeroPoint W z ≫ diagramMappingPrecomp (F.map (term T.toSSet)) W

/-- Constant coefficients commute with an actual native necklace operator. -/
theorem constantCoefficient_native (W : Source) (z : Vertex W)
    {T U : NecklaceCode} (f : T ⟶ U) (k : SimplexCategory) :
    constantCoefficient W z T k =
      constantCoefficient W z U k ≫ diagramMappingPrecomp (F.map f.map) W := by
  have hf : f.map ≫ term U.toSSet = term T.toSSet :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simp only [constantCoefficient, Category.assoc, ← diagramMappingPrecomp_comp,
    ← F.map_comp, hf]

/-- Constant coefficients commute with an actual parameter operator. -/
theorem constantCoefficient_ordinal (W : Source) (z : Vertex W) (T : NecklaceCode)
    {k l : SimplexCategory} (r : k ⟶ l) :
    constantCoefficient W z T k =
      SSet.stdSimplex.map r ≫ constantCoefficient W z T l := by
  have hr : SSet.stdSimplex.map r ≫ term (K l) = term (K k) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  simp only [constantCoefficient, ← Category.assoc, hr]

/-- The constant coefficient has both boundary vertices equal to the original vertex. -/
theorem constantCoefficient_boundary (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) :
    constantCoefficient W z T k ≫ (necklaceBoundaryRestriction W).app (op T) =
      term (K k) ≫ boundaryPoint W z z := by
  apply (cancel_mono (boundaryMappingIso W).hom).mp
  apply Limits.prod.hom_ext
  · simp only [Category.assoc, boundaryMappingIso_fst, boundaryPoint_first,
      constantCoefficient]
    change (term (K k) ≫ zeroPoint W z ≫ diagramMappingPrecomp (F.map (term T.toSSet)) W) ≫
      diagramMappingPrecomp (boundaryNecklace T) W ≫
        diagramMappingPrecomp (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    simp only [Category.assoc, ← diagramMappingPrecomp_comp]
    have ht : SSet.yonedaEquiv.symm T.first ≫ term T.toSSet =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have hleg : (coprod.inl : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundaryNecklace T ≫ F.map (term T.toSSet) = 𝟙 _ := by
      rw [boundaryNecklace, ← Category.assoc, coprod.inl_desc, ← F.map_comp,
        ht, F.map_id]
    rw [hleg, diagramMappingPrecomp_id, Category.comp_id]
  · simp only [Category.assoc, boundaryMappingIso_snd, boundaryPoint_last,
      constantCoefficient]
    change (term (K k) ≫ zeroPoint W z ≫ diagramMappingPrecomp (F.map (term T.toSSet)) W) ≫
      diagramMappingPrecomp (boundaryNecklace T) W ≫
        diagramMappingPrecomp (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) W = _
    simp only [Category.assoc, ← diagramMappingPrecomp_comp]
    have ht : SSet.yonedaEquiv.symm T.last ≫ term T.toSSet =
        𝟙 (Δ[0] : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    have hleg : (coprod.inr : F.obj (Δ[0] : SSet.{0}) ⟶ boundary) ≫
        boundaryNecklace T ≫ F.map (term T.toSSet) = 𝟙 _ := by
      rw [boundaryNecklace, ← Category.assoc, coprod.inr_desc, ← F.map_comp,
        ht, F.map_id]
    rw [hleg, diagramMappingPrecomp_id, Category.comp_id]

/-- The actual ordered label over the diagonal boundary point. -/
def constantLabel (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) :
    ((orderedNecklaceLabels W (boundaryPoint W z z)).obj (op T)).obj (op k) :=
  SSet.yonedaEquiv (pullback.lift (constantCoefficient W z T k) (term (K k))
    (constantCoefficient_boundary W z T k))

/-- The full coefficient of the actual ordered label is the prescribed constant label. -/
theorem coefficient_constantLabel (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) :
    JTOrderedLabelBinaryGlue.coefficient W z z T k (constantLabel W z T k) =
      constantCoefficient W z T k := by
  apply SSet.yonedaEquiv.injective
  simp only [JTOrderedLabelBinaryGlue.coefficient, Equiv.apply_symm_apply,
    JTRealizedLabelEndpoints.orderedLabel, constantLabel, Equiv.apply_symm_apply]
  change SSet.yonedaEquiv
      (pullback.lift (constantCoefficient W z T k) (term (K k))
        (constantCoefficient_boundary W z T k) ≫
        pullback.fst ((necklaceBoundaryRestriction W).app (op T))
          (boundaryPoint W z z)) = SSet.yonedaEquiv (constantCoefficient W z T k)
  rw [pullback.lift_fst]
  rfl

/-- The decorated object carrying the actual constant ordered label. -/
def constantIndex (W : Source) (z : Vertex W) (T : NecklaceCode)
    (k : SimplexCategory) : OrderedLabelElements.Index W (boundaryPoint W z z) :=
  OrderedLabelElements.mk W (boundaryPoint W z z) T k (constantLabel W z T k)

/-- Every native and ordinal operator gives an actual arrow of constant labels. -/
def constantIndexHom (W : Source) (z : Vertex W) {T U : NecklaceCode}
    (f : T ⟶ U) {k l : SimplexCategory} (r : k ⟶ l) :
    constantIndex W z T k ⟶ constantIndex W z U l := by
  let L := OrderedLabelElements.labelPresheaf W (boundaryPoint W z z)
  refine (CategoryOfElements.homMk (L.elementsMk (op (U, l)) (constantLabel W z U l))
    (L.elementsMk (op (T, k)) (constantLabel W z T k))
      ((show (T, k) ⟶ (U, l) from (f, r)).op) ?_).op
  change ((orderedNecklaceLabels W (boundaryPoint W z z)).obj (op T)).map r.op
      (((orderedNecklaceLabels W (boundaryPoint W z z)).map f.op).app (op l)
        (constantLabel W z U l)) = constantLabel W z T k
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.yonedaEquiv_symm_map, ← SSet.yonedaEquiv_symm_comp]
  simp only [constantLabel, Equiv.symm_apply_apply]
  let b := boundaryPoint W z z
  let G := orderedNecklaceLabels W b
  let pT := pullback.fst ((necklaceBoundaryRestriction W).app (op T)) b
  let pU := pullback.fst ((necklaceBoundaryRestriction W).app (op U)) b
  let qT := pullback.snd ((necklaceBoundaryRestriction W).app (op T)) b
  let qU := pullback.snd ((necklaceBoundaryRestriction W).app (op U)) b
  have hp : G.map f.op ≫ pT = pU ≫ diagramMappingPrecomp (F.map f.map) W := by
    simp only [G, pT, pU, orderedNecklaceLabels, orderedLabelDiagram,
      pullback.map, pullback.lift_fst]
    rfl
  have hq : G.map f.op ≫ qT = qU := by
    simp only [G, qT, qU, orderedNecklaceLabels, orderedLabelDiagram,
      pullback.map, pullback.lift_snd, Category.comp_id]
  change SSet.stdSimplex.map r ≫
      (pullback.lift (constantCoefficient W z U l) (term (K l))
        (constantCoefficient_boundary W z U l) ≫ G.map f.op) =
    pullback.lift (constantCoefficient W z T k) (term (K k))
      (constantCoefficient_boundary W z T k)
  apply pullback.hom_ext
  · calc
      (SSet.stdSimplex.map r ≫
          (pullback.lift (constantCoefficient W z U l) (term (K l))
            (constantCoefficient_boundary W z U l) ≫ G.map f.op)) ≫ pT =
        SSet.stdSimplex.map r ≫ constantCoefficient W z U l ≫
          diagramMappingPrecomp (F.map f.map) W := by
            simp only [Category.assoc, hp]
            simpa only [Category.assoc] using
              congrArg (fun a : K l ⟶ labels W U ↦
                SSet.stdSimplex.map r ≫ a ≫ diagramMappingPrecomp (F.map f.map) W)
                (pullback.lift_fst (constantCoefficient W z U l) (term (K l))
                  (constantCoefficient_boundary W z U l))
      _ = constantCoefficient W z T k := by
        rw [← Category.assoc, ← constantCoefficient_ordinal W z U r,
          ← constantCoefficient_native W z f k]
      _ = pullback.lift (constantCoefficient W z T k) (term (K k))
          (constantCoefficient_boundary W z T k) ≫ pT := by
            exact (pullback.lift_fst _ _ _).symm
  · calc
      (SSet.stdSimplex.map r ≫
          (pullback.lift (constantCoefficient W z U l) (term (K l))
            (constantCoefficient_boundary W z U l) ≫ G.map f.op)) ≫ qT =
        SSet.stdSimplex.map r ≫ term (K l) := by
          simp only [Category.assoc, hq]
          simpa only [Category.assoc] using
            congrArg (fun a : K l ⟶ (Δ[0] : SSet.{0}) ↦ SSet.stdSimplex.map r ≫ a)
              (pullback.lift_snd (constantCoefficient W z U l) (term (K l))
                (constantCoefficient_boundary W z U l))
      _ = term (K k) := SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
      _ = pullback.lift (constantCoefficient W z T k) (term (K k))
          (constantCoefficient_boundary W z T k) ≫ qT := by
            exact (pullback.lift_snd _ _ _).symm

end

end DaggerModels.PartII.JTConstantOrderedLabel
