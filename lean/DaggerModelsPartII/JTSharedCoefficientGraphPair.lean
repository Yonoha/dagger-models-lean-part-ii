import DaggerModelsPartII.JTDoubledGraphTime
import DaggerModelsPartII.JTHigherGraphTimeFamily
import DaggerModelsPartII.JTBinaryPrismRealization

/-! Comparison of two full graphs distinguished by their shared coefficient. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory CartesianMonoidalCategory
open DaggerModels DaggerChosenRigidificationNecklace NecklaceCode

namespace DaggerModels.PartII.JTSharedCoefficientGraphPair

open JTOrderedLabelBinaryGlue (Inputs code)
open OrderedNecklaceLabelDiagram (orderedNecklaceLabels)
open OrderedNecklaceVertexPoints (boundaryPoint)
open JTRealizedLabelEndpoints (orderedLabel)
open JTBinaryPrismRealization (realizeInputs realizeProduct collapse realizeInputs_over_wedge
  realizeOrderedProduct_reindex realizeProduct_reindexTime)
open JTDoubledGraphTime (degree extendPair fold)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev Vertex (W : Source) :=
  (JTProjectiveOrderedFiberComparison.row W ⦋0⦌).obj (op ⦋0⦌)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex
private abbrev L (W : Source) (x y : Vertex W) (T : NecklaceCode) :=
  (orderedNecklaceLabels W (boundaryPoint W x y)).obj (op T)

variable {W : Source} {x z y : Vertex W} {T U : NecklaceCode} {m n k l : SimplexCategory}

/-- Pull back both original labels along the specified shared coefficient maps. -/
def inputs (r : m ⟶ k) (r' : m ⟶ l)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l)) : Inputs W T U m x z y where
  left := (L W x z T).map r.op u
  right := (L W z y U).map r'.op v

private abbrev SL (T U : NecklaceCode) := tripleRightT T (single 1) U
private abbrev SR (T U : NecklaceCode) := tripleRightV T (single 1) U

variable {P : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W z)}
variable {Q : NecklacesOver (Raw W) (rawVertex W z) (rawVertex W y)}

/-- Two graphs agreeing after both shared coefficient restrictions
interpolate over the same original raw wedge. -/
theorem pair_over_wedge (r : m ⟶ k) (r' : m ⟶ l)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
    (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (p₀ p₁ : (code T U).toSSet ⊗ J.obj n ⟶ J.obj m)
    (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
    (hL₀ : (SL T U ▷ J.obj n) ≫ p₀ ≫ J.map r = s)
    (hL₁ : (SL T U ▷ J.obj n) ≫ p₁ ≫ J.map r = s)
    (hR₀ : (SR T U ▷ J.obj n) ≫ p₀ ≫ J.map r' = t)
    (hR₁ : (SR T U ▷ J.obj n) ≫ p₁ ≫ J.map r' = t)
    (hs : realizeProduct W k s (orderedLabel W x z T k u) = fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
    (ht : realizeProduct W l t (orderedLabel W z y U l v) = fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map) :
    realizeInputs (inputs r r' u v) (extendPair p₀ p₁) =
      fst (code T U).toSSet (J.obj (degree n)) ≫ (collapse c e).map ≫
        (NecklacesOver.wedge P Q).map := by
  apply realizeInputs_over_wedge
  · change realizeProduct W m ((SL T U ▷ J.obj (degree n)) ≫ extendPair p₀ p₁)
        (orderedLabel W x z T m ((L W x z T).map r.op u)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc,
      JTDoubledGraphTime.extendPair_over (SL T U) p₀ p₁ r s hL₀ hL₁,
      ← realizeProduct_reindexTime, hs, whiskerLeft_fst_assoc]
  · change realizeProduct W m ((SR T U ▷ J.obj (degree n)) ≫ extendPair p₀ p₁)
        (orderedLabel W z y U m ((L W z y U).map r'.op v)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc,
      JTDoubledGraphTime.extendPair_over (SR T U) p₀ p₁ r' t hR₀ hR₁,
      ← realizeProduct_reindexTime, ht, whiskerLeft_fst_assoc]

open JTHigherGraphTimeFamily (extendFamily extendFamily_over)
open JTHigherInterleavedParameter (common)

/-- A finite family with both side restrictions fixed has its entire
interpolated realization over the same original raw wedge. -/
theorem family_over_wedge {K : SimplexCategory} (r : m ⟶ k) (r' : m ⟶ l)
    (u : (L W x z T).obj (op k)) (v : (L W z y U).obj (op l))
    (c : T ⟶ P.code) (e : U ⟶ Q.code)
    (p : Fin (K.len + 1) → ((code T U).toSSet ⊗ J.obj n ⟶ J.obj m))
    (s : T.toSSet ⊗ J.obj n ⟶ J.obj k) (t : U.toSSet ⊗ J.obj n ⟶ J.obj l)
    (hL : ∀ i, (SL T U ▷ J.obj n) ≫ p i ≫ J.map r = s)
    (hR : ∀ i, (SR T U ▷ J.obj n) ≫ p i ≫ J.map r' = t)
    (hs : realizeProduct W k s (orderedLabel W x z T k u) = fst T.toSSet (J.obj n) ≫ c.map ≫ P.map)
    (ht : realizeProduct W l t (orderedLabel W z y U l v) = fst U.toSSet (J.obj n) ≫ e.map ≫ Q.map) :
    realizeInputs (inputs r r' u v) (extendFamily (k := K) p) =
      fst (code T U).toSSet (J.obj (common K n)) ≫ (collapse c e).map ≫
        (NecklacesOver.wedge P Q).map := by
  apply realizeInputs_over_wedge
  · change realizeProduct W m ((SL T U ▷ J.obj (common K n)) ≫ extendFamily (k := K) p)
        (orderedLabel W x z T m ((L W x z T).map r.op u)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc,
      extendFamily_over (SL T U) p r s hL,
      ← realizeProduct_reindexTime, hs, whiskerLeft_fst_assoc]
  · change realizeProduct W m ((SR T U ▷ J.obj (common K n)) ≫ extendFamily (k := K) p)
        (orderedLabel W z y U m ((L W z y U).map r'.op v)) = _
    rw [← realizeOrderedProduct_reindex, Category.assoc,
      extendFamily_over (SR T U) p r' t hR,
      ← realizeProduct_reindexTime, ht, whiskerLeft_fst_assoc]

end

end DaggerModels.PartII.JTSharedCoefficientGraphPair
