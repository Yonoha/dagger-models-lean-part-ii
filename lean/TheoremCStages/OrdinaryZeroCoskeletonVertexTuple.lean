import OrdinaryZeroCoskeleton
import OrdinarySegalVertexTupleFibres
import OrdinarySegalRestrictionTargetNaturality
import DaggerModelsPartII.ConstantDaggerSource
import NativeFinitePiWeak

/-!
# The zero coskeleton and every ordered vertex tuple

The row of the actual right adjoint to evaluation at zero is the finite
product indexed by all vertices of the original simplex. Mapping out of
the constant set of those vertices gives the same finite product. The
comparison retains the actual unit and is natural in the whole target.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial

namespace DaggerModels.PartII.OrdinaryZeroCoskeletonVertexTuple

open OrdinaryCSSLocalization (Space discrete)
open OrdinarySegalVertexTupleFibres (vertices vertexInclusion vertexMap)
open DaggerNativeFinitePiWeak (piObject piMap)
open DaggerNativeBisimplicialHorizontalMapping (horizontalMapping horizontalMap)

noncomputable section

private abbrev zero : SimplexCategoryᵒᵖ := op ⦋0⦌

/-- The original vertex `i`, viewed as a map toward degree zero in the
opposite simplex category. -/
def vertexOp (n : ℕ) (i : Fin (n + 1)) : op ⦋n⦌ ⟶ zero :=
  (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op

@[simp] theorem vertexOp_eval (n : ℕ) (i : Fin (n + 1)) :
    (vertexOp n i).unop.toOrderHom 0 = i := rfl

private theorem vertexOp_surj (n : ℕ) (a : op ⦋n⦌ ⟶ zero) :
    vertexOp n (a.unop.toOrderHom 0) = a := by
  apply Quiver.Hom.unop_inj
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  have hj : j = (0 : Fin 1) := by
    apply Fin.ext
    have hj := j.isLt
    change j.val < 1 at hj
    change j.val = 0
    omega
  rw [hj]
  exact vertexOp_eval n _

private def piCoordinate (K : SSet.{0}) (n : ℕ) (i : Fin (n + 1)) :
    piObject (fun _ : Fin (n + 1) ↦ K) ⟶ K where
  app q z := z i
  naturality q r α := by funext z; rfl

private theorem pi_hom_ext {A K : SSet.{0}} (n : ℕ)
    {f g : A ⟶ piObject (fun _ : Fin (n + 1) ↦ K)}
    (h : ∀ i, f ≫ piCoordinate K n i = g ≫ piCoordinate K n i) : f = g := by
  apply NatTrans.ext
  funext q z
  funext i
  exact congrFun (NatTrans.congr_app (h i) q) z

private theorem piMap_coordinate {K L : SSet.{0}} (n : ℕ) (u : K ⟶ L)
    (i : Fin (n + 1)) :
    piMap (fun _ : Fin (n + 1) ↦ u) ≫ piCoordinate L n i =
      piCoordinate K n i ≫ u := by
  apply NatTrans.ext
  funext q z
  rfl

private def coskToPi (K : SSet.{0}) (n : ℕ) :
    (OrdinaryZeroCoskeleton.coskeleton.obj K).obj (op ⦋n⦌) ⟶
      piObject (fun _ : Fin (n + 1) ↦ K) where
  app q z i :=
    ((Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ K) (vertexOp n i)).app q) z
  naturality q r α := by
    funext z
    funext i
    exact congrFun
      ((Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ K) (vertexOp n i)).naturality α) z

private theorem coskToPi_coordinate (K : SSet.{0}) (n : ℕ)
    (i : Fin (n + 1)) :
    coskToPi K n ≫ piCoordinate K n i =
      Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ K) (vertexOp n i) := by
  apply NatTrans.ext
  funext q z
  rfl

private def piToCosk (K : SSet.{0}) (n : ℕ) :
    piObject (fun _ : Fin (n + 1) ↦ K) ⟶
      (OrdinaryZeroCoskeleton.coskeleton.obj K).obj (op ⦋n⦌) :=
  Pi.lift (fun a : op ⦋n⦌ ⟶ zero ↦ piCoordinate K n (a.unop.toOrderHom 0))

/-- The right-adjoint row is the finite product of the actual zero row. -/
def coskeletonPiIso (K : SSet.{0}) (n : ℕ) :
    (OrdinaryZeroCoskeleton.coskeleton.obj K).obj (op ⦋n⦌) ≅
      piObject (fun _ : Fin (n + 1) ↦ K) where
  hom := coskToPi K n
  inv := piToCosk K n
  hom_inv_id := by
    apply Pi.hom_ext
    intro a
    obtain ⟨i, rfl⟩ : ∃ i, vertexOp n i = a :=
      ⟨a.unop.toOrderHom 0, vertexOp_surj n a⟩
    rw [Category.assoc, piToCosk, Pi.lift_π, Category.id_comp]
    exact coskToPi_coordinate K n i
  inv_hom_id := by
    apply pi_hom_ext n
    intro i
    rw [Category.assoc, coskToPi_coordinate]
    change piToCosk K n ≫
      Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ K) (vertexOp n i) =
        (𝟙 _) ≫ piCoordinate K n i
    rw [piToCosk, Pi.lift_π, Category.id_comp, vertexOp_eval]

/-- The same finite product arises by mapping the constant vertex set into
each horizontal row of the original space. -/
def horizontalVertexPiIso (W : Space) (n : ℕ) :
    horizontalMapping (vertices n) W ≅
      piObject (fun _ : Fin (n + 1) ↦ W.obj zero) :=
  NatIso.ofComponents
    (fun q ↦
      ((ConstantDaggerSource.fromZeroEquiv (Fin (n + 1))
        (W.flip.obj q)).symm).toIso)
    (by
      intro q r α
      funext g i
      rfl)

/-- Literal mapping spaces out of all vertices identify with the zero-row
finite product, without fibrancy or Segal assumptions. -/
def mappingVertexPiIso (W : Space) (n : ℕ) :
    diagramMappingSpace (discrete.obj (vertices n)) W ≅
      piObject (fun _ : Fin (n + 1) ↦ W.obj zero) :=
  OrdinaryDiscreteMapping.mappingIso (vertices n) W ≪≫
    horizontalVertexPiIso W n

private theorem coskeleton_map_coordinate {K L : SSet.{0}} (u : K ⟶ L)
    (n : ℕ) (i : Fin (n + 1)) :
    (OrdinaryZeroCoskeleton.coskeleton.map u).app (op ⦋n⦌) ≫
        Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ L) (vertexOp n i) =
      Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ K) (vertexOp n i) ≫ u := by
  simp [OrdinaryZeroCoskeleton.coskeleton, evaluationRightAdjoint_map_app]

/-- The product identification is natural in its zero-row simplicial set. -/
theorem coskeletonPiIso_natural {K L : SSet.{0}} (u : K ⟶ L) (n : ℕ) :
    (OrdinaryZeroCoskeleton.coskeleton.map u).app (op ⦋n⦌) ≫
        (coskeletonPiIso L n).hom =
      (coskeletonPiIso K n).hom ≫
        piMap (fun _ : Fin (n + 1) ↦ u) := by
  apply pi_hom_ext n
  intro i
  rw [Category.assoc, coskeletonPiIso, coskToPi_coordinate,
    Category.assoc, piMap_coordinate, ← Category.assoc,
    coskeletonPiIso, coskToPi_coordinate]
  exact coskeleton_map_coordinate u n i

/-- The mapping-space product identification is natural in every whole
target map, with the original component in horizontal degree zero. -/
theorem mappingVertexPiIso_natural {W Z : Space} (f : W ⟶ Z) (n : ℕ) :
    diagramMappingPostcomp (discrete.obj (vertices n)) f ≫
        (mappingVertexPiIso Z n).hom =
      (mappingVertexPiIso W n).hom ≫
        piMap (fun _ : Fin (n + 1) ↦ f.app zero) := by
  have h : horizontalMap (vertices n) f ≫
        (horizontalVertexPiIso Z n).hom =
      (horizontalVertexPiIso W n).hom ≫
        piMap (fun _ : Fin (n + 1) ↦ f.app zero) := by
    apply NatTrans.ext
    funext q g
    funext i
    rfl
  dsimp only [mappingVertexPiIso, Iso.trans_hom]
  rw [← Category.assoc,
    OrdinarySegalRestrictionTargetNaturality.mappingIso_post,
    Category.assoc, h, ← Category.assoc]

private theorem vertices_projection (W : Space) (n : ℕ) (i : Fin (n + 1)) :
    (OrdinaryZeroCoskeleton.vertices W).app (op ⦋n⦌) ≫
        Pi.π (fun _ : op ⦋n⦌ ⟶ zero ↦ W.obj zero) (vertexOp n i) =
      W.map (vertexOp n i) := by
  simp [OrdinaryZeroCoskeleton.vertices, evaluationAdjunctionLeft_unit_app_app]

private theorem vertexMap_coordinate (W : Space) (n : ℕ) (i : Fin (n + 1)) :
    vertexMap W n ≫ (mappingVertexPiIso W n).hom ≫
        piCoordinate (W.obj zero) n i = W.map (vertexOp n i) := by
  have hn := OrdinaryDiscreteMapping.mappingIso_natural (vertexInclusion n) W
  have h : vertexMap W n ≫ (mappingVertexPiIso W n).hom =
      (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso W n).inv ≫
        DaggerNativeBisimplicialHorizontalMapping.horizontalPre (vertexInclusion n) W ≫
          (horizontalVertexPiIso W n).hom := by
    have h0 := congrArg (fun m ↦
      (DaggerNativeBisimplicialHorizontalMapping.horizontalSimplexIso W n).inv ≫
        (OrdinaryDiscreteMapping.mappingIso (Δ[n] : SSet.{0}) W).inv ≫
          m ≫ (horizontalVertexPiIso W n).hom) hn
    simpa only [OrdinarySegalVertexTupleFibres.vertexMap,
      OrdinarySegalVertexTupleFibres.mappingVertexMap, mappingVertexPiIso,
      OrdinarySegalWalkingEvaluation.simplexMappingIso, Iso.trans_hom, Iso.trans_inv,
      Category.assoc, Iso.inv_hom_id_assoc] using h0
  rw [← Category.assoc, h]
  apply NatTrans.ext
  funext q x
  change ((SSet.yonedaEquiv (X := W.flip.obj q) (n := ⦋n⦌)).symm x).app (op ⦋0⦌)
      ((vertexInclusion n).app (op ⦋0⦌) i) =
    ((W.map (vertexOp n i)).app q) x
  rw [OrdinarySegalVertexTupleFibres.vertexInclusion_zero]
  rfl

/-- The actual zero-coskeleton unit is precisely restriction of the original
`n`-simplex to its complete ordered tuple of vertices. -/
theorem vertices_vertexMap_square (W : Space) (n : ℕ) :
    (OrdinaryZeroCoskeleton.vertices W).app (op ⦋n⦌) ≫
        (coskeletonPiIso (W.obj zero) n).hom =
      vertexMap W n ≫ (mappingVertexPiIso W n).hom := by
  apply pi_hom_ext n
  intro i
  rw [Category.assoc, coskeletonPiIso, coskToPi_coordinate,
    Category.assoc, vertexMap_coordinate]
  exact vertices_projection W n i

#print axioms coskeletonPiIso
#print axioms mappingVertexPiIso
#print axioms coskeletonPiIso_natural
#print axioms mappingVertexPiIso_natural
#print axioms vertices_vertexMap_square

end

end DaggerModels.PartII.OrdinaryZeroCoskeletonVertexTuple
