import OrdinaryCSSLocalization
import DaggerModelsPartII.DiagramMappingLimits
import DaggerModelsPartII.DiagramTensorMappingAdjunction
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Horizontal cotensor of an ordinary simplicial space

For a horizontal simplicial set `K`, the row in degree `n` is the strict
vertical mapping simplicial set from `discrete (K × Δ[n])` into `W`.
The horizontal operators are exact precomposition maps. The construction
is contravariant in `K` and covariant in `W`, with no Segal or fibrancy
assumption. This is structural data for a later Rezk-completion argument;
no Segal-preservation or weak-equivalence theorem is asserted here.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.OrdinarySegalHorizontalCotensor

open OrdinaryCSSLocalization (Space discrete)

noncomputable section

/-- The actual horizontal weight of `K` in every ordinary simplex degree. -/
def weight (K : SSet.{0}) : SimplexCategory ⥤ Space :=
  SSet.stdSimplex ⋙ tensorLeft K ⋙ discrete

/-- The horizontal cotensor uses the existing contravariant strict mapping
space, so its simplicial identities come from functor composition. -/
def cotensor (K : SSet.{0}) (W : Space) : Space :=
  (weight K).op ⋙ diagramMappingSource W

/-- The exact row formula in the original ordinary CSS diagram category. -/
theorem cotensor_row (K : SSet.{0}) (W : Space) (n : SimplexCategory) :
    (cotensor K W).obj (op n) =
      diagramMappingSpace (discrete.obj (K ⊗ SSet.stdSimplex.obj n)) W := rfl

/-- Horizontal operators are precomposition by the actual tensor of the
horizontal simplex operator, including its original variance. -/
theorem cotensor_map (K : SSet.{0}) (W : Space)
    {m n : SimplexCategory} (θ : m ⟶ n) :
    (cotensor K W).map θ.op =
      diagramMappingPrecomp
        (discrete.map (K ◁ SSet.stdSimplex.map θ)) W := rfl

/-- A map of horizontal parameters acts on the exact weight, naturally in
the simplex degree. -/
def weightMap {K L : SSet.{0}} (f : K ⟶ L) : weight K ⟶ weight L where
  app n := discrete.map (f ▷ SSet.stdSimplex.obj n)
  naturality := by
    intro m n θ
    change discrete.map (K ◁ SSet.stdSimplex.map θ) ≫
        discrete.map (f ▷ SSet.stdSimplex.obj n) =
      discrete.map (f ▷ SSet.stdSimplex.obj m) ≫
        discrete.map (L ◁ SSet.stdSimplex.map θ)
    rw [← discrete.map_comp, ← discrete.map_comp]
    exact congrArg discrete.map (whisker_exchange f (SSet.stdSimplex.map θ))

/-- Contravariant functoriality in the horizontal parameter. -/
def pre {K L : SSet.{0}} (f : K ⟶ L) (W : Space) :
    cotensor L W ⟶ cotensor K W :=
  Functor.whiskerRight (NatTrans.op (weightMap f)) (diagramMappingSource W)

/-- A map of target simplicial spaces acts by the original postcomposition
on every strict vertical mapping space. -/
def post (K : SSet.{0}) {W V : Space} (f : W ⟶ V) :
    cotensor K W ⟶ cotensor K V where
  app n := diagramMappingPostcomp ((weight K).obj n.unop) f
  naturality := by
    intro m n θ
    apply NatTrans.ext
    funext q η
    change (Functor.whiskerRight ((weight K).map θ.unop)
        (tensorRight (SSet.stdSimplex.obj q.unop)) ≫ η) ≫ f =
      Functor.whiskerRight ((weight K).map θ.unop)
        (tensorRight (SSet.stdSimplex.obj q.unop)) ≫ (η ≫ f)
    exact Category.assoc _ _ _

/-- Evaluation of a parameter map at every original horizontal row is
precisely precomposition by its tensor with that row's simplex. -/
theorem pre_app {K L : SSet.{0}} (f : K ⟶ L) (W : Space)
    (n : SimplexCategory) :
    (pre f W).app (op n) =
      diagramMappingPrecomp
        (discrete.map (f ▷ SSet.stdSimplex.obj n)) W := rfl

/-- The identity parameter map induces the identity of the exact cotensor. -/
theorem pre_id (K : SSet.{0}) (W : Space) :
    pre (𝟙 K) W = 𝟙 (cotensor K W) := by
  apply NatTrans.ext
  funext n
  change diagramMappingPrecomp
      (discrete.map ((𝟙 K) ▷ SSet.stdSimplex.obj n.unop)) W = 𝟙 _
  rw [MonoidalCategory.id_whiskerRight, discrete.map_id]
  exact diagramMappingPrecomp_id _ W

/-- Parameter precomposition reverses the literal order of composition. -/
theorem pre_comp {K L M : SSet.{0}} (f : K ⟶ L) (g : L ⟶ M)
    (W : Space) :
    pre (f ≫ g) W = pre g W ≫ pre f W := by
  apply NatTrans.ext
  funext n
  change diagramMappingPrecomp
      (discrete.map ((f ≫ g) ▷ SSet.stdSimplex.obj n.unop)) W =
    diagramMappingPrecomp
        (discrete.map (g ▷ SSet.stdSimplex.obj n.unop)) W ≫
      diagramMappingPrecomp
        (discrete.map (f ▷ SSet.stdSimplex.obj n.unop)) W
  rw [MonoidalCategory.comp_whiskerRight, discrete.map_comp,
    diagramMappingPrecomp_comp]

/-- Evaluation at a specified horizontal vertex keeps the exact target
space and maps into the point-parameter cotensor. -/
def evaluateVertex (K : SSet.{0}) (W : Space)
    (v : (Δ[0] : SSet.{0}) ⟶ K) :
    cotensor K W ⟶ cotensor (Δ[0] : SSet.{0}) W :=
  pre v W

/-- The unique map to the horizontal point induces the constant maps in
the opposite direction of parameter precomposition. -/
def constantMap (K : SSet.{0}) (W : Space) :
    cotensor (Δ[0] : SSet.{0}) W ⟶ cotensor K W :=
  pre (SSet.stdSimplex.isTerminalObj₀.from K) W

/-- The target action at every row is the existing mapping postcomposition. -/
theorem post_app (K : SSet.{0}) {W V : Space} (f : W ⟶ V)
    (n : SimplexCategory) :
    (post K f).app (op n) =
      diagramMappingPostcomp
        (discrete.obj (K ⊗ SSet.stdSimplex.obj n)) f := rfl

/-- The identity target map acts identically on the horizontal cotensor. -/
theorem post_id (K : SSet.{0}) (W : Space) :
    post K (𝟙 W) = 𝟙 (cotensor K W) := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q η
  exact Category.comp_id η

/-- Consecutive target maps act by their literal composite. -/
theorem post_comp (K : SSet.{0}) {W V U : Space}
    (f : W ⟶ V) (g : V ⟶ U) :
    post K (f ≫ g) = post K f ≫ post K g := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q η
  exact (Category.assoc η f g).symm

/-- Parameter precomposition commutes with target postcomposition on the
whole horizontal cotensor, including all vertical simplex degrees. -/
theorem pre_post {K L : SSet.{0}} (f : K ⟶ L)
    {W V : Space} (h : W ⟶ V) :
    pre f W ≫ post K h = post L h ≫ pre f V := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext q η
  change (Functor.whiskerRight
      (discrete.map (f ▷ SSet.stdSimplex.obj n.unop))
      (tensorRight (SSet.stdSimplex.obj q.unop)) ≫ η) ≫ h =
    Functor.whiskerRight
      (discrete.map (f ▷ SSet.stdSimplex.obj n.unop))
      (tensorRight (SSet.stdSimplex.obj q.unop)) ≫ (η ≫ h)
  exact Category.assoc _ _ _

#print axioms weight
#print axioms cotensor
#print axioms cotensor_row
#print axioms cotensor_map
#print axioms pre
#print axioms pre_id
#print axioms pre_comp
#print axioms evaluateVertex
#print axioms constantMap
#print axioms post
#print axioms post_id
#print axioms post_comp
#print axioms pre_post

end

end DaggerModels.PartII.OrdinarySegalHorizontalCotensor
