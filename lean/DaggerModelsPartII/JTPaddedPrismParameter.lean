import DaggerModelsPartII.JTFullPrismSupportedDiagram
import DaggerModelsPartII.JTOrderedLabelCoefficientPadding
import DaggerModelsPartII.JTJointRelativeParameters

/-! Add two stable outer labels to any diagram of full prism parameters. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory

namespace DaggerModels.PartII.JTPaddedPrismParameter

open JTPaddedTimeOperators (pad inside map_first map_inside map_last)
open JTOrderedLabelCoefficientPadding (embedding embedding_natural)
open JTFullPrismSupportedDiagram (prisms)
open JTJointRelativeParameters (parameterOfNaturalVertices parameterOfNaturalVertices_coord
  parameter_ext)
open JTCodiscreteParameterPairing (coord coord_map)

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev std := SSet.stdSimplex.{0}
private abbrev zero := op (⦋0⦌ : SimplexCategory)

private abbrev vert (d : SimplexCategory) : (std.obj d).obj zero ≃ Fin (d.len + 1) :=
  SSet.stdSimplex.obj₀Equiv (n := d.len)

private theorem vert_map {d e : SimplexCategory} (f : d ⟶ e) (v : (std.obj d).obj zero) :
    vert e ((std.map f).app zero v) = f.toOrderHom (vert d v) := rfl

private theorem map_vert {d e : SimplexCategory} (f : d ⟶ e) (v : Fin (d.len + 1)) :
    (std.map f).app zero ((vert d).symm v) = (vert e).symm (f.toOrderHom v) := by
  apply (vert e).injective
  rw [vert_map, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {I : Type} [SmallCategory I] {D t k : I ⥤ SimplexCategory}
variable (p : prisms D t ⟶ k ⋙ J)

/-- Padding the horizontal degree retains its entire original interior diagram. -/
abbrev padded (D : I ⥤ SimplexCategory) := D ⋙ JTPaddedTimeOperators.functor

private def labels (a : I) (i : Fin ((pad (D.obj a)).len + 1)) (v : (J.obj (t.obj a)).obj zero) :
    Fin ((pad (k.obj a)).len + 1) :=
  Fin.cases 0 (Fin.lastCases (Fin.last (pad (k.obj a)).len) (fun b ↦
    inside (k.obj a) (coord (k.obj a) zero
      ((p.app a).app zero ((vert (D.obj a)).symm b, v)) 0))) i

private theorem labels_first (a : I) (v : (J.obj (t.obj a)).obj zero) :
    labels p a 0 v = 0 := rfl

private theorem labels_inside (a : I) (b : Fin ((D.obj a).len + 1))
    (v : (J.obj (t.obj a)).obj zero) :
    labels p a (inside (D.obj a) b) v = inside (k.obj a) (coord (k.obj a) zero
      ((p.app a).app zero ((vert (D.obj a)).symm b, v)) 0) := by
  have hb : inside (D.obj a) b = b.castSucc.succ := rfl
  rw [hb, labels, Fin.cases_succ, Fin.lastCases_castSucc]

private theorem labels_last (a : I) (v : (J.obj (t.obj a)).obj zero) :
    labels p a (Fin.last (pad (D.obj a)).len) v = Fin.last (pad (k.obj a)).len := by
  have hb : Fin.last (pad (D.obj a)).len = (Fin.last ((D.obj a).len + 1)).succ := rfl
  rw [hb, labels, Fin.cases_succ, Fin.lastCases_last]

private theorem original_natural {a b : I} (f : a ⟶ b) (u : Fin ((D.obj a).len + 1))
    (v : (J.obj (t.obj a)).obj zero) :
    coord (k.obj b) zero ((p.app b).app zero
      ((vert (D.obj b)).symm ((D.map f).toOrderHom u), (J.map (t.map f)).app zero v)) 0 =
      (k.map f).toOrderHom (coord (k.obj a) zero
        ((p.app a).app zero ((vert (D.obj a)).symm u, v)) 0) := by
  have h := congrFun (NatTrans.congr_app (p.naturality f) zero) ((vert (D.obj a)).symm u, v)
  change (p.app b).app zero ((std.map (D.map f)).app zero ((vert (D.obj a)).symm u),
      (J.map (t.map f)).app zero v) =
    (J.map (k.map f)).app zero ((p.app a).app zero ((vert (D.obj a)).symm u, v)) at h
  rw [map_vert] at h
  rw [h, coord_map]

private theorem labels_natural {a b : I} (f : a ⟶ b)
    (i : Fin ((pad (D.obj a)).len + 1)) (v : (J.obj (t.obj a)).obj zero) :
    labels p b ((JTPaddedTimeOperators.map (D.map f)).toOrderHom i)
        ((J.map (t.map f)).app zero v) =
      (JTPaddedTimeOperators.map (k.map f)).toOrderHom (labels p a i v) := by
  induction i using Fin.cases with
  | zero => rw [map_first, labels_first, labels_first, map_first]
  | succ i =>
    induction i using Fin.lastCases with
    | last =>
      change labels p b ((JTPaddedTimeOperators.map (D.map f)).toOrderHom
        (Fin.last (pad (D.obj a)).len)) ((J.map (t.map f)).app zero v) =
          (JTPaddedTimeOperators.map (k.map f)).toOrderHom
            (labels p a (Fin.last (pad (D.obj a)).len) v)
      rw [map_last, labels_last, labels_last, map_last]
    | cast i =>
      change labels p b ((JTPaddedTimeOperators.map (D.map f)).toOrderHom (inside (D.obj a) i))
        ((J.map (t.map f)).app zero v) =
          (JTPaddedTimeOperators.map (k.map f)).toOrderHom (labels p a (inside (D.obj a) i) v)
      rw [map_inside, labels_inside, labels_inside, map_inside, original_natural p f]

private def assignment (a : I) (u : ((prisms (padded D) t).obj a).obj zero) :
    Fin (((padded k).obj a).len + 1) :=
  labels p a (vert (pad (D.obj a)) u.1) u.2

private theorem assignment_natural {a b : I} (f : a ⟶ b)
    (u : ((prisms (padded D) t).obj a).obj zero) :
    assignment p b (((prisms (padded D) t).map f).app zero u) =
      ((padded k).map f).toOrderHom (assignment p a u) := by
  change labels p b (vert (pad (D.obj b))
    ((std.map (JTPaddedTimeOperators.map (D.map f))).app zero u.1))
      ((J.map (t.map f)).app zero u.2) = _
  rw [vert_map]
  exact labels_natural p f (vert (pad (D.obj a)) u.1) u.2

/-- The padded prism keeps the original parameter inside and uses two fixed outside values. -/
def parameter : prisms (padded D) t ⟶ padded k ⋙ J :=
  parameterOfNaturalVertices (prisms (padded D) t) (padded k)
    (assignment p) (assignment_natural p)

/-- The original ordered positions are a natural subdiagram of the padded positions. -/
def includeInterior (D : I ⥤ SimplexCategory) : D ⟶ padded D where
  app a := embedding (D.obj a)
  naturality _ _ f := embedding_natural (D.map f)

/-- The entire original prism includes with its time unchanged. -/
def includePrisms (D t : I ⥤ SimplexCategory) : prisms D t ⟶ prisms (padded D) t :=
  Functor.whiskerRight
    (NatTrans.prod' (Functor.whiskerRight (includeInterior D) std) (𝟙 (t ⋙ J)))
    (MonoidalCategory.tensor SSet.{0})

/-- Pulling the padded parameter back to the full interior recovers the original
parameter followed by the original coefficient embedding. -/
theorem include_parameter :
    includePrisms D t ≫ parameter p = p ≫ Functor.whiskerRight (includeInterior k) J := by
  apply NatTrans.ext
  funext a
  apply parameter_ext
  intro v
  change coord ((padded k).obj a) zero
      (((parameter p).app a).app zero ((std.map (embedding (D.obj a))).app zero v.1, v.2)) 0 =
    coord ((padded k).obj a) zero
      ((J.map (embedding (k.obj a))).app zero ((p.app a).app zero v)) 0
  unfold parameter
  rw [parameterOfNaturalVertices_coord, coord_map]
  change labels p a (vert (pad (D.obj a)) ((std.map (embedding (D.obj a))).app zero v.1)) v.2 =
      inside (k.obj a) (coord (k.obj a) zero ((p.app a).app zero v) 0)
  rw [vert_map]
  change labels p a (inside (D.obj a) (vert (D.obj a) v.1)) v.2 = _
  rw [labels_inside, Equiv.symm_apply_apply]
  rfl

end
end DaggerModels.PartII.JTPaddedPrismParameter
