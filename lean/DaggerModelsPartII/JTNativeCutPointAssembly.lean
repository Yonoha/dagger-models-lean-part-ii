import OriginalCutFlagNaturality
import ChosenNecklaceUnitCodeMaps
import ChosenNecklaceIntervalSingle
import ChosenNecklaceCategory
import OriginalProductCrossingEndpoints

/-!
Reassemble the literal two cuts with an extra zero-length middle necklace.
The construction uses the existing point unitor and original cut-wedge map.
It keeps arbitrary cut-preserving native operators, without assuming that the
cut is a joint of the source necklace.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTNativeCutPointAssembly

open DaggerOriginalProductGadget

noncomputable section

local instance : SmallCategory NecklaceCode := NecklaceCode.category

private abbrev term := SSet.stdSimplex.isTerminalObj₀.from

private theorem hom_assoc {A B C D : NecklaceCode}
    (f : Hom.{0} A B) (g : Hom.{0} B C) (h : Hom.{0} C D) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) :=
  Hom.ext (Category.assoc f.map g.map h.map)

/-- Apply the existing left point unitor to any literal zero-length code. -/
def zeroUnit (Z T : NecklaceCode) (hZ : Z.len = 0) : wedge Z T ⟶ T := by
  obtain rfl := code_eq_point_of_zero Z hZ
  exact wedgeLeftUnitCode T

/-- The removed zero-length piece lands at the first point of the old right piece. -/
theorem zeroUnit_left (Z T : NecklaceCode) (hZ : Z.len = 0) :
    wedgeιLeft Z T ≫ (zeroUnit Z T hZ).map =
      term Z.toSSet ≫ pointAt T (ULift.up 0) := by
  obtain rfl := code_eq_point_of_zero Z hZ
  change wedgeιLeft point T ≫ (wedgeLeftUnit T).hom = _
  rw [wedgeLeftUnit_point]
  have ht : term point.toSSet = 𝟙 (Δ[0] : SSet.{0}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [ht]
  exact (Category.id_comp _).symm

/-- The full old right piece is retained by the unitor. -/
theorem zeroUnit_right (Z T : NecklaceCode) (hZ : Z.len = 0) :
    wedgeιRight Z T ≫ (zeroUnit Z T hZ).map = 𝟙 T.toSSet := by
  obtain rfl := code_eq_point_of_zero Z hZ
  exact (wedgeLeftUnit T).inv_hom_id

/-- Removing the zero-length piece commutes with every old native operator. -/
theorem zeroUnit_natural (Z : NecklaceCode) (hZ : Z.len = 0)
    {T U : NecklaceCode} (f : T ⟶ U) :
    wedgeMap (𝟙 Z) f ≫ zeroUnit Z U hZ = zeroUnit Z T hZ ≫ f := by
  apply NecklaceCode.Hom.ext
  change (wedgeMap (𝟙 Z) f).map ≫ (zeroUnit Z U hZ).map =
    (zeroUnit Z T hZ).map ≫ f.map
  apply (wedgeIsPushout Z T).hom_ext
  · calc
      _ = term Z.toSSet ≫ pointAt U (ULift.up 0) := by
        rw [← Category.assoc, wedgeMap_left]
        change (𝟙 _ ≫ wedgeιLeft Z U) ≫ (zeroUnit Z U hZ).map = _
        rw [Category.id_comp, zeroUnit_left]
      _ = wedgeιLeft Z T ≫ ((zeroUnit Z T hZ).map ≫ f.map) := by
        rw [← Category.assoc, zeroUnit_left, Category.assoc, pointAt_first_comp]
  · rw [← Category.assoc, wedgeMap_right, Category.assoc, zeroUnit_right,
      ← Category.assoc, zeroUnit_right]
    exact (Category.comp_id f.map).trans (Category.id_comp f.map).symm

/-- The original cuts with a literal zero-dimensional bead at their common vertex. -/
abbrev code (T : NecklaceCode) (v : Fin (T.len + 1)) :=
  wedge (cutLeft T v) (wedge (single 0) (cutRight T v))

/-- Remove the middle point and use the EXISTING original cut-wedge map. -/
def assembly (T : NecklaceCode) (v : Fin (T.len + 1)) : code T v ⟶ T :=
  wedgeMap (𝟙 (cutLeft T v)) (zeroUnit (single 0) (cutRight T v) rfl) ≫
    cutWedgeHom T v

/-- The whole old left cut is recovered literally. -/
theorem assembly_left (T : NecklaceCode) (v : Fin (T.len + 1)) :
    tripleRightT (cutLeft T v) (single 0) (cutRight T v) ≫ (assembly T v).map =
      cutLeftι T v := by
  change wedgeιLeft (cutLeft T v) (wedge (single 0) (cutRight T v)) ≫
    ((wedgeMap (Hom.id.{0} (cutLeft T v))
      (zeroUnit (single 0) (cutRight T v) rfl)).map ≫ cutWedgeMap T v) = cutLeftι T v
  rw [← Category.assoc, wedgeMap_left]
  change (𝟙 (cutLeft T v).toSSet ≫ wedgeιLeft (cutLeft T v) (cutRight T v)) ≫
    cutWedgeMap T v = cutLeftι T v
  rw [Category.id_comp, cutWedge_left]

/-- The whole old right cut is also recovered literally. -/
theorem assembly_right (T : NecklaceCode) (v : Fin (T.len + 1)) :
    tripleRightV (cutLeft T v) (single 0) (cutRight T v) ≫ (assembly T v).map =
      cutRightι T v := by
  change (wedgeιRight (single 0) (cutRight T v) ≫
      wedgeιRight (cutLeft T v) (wedge (single 0) (cutRight T v))) ≫
    ((wedgeMap (Hom.id.{0} (cutLeft T v))
      (zeroUnit (single 0) (cutRight T v) rfl)).map ≫ cutWedgeMap T v) = cutRightι T v
  simp only [Category.assoc]
  rw [← Category.assoc (wedgeιRight (cutLeft T v) (wedge (single 0) (cutRight T v))),
    wedgeMap_right]
  simp only [Category.assoc]
  rw [← Category.assoc (wedgeιRight (single 0) (cutRight T v)), zeroUnit_right,
    Category.id_comp, cutWedge_right]

/-- The entire inserted middle point returns to the actual old selected vertex. -/
theorem assembly_middle (T : NecklaceCode) (v : Fin (T.len + 1)) :
    tripleRightU (cutLeft T v) (single 0) (cutRight T v) ≫ (assembly T v).map =
      term (single 0).toSSet ≫ pointAt T (ULift.up v) := by
  change (wedgeιLeft (single 0) (cutRight T v) ≫
      wedgeιRight (cutLeft T v) (wedge (single 0) (cutRight T v))) ≫
    ((wedgeMap (Hom.id.{0} (cutLeft T v))
      (zeroUnit (single 0) (cutRight T v) rfl)).map ≫ cutWedgeMap T v) = _
  simp only [Category.assoc]
  rw [← Category.assoc (wedgeιRight (cutLeft T v) (wedge (single 0) (cutRight T v))),
    wedgeMap_right]
  simp only [Category.assoc]
  rw [← Category.assoc (wedgeιLeft (single 0) (cutRight T v)), zeroUnit_left]
  simp only [Category.assoc]
  rw [cutWedge_right, cutRight_joint]

/-- Every operator preserving the actual cut commutes with whole reassembly. -/
theorem assembly_natural {T U : NecklaceCode} (f : T ⟶ U)
    (v : Fin (T.len + 1)) (w : Fin (U.len + 1))
    (h : orderMap f.map v = w) :
    wedgeMap (cutLeftHom f v w h)
        (wedgeMap (𝟙 (single 0)) (cutRightHom f v w h)) ≫ assembly U w =
      assembly T v ≫ f := by
  let l := cutLeftHom f v w h
  let r := cutRightHom f v w h
  have hl : Hom.comp l (Hom.id (cutLeft U w)) = l := Hom.ext (Category.comp_id l.map)
  have hl' : Hom.comp (Hom.id (cutLeft T v)) l = l := Hom.ext (Category.id_comp l.map)
  have hu := zeroUnit_natural (single 0) rfl r
  change Hom.comp (wedgeMap (Hom.id.{0} (single 0)) r)
      (zeroUnit (single 0) (cutRight U w) rfl) =
    Hom.comp (zeroUnit (single 0) (cutRight T v) rfl) r at hu
  change Hom.comp (wedgeMap l (wedgeMap (Hom.id.{0} (single 0)) r))
      (Hom.comp (wedgeMap (Hom.id.{0} (cutLeft U w))
        (zeroUnit (single 0) (cutRight U w) rfl))
        (cutWedgeHom U w)) =
    Hom.comp (Hom.comp
      (wedgeMap (Hom.id.{0} (cutLeft T v)) (zeroUnit (single 0) (cutRight T v) rfl))
      (cutWedgeHom T v)) f
  rw [← hom_assoc, ← wedgeMap_comp, hl]
  rw [hu]
  rw [← hl', wedgeMap_comp, hom_assoc]
  exact congrArg (fun q : Hom.{0} (wedge (cutLeft T v) (cutRight T v)) U ↦
    Hom.comp (wedgeMap (Hom.id.{0} (cutLeft T v))
      (zeroUnit (single 0) (cutRight T v) rfl)) q)
      (cutWedgeHom_naturality f v w h).symm

end
end DaggerModels.PartII.JTNativeCutPointAssembly
