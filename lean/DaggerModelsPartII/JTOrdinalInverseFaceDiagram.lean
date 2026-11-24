import DaggerModelsPartII.JTOrdinalFaceInverseImage

/-! The full inverse-image face, natural over a small diagram of ordinal maps. -/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Simplicial

namespace DaggerModels.PartII.JTOrdinalInverseFaceDiagram

open JTOrdinalFaceInverseImage

noncomputable section

variable {I : Type} [SmallCategory I]
variable (S K D : I ⥤ SimplexCategory) (u : S ⟶ K) (α : D ⟶ K)
variable (hu : ∀ i : I, Mono (u.app i))
variable (hα : ∀ i : I, Function.Surjective (α.app i).toOrderHom)

/-- The full inverse-image ordinal at one object. -/
abbrev support (i : I) : SimplexCategory := ordinal (u.app i) (α.app i)

/-- Its inclusion into the unchanged degree ordinal. -/
abbrev inclusion (i : I) : support S K D u α i ⟶ D.obj i :=
  incl (u.app i) (α.app i) (hα i)

/-- Its exact map to the old support face. -/
abbrev toOldFace (i : I) : support S K D u α i ⟶ S.obj i :=
  toFace (u.app i) (α.app i) (hα i)
    (SimplexCategory.mono_iff_injective.mp (hu i))

/-- The strict objectwise inverse-image square. -/
theorem square (i : I) :
    toOldFace S K D u α hu hα i ≫ u.app i =
      inclusion S K D u α hα i ≫ α.app i :=
  toFace_fac (u.app i) (α.app i) (hα i)
    (SimplexCategory.mono_iff_injective.mp (hu i))

/-- Both original natural transformations carry the inverse-image square
along a diagram arrow. -/
private theorem map_square {i j : I} (f : i ⟶ j) :
    (inclusion S K D u α hα i ≫ D.map f) ≫ α.app j =
      (toOldFace S K D u α hu hα i ≫ S.map f) ≫ u.app j := by
  calc
    (inclusion S K D u α hα i ≫ D.map f) ≫ α.app j =
        inclusion S K D u α hα i ≫ (D.map f ≫ α.app j) :=
      Category.assoc _ _ _
    _ = inclusion S K D u α hα i ≫ (α.app i ≫ K.map f) := by
      rw [α.naturality]
    _ = (toOldFace S K D u α hu hα i ≫ u.app i) ≫ K.map f := by
      rw [← Category.assoc, square S K D u α hu hα i]
    _ = toOldFace S K D u α hu hα i ≫ (S.map f ≫ u.app j) := by
      rw [Category.assoc, u.naturality]
    _ = (toOldFace S K D u α hu hα i ≫ S.map f) ≫ u.app j := by
      rw [Category.assoc]

/-- The induced map of full inverse-image ordinals. -/
def supportMap {i j : I} (f : i ⟶ j) :
    support S K D u α i ⟶ support S K D u α j :=
  lift (u.app j) (α.app j) (hα j)
    (inclusion S K D u α hα i ≫ D.map f)
    (toOldFace S K D u α hu hα i ≫ S.map f)
    (map_square S K D u α hu hα f)

/-- The inverse-image inclusion is natural, strictly. -/
theorem supportMap_inclusion {i j : I} (f : i ⟶ j) :
    supportMap S K D u α hu hα f ≫ inclusion S K D u α hα j =
      inclusion S K D u α hα i ≫ D.map f :=
  lift_incl (u.app j) (α.app j) (hα j)
    (inclusion S K D u α hα i ≫ D.map f)
    (toOldFace S K D u α hu hα i ≫ S.map f)
    (map_square S K D u α hu hα f)

/-- The old support-face coordinate is also natural, strictly. -/
theorem supportMap_toOldFace {i j : I} (f : i ⟶ j) :
    supportMap S K D u α hu hα f ≫ toOldFace S K D u α hu hα j =
      toOldFace S K D u α hu hα i ≫ S.map f :=
  lift_toFace (u.app j) (α.app j) (hα j)
    (SimplexCategory.mono_iff_injective.mp (hu j))
    (inclusion S K D u α hα i ≫ D.map f)
    (toOldFace S K D u α hu hα i ≫ S.map f)
    (map_square S K D u α hu hα f)

/-- The natural full inverse-image support diagram. -/
def supportDiagram : I ⥤ SimplexCategory where
  obj := support S K D u α
  map := supportMap S K D u α hu hα
  map_id i := by
    haveI : Mono (inclusion S K D u α hα i) :=
      incl_mono (u.app i) (α.app i) (hα i)
    apply (cancel_mono (inclusion S K D u α hα i)).mp
    rw [supportMap_inclusion]
    simp
  map_comp {i j k} f g := by
    haveI : Mono (inclusion S K D u α hα k) :=
      incl_mono (u.app k) (α.app k) (hα k)
    apply (cancel_mono (inclusion S K D u α hα k)).mp
    rw [supportMap_inclusion, Category.assoc, supportMap_inclusion,
      ← Category.assoc, supportMap_inclusion, D.map_comp]
    rfl

/-- The entire inverse image is a natural subordinal of the old degree. -/
def inclNat : supportDiagram S K D u α hu hα ⟶ D where
  app := inclusion S K D u α hα
  naturality := by
    intro i j f
    exact supportMap_inclusion S K D u α hu hα f

/-- Its exact natural map to the old support-face diagram. -/
def toFaceNat : supportDiagram S K D u α hu hα ⟶ S where
  app := toOldFace S K D u α hu hα
  naturality := by
    intro i j f
    exact supportMap_toOldFace S K D u α hu hα f

/-- The strict natural inverse-image square. -/
theorem natural_square :
    toFaceNat S K D u α hu hα ≫ u =
      inclNat S K D u α hu hα ≫ α := by
  apply NatTrans.ext
  funext i
  exact square S K D u α hu hα i

/-- Each component of the natural inclusion remains a monomorphism. -/
theorem incl_mono (i : I) : Mono ((inclNat S K D u α hu hα).app i) :=
  show Mono (incl (u.app i) (α.app i) (hα i)) from
    JTOrdinalFaceInverseImage.incl_mono (u.app i) (α.app i) (hα i)

end
end DaggerModels.PartII.JTOrdinalInverseFaceDiagram
