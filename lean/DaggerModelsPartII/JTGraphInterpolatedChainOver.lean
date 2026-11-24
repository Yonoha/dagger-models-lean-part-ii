import DaggerModelsPartII.JTGraphInterpolatedOverOriginalSlice
import DaggerModelsPartII.JTGraphInterpolatedOverTime
import DaggerModelsPartII.JTGraphTransportRestriction
import DaggerModelsPartII.JTGraphMultiBeadIdentityLift

/-! Original graph lifts and cylinder comparisons along a chain. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTGraphInterpolatedChainOver

open JTProjectiveOrderedFiberComparison (row)
open JTGraphFactoredPresentation (TargetComma)
open JTGraphLiftTransport (GraphLift)
open JTGraphLiftRestriction (restrict restrict_comp)
open JTGraphInterpolatedComparison (Fiber sliceObject)
open JTGraphInterpolatedOverOriginal (overOriginal)
open JTGraphInterpolatedOverTime (overOriginal_reindex)
open JTNecklaceEndpointCylinder (under)
open JTGraphInterpolatedOverOriginalSlice (overOriginal_slice_iso)
open JTGraphTransportNaturality (toComma)

noncomputable section

private abbrev Source := SegalLocalizers.ReverseDaggerSpace.{0}
private abbrev Raw (W : Source) :=
  OrdinaryJTRealization.realization.obj (JTReversalInput.ordinaryInput.obj W)
private abbrev rawVertex := JTProjectiveRealizationMappingWeak.rawZeroGeneratorVertex

variable {W : Source} {x y : (row W ⦋0⦌).obj (op ⦋0⦌)}
variable {Q : NecklacesOver (Raw W) (rawVertex W x) (rawVertex W y)}

private abbrev nativeCode : TargetComma Q ⥤ NecklaceCode :=
  CostructuredArrow.proj (DecoratedCylinderNecklacePresentation.toTarget W x y) Q ⋙
    BoundaryNecklaceComma.sourceCode (DecoratedCylinderNecklacePresentation.underDiagram W x y)

section Interval

variable {I : Type} [Preorder I] (F : I ⥤ TargetComma Q)
variable (H : ∀ k, GraphLift (F.obj k).left (F.obj k).left.fiber.left)
variable (hH : ∀ k, (H k).collapse = 𝟙 _)
variable {i j k l m : I}

private abbrev arrow (h : i ≤ j) : F.obj i ⟶ F.obj j := F.map (homOfLE h)
private abbrev codeArrow (h : i ≤ j) : (F.obj i).left.fiber.left ⟶ (F.obj j).left.fiber.left :=
  nativeCode.map (arrow F h)

private theorem arrow_comp (h₁ : i ≤ k) (h₂ : k ≤ j) :
    arrow F (h₁.trans h₂) = arrow F h₁ ≫ arrow F h₂ :=
  F.map_comp (homOfLE h₁) (homOfLE h₂)

private theorem codeArrow_comp (h₁ : i ≤ k) (h₂ : k ≤ j) :
    codeArrow F (h₁.trans h₂) = codeArrow F h₁ ≫ codeArrow F h₂ :=
  (F ⋙ nativeCode).map_comp (homOfLE h₁) (homOfLE h₂)

/-- Restrict a chosen lift to the first native source, then transport it to the last target. -/
def intervalLift (hik : i ≤ k) (hkj : k ≤ j) :
    GraphLift (F.obj j).left (F.obj i).left.fiber.left :=
  (restrict (H k) (codeArrow F hik)).transport (arrow F hkj).left

include hH in
/-- The collapse is the whole interval's original native arrow. -/
theorem intervalLift_collapse (hik : i ≤ k) (hkj : k ≤ j) :
    (intervalLift F H hik hkj).collapse = codeArrow F (hik.trans hkj) := by
  change (codeArrow F hik ≫ (H k).collapse) ≫ codeArrow F hkj = _
  rw [hH k, Category.comp_id]
  exact (codeArrow_comp F hik hkj).symm

/-- Restriction from a smaller interval followed by transport to a larger one
recovers its original lift at every retained vertex. -/
theorem intervalLift_extend (hil : i ≤ l) (hlk : l ≤ k) (hkm : k ≤ m) (hmj : m ≤ j) :
    ((restrict (intervalLift F H hlk hkm) (codeArrow F hil)).transport (arrow F hmj).left) =
      intervalLift F H (hil.trans hlk) (hkm.trans hmj) := by
  unfold intervalLift
  rw [← JTGraphTransportRestriction.transport_restrict
    (restrict (H k) (codeArrow F hlk)) (codeArrow F hil) (arrow F hkm)]
  rw [restrict_comp, GraphLift.transport_comp]
  rw [← codeArrow_comp F hil hlk]
  have ha : (arrow F hkm).left ≫ (arrow F hmj).left = (arrow F (hkm.trans hmj)).left :=
    congrArg (fun f : F.obj k ⟶ F.obj j ↦ f.left) (arrow_comp F hkm hmj).symm
  rw [ha]

end Interval

section Simplex

variable {n : SimplexCategory} (F : Fin (n.len + 1) ⥤ TargetComma Q)
variable (H : ∀ i, GraphLift (F.obj i).left (F.obj i).left.fiber.left)
variable (hH : ∀ i, (H i).collapse = 𝟙 _)

private abbrev last : Fin (n.len + 1) := Fin.last n.len

/-- Each vertex of a finite original comma simplex determines its lift over the last object. -/
def chainFamily (i : Fin (n.len + 1)) :
    GraphLift (F.obj last).left (F.obj 0).left.fiber.left :=
  intervalLift F H (Fin.zero_le i) (Fin.le_last i)

include hH in
/-- All lifts of the chain use its same original native collapse. -/
theorem chainFamily_collapse (i : Fin (n.len + 1)) :
    (chainFamily F H i).collapse = codeArrow F (Fin.zero_le last) :=
  intervalLift_collapse F H hH (Fin.zero_le i) (Fin.le_last i)

/-- The full interpolated cylinder over the last object of a finite original comma simplex. -/
def chainOver : Fiber (F.obj 0).left.fiber.left n ⥤ Over (F.obj last) :=
  overOriginal (codeArrow F (Fin.zero_le last)) (chainFamily F H) (chainFamily_collapse F H hH)

/-- Each time vertex has its prescribed graph lift with the arrow to the last object. -/
def chainSliceIso (i : Fin (n.len + 1)) :
    (chainOver F H hH).obj (sliceObject (F.obj 0).left.fiber.left n i) ≅
      Over.mk (toComma (chainFamily F H i)) :=
  overOriginal_slice_iso (codeArrow F (Fin.zero_le last)) (chainFamily F H)
    (chainFamily_collapse F H hH) i

/-- Extend the vertex lifts of the reindexed subchain to the endpoints of the whole chain. -/
def subchainFamily {m : SimplexCategory} (θ : m ⟶ n) (i : Fin (m.len + 1)) :
    GraphLift (F.obj last).left (F.obj 0).left.fiber.left :=
  (restrict (intervalLift F H (θ.toOrderHom.monotone (Fin.zero_le i))
        (θ.toOrderHom.monotone (Fin.le_last i)))
      (codeArrow F (Fin.zero_le (θ.toOrderHom 0)))).transport
        (arrow F (Fin.le_last (θ.toOrderHom (Fin.last m.len)))).left

/-- Reindexing the original chain keeps exactly the lifts of the extended subchain. -/
theorem chainFamily_reindex {m : SimplexCategory} (θ : m ⟶ n) (i : Fin (m.len + 1)) :
    subchainFamily F H θ i = chainFamily F H (θ.toOrderHom i) :=
  intervalLift_extend F H (Fin.zero_le (θ.toOrderHom 0))
    (θ.toOrderHom.monotone (Fin.zero_le i)) (θ.toOrderHom.monotone (Fin.le_last i))
    (Fin.le_last (θ.toOrderHom (Fin.last m.len)))

include hH in
/-- Every extended subchain retains the native collapse of the whole chain. -/
theorem subchainFamily_collapse {m : SimplexCategory} (θ : m ⟶ n) (i : Fin (m.len + 1)) :
    (subchainFamily F H θ i).collapse = codeArrow F (Fin.zero_le last) := by
  rw [chainFamily_reindex]
  exact chainFamily_collapse F H hH (θ.toOrderHom i)

private theorem overOriginal_family_eq {V : TargetComma Q} {S : NecklaceCode}
    {m : SimplexCategory} (c : S ⟶ V.left.fiber.left)
    {D D' : Fin (m.len + 1) → GraphLift V.left S}
    (hD : ∀ i, (D i).collapse = c) (hD' : ∀ i, (D' i).collapse = c)
    (h : D = D') : overOriginal (n := m) c D hD = overOriginal (n := m) c D' hD' := by
  subst D'
  rfl

/-- Restriction of the entire cylinder agrees with the extended subchain cylinder
in the original slice over the last object. -/
theorem chainOver_reindex {m : SimplexCategory} (θ : m ⟶ n) :
    CostructuredArrow.map (S := BoundaryNecklaceComma.necklaceUnder)
        ((under (F.obj 0).left.fiber.left).map θ) ⋙ chainOver F H hH =
      overOriginal (n := m) (codeArrow F (Fin.zero_le last)) (subchainFamily F H θ)
        (subchainFamily_collapse F H hH θ) := by
  let c := codeArrow F (Fin.zero_le last)
  let D : Fin (m.len + 1) → GraphLift (F.obj last).left (F.obj 0).left.fiber.left :=
    fun i ↦ chainFamily F H (θ.toOrderHom i)
  have hD : ∀ i, (D i).collapse = c := fun i ↦ chainFamily_collapse F H hH (θ.toOrderHom i)
  have h : D = subchainFamily F H θ := funext fun i ↦ (chainFamily_reindex F H θ i).symm
  calc
    _ = overOriginal (n := m) c D hD :=
      overOriginal_reindex c (chainFamily F H) (chainFamily_collapse F H hH) θ
    _ = _ := overOriginal_family_eq c hD (subchainFamily_collapse F H hH θ) h

end Simplex

/-- Choose one identity-collapse lift at each original comma object. The choice
is indexed by the object, so different simplices use the same lift at a shared vertex. -/
def identityLift (U : TargetComma Q) :
    {D : GraphLift U.left U.left.fiber.left // D.collapse = 𝟙 _} :=
  let h := JTGraphMultiBeadIdentityLift.exists_identity_lift U.left
  ⟨h.choose, h.choose_spec⟩

/-- Every finite simplex of the original comma admits its whole cylinder comparison
using the identity-collapse lifts of its vertices. -/
def originalChainOver {n : SimplexCategory} (F : Fin (n.len + 1) ⥤ TargetComma Q) :
    Fiber (F.obj 0).left.fiber.left n ⥤ Over (F.obj (Fin.last n.len)) :=
  chainOver F (fun i ↦ (identityLift (F.obj i)).val) (fun i ↦ (identityLift (F.obj i)).property)


end

end DaggerModels.PartII.JTGraphInterpolatedChainOver
