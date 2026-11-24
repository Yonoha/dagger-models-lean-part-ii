import DaggerModelsPartII.JTCorrectedIntervalAssembly
import DaggerModelsPartII.JTJointCutSubdivision
import DaggerModelsPartII.JTNativeCutPointAssembly

/-!
# Concatenate the corrected split over the SAME original necklace

All four outer correction pieces are retained. Remove only the zero-length
inserted piece, reassociate the existing wedges, and apply the existing actual
interval concatenation. The map is constructed in NecklacesOver the original T,
so its full native triangle holds BEFORE any map to Q. This is a native result,
not a decorated-coefficient, raw, evaluation or higher coherence theorem.
-/

set_option autoImplicit false
set_option warningAsError true

open CategoryTheory Limits Opposite Simplicial
open DaggerChosenRigidificationNecklace DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTCorrectedCoarseIntervalComparison

noncomputable section

private def invCode {T U : NecklaceCode} (e : T.toSSet ≅ U.toSSet)
    (hf : e.hom.app (op ⦋0⦌) T.first = U.first)
    (hl : e.hom.app (op ⦋0⦌) T.last = U.last) : U ⟶ T where
  map := e.inv
  first := by
    have h := congrArg (fun f : T.toSSet ⟶ T.toSSet ↦ f.app (op ⦋0⦌) T.first)
      e.hom_inv_id
    change e.inv.app (op ⦋0⦌) (e.hom.app (op ⦋0⦌) T.first) = T.first at h
    simpa only [hf] using h
  last := by
    have h := congrArg (fun f : T.toSSet ⟶ T.toSSet ↦ f.app (op ⦋0⦌) T.last)
      e.hom_inv_id
    change e.inv.app (op ⦋0⦌) (e.hom.app (op ⦋0⦌) T.last) = T.last at h
    simpa only [hl] using h

private def assocInvOver {X : SSet.{0}} {a b c d : X.obj (op ⦋0⦌)}
    (P : NecklacesOver X a b) (Q : NecklacesOver X b c) (R : NecklacesOver X c d) :
    NecklacesOver.wedge P (NecklacesOver.wedge Q R) ⟶
      NecklacesOver.wedge (NecklacesOver.wedge P Q) R where
  hom := invCode (wedgeAssoc P.code Q.code R.code)
    (wedgeAssoc_first P.code Q.code R.code) (wedgeAssoc_last P.code Q.code R.code)
  w := by
    change (wedgeAssoc P.code Q.code R.code).inv ≫
        (NecklacesOver.wedge (NecklacesOver.wedge P Q) R).map =
      (NecklacesOver.wedge P (NecklacesOver.wedge Q R)).map
    calc
      _ = (wedgeAssoc P.code Q.code R.code).inv ≫
          ((wedgeAssoc P.code Q.code R.code).hom ≫
            (NecklacesOver.wedge P (NecklacesOver.wedge Q R)).map) :=
        congrArg ((wedgeAssoc P.code Q.code R.code).inv ≫ ·)
          (NecklacesOver.wedgeAssocOver P Q R).w.symm
      _ = _ := Iso.inv_hom_id_assoc _ _

private def zeroUnitOver {X : SSet.{0}} {a b : X.obj (op ⦋0⦌)}
    (Z : NecklaceCode) (hZ : Z.len = 0) (R : NecklacesOver X a b) :
    NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver Z a) R ⟶ R where
  hom := JTNativeCutPointAssembly.zeroUnit Z R.code hZ
  w := by
    dsimp only [NecklacesOver.wedge, JTCorrectedIntervalAssembly.constantOver]
    apply (wedgeIsPushout Z R.code).hom_ext
    · rw [← Category.assoc, JTNativeCutPointAssembly.zeroUnit_left,
        wedgeDesc_left, Category.assoc]
      have h : pointAt R.code (ULift.up 0) ≫ R.map = SSet.yonedaEquiv.symm a := by
        apply SSet.yonedaEquiv.injective
        simpa only [SSet.yonedaEquiv_comp, pointAt_vertex,
          SSet.yonedaEquiv.apply_symm_apply] using R.first
      exact congrArg (SSet.stdSimplex.isTerminalObj₀.from Z.toSSet ≫ ·) h
    · rw [← Category.assoc, JTNativeCutPointAssembly.zeroUnit_right,
        Category.id_comp,
        wedgeDesc_right]

private def paddedConcat {X : SSet.{0}} {u a b c v : X.obj (op ⦋0⦌)}
    (A : NecklacesOver X u a) (e : NecklacesOver X a a) (B : NecklacesOver X a b)
    (C : NecklacesOver X b c) (f : NecklacesOver X c c) (D : NecklacesOver X c v)
    (K : NecklacesOver X a c) (μ : NecklacesOver.wedge B C ⟶ K)
    (Z : NecklaceCode) (hZ : Z.len = 0) :
    NecklacesOver.wedge (NecklacesOver.wedge A (NecklacesOver.wedge e B))
        (NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver Z b)
          (NecklacesOver.wedge C (NecklacesOver.wedge f D))) ⟶
      NecklacesOver.wedge A
        (NecklacesOver.wedge (NecklacesOver.wedge e (NecklacesOver.wedge K f)) D) :=
  NecklacesOver.wedgeHom
    (NecklacesOver.Hom.id (NecklacesOver.wedge A (NecklacesOver.wedge e B)))
    (zeroUnitOver Z hZ (NecklacesOver.wedge C (NecklacesOver.wedge f D))) ≫
    NecklacesOver.wedgeAssocOver A (NecklacesOver.wedge e B)
      (NecklacesOver.wedge C (NecklacesOver.wedge f D)) ≫
    NecklacesOver.wedgeHom (NecklacesOver.Hom.id A)
      (NecklacesOver.wedgeAssocOver e B (NecklacesOver.wedge C (NecklacesOver.wedge f D))) ≫
    NecklacesOver.wedgeHom (NecklacesOver.Hom.id A) (NecklacesOver.wedgeHom (NecklacesOver.Hom.id e)
      (assocInvOver B C (NecklacesOver.wedge f D))) ≫
    NecklacesOver.wedgeHom (NecklacesOver.Hom.id A) (NecklacesOver.wedgeHom (NecklacesOver.Hom.id e)
      (NecklacesOver.wedgeHom μ (NecklacesOver.Hom.id (NecklacesOver.wedge f D)))) ≫
    NecklacesOver.wedgeHom (NecklacesOver.Hom.id A)
      (NecklacesOver.wedgeHom (NecklacesOver.Hom.id e) (assocInvOver K f D)) ≫
    NecklacesOver.wedgeHom (NecklacesOver.Hom.id A) (assocInvOver e (NecklacesOver.wedge K f) D)

variable (T : NecklaceCode) (a b c : Fin (T.len + 1)) (hab : a ≤ b) (hbc : b ≤ c)

private abbrev vertex (v : Fin (T.len + 1)) := T.verticesEquiv.symm (ULift.up v)
private abbrev E := single 1

/-- The coarse interval keeps the original ending/starting corrections at BOTH cuts. -/
def coarseOver (hac : a ≤ c) :
    NecklacesOver T.toSSet (vertex T 0) (vertex T (Fin.last T.len)) :=
  NecklacesOver.wedge
    (NecklacesOver.wedge (intervalOver T 0 a (Fin.zero_le a))
      (JTCorrectedIntervalAssembly.constantOver E (vertex T a)))
    (NecklacesOver.wedge
      (NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver E (vertex T a))
        (NecklacesOver.wedge (intervalOver T a c hac)
          (JTCorrectedIntervalAssembly.constantOver E (vertex T c))))
      (NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver E (vertex T c))
        (intervalOver T c (Fin.last T.len) (Fin.le_last c))))

/-- The actual corrected split concatenates over the original T, including zero intervals. -/
def comparisonOver :
    JTCorrectedIntervalAssembly.wholeOver T a b c hab hbc (single 0) ⟶
      coarseOver T a c (hab.trans hbc) :=
  paddedConcat
    (NecklacesOver.wedge (intervalOver T 0 a (Fin.zero_le a))
      (JTCorrectedIntervalAssembly.constantOver E (vertex T a)))
    (JTCorrectedIntervalAssembly.constantOver E (vertex T a)) (intervalOver T a b hab)
    (intervalOver T b c hbc) (JTCorrectedIntervalAssembly.constantOver E (vertex T c))
    (NecklacesOver.wedge (JTCorrectedIntervalAssembly.constantOver E (vertex T c))
      (intervalOver T c (Fin.last T.len) (Fin.le_last c)))
    (intervalOver T a c (hab.trans hbc)) (JTJointCutSubdivision.concat T a b c hab hbc)
    (single 0) rfl

/-- The complete corrected coarse assembly retains the original GLOBAL endpoints. -/
def assembly (hac : a ≤ c) : (coarseOver T a c hac).code ⟶ T where
  map := (coarseOver T a c hac).map
  first := (coarseOver T a c hac).first
  last := (coarseOver T a c hac).last

/-- The full native comparison commutes BEFORE postcomposition with any target Q. -/
theorem comparison_assembly :
    (comparisonOver T a b c hab hbc).hom ≫ assembly T a c (hab.trans hbc) =
      JTCorrectedIntervalAssembly.assembly T a b c hab hbc (single 0) :=
  NecklaceCode.Hom.ext (comparisonOver T a b c hab hbc).w

end
end DaggerModels.PartII.JTCorrectedCoarseIntervalComparison
