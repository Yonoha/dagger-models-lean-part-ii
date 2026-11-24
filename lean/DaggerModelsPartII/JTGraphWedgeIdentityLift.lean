import DaggerModelsPartII.JTGraphJointSeparation
import DaggerModelsPartII.JTInternalNecklaceGraphLift
import DaggerModelsPartII.JTNativeNecklaceBoundaryConstant

/-!
# Graph parameters on the original native wedge
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MonoidalCategory DaggerModels
open CartesianMonoidalCategory
open DaggerChosenRigidificationNecklace
open DaggerChosenRigidificationNecklace.NecklaceCode

namespace DaggerModels.PartII.JTGraphWedgeIdentityLift

open JTInternalNecklaceGraphLift JTNecklaceEndpointCylinder
open JTNativeNecklaceBoundaryConstant

noncomputable section

private abbrev J := GroupoidSimplex.parameter
private abbrev C (T : NecklaceCode) (k : SimplexCategory) := (value T).obj k
private abbrev aug := NecklaceCylinderAugmentation.augmentation
private abbrev firstPoint (T : NecklaceCode) := pointAt T (ULift.up 0)
private abbrev lastPoint (T : NecklaceCode) := pointAt T (ULift.up (Fin.last T.len))
private abbrev terminalFrom (X : SSet.{0}) := SSet.stdSimplex.isTerminalObj₀.from X

variable {T : NecklaceCode} {k : SimplexCategory}

/-- Over the boundary of the label, replacing the parameter preserves the cylinder map. -/
private theorem graph_eq_of_boundary {X : SSet.{0}} {u : X ⟶ C T k}
    (b : X ⟶ JTXiEndpointCollapse.boundary) (hb : u ≫ aug T k = b ≫ endpointInclusion T)
    (s t : X ⟶ J.obj k) : graph u s = graph u t := by
  unfold graph
  rw [hb, JTNecklaceCylinderConnector.boundary_collapse,
    JTNecklaceCylinderConnector.boundary_collapse]

variable {a b c : (C T k).obj (op ⦋0⦌)}

/-- Compatible parameters glue by the native wedge pushout. -/
private theorem wedge_parameter_of_agreement
    (P : NecklacesOver (C T k) a b) (Q : NecklacesOver (C T k) b c)
    (s : P.code.toSSet ⟶ J.obj k) (t : Q.code.toSSet ⟶ J.obj k)
    (hs : graph P.map s = P.map) (ht : graph Q.map t = Q.map)
    (h : lastPoint P.code ≫ s = firstPoint Q.code ≫ t) :
    ∃ p : (NecklacesOver.wedge P Q).code.toSSet ⟶ J.obj k,
      graph (NecklacesOver.wedge P Q).map p = (NecklacesOver.wedge P Q).map := by
  refine ⟨wedgeDesc P.code Q.code s t h, (wedgeIsPushout P.code Q.code).hom_ext ?_ ?_⟩
  · rw [graph_comp, NecklacesOver.wedge_left, wedgeDesc_left]
    exact hs
  · rw [graph_comp, NecklacesOver.wedge_right, wedgeDesc_right]
    exact ht

/-- Two bead blocks with graph parameters admit a parameter on their original wedge. -/
theorem exists_wedge_parameter
    (P : NecklacesOver (C T k) a b) (Q : NecklacesOver (C T k) b c)
    (s : P.code.toSSet ⟶ J.obj k) (t : Q.code.toSSet ⟶ J.obj k)
    (hs : graph P.map s = P.map) (ht : graph Q.map t = Q.map) :
    ∃ p : (NecklacesOver.wedge P Q).code.toSSet ⟶ J.obj k,
      graph (NecklacesOver.wedge P Q).map p = (NecklacesOver.wedge P Q).map := by
  let j := lastPoint P.code ≫ P.map
  let u := lastPoint P.code ≫ s
  let v := firstPoint Q.code ≫ t
  have hleft : graph j u = j := by
    rw [← graph_comp, hs]
  have hright : graph j v = j := by
    change graph (lastPoint P.code ≫ P.map) (firstPoint Q.code ≫ t) = _
    rw [NecklacesOver.wedge_compat P Q, ← graph_comp, ht]
    exact (NecklacesOver.wedge_compat P Q).symm
  have h := (hleft.trans hright.symm : graph j u = graph j v)
  rcases JTGraphJointSeparation.parameter_eq_or_endpoint T k (j ≫ aug T k) u v h with
    huv | hfirst | hlast
  · exact wedge_parameter_of_agreement P Q s t hs ht huv
  · let p := terminalFrom P.code.toSSet ≫ v
    have hP : P.map ≫ aug T k = terminalFrom P.code.toSSet ≫ firstPoint T :=
      constant_of_last_first (P.map ≫ aug T k) ((Category.assoc _ _ _).symm.trans hfirst)
    have he : SSet.boundary₁.ι₀ ≫ endpointInclusion T = firstPoint T :=
      SSet.boundary₁.ι₀_desc _ _
    have hb : P.map ≫ aug T k =
        (terminalFrom P.code.toSSet ≫ SSet.boundary₁.ι₀) ≫ endpointInclusion T := by
      rw [hP, Category.assoc, he]
    refine wedge_parameter_of_agreement P Q p t ((graph_eq_of_boundary _ hb p s).trans hs)
      ht ?_
    have hterm : lastPoint P.code ≫ terminalFrom P.code.toSSet = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    dsimp only [p]
    rw [← Category.assoc, hterm, Category.id_comp]
  · let q := terminalFrom Q.code.toSSet ≫ u
    have hQ : Q.map ≫ aug T k = terminalFrom Q.code.toSSet ≫ lastPoint T := by
      apply constant_of_first_last
      rw [← Category.assoc, ← NecklacesOver.wedge_compat P Q]
      exact hlast
    have he : SSet.boundary₁.ι₁ ≫ endpointInclusion T = lastPoint T :=
      SSet.boundary₁.ι₁_desc _ _
    have hb : Q.map ≫ aug T k =
        (terminalFrom Q.code.toSSet ≫ SSet.boundary₁.ι₁) ≫ endpointInclusion T := by
      rw [hQ, Category.assoc, he]
    refine wedge_parameter_of_agreement P Q s q hs
      ((graph_eq_of_boundary _ hb q t).trans ht) ?_
    have hterm : firstPoint Q.code ≫ terminalFrom Q.code.toSSet = 𝟙 _ :=
      SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
    dsimp only [q]
    rw [← Category.assoc, hterm, Category.id_comp]

end

end DaggerModels.PartII.JTGraphWedgeIdentityLift
