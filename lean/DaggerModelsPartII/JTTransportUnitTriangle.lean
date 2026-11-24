import DaggerModelsPartII.JTStrictTransport

/-!
# The actual strict unit triangle for transport

The specified Theta and its actual right mate Omega identify the composite
frame adjoint of a rigidification map with its original Part I adjoint.
The displayed equation uses the original delta unit. It is a strict input
to the manuscript's derived unit triangle; no Quillen or weak-unit claim
is inferred from the equation alone.
-/

set_option autoImplicit false

open CategoryTheory DaggerModels
open OrdinaryRigidification.DaggerRigidification
open OrdinaryRigidification.DaggerNerve

namespace DaggerModels.PartII.JTTransportUnitTriangle

open ConstantVertexAdjunction JTFrameAdjunction JTStrictTransport
open SegalLocalizers

noncomputable section

/-- The actual frame adjoint of the prescribed Theta transport followed by a. -/
def transportedFrameAdjoint (X : DaggerSSet.{0}) (C : DaggerSimplicialCat.{0, 0})
    (a : daggerRigidification.obj X ⟶ C) : delta.obj X ⟶ frameNerve.obj C :=
  JTFrameAdjunction.adjunction.homEquiv (delta.obj X) C (Theta.hom.app X ≫ a)

/-- The actual composite adjunction sends the prescribed transported map
into the original Part I adjoint followed by Omega inverse. -/
theorem compositeAdjoint_transport (X : DaggerSSet.{0})
    (C : DaggerSimplicialCat.{0, 0}) (a : daggerRigidification.obj X ⟶ C) :
    frameVertexAdjunction.homEquiv X C (Theta.hom.app X ≫ a) =
      DaggerActualRigidificationQuillen.adjunction.homEquiv X C a ≫
        Omega.inv.app C := by
  have hu := unit_conjugateEquiv DaggerActualRigidificationQuillen.adjunction
    frameVertexAdjunction Theta.hom X
  rw [Omega_inv_mate] at hu
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  rw [Functor.map_comp, ← Category.assoc, ← hu, Category.assoc]
  rw [← Omega.inv.naturality a, ← Category.assoc]

/-- The original delta unit followed by the actual vertex image of the
transported frame adjoint is the composite adjunction's actual adjoint. -/
theorem deltaUnit_transportedFrameAdjoint (X : DaggerSSet.{0})
    (C : DaggerSimplicialCat.{0, 0}) (a : daggerRigidification.obj X ⟶ C) :
    ConstantVertexAdjunction.adjunction.unit.app X ≫
        vertex.map (transportedFrameAdjoint X C a) =
      frameVertexAdjunction.homEquiv X C (Theta.hom.app X ≫ a) := by
  rw [frameVertexAdjunction, Adjunction.comp_homEquiv]
  rfl

/-- The strict original unit triangle, with the prescribed Theta/Omega,
original delta unit and original rigidification adjunction all retained. -/
theorem unit_triangle (X : DaggerSSet.{0}) (C : DaggerSimplicialCat.{0, 0})
    (a : daggerRigidification.obj X ⟶ C) :
    (ConstantVertexAdjunction.adjunction.unit.app X ≫
      vertex.map (transportedFrameAdjoint X C a)) ≫ Omega.hom.app C =
        DaggerActualRigidificationQuillen.adjunction.homEquiv X C a := by
  rw [deltaUnit_transportedFrameAdjoint, compositeAdjoint_transport,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end

end DaggerModels.PartII.JTTransportUnitTriangle
