import DaggerModelsPartII.SynchronizedSimplicialParameters

/-! Simultaneous maps of independent parameter diagrams over the original time. -/

set_option autoImplicit false

open CategoryTheory Opposite Simplicial MonoidalCategory
open CartesianMonoidalCategory

namespace DaggerModels.PartII.SynchronizedSimplicialParameters

open GrothendieckTotalElements (totalDiagram)

noncomputable section

variable {C C' D D' : Type}
variable [SmallCategory C] [SmallCategory C'] [SmallCategory D] [SmallCategory D']

section Single

variable {G : C ⥤ SSet.{0}} {G' : C' ⥤ SSet.{0}}
variable (F : C ⥤ C') (α : G ⟶ F ⋙ G')

private def mapForward : (totalDiagram G).Elements ⥤ (totalDiagram G').Elements where
  obj p := ⟨(F.obj p.1.1, p.1.2), (α.app p.1.1).app p.1.2 p.2⟩
  map {p q} f := ⟨(F.map f.val.1, f.val.2), by
    let g : (F.obj p.1.1, p.1.2) ⟶ (F.obj q.1.1, q.1.2) := (F.map f.val.1, f.val.2)
    have h := congrFun ((Functor.uncurry.map α).naturality f.val) p.2
    change (α.app q.1.1).app q.1.2 ((totalDiagram G).map f.val p.2) =
      (totalDiagram G').map g ((α.app p.1.1).app p.1.2 p.2) at h
    rw [f.property] at h
    exact h.symm⟩
  map_id p := by
    apply CategoryOfElements.ext
    exact Prod.ext (F.map_id p.1.1) rfl
  map_comp f g := by
    apply CategoryOfElements.ext
    exact Prod.ext (F.map_comp f.val.1 g.val.1) rfl

/-- Map the base and every parameter while leaving the time operator unchanged. -/
def mapIndex : (totalDiagram G).Elementsᵒᵖ ⥤ (totalDiagram G').Elementsᵒᵖ :=
  (mapForward F α).op

theorem mapIndex_time : mapIndex F α ⋙ time G' = time G := rfl

end Single

variable {G : C ⥤ SSet.{0}} {G' : C' ⥤ SSet.{0}}
variable {H : D ⥤ SSet.{0}} {H' : D' ⥤ SSet.{0}}
variable (F : C ⥤ C') (K : D ⥤ D') (α : G ⟶ F ⋙ G') (β : H ⟶ K ⋙ H')

private def pairNat : pairSpace G H ⟶ F.prod K ⋙ pairSpace G' H' :=
  Functor.whiskerRight (NatTrans.prod α β) (MonoidalCategory.tensor SSet.{0})

/-- Transport the two complete parameters along independent base maps at the same time. -/
def mapPair : Index G H ⥤ Index G' H' := mapIndex (F.prod K) (pairNat F K α β)

theorem mapPair_time : mapPair F K α β ⋙ time (pairSpace G' H') =
    time (pairSpace G H) := rfl

/-- Transport commutes with retaining the full left parameter, on objects and arrows. -/
theorem mapPair_left : mapPair F K α β ⋙ left G' H' = left G H ⋙ mapIndex F α := by
  rfl

/-- Transport commutes with retaining the full right parameter, on objects and arrows. -/
theorem mapPair_right : mapPair F K α β ⋙ right G' H' = right G H ⋙ mapIndex K β := by
  rfl

section Ext

private theorem obj_ext {p q : Index G H}
    (h₁ : (left G H).obj p = (left G H).obj q)
    (h₂ : (right G H).obj p = (right G H).obj q) : p = q := by
  apply Opposite.unop_injective
  rcases p with ⟨⟨⟨⟨c, d⟩, n⟩, u⟩⟩
  rcases q with ⟨⟨⟨⟨c', d'⟩, n'⟩, v⟩⟩
  have hc : c = c' := congrArg (fun t ↦ t.unop.fst.1) h₁
  have hd : d = d' := congrArg (fun t ↦ t.unop.fst.1) h₂
  have hn : n = n' := congrArg (fun t ↦ t.unop.fst.2) h₁
  subst c'
  subst d'
  subst n'
  apply congrArg (fun t ↦ (⟨((c, d), n), t⟩ : (totalDiagram (pairSpace G H)).Elements))
  exact Prod.ext
    (eq_of_heq ((Sigma.mk.inj_iff.mp (congrArg Opposite.unop h₁)).2))
    (eq_of_heq ((Sigma.mk.inj_iff.mp (congrArg Opposite.unop h₂)).2))

private theorem map_ext {p q : Index G H} {f g : p ⟶ q}
    (h₁ : (left G H).map f = (left G H).map g)
    (h₂ : (right G H).map f = (right G H).map g) : f = g := by
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Prod.ext
  · exact Prod.ext
      (congrArg (fun a ↦ a.unop.val.1) h₁)
      (congrArg (fun a ↦ a.unop.val.1) h₂)
  · exact congrArg (fun a ↦ a.unop.val.2) h₁

/-- The two original projections determine any functor to the synchronized index. -/
theorem joint_functor_ext {A : Type} [SmallCategory A] {L M : A ⥤ Index G H}
    (h₁ : L ⋙ left G H = M ⋙ left G H)
    (h₂ : L ⋙ right G H = M ⋙ right G H) : L = M := by
  have hobj (p : A) : L.obj p = M.obj p :=
    obj_ext (Functor.congr_obj h₁ p) (Functor.congr_obj h₂ p)
  refine CategoryTheory.Functor.ext hobj ?_
  intro p q f
  apply map_ext
  · simpa only [Functor.map_comp, eqToHom_map] using Functor.congr_hom h₁ f
  · simpa only [Functor.map_comp, eqToHom_map] using Functor.congr_hom h₂ f

end Ext

end

end DaggerModels.PartII.SynchronizedSimplicialParameters
