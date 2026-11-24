import DaggerModelsPartII.JTBoundaryNecklaceConeTriangle

/-! Compare two presentations of the same diagram of original necklaces. -/

set_option autoImplicit false

open CategoryTheory DaggerModels DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklacePresentationTransport

open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)
open JTBoundaryNecklacePresentationCone (mapPresentation mapPresentation_code)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

variable {I J : Type} [SmallCategory I] [SmallCategory J]
variable (E : I ⥤ Under B) (F : J ⥤ Under B)
variable {L L' : J ⥤ I} (p : F ⟶ L ⋙ E) (q : F ⟶ L' ⋙ E) (α : L ⟶ L')
variable (h : ∀ i, p.app i ≫ E.map (α.app i) = q.app i)

private def component (P : BoundaryNecklaceComma.Presentation F) :
    (mapPresentation E F L p).obj P ⟶ (mapPresentation E F L' q).obj P :=
  ⟨α.app P.base, CostructuredArrow.homMk (𝟙 P.fiber.left) (by
    change necklaceUnder.map (𝟙 P.fiber.left) ≫ (P.fiber.hom ≫ q.app P.base) =
      (P.fiber.hom ≫ p.app P.base) ≫ E.map (α.app P.base)
    rw [necklaceUnder.map_id, Category.id_comp, Category.assoc, h])⟩

/-- A natural change of label with the same underlying traversal induces a
comparison on the full presentations. Its native operator is the identity. -/
def comparison : mapPresentation E F L p ⟶ mapPresentation E F L' q where
  app := component E F p q α h
  naturality {P P'} f := by
    apply JTTargetCommaPullback.operator_ext
    · exact α.naturality f.base
    · change (sourceCode E).map (_ ≫ _) = (sourceCode E).map (_ ≫ _)
      rw [(sourceCode E).map_comp, (sourceCode E).map_comp, mapPresentation_code E F L p,
        mapPresentation_code E F L' q]
      change f.fiber.left ≫ 𝟙 P'.fiber.left = 𝟙 P.fiber.left ≫ f.fiber.left
      rw [Category.comp_id, Category.id_comp]

/-- Evaluating a whiskered lift agrees with reindexing the entire original presentation. -/
theorem mapPresentation_reindex {K : Type} [SmallCategory K] (G : K ⥤ J) :
    mapPresentation E (G ⋙ F) (G ⋙ L) (Functor.whiskerLeft G p) =
      Grothendieck.pre (fiberDiagram F) G ⋙ mapPresentation E F L p := rfl

/-- Compare presentations along a change of indices and a change of labels. -/
def comparisonWhisker {K : Type} [SmallCategory K] (G : K ⥤ J) {M : K ⥤ I}
    (p₀ : G ⋙ F ⟶ M ⋙ E) (α₀ : M ⟶ G ⋙ L)
    (h₀ : ∀ i, p₀.app i ≫ E.map (α₀.app i) = p.app (G.obj i)) :
    mapPresentation E (G ⋙ F) M p₀ ⟶
      Grothendieck.pre (fiberDiagram F) G ⋙ mapPresentation E F L p :=
  comparison E (G ⋙ F) p₀ (Functor.whiskerLeft G p) α₀ h₀ ≫
    eqToHom (mapPresentation_reindex E F p G)

section Joint

variable {K R : Type} [SmallCategory K] [SmallCategory R]
variable (G : K ⥤ J) (A : J ⥤ R) (A₀ : K ⥤ R)

/-- Reindex a Grothendieck construction while retaining its diagram over a common base. -/
def preJoint (D : R ⥤ Cat.{0, 0}) (hJoint : G ⋙ A = A₀) :
    Grothendieck (A₀ ⋙ D) ⥤ Grothendieck (A ⋙ D) := by
  subst A₀
  exact Grothendieck.pre (A ⋙ D) G

variable (T : R ⥤ Under B) (hJoint : G ⋙ A = A₀)

variable {L₁ : J ⥤ I} {M : K ⥤ I}
variable (p₁ : A ⋙ T ⟶ L₁ ⋙ E) (p₀ : A₀ ⋙ T ⟶ M ⋙ E) (α₀ : M ⟶ G ⋙ L₁)
variable (h₀ : ∀ i, HEq (p₀.app i ≫ E.map (α₀.app i)) (p₁.app (G.obj i)))

/-- Change labels along a common diagram, retaining the full internal fibers. -/
def comparisonJoint {C : Type*} [Category* C] (H : BoundaryNecklaceComma.Presentation E ⥤ C) :
    mapPresentation E (A₀ ⋙ T) M p₀ ⋙ H ⟶
      preJoint G A A₀ (T ⋙ BoundaryNecklaceComma.diagram) hJoint ⋙
        mapPresentation E (A ⋙ T) L₁ p₁ ⋙ H := by
  subst A₀
  have hs (i : K) : p₀.app i ≫ E.map (α₀.app i) = p₁.app (G.obj i) := by
    exact eq_of_heq (h₀ i)
  exact Functor.whiskerRight (comparisonWhisker E (A ⋙ T) p₁ G p₀ α₀ hs) H

end Joint

section WhiskerOperators

variable {K : Type} [SmallCategory K] (G : K ⥤ J) {M : K ⥤ I}
variable (p₀ : G ⋙ F ⟶ M ⋙ E) (α₀ : M ⟶ G ⋙ L)
variable (h₀ : ∀ i, p₀.app i ≫ E.map (α₀.app i) = p.app (G.obj i))

/-- Reindexing a comparison changes its decorated operator by the given label map. -/
theorem comparisonWhisker_base (P : BoundaryNecklaceComma.Presentation (G ⋙ F)) :
    ((comparisonWhisker E F p G p₀ α₀ h₀).app P).base = α₀.app P.base := by
  simp only [comparisonWhisker, eqToHom_refl, Category.comp_id]
  rfl

/-- Reindexing a comparison retains the entire internal necklace. -/
theorem comparisonWhisker_code (P : BoundaryNecklaceComma.Presentation (G ⋙ F)) :
    (sourceCode E).map ((comparisonWhisker E F p G p₀ α₀ h₀).app P) = 𝟙 P.fiber.left := by
  simp only [comparisonWhisker, eqToHom_refl, Category.comp_id]
  rfl

variable {K₁ : Type} [SmallCategory K₁] (H : K₁ ⥤ K) {L₁ : K₁ ⥤ I}
variable (p₁ : H ⋙ G ⋙ F ⟶ L₁ ⋙ E) (β : L₁ ⟶ H ⋙ M)
variable (h' : ∀ i, p₁.app i ≫ E.map (β.app i) = p₀.app (H.obj i))

include h₀ h' in
private theorem comp_square (i : K₁) :
    p₁.app i ≫ E.map ((β ≫ Functor.whiskerLeft H α₀).app i) =
      p.app ((H ⋙ G).obj i) := by
  change p₁.app i ≫ E.map (β.app i ≫ α₀.app (H.obj i)) = _
  rw [E.map_comp, ← Category.assoc, h' i]
  exact h₀ (H.obj i)

set_option maxHeartbeats 500000 in
/-- Comparing along two changes of index and label gives their pasted comparison. -/
theorem comparisonWhisker_comp :
    comparisonWhisker E F p (H ⋙ G) p₁ (β ≫ Functor.whiskerLeft H α₀)
        (comp_square E F p G p₀ α₀ h₀ H p₁ β h') =
      comparisonWhisker E (G ⋙ F) p₀ H p₁ β h' ≫
        Functor.whiskerLeft (Grothendieck.pre (fiberDiagram (G ⋙ F)) H)
          (comparisonWhisker E F p G p₀ α₀ h₀) := by
  apply NatTrans.ext
  funext P
  apply JTTargetCommaPullback.operator_ext
  · simp only [comparisonWhisker_base, NatTrans.comp_app, Functor.whiskerLeft_app,
      Grothendieck.comp_base, Grothendieck.pre_obj_base]
  · let N := sourceCode E
    let f := (comparisonWhisker E (G ⋙ F) p₀ H p₁ β h').app P
    let g := (comparisonWhisker E F p G p₀ α₀ h₀).app
      ((Grothendieck.pre (fiberDiagram (G ⋙ F)) H).obj P)
    let k := (comparisonWhisker E F p (H ⋙ G) p₁ (β ≫ Functor.whiskerLeft H α₀)
      (comp_square E F p G p₀ α₀ h₀ H p₁ β h')).app P
    change N.map k = N.map (f ≫ g)
    have hf : N.map f = 𝟙 P.fiber.left := comparisonWhisker_code E (G ⋙ F) p₀ H p₁ β h' P
    have hg : N.map g = 𝟙 P.fiber.left :=
      comparisonWhisker_code E F p G p₀ α₀ h₀ ((Grothendieck.pre (fiberDiagram (G ⋙ F)) H).obj P)
    exact (comparisonWhisker_code E F p (H ⋙ G) p₁ (β ≫ Functor.whiskerLeft H α₀)
      (comp_square E F p G p₀ α₀ h₀ H p₁ β h') P).trans
      ((N.map_comp f g).trans ((congrArg₂ (· ≫ ·) hf hg).trans (Category.id_comp _))).symm

end WhiskerOperators

section Cones

open JTBoundaryNecklacePresentationCone (coneFromVariableDiagram)

variable {U V : BoundaryNecklaceComma.Presentation E} (a : U ⟶ V)
variable (l : L ⟶ (Functor.const J).obj U.base)
  (l' : L' ⟶ (Functor.const J).obj V.base)
variable (n : F ⟶ (Functor.const J).obj (necklaceUnder.obj U.fiber.left))
  (n' : F ⟶ (Functor.const J).obj (necklaceUnder.obj V.fiber.left))
variable (hp : ∀ j, p.app j ≫ E.map (l.app j) = n.app j ≫ U.fiber.hom)
  (hq : ∀ j, q.app j ≫ E.map (l'.app j) = n'.app j ≫ V.fiber.hom)

/-- Comparing diagrams before collapsing agrees with collapsing before
transport, when both decorated and native operators form triangles. -/
theorem comparison_cone
    (hl : ∀ j, α.app j ≫ l'.app j = l.app j ≫ a.base)
    (hn : ∀ j, n'.app j = n.app j ≫ necklaceUnder.map a.fiber.left) :
    comparison E F p q α h ≫ coneFromVariableDiagram E V F L' q l' n' hq =
      coneFromVariableDiagram E U F L p l n hp ≫ (Functor.const _).map a := by
  apply NatTrans.ext
  funext P
  apply JTTargetCommaPullback.operator_ext
  · change α.app P.base ≫ l'.app P.base = l.app P.base ≫ a.base
    exact hl P.base
  · let C := sourceCode E
    change C.map (_ ≫ _) = C.map (_ ≫ _)
    rw [C.map_comp, C.map_comp]
    apply NecklaceCode.Hom.ext
    change NecklaceCode.simplicialFunctor.map (𝟙 P.fiber.left) ≫
      (P.fiber.hom ≫ n'.app P.base).right =
      (P.fiber.hom ≫ n.app P.base).right ≫ a.fiber.left.map
    rw [NecklaceCode.simplicialFunctor.map_id, Category.id_comp, hn]
    change P.fiber.hom.right ≫ (n.app P.base).right ≫ a.fiber.left.map =
      (P.fiber.hom.right ≫ (n.app P.base).right) ≫ a.fiber.left.map
    exact (Category.assoc _ _ _).symm

end Cones

section WhiskeredCones

open JTBoundaryNecklacePresentationCone (coneFromVariableDiagram)

variable {K : Type} [SmallCategory K] (G : K ⥤ J) {M : K ⥤ I}
variable {U V : BoundaryNecklaceComma.Presentation E} (a : U ⟶ V)
variable (p₀ : G ⋙ F ⟶ M ⋙ E) (α₀ : M ⟶ G ⋙ L)
variable (h₀ : ∀ i, p₀.app i ≫ E.map (α₀.app i) = p.app (G.obj i))
variable (l₀ : M ⟶ (Functor.const K).obj U.base) (l : L ⟶ (Functor.const J).obj V.base)
variable (n₀ : G ⋙ F ⟶ (Functor.const K).obj (necklaceUnder.obj U.fiber.left))
variable (n : F ⟶ (Functor.const J).obj (necklaceUnder.obj V.fiber.left))
variable (hp₀ : ∀ j, p₀.app j ≫ E.map (l₀.app j) = n₀.app j ≫ U.fiber.hom)
variable (hp : ∀ j, p.app j ≫ E.map (l.app j) = n.app j ≫ V.fiber.hom)

private theorem cone_reindex :
    eqToHom (mapPresentation_reindex E F p G) ≫
        Functor.whiskerLeft (Grothendieck.pre (fiberDiagram F) G)
          (coneFromVariableDiagram E V F L p l n hp) =
      coneFromVariableDiagram E V (G ⋙ F) (G ⋙ L) (Functor.whiskerLeft G p)
        (Functor.whiskerLeft G l) (Functor.whiskerLeft G n) (fun j ↦ hp (G.obj j)) := by
  have he : mapPresentation_reindex E F p G = rfl := Subsingleton.elim _ _
  rw [he, eqToHom_refl, Category.id_comp]
  apply NatTrans.ext
  funext P
  apply JTTargetCommaPullback.operator_ext
  · rfl
  · rfl

set_option maxHeartbeats 300000 in
/-- The natural comparison respects compatible original cones after reindexing. -/
theorem comparisonWhisker_cone
    (hl : ∀ j, α₀.app j ≫ l.app (G.obj j) = l₀.app j ≫ a.base)
    (hn : ∀ j, n.app (G.obj j) = n₀.app j ≫ necklaceUnder.map a.fiber.left) :
    comparisonWhisker E F p G p₀ α₀ h₀ ≫
        Functor.whiskerLeft (Grothendieck.pre (fiberDiagram F) G)
          (coneFromVariableDiagram E V F L p l n hp) =
      coneFromVariableDiagram E U (G ⋙ F) M p₀ l₀ n₀ hp₀ ≫ (Functor.const _).map a := by
  rw [comparisonWhisker, Category.assoc, cone_reindex]
  exact comparison_cone (I := I) (J := K) (L := M) (L' := G ⋙ L)
    E (G ⋙ F) p₀ (Functor.whiskerLeft G p) α₀ h₀ (U := U) (V := V) a l₀
    (Functor.whiskerLeft G l) n₀ (Functor.whiskerLeft G n) hp₀ (fun j ↦ hp (G.obj j)) hl hn

end WhiskeredCones

section JointCones

open JTBoundaryNecklacePresentationCone (coneFromVariableDiagram)
open JTBoundaryNecklaceConeReindex (mapCone)
open JTBoundaryNecklaceConeTriangle (mapCone_triangle)

variable {K R : Type} [SmallCategory K] [SmallCategory R]
variable (G : K ⥤ J) (A : J ⥤ R) (A₀ : K ⥤ R)
variable (T : R ⥤ Under B) (hJoint : G ⋙ A = A₀)
variable {L₁ : J ⥤ I} {M : K ⥤ I}
variable (p₁ : A ⋙ T ⟶ L₁ ⋙ E) (p₀ : A₀ ⋙ T ⟶ M ⋙ E) (α₀ : M ⟶ G ⋙ L₁)
variable (h₀ : ∀ i, HEq (p₀.app i ≫ E.map (α₀.app i)) (p₁.app (G.obj i)))

variable {U V : BoundaryNecklaceComma.Presentation E} (a : U ⟶ V)
variable (l₀ : M ⟶ (Functor.const K).obj U.base) (l₁ : L₁ ⟶ (Functor.const J).obj V.base)
variable (n₀ : A₀ ⋙ T ⟶ (Functor.const K).obj (necklaceUnder.obj U.fiber.left))
variable (n₁ : A ⋙ T ⟶ (Functor.const J).obj (necklaceUnder.obj V.fiber.left))
variable (hp₀ : ∀ j, p₀.app j ≫ E.map (l₀.app j) = n₀.app j ≫ U.fiber.hom)
variable (hp₁ : ∀ j, p₁.app j ≫ E.map (l₁.app j) = n₁.app j ≫ V.fiber.hom)

set_option maxHeartbeats 300000 in
/-- The joint comparison carries each compatible cone to the original cone. -/
theorem comparisonJoint_mapCone {C : Type*} [Category* C]
    (H : BoundaryNecklaceComma.Presentation E ⥤ C)
    {X Y : C} (s : H.obj U ⟶ X) (t : H.obj V ⟶ Y) (d : X ⟶ Y)
    (hd : H.map a ≫ t = s ≫ d)
    (hl : ∀ j, α₀.app j ≫ l₁.app (G.obj j) = l₀.app j ≫ a.base)
    (hn : ∀ j, HEq (n₁.app (G.obj j)) (n₀.app j ≫ necklaceUnder.map a.fiber.left)) :
    comparisonJoint E G A A₀ T hJoint p₁ p₀ α₀ h₀ H ≫
        Functor.whiskerLeft (preJoint G A A₀ (T ⋙ BoundaryNecklaceComma.diagram) hJoint)
          (mapCone (coneFromVariableDiagram E V (A ⋙ T) L₁ p₁ l₁ n₁ hp₁) H t) =
      mapCone (coneFromVariableDiagram E U (A₀ ⋙ T) M p₀ l₀ n₀ hp₀) H s ≫
        (Functor.const _).map d := by
  subst A₀
  have hs (j : K) : p₀.app j ≫ E.map (α₀.app j) = p₁.app (G.obj j) := by
    exact eq_of_heq (h₀ j)
  have hN (j : K) : n₁.app (G.obj j) = n₀.app j ≫ necklaceUnder.map a.fiber.left := by
    exact eq_of_heq (hn j)
  exact mapCone_triangle (Grothendieck.pre (fiberDiagram (A ⋙ T)) G)
    (coneFromVariableDiagram E U ((G ⋙ A) ⋙ T) M p₀ l₀ n₀ hp₀)
    (coneFromVariableDiagram E V (A ⋙ T) L₁ p₁ l₁ n₁ hp₁)
    (comparisonWhisker E (A ⋙ T) p₁ G p₀ α₀ hs) a
    (comparisonWhisker_cone E (A ⋙ T) p₁ G a p₀ α₀ hs l₀ l₁ n₀ n₁ hp₀ hp₁ hl hN)
    H s t d hd

end JointCones

end
end DaggerModels.PartII.JTBoundaryNecklacePresentationTransport
