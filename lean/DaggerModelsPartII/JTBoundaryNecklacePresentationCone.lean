import DaggerModelsPartII.JTTargetCommaPullback

/-!
# A cone from a whole boundary necklace fiber to a presentation
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory Opposite Simplicial DaggerModels
open DaggerChosenRigidificationNecklace

namespace DaggerModels.PartII.JTBoundaryNecklacePresentationCone

open BoundaryNecklaceComma (necklaceUnder fiberDiagram sourceCode)

noncomputable section

private abbrev B := JTXiEndpointCollapse.boundary

private def nativeArrow {T V : NecklaceCode}
    (f : necklaceUnder.obj T ⟶ necklaceUnder.obj V) : T ⟶ V :=
  let h : (f.right.app (op ⦋0⦌) T.first, f.right.app (op ⦋0⦌) T.last) =
      (V.first, V.last) := by
    have hw := Under.w f
    change JTNecklaceEndpointCylinder.endpointInclusion T ≫ f.right =
      JTNecklaceEndpointCylinder.endpointInclusion V at hw
    rw [JTNecklaceEndpointCylinder.endpointInclusion,
      JTGeneralOrderedFiberWeak.orderedBoundary_natural] at hw
    exact (JTEndpointObjects.boundaryHomEquiv _).symm.injective hw
  ⟨f.right, congrArg Prod.fst h, congrArg Prod.snd h⟩

private theorem nativeArrow_right {T V : NecklaceCode}
    (f : necklaceUnder.obj T ⟶ necklaceUnder.obj V) : (nativeArrow f).map = f.right := rfl

private theorem nativeArrow_natural {T V W : NecklaceCode}
    (u : T ⟶ V) (f : necklaceUnder.obj V ⟶ necklaceUnder.obj W) :
    u ≫ nativeArrow f = nativeArrow (necklaceUnder.map u ≫ f) := by
  apply NecklaceCode.Hom.ext
  rfl

private theorem eqToHom_left {V : Under B}
    {P P' : CostructuredArrow necklaceUnder V} (h : P = P') :
    (eqToHom h).left = eqToHom (congrArg (fun X ↦ X.left) h) := by
  cases h
  rfl

private theorem sourceCode_ι {I : Type} [SmallCategory I] (E : I ⥤ Under B)
    (i : I) {P P' : CostructuredArrow necklaceUnder (E.obj i)} (f : P ⟶ P') :
    (sourceCode E).map ((Grothendieck.ι (fiberDiagram E) i).map f) = f.left := by
  change ((Grothendieck.ι (fiberDiagram E) i).map f).fiber.left = f.left
  rw [Grothendieck.ι_map]
  dsimp only
  rw [CostructuredArrow.comp_left, eqToHom_left]
  exact Category.id_comp _

variable {I : Type} [SmallCategory I] (E : I ⥤ Under B)
variable {i : I} {A : Under B} (p : A ⟶ E.obj i)
variable (U : BoundaryNecklaceComma.Presentation E)

private def component (a : i ⟶ U.base)
    (b : A ⟶ necklaceUnder.obj U.fiber.left)
    (h : p ≫ E.map a = b ≫ U.fiber.hom)
    (P : CostructuredArrow necklaceUnder A) :
    (CostructuredArrow.map p ⋙ Grothendieck.ι (fiberDiagram E) i).obj P ⟶ U :=
  ⟨a, CostructuredArrow.homMk (nativeArrow (P.hom ≫ b)) (by
    apply Under.UnderMorphism.ext
    change (necklaceUnder.map (nativeArrow (P.hom ≫ b)) ≫ U.fiber.hom).right =
      (P.hom ≫ p ≫ E.map a).right
    have hn : necklaceUnder.map (nativeArrow (P.hom ≫ b)) = P.hom ≫ b :=
      Under.UnderMorphism.ext rfl
    rw [hn]
    have hh : (P.hom ≫ b) ≫ U.fiber.hom = P.hom ≫ p ≫ E.map a := by
      calc
        _ = P.hom ≫ (b ≫ U.fiber.hom) := Category.assoc _ _ _
        _ = P.hom ≫ (p ≫ E.map a) := congrArg (fun m ↦ P.hom ≫ m) h.symm
        _ = _ := rfl
    exact congrArg
      (fun m : necklaceUnder.obj P.left ⟶ E.obj U.base ↦ m.right) hh)⟩

/-- The whole fiber comparison, with the prescribed base and native map. -/
def cone (a : i ⟶ U.base) (b : A ⟶ necklaceUnder.obj U.fiber.left)
    (h : p ≫ E.map a = b ≫ U.fiber.hom) :
    CostructuredArrow.map p ⋙ Grothendieck.ι (fiberDiagram E) i ⟶
      (Functor.const _).obj U where
  app := component E p U a b h
  naturality := by
    intro P P' f
    apply JTTargetCommaPullback.operator_ext
    · change (𝟙 i) ≫ a = a ≫ 𝟙 U.base
      simp
    · change (sourceCode E).map
          (((CostructuredArrow.map p ⋙ Grothendieck.ι (fiberDiagram E) i).map f) ≫
            component E p U a b h P') =
        (sourceCode E).map
          (component E p U a b h P ≫ ((Functor.const _).obj U).map f)
      rw [Functor.map_comp, Functor.map_comp]
      have hs : (sourceCode E).map
          ((CostructuredArrow.map p ⋙ Grothendieck.ι (fiberDiagram E) i).map f) =
          f.left := by
        change (sourceCode E).map
          ((Grothendieck.ι (fiberDiagram E) i).map
            ((CostructuredArrow.map p).map f)) = f.left
        rw [sourceCode_ι]
        rfl
      rw [hs]
      have hcP : (sourceCode E).map (component E p U a b h P) =
          nativeArrow (P.hom ≫ b) := rfl
      have hcP' : (sourceCode E).map (component E p U a b h P') =
          nativeArrow (P'.hom ≫ b) := rfl
      have hid : (sourceCode E).map (((Functor.const _).obj U).map f) =
          𝟙 U.fiber.left := by
        change (sourceCode E).map (𝟙 U) = 𝟙 U.fiber.left
        exact (sourceCode E).map_id U
      rw [hcP, hcP', hid]
      calc
        f.left ≫ nativeArrow (P'.hom ≫ b) =
            nativeArrow (necklaceUnder.map f.left ≫ (P'.hom ≫ b)) :=
          nativeArrow_natural f.left (P'.hom ≫ b)
        _ = nativeArrow (P.hom ≫ b) := by
          apply NecklaceCode.Hom.ext
          simpa only [Category.assoc] using
            congrArg (fun k ↦ (k ≫ b).right) (CostructuredArrow.w f)
        _ = nativeArrow (P.hom ≫ b) ≫ 𝟙 U.fiber.left :=
          (Category.comp_id _).symm

theorem cone_base (a : i ⟶ U.base) (b : A ⟶ necklaceUnder.obj U.fiber.left)
    (h : p ≫ E.map a = b ≫ U.fiber.hom)
    (P : CostructuredArrow necklaceUnder A) :
    ((cone E p U a b h).app P).base = a := rfl

theorem cone_native_map (a : i ⟶ U.base) (b : A ⟶ necklaceUnder.obj U.fiber.left)
    (h : p ≫ E.map a = b ≫ U.fiber.hom)
    (P : CostructuredArrow necklaceUnder A) :
    ((cone E p U a b h).app P).fiber.left.map = (P.hom ≫ b).right := rfl

/-- A compatible pair of cocones yields a comparison from every fiber,
natural in both the boundary parameter and the internal necklace. -/
def coneFromDiagram {J : Type} [SmallCategory J] (F : J ⥤ Under B)
    (ρ : F ⟶ (Functor.const J).obj (E.obj i))
    (α : (Functor.const J).obj i ⟶ (Functor.const J).obj U.base)
    (β : F ⟶ (Functor.const J).obj (necklaceUnder.obj U.fiber.left))
    (h : ∀ j, ρ.app j ≫ E.map (α.app j) = β.app j ≫ U.fiber.hom) :
    BoundaryNecklaceComma.toTarget F ρ ⋙ Grothendieck.ι (fiberDiagram E) i ⟶
      (Functor.const _).obj U where
  app P := component E (ρ.app P.base) U (α.app P.base) (β.app P.base) (h P.base) P.fiber
  naturality {P P'} f := by
    apply JTTargetCommaPullback.operator_ext
    · exact α.naturality f.base
    · change (sourceCode E).map (_ ≫ _) = (sourceCode E).map (_ ≫ _)
      rw [Functor.map_comp, Functor.map_comp]
      change (sourceCode E).map ((Grothendieck.ι (fiberDiagram E) i).map
          ((BoundaryNecklaceComma.toTarget F ρ).map f)) ≫
            nativeArrow (P'.fiber.hom ≫ β.app P'.base) =
        nativeArrow (P.fiber.hom ≫ β.app P.base) ≫ (sourceCode E).map (𝟙 U)
      rw [sourceCode_ι, BoundaryNecklaceComma.toTarget_map_left, (sourceCode E).map_id]
      change f.fiber.left ≫ nativeArrow (P'.fiber.hom ≫ β.app P'.base) =
        nativeArrow (P.fiber.hom ≫ β.app P.base) ≫ 𝟙 U.fiber.left
      rw [Category.comp_id, nativeArrow_natural]
      apply NecklaceCode.Hom.ext
      exact congrArg (fun g ↦ g.right)
        (CostructuredArrow.w ((BoundaryNecklaceComma.toTarget F β).map f))

theorem coneFromDiagram_base {J : Type} [SmallCategory J] (F : J ⥤ Under B)
    (ρ : F ⟶ (Functor.const J).obj (E.obj i))
    (α : (Functor.const J).obj i ⟶ (Functor.const J).obj U.base)
    (β : F ⟶ (Functor.const J).obj (necklaceUnder.obj U.fiber.left))
    (h : ∀ j, ρ.app j ≫ E.map (α.app j) = β.app j ≫ U.fiber.hom)
    (P : BoundaryNecklaceComma.Presentation F) :
    ((coneFromDiagram E U F ρ α β h).app P).base = α.app P.base := rfl

theorem coneFromDiagram_native_map {J : Type} [SmallCategory J] (F : J ⥤ Under B)
    (ρ : F ⟶ (Functor.const J).obj (E.obj i))
    (α : (Functor.const J).obj i ⟶ (Functor.const J).obj U.base)
    (β : F ⟶ (Functor.const J).obj (necklaceUnder.obj U.fiber.left))
    (h : ∀ j, ρ.app j ≫ E.map (α.app j) = β.app j ≫ U.fiber.hom)
    (P : BoundaryNecklaceComma.Presentation F) :
    ((coneFromDiagram E U F ρ α β h).app P).fiber.left.map =
      (P.fiber.hom ≫ β.app P.base).right := rfl

section VariableBase

variable {J : Type} [SmallCategory J] (F : J ⥤ Under B) (L : J ⥤ I)
variable (ρ : F ⟶ L ⋙ E)

/-- Map the whole boundary diagram using the prescribed varying decorated base. -/
abbrev mapPresentation : BoundaryNecklaceComma.Presentation F ⥤
    BoundaryNecklaceComma.Presentation E :=
  Grothendieck.map (Functor.whiskerRight ρ BoundaryNecklaceComma.diagram) ⋙
    Grothendieck.pre (fiberDiagram E) L

/-- Mapping a presentation retains each morphism's original internal necklace operator. -/
theorem mapPresentation_code {P P' : BoundaryNecklaceComma.Presentation F}
    (f : P ⟶ P') : (sourceCode E).map ((mapPresentation E F L ρ).map f) =
      f.fiber.left := by
  change ((Grothendieck.map (Functor.whiskerRight ρ BoundaryNecklaceComma.diagram)).map f).fiber.left =
    f.fiber.left
  rw [Grothendieck.map_map]
  simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  let M := Functor.whiskerRight ρ BoundaryNecklaceComma.diagram
  have h := congrArg
    (fun G : (fiberDiagram F).obj P.base ⟶ ((L ⋙ fiberDiagram E).obj P'.base) ↦
      G.toFunctor.obj P.fiber) (M.naturality f.base).symm
  change (eqToHom h ≫ (CostructuredArrow.map (ρ.app P'.base)).map f.fiber).left = f.fiber.left
  rw [CostructuredArrow.comp_left, eqToHom_left]
  change 𝟙 P.fiber.left ≫ f.fiber.left = f.fiber.left
  exact Category.id_comp _

/-- A cocone on the decorated base and a compatible native cocone give a
cone on the full presentation, even when the decorated labels vary. -/
def coneFromVariableDiagram (α : L ⟶ (Functor.const J).obj U.base)
    (β : F ⟶ (Functor.const J).obj (necklaceUnder.obj U.fiber.left))
    (h : ∀ j, ρ.app j ≫ E.map (α.app j) = β.app j ≫ U.fiber.hom) :
    mapPresentation E F L ρ ⟶ (Functor.const _).obj U where
  app P := component E (ρ.app P.base) U (α.app P.base) (β.app P.base) (h P.base) P.fiber
  naturality {P P'} f := by
    apply JTTargetCommaPullback.operator_ext
    · exact α.naturality f.base
    · change (sourceCode E).map (_ ≫ _) = (sourceCode E).map (_ ≫ _)
      rw [Functor.map_comp, Functor.map_comp]
      change (sourceCode E).map ((mapPresentation E F L ρ).map f) ≫
          nativeArrow (P'.fiber.hom ≫ β.app P'.base) =
        nativeArrow (P.fiber.hom ≫ β.app P.base) ≫ (sourceCode E).map (𝟙 U)
      rw [mapPresentation_code, (sourceCode E).map_id]
      change f.fiber.left ≫ nativeArrow (P'.fiber.hom ≫ β.app P'.base) =
        nativeArrow (P.fiber.hom ≫ β.app P.base) ≫ 𝟙 U.fiber.left
      rw [Category.comp_id, nativeArrow_natural]
      apply NecklaceCode.Hom.ext
      exact congrArg (fun g ↦ g.right)
        (CostructuredArrow.w ((BoundaryNecklaceComma.toTarget F β).map f))

/-- Reindex a varying decorated and native cone while retaining every
internal necklace operator. The source is the original presentation map
restricted along the complete Grothendieck presentation of `G ⋙ F`. -/
def coneFromReindexedVariableDiagram {K : Type} [SmallCategory K] (G : K ⥤ J)
    (α : G ⋙ L ⟶ (Functor.const K).obj U.base)
    (β : G ⋙ F ⟶ (Functor.const K).obj (necklaceUnder.obj U.fiber.left))
    (h : ∀ k, (Functor.whiskerLeft G ρ).app k ≫ E.map (α.app k) =
      β.app k ≫ U.fiber.hom) :
    Grothendieck.pre (fiberDiagram F) G ⋙ mapPresentation E F L ρ ⟶
      (Functor.const (BoundaryNecklaceComma.Presentation (G ⋙ F))).obj U := by
  let c := coneFromVariableDiagram E U (G ⋙ F) (G ⋙ L)
    (Functor.whiskerLeft G ρ) α β h
  exact {
    app := fun P ↦ c.app P
    naturality := by
      intro P Q f
      exact c.naturality f }

end VariableBase

end

end DaggerModels.PartII.JTBoundaryNecklacePresentationCone
