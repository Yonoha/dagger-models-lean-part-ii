import DaggerModelsPartII.ReedyBoundary
import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# One degree of the Reedy factorization

A factorization of the lower diagram gives a map from the relative latching
source to the relative matching target. Factoring this map in the coefficient
category gives the new object and the compatible maps in the next degree.
-/

set_option autoImplicit false

open CategoryTheory Limits Opposite Simplicial MorphismProperty

universe v u

namespace DaggerModels.PartII

noncomputable section

variable {C : Type u} [Category.{v} C] [HasLimitsOfSize.{0, 0} C]
  [HasColimitsOfSize.{0, 0} C]

/-- Latching of a diagram defined strictly below degree `n`. -/
def lowerLatching (n : ℕ) : (BelowDegree n ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ _).obj (latchingBelow n) ⋙ colim

/-- Matching of a diagram defined strictly below degree `n`. -/
def lowerMatching (n : ℕ) : (BelowDegree n ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft _ _ _).obj (matchingBelow n) ⋙ lim

variable {n : ℕ}

theorem lowerBoundaryMap_naturality {Z T : BelowDegree n ⥤ C} (a : Z ⟶ T) :
    (lowerLatching n).map a ≫ lowerBoundaryMap T =
      lowerBoundaryMap Z ≫ (lowerMatching n).map a := by
  apply colimit.hom_ext
  intro s
  apply limit.hom_ext
  intro t
  change (colimit.ι _ s ≫ colimMap (Functor.whiskerLeft _ a) ≫
      colimit.desc _ (lowerBoundaryCocone T)) ≫ limit.π _ t =
    (colimit.ι _ s ≫ colimit.desc _ (lowerBoundaryCocone Z) ≫
      limMap (Functor.whiskerLeft _ a)) ≫ limit.π _ t
  simp only [Category.assoc, ι_colimMap_assoc, colimit.ι_desc_assoc, limMap_π,
    lowerBoundaryCocone, limit.lift_π, limit.lift_π_assoc]
  exact (a.naturality (boundaryArrow s t)).symm

/-- An object in degree `n` with latching and matching structure compatible with the lower diagram. -/
structure DegreeExtension (Z : BelowDegree n ⥤ C) where
  obj : C
  fromLatching : (lowerLatching n).obj Z ⟶ obj
  toMatching : obj ⟶ (lowerMatching n).obj Z
  boundary : fromLatching ≫ toMatching = lowerBoundaryMap Z

/-- A full simplicial diagram supplies the degree-extension data at every degree. -/
def DegreeExtension.ofDiagram (n : ℕ) (Z : SimplexCategoryᵒᵖ ⥤ C) :
    DegreeExtension (lowerDiagram n Z) where
  obj := Z.obj (op ⦋n⦌)
  fromLatching := (latchingComparison n).app Z
  toMatching := (matchingComparison n).app Z
  boundary := (lowerBoundaryMap_factor n Z).symm

/-- Compatibility of a degree-`n` map with a given map of lower diagrams. -/
structure DegreeExtension.Hom {Z T : BelowDegree n ⥤ C} (a : Z ⟶ T)
    (X : DegreeExtension Z) (Y : DegreeExtension T) where
  app : X.obj ⟶ Y.obj
  latching_naturality : (lowerLatching n).map a ≫ Y.fromLatching = X.fromLatching ≫ app
  matching_naturality : app ≫ Y.toMatching = X.toMatching ≫ (lowerMatching n).map a

/-- A map of full simplicial diagrams supplies compatible degree maps. -/
def DegreeExtension.Hom.ofDiagram {X Y : SimplexCategoryᵒᵖ ⥤ C} (f : X ⟶ Y) (n : ℕ) :
    DegreeExtension.Hom (Functor.whiskerLeft (belowDegree n).ι f)
      (DegreeExtension.ofDiagram n X) (DegreeExtension.ofDiagram n Y) where
  app := f.app (op ⦋n⦌)
  latching_naturality := (latchingComparison n).naturality f
  matching_naturality := (matchingComparison n).naturality f

/-- The degree-extension analogue of the relative latching map. -/
def DegreeExtension.Hom.relativeLatching {Z T : BelowDegree n ⥤ C} {a : Z ⟶ T}
    {X : DegreeExtension Z} {Y : DegreeExtension T} (f : DegreeExtension.Hom a X Y) :
    pushout X.fromLatching ((lowerLatching n).map a) ⟶ Y.obj :=
  pushout.desc f.app Y.fromLatching f.latching_naturality.symm

/-- The degree-extension analogue of the relative matching map. -/
def DegreeExtension.Hom.relativeMatching {Z T : BelowDegree n ⥤ C} {a : Z ⟶ T}
    {X : DegreeExtension Z} {Y : DegreeExtension T} (f : DegreeExtension.Hom a X Y) :
    X.obj ⟶ pullback ((lowerMatching n).map a) Y.toMatching :=
  pullback.lift X.toMatching f.app f.matching_naturality.symm

section Factorization

variable {Xₗ Zₗ Yₗ : BelowDegree n ⥤ C}
  {X : DegreeExtension Xₗ} {Y : DegreeExtension Yₗ}
  {f : Xₗ ⟶ Yₗ} (F : DegreeExtension.Hom f X Y)
  (a : Xₗ ⟶ Zₗ) (b : Zₗ ⟶ Yₗ) (h : a ≫ b = f)

/-- The relative latching source maps to the matching object of the intermediate lower diagram. -/
def degreeFactorizationToMatching :
    pushout X.fromLatching ((lowerLatching n).map a) ⟶ (lowerMatching n).obj Zₗ :=
  pushout.desc (X.toMatching ≫ (lowerMatching n).map a) (lowerBoundaryMap Zₗ) (by
    rw [← Category.assoc, X.boundary, lowerBoundaryMap_naturality])

/-- The relative latching source maps to the original degree-`n` target object. -/
def degreeFactorizationToTarget :
    pushout X.fromLatching ((lowerLatching n).map a) ⟶ Y.obj :=
  pushout.desc F.app ((lowerLatching n).map b ≫ Y.fromLatching) (by
    rw [← Category.assoc, ← (lowerLatching n).map_comp, h, F.latching_naturality])

/-- The map in the coefficient category to factor at the new degree. -/
def degreeFactorizationMap :
    pushout X.fromLatching ((lowerLatching n).map a) ⟶
      pullback ((lowerMatching n).map b) Y.toMatching :=
  pullback.lift (degreeFactorizationToMatching a) (degreeFactorizationToTarget F a b h) (by
    apply pushout.hom_ext
    · simp only [Category.assoc, degreeFactorizationToMatching, degreeFactorizationToTarget,
        pushout.inl_desc_assoc]
      rw [← (lowerMatching n).map_comp, h, F.matching_naturality]
    · simp only [Category.assoc, degreeFactorizationToMatching, degreeFactorizationToTarget,
        pushout.inr_desc_assoc]
      rw [← lowerBoundaryMap_naturality, Y.boundary])

variable {A : C}
  (i : pushout X.fromLatching ((lowerLatching n).map a) ⟶ A)
  (p : A ⟶ pullback ((lowerMatching n).map b) Y.toMatching)
  (fac : i ≫ p = degreeFactorizationMap F a b h)

/-- The new degree object carries its required boundary factorization. -/
def factoredDegreeExtension : DegreeExtension Zₗ where
  obj := A
  fromLatching := pushout.inr _ _ ≫ i
  toMatching := p ≫ pullback.fst _ _
  boundary := by
    simp only [Category.assoc, ← Category.assoc i, fac, degreeFactorizationMap,
      pullback.lift_fst, degreeFactorizationToMatching, pushout.inr_desc]

/-- The degree component of the left factor extends the lower-diagram map `a`. -/
def factoredDegreeLeft :
    DegreeExtension.Hom a X (factoredDegreeExtension F a b h i p fac) where
  app := pushout.inl _ _ ≫ i
  latching_naturality := by
    change (lowerLatching n).map a ≫ pushout.inr _ _ ≫ i =
      X.fromLatching ≫ pushout.inl _ _ ≫ i
    rw [← Category.assoc, ← Category.assoc, pushout.condition]
  matching_naturality := by
    change (pushout.inl _ _ ≫ i) ≫ p ≫ pullback.fst _ _ =
      X.toMatching ≫ (lowerMatching n).map a
    simp only [Category.assoc, ← Category.assoc i, fac, degreeFactorizationMap,
      pullback.lift_fst, degreeFactorizationToMatching, pushout.inl_desc]

/-- The degree component of the right factor extends the lower-diagram map `b`. -/
def factoredDegreeRight :
    DegreeExtension.Hom b (factoredDegreeExtension F a b h i p fac) Y where
  app := p ≫ pullback.snd _ _
  latching_naturality := by
    change (lowerLatching n).map b ≫ Y.fromLatching =
      (pushout.inr _ _ ≫ i) ≫ p ≫ pullback.snd _ _
    simp only [Category.assoc, ← Category.assoc i, fac, degreeFactorizationMap,
      pullback.lift_snd, degreeFactorizationToTarget, pushout.inr_desc]
  matching_naturality := by
    change (p ≫ pullback.snd _ _) ≫ Y.toMatching =
      (p ≫ pullback.fst _ _) ≫ (lowerMatching n).map b
    rw [Category.assoc, Category.assoc, pullback.condition]

theorem factoredDegree_fac :
    (factoredDegreeLeft F a b h i p fac).app ≫ (factoredDegreeRight F a b h i p fac).app =
      F.app := by
  change (pushout.inl _ _ ≫ i) ≫ p ≫ pullback.snd _ _ = F.app
  simp only [Category.assoc, ← Category.assoc i, fac, degreeFactorizationMap,
    pullback.lift_snd, degreeFactorizationToTarget, pushout.inl_desc]

/-- The actual relative latching map of the extended left factor is the chosen left map. -/
theorem factoredDegree_relativeLatching :
    (factoredDegreeLeft F a b h i p fac).relativeLatching = i := by
  apply pushout.hom_ext
  · exact pushout.inl_desc _ _ _
  · exact pushout.inr_desc _ _ _

/-- The actual relative matching map of the extended right factor is the chosen right map. -/
theorem factoredDegree_relativeMatching :
    (factoredDegreeRight F a b h i p fac).relativeMatching = p := by
  apply pullback.hom_ext
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

include h in
/-- The coefficient factorization axiom supplies the compatible factorization at degree `n`. -/
theorem exists_factoredDegree (L R : MorphismProperty C) [HasFactorization L R] :
    ∃ Z : DegreeExtension Zₗ, ∃ left : DegreeExtension.Hom a X Z,
      ∃ right : DegreeExtension.Hom b Z Y, left.app ≫ right.app = F.app ∧
        L left.relativeLatching ∧ R right.relativeMatching := by
  let d := factorizationData L R (degreeFactorizationMap F a b h)
  refine ⟨factoredDegreeExtension F a b h d.i d.p d.fac,
    factoredDegreeLeft F a b h d.i d.p d.fac, factoredDegreeRight F a b h d.i d.p d.fac,
    factoredDegree_fac F a b h d.i d.p d.fac, ?_, ?_⟩
  · rw [factoredDegree_relativeLatching]
    exact d.hi
  · rw [factoredDegree_relativeMatching]
    exact d.hp

end Factorization

end

end DaggerModels.PartII
