import DaggerModelsPartII.OrdinaryDwyerKanCore
import DaggerModelsPartII.OrdinaryHomotopyEndpointTransport
import OriginalOrdinaryHomRetractsReconciled
import Mathlib.AlgebraicTopology.ModelCategory.Instances

/-!
# Two-of-three and retract closure of the retained ordinary DK condition

Essential surjectivity moves both actual source endpoints to image objects.
The checked ordinary component-isomorphism transport then transfers the native
weak Hom condition. Retract closure uses the existing actual Hom retracts and
the native component functors, retaining both endpoint equations.
No ordinary model structure is installed by these closure statements.
-/

set_option autoImplicit false

open CategoryTheory HomotopicalAlgebra Opposite Simplicial DaggerModels
open scoped SSet.modelCategoryQuillen

universe u

namespace DaggerModels.OrdinaryDwyerKanClosure

open OrdinaryDwyerKanCore OrdinaryHomotopyEndpointTransport
open DaggerOriginalSimplicialPiZeroCategory

noncomputable section

/-- A DK functor can be cancelled from the first position of a composite.
Both arbitrary target endpoints are moved using the actual component isomorphisms. -/
theorem of_precomp {C D E : SimplicialCat.{u, u}} (F : C ⟶ D) (G : D ⟶ E)
    (hF : W F) (hFG : W (F ≫ G)) : W G := by
  constructor
  · apply (localGeometric_iff_native G).2
    intro x y
    have : (componentFunctor F).EssSurj := hF.2
    let a := (componentFunctor F).objPreimage x
    let b := (componentFunctor F).objPreimage y
    let e : (componentFunctor F).obj a ≅ x :=
      (componentFunctor F).objObjPreimageIso x
    let f : (componentFunctor F).obj b ≅ y :=
      (componentFunctor F).objObjPreimageIso y
    obtain ⟨α, hα⟩ := SSet.π₀.mk_surjective e.hom
    obtain ⟨β, hβ⟩ := SSet.π₀.mk_surjective f.hom
    have hαiso : @IsIso (componentObjects D) (componentCategory D)
        (F.obj a) x (SSet.π₀.mk α) := by
      rw [hα]
      infer_instance
    have hβiso : @IsIso (componentObjects D) (componentCategory D)
        (F.obj b) y (SSet.π₀.mk β) := by
      rw [hβ]
      infer_instance
    have hImage : WeakEquivalence (G.map (F.obj a) (F.obj b)) := by
      have : WeakEquivalence (F.map a b) :=
        (localGeometric_iff_native F).1 hF.1 a b
      have : WeakEquivalence (F.map a b ≫ G.map (F.obj a) (F.obj b)) :=
        (localGeometric_iff_native (F ≫ G)).1 hFG.1 a b
      exact weakEquivalence_of_precomp (F.map a b) (G.map (F.obj a) (F.obj b))
    exact (local_map_weak_iff_of_endpoint_isos G α hαiso β hβiso).1 hImage
  · constructor
    intro z
    obtain ⟨a, ⟨e⟩⟩ := hFG.2.mem_essImage z
    exact ⟨F.obj a, ⟨e⟩⟩

instance W_ofPrecomp : W.{u}.HasOfPrecompProperty W.{u} where
  of_precomp F G hF hFG := of_precomp F G hF hFG

instance W_ofPostcomp : W.{u}.HasOfPostcompProperty W.{u} where
  of_postcomp F G hG hFG := OrdinaryDwyerKanCore.of_postcomp F G hG hFG

instance W_twoOutOfThree : W.{u}.HasTwoOutOfThreeProperty := ⟨⟩

/-- An arrow retract of an ordinary DK functor satisfies the same original
local Hom condition and actual component essential-surjectivity condition. -/
theorem of_retract {C D C' D' : SimplicialCat.{u, u}}
    {F : C ⟶ D} {G : C' ⟶ D'} (h : RetractArrow F G) (hG : W G) : W F := by
  constructor
  · let P := OriginalOrdinaryHomRetracts.localHomProperty (weakEquivalences SSet.{u})
    have hGP : P G := by
      intro x y
      exact (weakEquivalence_iff _).1 ((localGeometric_iff_native G).1 hG.1 x y)
    have hFP : P F := MorphismProperty.of_retract (P := P) h hGP
    apply (localGeometric_iff_native F).2
    intro x y
    exact (weakEquivalence_iff _).2 (hFP x y)
  · constructor
    intro y
    obtain ⟨a, ⟨e⟩⟩ := hG.2.mem_essImage (h.i.right.obj y)
    have hobj : F.obj (h.r.left.obj a) = h.r.right.obj (G.obj a) :=
      congrArg (fun T : C' ⟶ D ↦ T.obj a) h.r_w
    have hsplit : h.r.right.obj (h.i.right.obj y) = y :=
      congrArg (fun T : D ⟶ D ↦ T.obj y) h.retract_right
    exact ⟨h.r.left.obj a,
      ⟨eqToIso hobj ≪≫ (componentFunctor h.r.right).mapIso e ≪≫ eqToIso hsplit⟩⟩

instance W_retractStable : W.{u}.IsStableUnderRetracts where
  of_retract h hG := of_retract h hG

end

end DaggerModels.OrdinaryDwyerKanClosure
