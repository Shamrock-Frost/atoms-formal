import Atoms.Homotopical.Simplicial.KanDatum
import Atoms.TestCategory.Nerve.Elements
import Atoms.TestCategory.Localizer.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction

open CategoryTheory Limits Opposite
open Atoms.Homotopical Simplicial MorphismProperty

universe u

namespace Atoms.TestCategory

def ordinaryNerveElements (A : Type u) [SmallCategory A] :
    (Aᵒᵖ ⥤ Type u) ⥤ SSet.{u} := elementsFunctor A ⋙ CategoryTheory.nerveFunctor

def simplicialRestriction {C : Type u} [SmallCategory C] (k : C ⥤ SSet.{u}) :
    SSet.{u} ⥤ (Cᵒᵖ ⥤ Type u) :=
  yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ SSet.{u}ᵒᵖ (Type u)).obj k.op

def simplicialRestrictionMap {C : Type u} [SmallCategory C] {k k' : C ⥤ SSet.{u}}
    (θ : k ⟶ k') : simplicialRestriction k' ⟶ simplicialRestriction k :=
  Functor.whiskerLeft yoneda
    ((Functor.whiskeringLeft Cᵒᵖ SSet.{u}ᵒᵖ (Type u)).map (NatTrans.op θ))

def ordinaryNerveElementsRightAdjoint (A : Type u) [SmallCategory A] :
    SSet.{u} ⥤ (Aᵒᵖ ⥤ Type u) :=
  simplicialRestriction (Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor)

noncomputable def ordinaryNerveElementsRightAdjointNerveIso (A : Type u) [SmallCategory A] :
    CategoryTheory.nerveFunctor ⋙ ordinaryNerveElementsRightAdjoint A ≅
      Atoms.TestCategory.nerveFunctor A :=
  NatIso.ofComponents
    (fun C => NatIso.ofComponents
      (fun a => (CategoryTheory.nerveFunctor.fullyfaithful.homEquiv
        (X := Cat.of (Over (unop a))) (Y := C)).symm.toIso)
      (by
        intro a b f
        ext g
        change CategoryTheory.nerveFunctor.obj (Cat.of (Over (unop a))) ⟶
          CategoryTheory.nerveFunctor.obj C at g
        change CategoryTheory.nerveFunctor.preimage
          (CategoryTheory.nerveFunctor.map ((Over.mapFunctor A).map f.unop) ≫ g) =
            ((Over.mapFunctor A).map f.unop) ≫ CategoryTheory.nerveFunctor.preimage g
        apply CategoryTheory.nerveFunctor.map_injective
        exact (CategoryTheory.nerveFunctor.map_preimage _).trans (by
          rw [Functor.map_comp]
          exact congrArg _ (CategoryTheory.nerveFunctor.map_preimage g).symm)))
    (by
      intro C D f
      ext a g
      change CategoryTheory.nerveFunctor.obj (Cat.of (Over (unop a))) ⟶
        CategoryTheory.nerveFunctor.obj C at g
      change CategoryTheory.nerveFunctor.preimage
        (g ≫ CategoryTheory.nerveFunctor.map f) =
          CategoryTheory.nerveFunctor.preimage g ≫ f
      apply CategoryTheory.nerveFunctor.map_injective
      exact (CategoryTheory.nerveFunctor.map_preimage _).trans (by
        rw [Functor.map_comp]
        exact congrArg (fun h => h ≫ CategoryTheory.nerveFunctor.map f)
          (CategoryTheory.nerveFunctor.map_preimage g).symm))

def ordinalEvaluationIso (A : Type u) [SmallCategory A] (n : ℕ) :
    ordinaryNerveElements A ⋙
        (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋n⦌) ≅
      Types.sigmaEvaluation A fun G : Fin (n + 1) ⥤ A => G.obj (Fin.last n) :=
  NatIso.ofComponents
    (fun X => (elementsLiftEquiv (X := X) (Fin.isTerminalLast n)).toIso)
    (fun f => by ext; rfl)

instance (A : Type u) [SmallCategory A] :
    PreservesColimitsOfSize.{u, u} (ordinaryNerveElements A) :=
  preservesColimits_of_evaluation _ fun b =>
    preservesColimits_of_natIso (ordinalEvaluationIso A b.unop.len).symm

def ordinalRepresentableIso (A : Type u) [SmallCategory A] :
    Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor ≅
      uliftYoneda.{u} ⋙ ordinaryNerveElements A :=
  Functor.isoWhiskerRight (elementsYonedaFunctorIso A).symm
      CategoryTheory.nerveFunctor ≪≫
    Functor.associator yoneda (elementsFunctor A) CategoryTheory.nerveFunctor ≪≫
      Functor.isoWhiskerRight uliftYonedaIsoYoneda.{u}.symm
        (ordinaryNerveElements A)

noncomputable def ordinaryNerveElementsAdjunction (A : Type u) [SmallCategory A] :
    ordinaryNerveElements A ⊣ ordinaryNerveElementsRightAdjoint A :=
  let e := ordinalRepresentableIso A
  let r : Presheaf.restrictedULiftYoneda.{u}
      (Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor) ≅
        ordinaryNerveElementsRightAdjoint A :=
    Functor.isoWhiskerRight uliftYonedaIsoYoneda.{u}
      ((Functor.whiskeringLeft Aᵒᵖ SSet.{u}ᵒᵖ (Type u)).obj
        (Over.mapFunctor A ⋙ CategoryTheory.nerveFunctor).op)
  have : (ordinaryNerveElements A).IsLeftKanExtension e.hom :=
    Presheaf.isLeftKanExtension_of_preservesColimits _ e
  (Presheaf.uliftYonedaAdjunction _ e.hom).ofNatIsoRight r

namespace BasicLocalizer

theorem locallyAspherical_rightAdjoint_interval
    (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A] :
    𝒲.LocallyAspherical A ((ordinaryNerveElementsRightAdjoint A).obj Δ[1]) := by
  let C : Cat.{u, u} := Cat.of (ULift (Fin 2))
  let e : (ordinaryNerveElementsRightAdjoint A).obj Δ[1] ≅ (nerveFunctor A).obj C :=
    (ordinaryNerveElementsRightAdjoint A).mapIso (SSet.stdSimplex.isoNerve 1) ≪≫
      (ordinaryNerveElementsRightAdjointNerveIso A).app C
  have hc : HasTerminal (ULift (Fin 2)) := by
    let t : IsTerminal (ULift.up (Fin.last 1) : ULift (Fin 2)) :=
      IsTerminal.ofUniqueHom
        (fun (Y : ULift (Fin 2)) => homOfLE (show Y.down ≤ Fin.last 1 from Fin.le_last _))
        (fun _ _ => rfl)
    exact t.hasTerminal
  have : HasTerminal C := hc
  intro a
  exact (𝒲.pshAspherical_iff_of_iso _ (prod.mapIso (Iso.refl _) e).symm).1
    (𝒲.locallyAspherical_nerveFunctor_obj_of_isLocalTest A C a)

end BasicLocalizer

noncomputable def rightAdjointInitialIsInitial (A : Type u) [SmallCategory A] :
    IsInitial ((ordinaryNerveElementsRightAdjoint A).obj (⊥_ SSet.{u})) := by
  let R := ordinaryNerveElementsRightAdjoint A
  have hempty : ∀ (a : Aᵒᵖ), IsEmpty ((R.obj (⊥_ SSet.{u})).obj a) := by
    intro a
    refine ⟨fun h => ?_⟩
    let c : (CategoryTheory.nerve (Over a.unop)).obj (op ⦋0⦌) :=
      ComposableArrows.mk₀ (Over.mk (𝟙 a.unop))
    exact (FunctorToTypes.isEmpty_initial_obj (op ⦋0⦌)).false (h.app _ c)
  refine IsInitial.ofUniqueHom (fun Y => ?_) (fun Y f => ?_)
  · exact { app := fun a => TypeCat.ofHom (fun x => (hempty a).elim x)
            naturality := by intro a b g; ext x; exact (hempty a).elim x }
  · ext a x
    exact (hempty a).elim x

instance rightAdjoint_preservesLimits (A : Type u) [SmallCategory A] :
    PreservesLimits (ordinaryNerveElementsRightAdjoint A) :=
  (ordinaryNerveElementsAdjunction A).rightAdjoint_preservesLimits

noncomputable def rightAdjointSeparatingInterval (A : Type u) [SmallCategory A] :
    SeparatingInterval A :=
  .ofFunctor simplicialPoint isPullback_simplicialPoint (ordinaryNerveElementsRightAdjoint A)
    (rightAdjointInitialIsInitial A)

namespace BasicLocalizer

theorem rightAdjointSeparatingInterval_weakEquivalences_le
    (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A] :
    (rightAdjointSeparatingInterval A).cylinder.weakEquivalences
        (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type u)) ≤ 𝒲.wPsh A := by
  let : (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type u)).IsSmall.{u} :=
    MorphismProperty.isSmall_bot
  refine (rightAdjointSeparatingInterval A).cylinder.weakEquivalences_le_of_endpoint_mem
    (⊥ : MorphismProperty (Aᵒᵖ ⥤ Type u)) bot_le bot_le fun ε X ↦ ?_
  apply (IsALocalizer.endpoint_mem_iff_contraction_mem (rightAdjointSeparatingInterval A).cylinder
    ε X).2
  exact 𝒲.wPsh_snd_of_locallyAspherical A
    (𝒲.locallyAspherical_rightAdjoint_interval A) X

end BasicLocalizer

end Atoms.TestCategory
