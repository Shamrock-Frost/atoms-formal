import Atoms.ForMathlib.CategoryTheory.Limits.Types.Coproducts
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Composition
import Atoms.TestCategory.IsTest

open CategoryTheory Limits MorphismProperty Opposite

namespace Atoms.TestCategory

universe w w' u

variable (𝒲 : BasicLocalizer.{u}) (A B : Type u) [SmallCategory A] [SmallCategory B]

section Evaluation

variable {A B}

noncomputable def nerveElementsEquiv (b : B) (X : Aᵒᵖ ⥤ Type u) :
    ((elementsFunctor A ⋙ nerveFunctor B).obj X).obj (op b) ≃
      (Types.sigmaEvaluation A fun G : Over b ⥤ A => G.obj (Over.mk (𝟙 b))).obj X :=
  (Cat.Hom.equivFunctor (Cat.of (Over b)) (Cat.of (X.Elements)ᵒᵖ)).trans
    (elementsLiftEquiv Over.mkIdTerminal)

noncomputable def nerveElementsEvaluationIso (b : B) :
    (elementsFunctor A ⋙ nerveFunctor B) ⋙ (evaluation Bᵒᵖ (Type u)).obj (op b) ≅
      Types.sigmaEvaluation A fun G : Over b ⥤ A => G.obj (Over.mk (𝟙 b)) :=
  NatIso.ofComponents
    (fun X => (nerveElementsEquiv b X).toIso)
    (fun _ => by ext; rfl)

end Evaluation

instance preservesColimitsOfSize_elementsFunctor_comp_nerveFunctor :
    PreservesColimitsOfSize.{u, u} (elementsFunctor A ⋙ nerveFunctor B) :=
  preservesColimits_of_evaluation _ fun b =>
    preservesColimits_of_natIso (nerveElementsEvaluationIso (unop b)).symm

theorem injective_elementsFunctor_map_obj (A : Type u) [SmallCategory A]
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) [Mono f] :
    Function.Injective ((elementsFunctor A).map f).toFunctor.obj := by
  rintro ⟨a, x⟩ ⟨b, y⟩ h
  obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.1 (congrArg unop h)
  have hinj :=
    (mono_iff_injective (f.app a)).1 ((NatTrans.mono_iff_mono_app f).1 inferInstance a)
  rw [hinj (eq_of_heq h)]

instance faithful_elementsFunctor_map (A : Type u) [SmallCategory A]
    {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) : ((elementsFunctor A).map f).toFunctor.Faithful where
  map_injective {_ _} g h e :=
    Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (congrArg (fun k ↦ k.unop.1)
      (show ((CategoryOfElements.map f).map g.unop).op =
        ((CategoryOfElements.map f).map h.unop).op from e)))

theorem mono_nerveFunctor_map_of_faithful (A : Type u) [SmallCategory A] {C D : Cat.{u, u}}
    (G : C ⟶ D) [G.toFunctor.Faithful] (hG : Function.Injective G.toFunctor.obj) :
    Mono ((nerveFunctor A).map G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [mono_iff_injective]
  intro x y h
  have h : x.toFunctor ⋙ G.toFunctor = y.toFunctor ⋙ G.toFunctor := congrArg Cat.Hom.toFunctor h
  refine Cat.Hom.ext (CategoryTheory.Functor.ext (fun i => hG (Functor.congr_obj h i))
    fun i j g => ?_)
  apply G.toFunctor.map_injective
  rw [G.toFunctor.map_comp, G.toFunctor.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom h g

theorem mono_map_elementsFunctor_comp_nerveFunctor {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : Mono f) : Mono ((elementsFunctor A ⋙ nerveFunctor B).map f) :=
  have := hf
  mono_nerveFunctor_map_of_faithful B ((elementsFunctor A).map f)
    (injective_elementsFunctor_map_obj A f)

namespace BasicLocalizer

theorem wPsh_eq_inverseImage_elementsFunctor_comp_nerveFunctor [hB : 𝒲.IsWeakTest B] :
    𝒲.wPsh A = (𝒲.wPsh B).inverseImage (elementsFunctor A ⋙ nerveFunctor B) := by
  ext X Y f
  exact MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction B) 𝒲.W hB.counit_mem
    ((elementsFunctor A).map f)

end BasicLocalizer

end Atoms.TestCategory
