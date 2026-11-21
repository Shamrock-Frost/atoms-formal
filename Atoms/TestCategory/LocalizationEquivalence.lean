import Atoms.TestCategory.IsTest
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Composition
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

open CategoryTheory

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

theorem wPsh_isInvertedBy_elementsFunctor_comp_Q :
    (𝒲.wPsh A).IsInvertedBy (elementsFunctor A ⋙ 𝒲.W.Q) :=
  fun _ _ _ hf => MorphismProperty.Q_inverts 𝒲.W _ hf

theorem W_isInvertedBy_nerveFunctor_comp_Q [h : 𝒲.IsWeakTest A] :
    𝒲.W.IsInvertedBy (nerveFunctor A ⋙ (𝒲.wPsh A).Q) :=
  fun _ _ f hf => MorphismProperty.Q_inverts (𝒲.wPsh A) _
    ((MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction A) 𝒲.W h.counit_mem f).1 hf)

noncomputable def localizedElements : (𝒲.wPsh A).Localization ⥤ 𝒲.W.Localization :=
  Localization.lift (elementsFunctor A ⋙ 𝒲.W.Q)
    (𝒲.wPsh_isInvertedBy_elementsFunctor_comp_Q A) (𝒲.wPsh A).Q

noncomputable def localizedNerve [𝒲.IsWeakTest A] :
    𝒲.W.Localization ⥤ (𝒲.wPsh A).Localization :=
  Localization.lift (nerveFunctor A ⋙ (𝒲.wPsh A).Q)
    (𝒲.W_isInvertedBy_nerveFunctor_comp_Q A) 𝒲.W.Q

noncomputable instance catCommSqElements :
    CatCommSq (elementsFunctor A) (𝒲.wPsh A).Q 𝒲.W.Q (𝒲.localizedElements A) :=
  ⟨(Localization.fac _ _ _).symm⟩

@[instance_reducible]
noncomputable def catCommSqNerve [𝒲.IsWeakTest A] :
    CatCommSq (nerveFunctor A) 𝒲.W.Q (𝒲.wPsh A).Q (𝒲.localizedNerve A) :=
  ⟨(Localization.fac _ _ _).symm⟩

noncomputable def localizationAdjunction [𝒲.IsWeakTest A] :
    𝒲.localizedElements A ⊣ 𝒲.localizedNerve A :=
  letI := 𝒲.catCommSqNerve A
  (nerveAdjunction A).localization (𝒲.wPsh A).Q (𝒲.wPsh A) 𝒲.W.Q 𝒲.W _ _

instance isIso_localizationAdjunction_unit_app [h : 𝒲.IsWeakTest A]
    (X : (𝒲.wPsh A).Localization) : IsIso ((𝒲.localizationAdjunction A).unit.app X) := by
  obtain ⟨X, rfl⟩ : ∃ X', (𝒲.wPsh A).Q.obj X' = X :=
    ⟨_, (Localization.Construction.objEquiv (𝒲.wPsh A)).right_inv X⟩
  let := 𝒲.catCommSqNerve A
  have : IsIso ((𝒲.wPsh A).Q.map ((nerveAdjunction A).unit.app X)) :=
    Localization.inverts (𝒲.wPsh A).Q (𝒲.wPsh A) _
      (MorphismProperty.map_unit_app_mem_of_counit (nerveAdjunction A) 𝒲.W h.counit_mem X)
  dsimp only [localizationAdjunction]
  rw [Adjunction.localization_unit_app]
  infer_instance

instance isIso_localizationAdjunction_counit_app [h : 𝒲.IsWeakTest A]
    (C : 𝒲.W.Localization) : IsIso ((𝒲.localizationAdjunction A).counit.app C) := by
  obtain ⟨C, rfl⟩ : ∃ C', 𝒲.W.Q.obj C' = C :=
    ⟨_, (Localization.Construction.objEquiv 𝒲.W).right_inv C⟩
  let := 𝒲.catCommSqNerve A
  have : IsIso (𝒲.W.Q.map ((nerveAdjunction A).counit.app C)) :=
    Localization.inverts 𝒲.W.Q 𝒲.W _ (h.counit_mem C)
  dsimp only [localizationAdjunction]
  rw [Adjunction.localization_counit_app]
  infer_instance

noncomputable def localizationEquivalence [𝒲.IsWeakTest A] :
    (𝒲.wPsh A).Localization ≌ 𝒲.W.Localization :=
  (𝒲.localizationAdjunction A).toEquivalence

@[simps functor]
def elementsLocalizerMorphism : LocalizerMorphism (𝒲.wPsh A) 𝒲.W where
  functor := elementsFunctor A
  map := le_rfl

theorem isLocalizedEquivalence_elementsLocalizerMorphism [𝒲.IsWeakTest A] :
    (𝒲.elementsLocalizerMorphism A).IsLocalizedEquivalence := by
  have : (𝒲.localizedElements A).IsEquivalence :=
    (𝒲.localizationEquivalence A).isEquivalence_functor
  have : CatCommSq (𝒲.elementsLocalizerMorphism A).functor (𝒲.wPsh A).Q 𝒲.W.Q
      (𝒲.localizedElements A) := 𝒲.catCommSqElements A
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' _ (𝒲.wPsh A).Q 𝒲.W.Q
    (𝒲.localizedElements A)

theorem nonempty_equivalence_of_isTest [𝒲.IsTest A] :
    Nonempty ((𝒲.wPsh A).Localization ≌ 𝒲.W.Localization) :=
  ⟨𝒲.localizationEquivalence A⟩

end BasicLocalizer

end Atoms.TestCategory
