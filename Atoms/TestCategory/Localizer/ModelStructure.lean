import Atoms.Homotopical.Localizer.InverseImage
import Atoms.Homotopical.Regular.Completion
import Atoms.TestCategory.FiniteSetsTest
import Atoms.TestCategory.BasicLocalizer.Generation
import Atoms.TestCategory.Nerve.Elements
import Atoms.TestCategory.Localizer.TestLocalizer
import Atoms.TestCategory.Localizer.Basic
import Atoms.TestCategory.Localizer.Regular

open CategoryTheory Limits MorphismProperty Opposite Atoms.Homotopical HomotopicalAlgebra

namespace Atoms.TestCategory

universe u

section Test

variable (𝒲 : BasicLocalizer.{u}) {C : Type u} [SmallCategory C]

namespace BasicLocalizer

instance isTestALocalizer_wPsh [𝒲.IsTest C] : IsTestALocalizer (𝒲.wPsh C) where
  toIsRegularALocalizer :=
    𝒲.isRegularALocalizer_wPsh (𝒲.rlp_monomorphisms_le_wPsh_of_isLocalTest C)
  terminal_from_yoneda c :=
    (𝒲.pshAspherical_iff_wPsh_terminal_from C 𝒲.aspherical_of_isWeakTest _).1
      (𝒲.pshAspherical_yoneda C c)

end BasicLocalizer

instance isTestALocalizer_regularCompletion (S : MorphismProperty (Cᵒᵖ ⥤ Type u)) :
    IsTestALocalizer (regularCompletion (generatedALocalizer.{u, u}
      (S ⊔ MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c)))) where
  terminal_from_yoneda c := le_regularCompletion _ _
    (le_generatedALocalizer _ _ (le_sup_right (a := S) _ (ofHoms.mk c)))

theorem isAccessibleALocalizer_regularCompletion_map_nerveFunctor
    (T : MorphismProperty Cat.{u, u}) [T.IsSmall.{u}] :
    IsAccessibleALocalizer.{u, u} (regularCompletion (generatedALocalizer (T.map (nerveFunctor C) ⊔
      MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c)))) := by
  suffices IsAccessibleALocalizer (generatedALocalizer (T.map (nerveFunctor C) ⊔
      MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c))) from inferInstance
  obtain ⟨ι, A, B, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{u} T).1 inferInstance
  let S₀ : MorphismProperty (Cᵒᵖ ⥤ Type u) :=
    MorphismProperty.ofHoms (fun i ↦ (nerveFunctor C).map (f i)) ⊔
      MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c)
  have hS₀ : S₀.IsSmall.{u} := inferInstance
  refine ⟨S₀, hS₀, le_antisymm (generatedALocalizer_mono (sup_le_sup_right ?_ _))
    (generatedALocalizer_le (sup_le ?_ (le_sup_right.trans (le_generatedALocalizer _))))⟩
  · rintro _ _ _ ⟨i⟩
    exact map_mem_map _ _ _ (ofHoms.mk i)
  · rw [map_le_iff]
    rintro _ _ _ ⟨i⟩
    exact le_generatedALocalizer _ _ (le_sup_left (a := MorphismProperty.ofHoms
      (fun i ↦ (nerveFunctor C).map (f i))) _ (ofHoms.mk i))

namespace BasicLocalizer

variable (C) in
theorem wPsh_eq_regularCompletion [hC : 𝒲.IsTest C] (T : MorphismProperty Cat.{u, u})
    [T.IsSmall.{u}] (hT : (BasicLocalizer.generated T).W = 𝒲.W) :
    𝒲.wPsh C = regularCompletion (generatedALocalizer.{u, u} (T.map (nerveFunctor C) ⊔
      MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c))) := by
  refine le_antisymm ?_ (regularCompletion_le (generatedALocalizer_le (sup_le ?_ ?_)))
  · have := isAccessibleALocalizer_regularCompletion_map_nerveFunctor (C := C) T
    let V := regularCompletion (generatedALocalizer.{u, u} (T.map (nerveFunctor C) ⊔
      MorphismProperty.ofHoms fun c : C ↦ terminal.from (yoneda.obj c)))
    have hle : 𝒲.W ≤ (BasicLocalizer.ofTestALocalizer V).W := by
      rw [← hT]
      refine BasicLocalizer.generated_W_le T _ fun _ _ u hu ↦ ?_
      exact le_regularCompletion _ _ (le_generatedALocalizer _ _
        (le_sup_left (a := T.map (nerveFunctor C)) _ (map_mem_map _ _ _ hu)))
    calc 𝒲.wPsh C ≤ (BasicLocalizer.ofTestALocalizer V).wPsh C := fun _ _ _ hf ↦ hle _ hf
      _ = _ := BasicLocalizer.ofTestALocalizer_wPsh V
  · rw [map_le_iff]
    intro _ _ u hu
    refine (MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction C) 𝒲.W hC.counit_mem u).1 ?_
    rw [← hT]
    exact BasicLocalizer.le_generated_W T _ hu
  · rintro _ _ _ ⟨c⟩
    exact IsTestALocalizer.terminal_from_yoneda c

theorem isAccessibleALocalizer_wPsh_of_isTest (hW : 𝒲.IsAccessible) [𝒲.IsTest C] :
    IsAccessibleALocalizer (𝒲.wPsh C) := by
  obtain ⟨T, hTs, hT⟩ := (BasicLocalizer.isAccessible_iff_generated 𝒲).1 hW
  rw [𝒲.wPsh_eq_regularCompletion C T hT]
  exact isAccessibleALocalizer_regularCompletion_map_nerveFunctor T

theorem ofTestALocalizer_wPsh_eq_self [hC : 𝒲.IsTest C] [IsAccessibleALocalizer (𝒲.wPsh C)] :
    BasicLocalizer.ofTestALocalizer (𝒲.wPsh C) = 𝒲 := by
  ext D E u
  exact (MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction C) 𝒲.W hC.counit_mem u).symm

theorem isAccessible_ofTestALocalizer (V : MorphismProperty (Cᵒᵖ ⥤ Type u))
    [hV : IsAccessibleALocalizer V] [IsTestALocalizer V] :
    (BasicLocalizer.ofTestALocalizer V).IsAccessible := by
  obtain ⟨S, hS, hSV⟩ := hV.exists_generatedALocalizer_eq
  obtain ⟨ι, X, Y, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{u} S).1 hS
  let L := (nerveFunctor C).obj interval.{u}
  let T : MorphismProperty Cat.{u, u} :=
    MorphismProperty.ofHoms (fun i ↦ (elementsFunctor C).map (f i)) ⊔
      (MorphismProperty.ofHoms (fun _ : Unit ↦ terminal.from (Cat.of C)) ⊔
        MorphismProperty.ofHoms fun c : C ↦
          terminal.from ((elementsFunctor C).obj (yoneda.obj c ⨯ L)))
  have hC := isTest_ofTestALocalizer V
  refine ⟨T, inferInstance, sup_le ?_ (sup_le ?_ ?_), fun 𝒱 hT ↦ ?_⟩
  · rintro _ _ _ ⟨i⟩
    change (BasicLocalizer.ofTestALocalizer V).wPsh C (f i)
    rw [BasicLocalizer.ofTestALocalizer_wPsh, ← hSV]
    exact le_generatedALocalizer _ _ ⟨i⟩
  · rintro _ _ _ ⟨⟩
    exact aspherical_of_isWeakTest _
  · rintro _ _ _ ⟨c⟩
    exact locallyAspherical_nerveFunctor_obj_of_isLocalTest _ C _ c
  have h𝒱 : 𝒱.IsTest C := 𝒱.isTest_of_separatingInterval C
    ⟨L, nervePoint, isPullback_nervePoint⟩ (fun c ↦ hT _ (Or.inr (Or.inr ⟨c⟩)))
    (hT _ (Or.inr (Or.inl ⟨()⟩)))
  have hle : V ≤ 𝒱.wPsh C := by
    rw [← hSV]
    exact generatedALocalizer_le fun _ _ _ ⟨i⟩ ↦ hT _ (Or.inl ⟨i⟩)
  intro D E u hu
  exact (MorphismProperty.mem_iff_map_map_of_counit (nerveAdjunction C) 𝒱.W h𝒱.counit_mem u).2
    (hle _ hu)

theorem isAccessible_iff_isAccessibleALocalizer_wPsh [𝒲.IsTest C] :
    𝒲.IsAccessible ↔ IsAccessibleALocalizer (𝒲.wPsh C) := by
  refine ⟨fun hW ↦ 𝒲.isAccessibleALocalizer_wPsh_of_isTest hW, fun h ↦ ?_⟩
  rw [← 𝒲.ofTestALocalizer_wPsh_eq_self (C := C)]
  exact isAccessible_ofTestALocalizer (𝒲.wPsh C)

end BasicLocalizer

end Test

namespace BasicLocalizer

theorem isAccessibleALocalizer_wPsh (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    (hW : 𝒲.IsAccessible) [𝒲.IsLocalTest A] :
    IsAccessibleALocalizer (𝒲.wPsh A) := by
  have hWB : IsAccessibleALocalizer (𝒲.wPsh NonemptyFinSet.{u}) :=
    𝒲.isAccessibleALocalizer_wPsh_of_isTest hW
  have he := 𝒲.wPsh_eq_inverseImage_elementsFunctor_comp_nerveFunctor A NonemptyFinSet.{u}
  have hV := 𝒲.isALocalizer_wPsh_of_isLocalTest A
  rw [he] at hV ⊢
  exact hWB.inverseImage _ (mono_map_elementsFunctor_comp_nerveFunctor A NonemptyFinSet.{u})

end BasicLocalizer

instance isAccessibleALocalizer_minimal_wPsh (A : Type u) [SmallCategory A]
    [minimalBasicLocalizer.{u}.IsLocalTest A] :
    IsAccessibleALocalizer (minimalBasicLocalizer.{u}.wPsh A) :=
  minimalBasicLocalizer.isAccessibleALocalizer_wPsh A isAccessible_minimalBasicLocalizer

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

namespace BasicLocalizer

theorem exists_generators_of_isLocalTest (𝕀 : ExactCylinder.{u} (Aᵒᵖ ⥤ Type u))
    (hW : 𝒲.IsAccessible)
    [𝒲.IsLocalTest A] (hI : CylinderCompatibleWith (Aᵒᵖ ⥤ Type u) (𝒲.wPsh A) 𝕀) :
    ∃ S : MorphismProperty (Aᵒᵖ ⥤ Type u),
      MorphismProperty.IsSmall.{u} S ∧ S ≤ MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type u) ∧
        𝕀.weakEquivalences S = 𝒲.wPsh A :=
  (𝒲.isAccessibleALocalizer_wPsh A hW).exists_weakEquivalences_eq 𝕀 hI

end BasicLocalizer

end Atoms.TestCategory
