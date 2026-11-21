import Atoms.TestCategory.Localizer.TestLocalizer
import Atoms.TestCategory.Localizer.Regular
import Atoms.TestCategory.Presheaf.ElementsSlice
import Atoms.TestCategory.BasicLocalizer.Generation
import Atoms.Homotopical.Regular.Completion

open CategoryTheory Limits Opposite Atoms.Homotopical MorphismProperty

namespace Atoms.TestCategory

universe u

def representableMaps (A : Type u) [SmallCategory A] : MorphismProperty (Aᵒᵖ ⥤ Type u) :=
  MorphismProperty.ofHoms (fun i : Σ a : A, Σ b : A, a ⟶ b => yoneda.map i.2.2)

def representableCompletion (A : Type u) [SmallCategory A] : MorphismProperty (Aᵒᵖ ⥤ Type u) :=
  regularCompletion (representableMaps A)

instance isALocalizer_representableCompletion (A : Type u) [SmallCategory A] :
    IsALocalizer (representableCompletion A) :=
  isALocalizer_regularCompletion _

instance isRegularALocalizer_representableCompletion (A : Type u) [SmallCategory A] :
    IsRegularALocalizer (representableCompletion A) :=
  isRegularALocalizer_regularCompletion _

instance isSmall_representableMaps (A : Type u) [SmallCategory A] :
    (representableMaps A).IsSmall.{u} :=
  MorphismProperty.isSmall_ofHoms _

theorem yoneda_map_mem_representableCompletion (A : Type u) [SmallCategory A] {a b : A}
    (g : a ⟶ b) : representableCompletion A (yoneda.map g) :=
  le_regularCompletion _ _ (ofHoms.mk (⟨a, b, g⟩ : Σ a : A, Σ b : A, a ⟶ b))

theorem representableCompletion_eq_regularCompletion_generatedALocalizer (A : Type u)
    [SmallCategory A] :
    representableCompletion A =
      regularCompletion (generatedALocalizer.{u, u} (representableMaps A)) :=
  le_antisymm (regularCompletion_mono (le_generatedALocalizer _))
    (regularCompletion_le (generatedALocalizer_le (le_regularCompletion _)))

instance isAccessible_representableCompletion (A : Type u) [SmallCategory A] :
    IsAccessibleALocalizer (representableCompletion A) := by
  rw [representableCompletion_eq_regularCompletion_generatedALocalizer]
  infer_instance

namespace BasicLocalizer

theorem representableCompletion_le_wPsh (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]
    [𝒲.IsLocalTest A] :
    representableCompletion A ≤ 𝒲.wPsh A := by
  have := 𝒲.isALocalizer_wPsh_of_isLocalTest A
  have := 𝒲.isRegularALocalizer_wPsh (𝒲.rlp_monomorphisms_le_wPsh_of_isLocalTest A)
  refine regularCompletion_le ?_
  rintro _ _ _ ⟨i⟩
  exact 𝒲.wPsh_yoneda_map A i.2.2

end BasicLocalizer

instance isTestALocalizer_representableCompletion_of_terminal (A : Type u) [SmallCategory A]
    [HasTerminal A] : IsTestALocalizer (representableCompletion A) := by
  refine ⟨fun a ↦ ?_⟩
  let e : yoneda.obj (⊤_ A) ≅ ⊤_ (Aᵒᵖ ⥤ Type u) :=
    (IsTerminal.isTerminalObj yoneda _ terminalIsTerminal).uniqueUpToIso terminalIsTerminal
  have h : terminal.from (yoneda.obj a) = yoneda.map (terminal.from a) ≫ e.hom :=
    terminal.hom_ext _ _
  rw [h]
  exact MorphismProperty.comp_mem _ _ _
    (yoneda_map_mem_representableCompletion A (terminal.from a))
    (IsALocalizer.isomorphisms_le _ (MorphismProperty.isomorphisms.infer_property e.hom))

theorem representableCompletion_eq_minimal_of_terminal (A : Type u) [SmallCategory A]
    [HasTerminal A] [minimalBasicLocalizer.{u}.IsLocalTest A] :
    representableCompletion A = minimalBasicLocalizer.{u}.wPsh A := by
  refine le_antisymm (BasicLocalizer.representableCompletion_le_wPsh _ A) fun X Y f hf ↦ ?_
  rw [← BasicLocalizer.ofTestALocalizer_wPsh (representableCompletion A)]
  exact BasicLocalizer.generated_W_le ⊥ _ bot_le _ hf

theorem sliceHom_yoneda_map_mem_representableCompletion {A : Type u} [SmallCategory A]
    {a a' : A} (f : a ⟶ a') :
    representableCompletion (CostructuredArrow yoneda (yoneda.obj a'))
      (sliceHom (yoneda.map f) (𝟙 (yoneda.obj a'))) := by
  let φ : CostructuredArrow.mk (yoneda.map f ≫ 𝟙 (yoneda.obj a')) ⟶
      CostructuredArrow.mk (𝟙 (yoneda.obj a')) := CostructuredArrow.homMk f
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoOfNatIso
    (CostructuredArrow.toOverCompOverEquivPresheafCostructuredArrow (yoneda.obj a'))
    (Arrow.mk φ))).2 (yoneda_map_mem_representableCompletion _ φ)

end Atoms.TestCategory
