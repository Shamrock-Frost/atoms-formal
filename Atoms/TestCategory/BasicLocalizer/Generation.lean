import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Saturation
import Atoms.TestCategory.BasicLocalizer.Basic

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

def sInfW (𝔖 : Set BasicLocalizer.{u}) : MorphismProperty Cat.{u, u} :=
  fun _ _ F ↦ ∀ 𝒲 ∈ 𝔖, 𝒲.W F

def sInf (𝔖 : Set BasicLocalizer.{u}) : BasicLocalizer.{u} where
  W := sInfW 𝔖
  containsIdentities := ⟨fun _ 𝒲 _ ↦ 𝒲.W.id_mem _⟩
  hasTwoOutOfThree :=
    { comp_mem := fun f g hf hg 𝒲 h𝒲 ↦ 𝒲.W.comp_mem f g (hf 𝒲 h𝒲) (hg 𝒲 h𝒲)
      of_postcomp := fun f g hg hfg 𝒲 h𝒲 ↦ 𝒲.W.of_postcomp f g (hg 𝒲 h𝒲) (hfg 𝒲 h𝒲)
      of_precomp := fun f g hf hfg 𝒲 h𝒲 ↦ 𝒲.W.of_precomp f g (hf 𝒲 h𝒲) (hfg 𝒲 h𝒲) }
  isStableUnderRetracts := ⟨fun h hg 𝒲 h𝒲 ↦ 𝒲.W.of_retract h (hg 𝒲 h𝒲)⟩
  terminal_aspherical C _ := fun 𝒲 _ ↦ 𝒲.terminal_aspherical C
  quillenA u v h := fun 𝒲 h𝒲 ↦ 𝒲.quillenA u v fun c ↦ h c 𝒲 h𝒲

theorem sInf_W_iff (𝔖 : Set BasicLocalizer.{u}) {C D : Cat.{u, u}} (F : C ⟶ D) :
    (sInf 𝔖).W F ↔ ∀ 𝒲 ∈ 𝔖, 𝒲.W F := Iff.rfl

def generated (T : MorphismProperty Cat.{u, u}) : BasicLocalizer.{u} :=
  sInf {𝒲 | T ≤ 𝒲.W}

theorem le_generated_W (T : MorphismProperty Cat.{u, u}) : T ≤ (generated T).W :=
  fun _ _ _ hF _ h𝒲 ↦ h𝒲 _ hF

theorem generated_W_le (T : MorphismProperty Cat.{u, u}) (𝒲 : BasicLocalizer.{u})
    (h : T ≤ 𝒲.W) : (generated T).W ≤ 𝒲.W :=
  fun _ _ _ hF ↦ hF 𝒲 h

theorem isAccessible_iff_generated (𝒲 : BasicLocalizer.{u}) :
    𝒲.IsAccessible ↔
      ∃ T : MorphismProperty Cat.{u, u}, T.IsSmall.{u} ∧ (generated T).W = 𝒲.W := by
  constructor
  · rintro ⟨T, hT, hle, hmin⟩
    exact ⟨T, hT, le_antisymm (generated_W_le T 𝒲 hle)
      (hmin (generated T) (le_generated_W T))⟩
  · rintro ⟨T, hT, heq⟩
    exact ⟨T, hT, heq ▸ le_generated_W T, fun 𝒱 h𝒱 ↦ heq ▸ generated_W_le T 𝒱 h𝒱⟩

theorem isAccessible_generated (T : MorphismProperty Cat.{u, u}) [T.IsSmall.{u}] :
    (generated T).IsAccessible :=
  (isAccessible_iff_generated (generated T)).2 ⟨T, inferInstance, rfl⟩

end BasicLocalizer

def minimalBasicLocalizer : BasicLocalizer.{u} := BasicLocalizer.generated ⊥

theorem minimalBasicLocalizer_W_iff {C D : Cat.{u, u}} (F : C ⟶ D) :
    minimalBasicLocalizer.W F ↔ ∀ 𝒲 : BasicLocalizer.{u}, 𝒲.W F :=
  ⟨fun h 𝒲 ↦ h 𝒲 (show ⊥ ≤ 𝒲.W from bot_le), fun h 𝒲 _ ↦ h 𝒲⟩

theorem isAccessible_minimalBasicLocalizer : minimalBasicLocalizer.{u}.IsAccessible :=
  BasicLocalizer.isAccessible_generated ⊥

end Atoms.TestCategory
