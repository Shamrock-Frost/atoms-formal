import Atoms.Homotopical.Localizer.Transport
import Atoms.TestCategory.Presheaf.ElementsSlice

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

open Atoms.Homotopical

variable (𝒲 : BasicLocalizer.{u}) {B B' : Type u} [SmallCategory B] [SmallCategory B']

noncomputable def elementsEquivalenceMapIso (e : B ≌ B') {X Y : Bᵒᵖ ⥤ Type u} (f : X ⟶ Y) :
    (elementsEquivalence e X).functor ⋙
        CostructuredArrow.map (e.op.congrLeft.functor.map f) ≅
      CostructuredArrow.map f ⋙ (elementsEquivalence e Y).functor :=
  NatIso.ofComponents (fun c ↦ CostructuredArrow.isoMk (Iso.refl _)
    ((eq_whisker (yoneda.map_id _) _).trans ((Category.id_comp _).trans
      ((congrArg ((elementsEquivalenceRepresentablesIso e X).hom.app c ≫ ·)
        (e.op.congrLeft.functor.map_comp c.hom f)).trans
          (Category.assoc _ _ _).symm)))) fun _ ↦ by
    ext
    exact (Category.comp_id _).trans (Category.id_comp _).symm

namespace BasicLocalizer

theorem wPsh_eq_inverseImage_presheafEquivalence (e : B ≌ B') :
    𝒲.wPsh B = (𝒲.wPsh B').inverseImage e.op.congrLeft.functor := by
  ext X Y f
  change 𝒲.W ((elementsFunctor B).map f) ↔
    𝒲.W ((elementsFunctor B').map (e.op.congrLeft.functor.map f))
  rw [𝒲.W_elementsFunctor_map_iff, 𝒲.W_elementsFunctor_map_iff]
  exact 𝒲.W_iff_of_isEquivalence_of_iso (elementsEquivalence e X).functor.toCatHom
    (elementsEquivalence e Y).functor.toCatHom (elementsEquivalence e X).isEquivalence_functor
    (elementsEquivalence e Y).isEquivalence_functor _ _ (elementsEquivalenceMapIso e f)

theorem isLocalTest_iff_of_equivalence (e : B ≌ B') :
    𝒲.IsLocalTest B ↔ 𝒲.IsLocalTest B' := by
  rw [← 𝒲.isALocalizer_wPsh_iff B, ← 𝒲.isALocalizer_wPsh_iff B',
    𝒲.wPsh_eq_inverseImage_presheafEquivalence e]
  exact isALocalizer_inverseImage_iff e _

theorem isTest_iff_aspherical_and_isLocalTest (A : Type u) [SmallCategory A] :
    𝒲.IsTest A ↔ 𝒲.Aspherical (Cat.of A) ∧ 𝒲.IsLocalTest A :=
  ⟨fun _ ↦ ⟨𝒲.aspherical_of_isWeakTest, inferInstance⟩, fun ⟨h, _⟩ ↦
    𝒲.isTest_of_rlp_le A h (𝒲.rlp_monomorphisms_le_wPsh_of_isLocalTest A)⟩

theorem isTest_iff_of_equivalence (e : B ≌ B') : 𝒲.IsTest B ↔ 𝒲.IsTest B' := by
  rw [isTest_iff_aspherical_and_isLocalTest, isTest_iff_aspherical_and_isLocalTest,
    𝒲.isLocalTest_iff_of_equivalence e]
  exact Iff.and ⟨𝒲.aspherical_of_equivalence (A := Cat.of B) (B := Cat.of B') e,
    𝒲.aspherical_of_equivalence (A := Cat.of B') (B := Cat.of B) e.symm⟩ Iff.rfl

end BasicLocalizer

end Atoms.TestCategory
