import Atoms.Homotopical.IteratedSlice
import Atoms.TestCategory.Localizer.Basic

open CategoryTheory Limits MorphismProperty

namespace Atoms.TestCategory

universe u

open Atoms.Homotopical

variable {A : Type u} [SmallCategory A]

namespace BasicLocalizer

theorem wPsh_costructuredArrow_eq (𝒲 : BasicLocalizer.{u}) (X : Aᵒᵖ ⥤ Type u) :
    𝒲.wPsh (CostructuredArrow yoneda X) = (𝒲.wPsh A).inverseImage (sliceForget X) := by
  ext Z Z' f
  change 𝒲.W ((elementsFunctor _).map f) ↔ 𝒲.W ((elementsFunctor A).map ((sliceForget X).map f))
  rw [𝒲.W_elementsFunctor_map_iff, 𝒲.W_elementsFunctor_map_iff]
  exact 𝒲.W_iff_of_isEquivalence_of_iso (costructuredArrowSliceEquivalence X Z).functor.toCatHom
    (costructuredArrowSliceEquivalence X Z').functor.toCatHom
    (costructuredArrowSliceEquivalence X Z).isEquivalence_functor
    (costructuredArrowSliceEquivalence X Z').isEquivalence_functor _ _
    (costructuredArrowSliceEquivalenceMapIso X f)

theorem pshAspherical_costructuredArrow_iff (𝒲 : BasicLocalizer.{u}) (X : Aᵒᵖ ⥤ Type u)
    (Z : (CostructuredArrow yoneda X)ᵒᵖ ⥤ Type u) :
    𝒲.PshAspherical (CostructuredArrow yoneda X) Z ↔
      𝒲.PshAspherical A ((sliceForget X).obj Z) := by
  rw [𝒲.pshAspherical_iff_aspherical_costructuredArrow,
    𝒲.pshAspherical_iff_aspherical_costructuredArrow]
  exact 𝒲.aspherical_iff_of_equivalence (costructuredArrowSliceEquivalence X Z)

instance isLocalTest_costructuredArrow (𝒲 : BasicLocalizer.{u})
    [𝒲.IsLocalTest A] (X : Aᵒᵖ ⥤ Type u) :
    𝒲.IsLocalTest (CostructuredArrow yoneda X) := by
  refine 𝒲.isLocalTest_of_rlp_le (CostructuredArrow yoneda X) ?_
  rw [monomorphisms_eq_inverseImage_sliceForget, wPsh_costructuredArrow_eq,
    rlp_inverseImage_sliceForget_of_respectsIso]
  exact fun _ _ f hf => 𝒲.rlp_monomorphisms_le_wPsh_of_isLocalTest A _ hf

end BasicLocalizer

end Atoms.TestCategory
