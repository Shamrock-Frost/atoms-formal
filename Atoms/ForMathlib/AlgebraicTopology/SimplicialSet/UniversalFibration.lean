import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Left
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Right
import Atoms.ForMathlib.CategoryTheory.Topos.PresheafUniverseLocal
import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

instance : leftFibrations.{u}.IsStableUnderBaseChange :=
  inferInstanceAs leftHornInclusions.rlp.IsStableUnderBaseChange

instance : rightFibrations.{u}.IsStableUnderBaseChange :=
  inferInstanceAs rightHornInclusions.rlp.IsStableUnderBaseChange

private theorem exists_iso_of_le_J {T : MorphismProperty SSet.{u + 1}}
    (hT : T ≤ modelCategoryQuillen.J) ⦃K L : SSet.{u + 1}⦄ (j : K ⟶ L) (hj : T j) :
    ∃ a : SimplexCategory, Nonempty (L ≅ uliftYoneda.{u + 1}.obj a) := by
  have hj := hT _ hj
  simp only [modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨_, ⟨_⟩⟩ := hj
  exact ⟨_, ⟨Iso.refl _⟩⟩

abbrev leftFibrationUniverse : SSet.{u + 1} :=
  (presheafUniverseSub.{u} SimplexCategory leftFibrations.{u + 1}).toFunctor

theorem leftFibrations_universalLeftFibration :
    leftFibrations (presheafUniverseSubTotalπ.{u} SimplexCategory leftFibrations.{u + 1}) :=
  rlp_presheafUniverseSubTotalπ SimplexCategory (exists_iso_of_le_J leftHornInclusions_le_J)

theorem leftFibrations_iff_exists_isPullback {E F : SSet.{u + 1}} (p : E ⟶ F)
    (hp : ∀ (n : SimplexCategoryᵒᵖ) (x : F.obj n), Small.{u} {e : E.obj n // p.app n e = x}) :
    leftFibrations p ↔ ∃ (χ : F ⟶ leftFibrationUniverse.{u}) (q : E ⟶ _),
      IsPullback q p (presheafUniverseSubTotalπ.{u} SimplexCategory leftFibrations.{u + 1}) χ :=
  rlp_iff_exists_isPullback SimplexCategory (exists_iso_of_le_J leftHornInclusions_le_J) p hp

abbrev rightFibrationUniverse : SSet.{u + 1} :=
  (presheafUniverseSub.{u} SimplexCategory rightFibrations.{u + 1}).toFunctor

theorem rightFibrations_universalRightFibration :
    rightFibrations (presheafUniverseSubTotalπ.{u} SimplexCategory rightFibrations.{u + 1}) :=
  rlp_presheafUniverseSubTotalπ SimplexCategory (exists_iso_of_le_J rightHornInclusions_le_J)

theorem rightFibrations_iff_exists_isPullback {E F : SSet.{u + 1}} (p : E ⟶ F)
    (hp : ∀ (n : SimplexCategoryᵒᵖ) (x : F.obj n), Small.{u} {e : E.obj n // p.app n e = x}) :
    rightFibrations p ↔ ∃ (χ : F ⟶ rightFibrationUniverse.{u}) (q : E ⟶ _),
      IsPullback q p (presheafUniverseSubTotalπ.{u} SimplexCategory rightFibrations.{u + 1}) χ :=
  rlp_iff_exists_isPullback SimplexCategory (exists_iso_of_le_J rightHornInclusions_le_J) p hp

abbrev innerFibrationUniverse : SSet.{u + 1} :=
  (presheafUniverseSub.{u} SimplexCategory innerFibrations.{u + 1}).toFunctor

theorem innerFibrations_universalInnerFibration :
    innerFibrations (presheafUniverseSubTotalπ.{u} SimplexCategory innerFibrations.{u + 1}) :=
  rlp_presheafUniverseSubTotalπ SimplexCategory (exists_iso_of_le_J innerHornInclusions_le_J)

theorem innerFibrations_iff_exists_isPullback {E F : SSet.{u + 1}} (p : E ⟶ F)
    (hp : ∀ (n : SimplexCategoryᵒᵖ) (x : F.obj n), Small.{u} {e : E.obj n // p.app n e = x}) :
    innerFibrations p ↔ ∃ (χ : F ⟶ innerFibrationUniverse.{u}) (q : E ⟶ _),
      IsPullback q p (presheafUniverseSubTotalπ.{u} SimplexCategory innerFibrations.{u + 1}) χ :=
  rlp_iff_exists_isPullback SimplexCategory (exists_iso_of_le_J innerHornInclusions_le_J) p hp

abbrev kanFibrationUniverse : SSet.{u + 1} :=
  (presheafUniverseSub.{u} SimplexCategory modelCategoryQuillen.J.{u + 1}.rlp).toFunctor

theorem rlp_J_universalKanFibration :
    modelCategoryQuillen.J.rlp
      (presheafUniverseSubTotalπ.{u} SimplexCategory modelCategoryQuillen.J.{u + 1}.rlp) :=
  rlp_presheafUniverseSubTotalπ SimplexCategory (exists_iso_of_le_J le_rfl)

theorem rlp_J_iff_exists_isPullback {E F : SSet.{u + 1}} (p : E ⟶ F)
    (hp : ∀ (n : SimplexCategoryᵒᵖ) (x : F.obj n), Small.{u} {e : E.obj n // p.app n e = x}) :
    modelCategoryQuillen.J.rlp p ↔ ∃ (χ : F ⟶ kanFibrationUniverse.{u}) (q : E ⟶ _),
      IsPullback q p
        (presheafUniverseSubTotalπ.{u} SimplexCategory modelCategoryQuillen.J.{u + 1}.rlp) χ :=
  rlp_iff_exists_isPullback SimplexCategory (exists_iso_of_le_J le_rfl) p hp

end SSet
