import Atoms.ForMathlib.AlgebraicTopology.Reedy.Elegant
import Atoms.Homotopical.EilenbergZilber.Lemma
import Mathlib.Data.Nat.SuccPred

open CategoryTheory MorphismProperty

namespace Atoms.Homotopical.EZCategory

universe w v u

variable {A : Type u} [Category.{v} A]

private theorem identities_of_isIso [HasTrivialAutomorphisms A] (hA : Skeletal A) {a b : A}
    (f : a ⟶ b) [IsIso f] : identities A f := by
  obtain rfl : a = b := hA ⟨asIso f⟩
  obtain rfl : f = 𝟙 a := congrArg Iso.hom (Subsingleton.elim (asIso f) (Iso.refl a))
  exact ⟨_⟩

variable [EZCategory A]

def reedyStructure [HasTrivialAutomorphisms A] (hA : Skeletal A) :
    HomotopicalAlgebra.ReedyStructure (MorphismProperty.splitEpimorphisms A)
      (MorphismProperty.monomorphisms A) ℕ where
  deg := deg
  lt₁ f hf hf' := by
    have : IsSplitEpi f := hf
    refine (deg_le_of_isSplitEpi f).lt_of_ne fun h ↦ hf' ?_
    have := isIso_of_isSplitEpi_of_deg_eq f h
    exact identities_of_isIso hA f
  lt₂ f hf hf' :=
    (deg_le_of_mono f hf).lt_of_ne fun h ↦ hf' (by
      have := isIso_of_mono_of_deg_eq f hf h
      exact identities_of_isIso hA f)
  nonempty_unique f := by
    obtain ⟨c, p, i, hp, hi, rfl⟩ := exists_factorization f
    have : Subsingleton ((splitEpimorphisms A).MapFactorizationData (monomorphisms A) (p ≫ i)) :=
      ⟨fun ⟨Z, i₁, p₁, fac₁, hi₁, hp₁⟩ ⟨Z', i₂, p₂, fac₂, hi₂, hp₂⟩ ↦ by
        obtain ⟨e, he, he'⟩ := exists_iso_of_isSplitEpi_of_mono i₁ p₁ i₂ p₂ hi₁ hp₁ hi₂ hp₂
          (fac₁.trans fac₂.symm)
        obtain rfl : Z = Z' := hA ⟨e⟩
        obtain rfl : e = Iso.refl Z := Subsingleton.elim _ _
        simp only [Iso.refl_hom, Category.comp_id, Category.id_comp] at he he'
        subst he he'
        rfl⟩
    exact ⟨uniqueOfSubsingleton ⟨c, p, i, rfl, hp, hi⟩⟩

theorem hasStrongPushouts : (MorphismProperty.splitEpimorphisms A).HasStrongPushouts :=
  fun _ _ _ σ₁ σ₂ hσ₁ hσ₂ ↦ by
    obtain ⟨d, τ₁, τ₂, sq⟩ := exists_absolutePushout σ₁ σ₂ hσ₁ hσ₂
    exact ⟨d, τ₁, τ₂, isSplitEpi_of_isAbsolutePushout sq.flip hσ₂,
      isSplitEpi_of_isAbsolutePushout sq hσ₁, sq⟩

theorem isElegant [HasTrivialAutomorphisms A] (hA : Skeletal A) :
    (MorphismProperty.splitEpimorphisms A).IsElegant.{w} :=
  (reedyStructure hA).isElegant_of_hasStrongPushouts hasStrongPushouts

end Atoms.Homotopical.EZCategory
