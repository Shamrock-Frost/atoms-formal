import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Subcomplex
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

universe u

namespace SSet

open CategoryTheory MorphismProperty

lemma anodyneExtensions_le_monomorphisms :
    anodyneExtensions.{u} ≤ monomorphisms SSet.{u} := by
  rw [anodyneExtensions_eq_retracts_transfiniteCompositions, retracts_le_iff,
    transfiniteCompositions_le_iff, pushouts_le_iff, coproducts_le_iff]
  exact modelCategoryQuillen.J_le_monomorphisms

open Simplicial in
theorem anodyneExtensions.hom_comp_ι_of_eq_horn {n : ℕ} [NeZero n] {k : Fin (n + 1)}
    {Z : SSet.{u}} (S : (Δ[n] : SSet.{u}).Subcomplex) (h : S = horn n k) (e : Z ≅ S) :
    anodyneExtensions (e.hom ≫ S.ι) := by
  subst h
  exact anodyneExtensions.comp_mem _ _ (anodyneExtensions.of_isIso _)
    (anodyneExtensions.horn_ι k)

lemma anodyneExtensions_preimage_ι {X Y : SSet.{u}} (e : X ⟶ Y) [IsIso e] {A : Y.Subcomplex}
    (hA : anodyneExtensions A.ι) : anodyneExtensions (A.preimage e).ι := by
  have h₁ : Subcomplex.range ((A.preimage e).ι ≫ e) ≤ A := by
    rintro n _ ⟨x, rfl⟩
    exact x.2
  have h₂ : Subcomplex.range (A.ι ≫ inv e) ≤ A.preimage e := by
    rintro n _ ⟨x, rfl⟩
    change e.app n ((inv e).app n x.1) ∈ A.obj n
    rw [← NatTrans.comp_app_apply, IsIso.inv_hom_id]
    exact x.2
  let i : (A.preimage e : SSet.{u}) ≅ (A : SSet.{u}) :=
    { hom := Subcomplex.lift _ h₁
      inv := Subcomplex.lift _ h₂
      hom_inv_id := by
        rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι,
          Subcomplex.lift_ι_assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
          Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono (Subcomplex.ι _), Category.assoc, Subcomplex.lift_ι,
          Subcomplex.lift_ι_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
          Category.id_comp] }
  exact (anodyneExtensions.arrow_mk_iso_iff (Arrow.isoMk i (asIso e) rfl)).2 hA

end SSet
