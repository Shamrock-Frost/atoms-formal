import Atoms.ForMathlib.AlgebraicTopology.Reedy.Elegant
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.Data.Nat.SuccPred

universe w

open CategoryTheory MorphismProperty Limits Simplicial

namespace SimplexCategory

section LeastSection

variable {c d : SimplexCategory} (σ : c ⟶ d) (hσ : Function.Surjective σ.toOrderHom)

private def above (j : Fin (d.len + 1)) : Finset (Fin (c.len + 1)) :=
  Finset.univ.filter fun k ↦ j ≤ σ.toOrderHom k

include hσ in
private theorem above_nonempty (j : Fin (d.len + 1)) : (above σ j).Nonempty := by
  obtain ⟨k, hk⟩ := hσ j
  exact ⟨k, by simp [above, hk]⟩

private def leastSection : d ⟶ c :=
  Hom.mk ⟨fun j ↦ (above σ j).min' (above_nonempty σ hσ j), fun j j' hj ↦
    Finset.min'_le _ _ (by
      have := Finset.min'_mem _ (above_nonempty σ hσ j')
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
      exact hj.trans this)⟩

private theorem leastSection_le (k : Fin (c.len + 1)) :
    (leastSection σ hσ).toOrderHom (σ.toOrderHom k) ≤ k :=
  Finset.min'_le _ _ (by simp [above])

private theorem leastSection_comp : leastSection σ hσ ≫ σ = 𝟙 d := by
  ext j
  obtain ⟨k, rfl⟩ := hσ j
  have hmem := Finset.min'_mem _ (above_nonempty σ hσ (σ.toOrderHom k))
  simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  exact le_antisymm (σ.toOrderHom.monotone (leastSection_le σ hσ k)) hmem

end LeastSection

private theorem mapFactorizationData_eq {X Y : SimplexCategory} {f : X ⟶ Y}
    (a : (epimorphisms SimplexCategory).MapFactorizationData (monomorphisms SimplexCategory) f) :
    a = ⟨image f, factorThruImage f, image.ι f, image.fac f, inferInstanceAs (Epi _),
      inferInstanceAs (Mono _)⟩ := by
  obtain ⟨Z, i, p, fac, hi, hp⟩ := a
  have : Epi i := hi
  have : Mono p := hp
  obtain rfl := image_eq fac
  obtain rfl := image_ι_eq fac
  obtain rfl := factorThruImage_eq fac
  rfl

def reedyStructure : HomotopicalAlgebra.ReedyStructure
    (MorphismProperty.epimorphisms SimplexCategory)
    (MorphismProperty.monomorphisms SimplexCategory) ℕ where
  deg n := n.len
  lt₁ {X Y} f hf hf' := by
    have : Epi f := hf
    refine (len_le_of_epi f).lt_of_ne fun h ↦ hf' ?_
    obtain rfl : X = Y := SimplexCategory.ext h.symm
    obtain rfl := eq_id_of_epi f
    exact ⟨_⟩
  lt₂ {X Y} f hf hf' := by
    have : Mono f := hf
    refine (len_le_of_mono f).lt_of_ne fun h ↦ hf' ?_
    obtain rfl : X = Y := SimplexCategory.ext h
    obtain rfl := eq_id_of_mono f
    exact ⟨_⟩
  nonempty_unique f :=
    ⟨{ default := ⟨image f, factorThruImage f, image.ι f, image.fac f, inferInstanceAs (Epi _),
        inferInstanceAs (Mono _)⟩
       uniq := mapFactorizationData_eq }⟩

@[simp] theorem reedyStructure_deg (n : SimplexCategory) : reedyStructure.deg n = n.len := rfl

theorem isEZReedy_epimorphisms :
    (MorphismProperty.epimorphisms SimplexCategory).IsEZReedy where
  isSplitEpi _ _ σ hσ := by
    have : Epi σ := hσ
    exact isSplitEpi_of_epi σ
  eq_of_sections c d σ σ' hσ hσ' h := by
    have hs := epi_iff_surjective.1 hσ
    have hs' := epi_iff_surjective.1 hσ'
    have h₁ : leastSection σ hs ≫ σ' = 𝟙 d := (h _).1 (leastSection_comp σ hs)
    have h₂ : leastSection σ' hs' ≫ σ = 𝟙 d := (h _).2 (leastSection_comp σ' hs')
    have key : ∀ (τ τ' : c ⟶ d) (ht : Function.Surjective τ.toOrderHom),
        leastSection τ ht ≫ τ' = 𝟙 d → ∀ k, τ.toOrderHom k ≤ τ'.toOrderHom k := by
      intro τ τ' ht hτ k
      have := congrArg (fun g ↦ g.toOrderHom (τ.toOrderHom k)) hτ
      simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply, id_toOrderHom,
        OrderHom.id_coe, id_eq] at this
      exact this ▸ τ'.toOrderHom.monotone (leastSection_le τ ht k)
    ext k
    exact le_antisymm (key σ σ' hs h₁ k) (key σ' σ hs' h₂ k)

theorem isElegant_epimorphisms :
    (MorphismProperty.epimorphisms SimplexCategory).IsElegant.{w} :=
  reedyStructure.isElegant_of_isEZReedy isEZReedy_epimorphisms

theorem _root_.SSet.isDegenerate_epimorphisms_iff {X : SSet.{w}} {n : ℕ} (x : X _⦋n⦌) :
    (MorphismProperty.epimorphisms SimplexCategory).IsDegenerate X x ↔ x ∈ X.degenerate n := by
  rw [SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨d, σ, hσ, hσ', y, rfl⟩
    have : Epi σ := hσ
    refine ⟨d.len, (len_le_of_epi σ).lt_of_ne fun h ↦ hσ' ?_, σ, hσ, y, rfl⟩
    obtain rfl : d = ⦋n⦌ := SimplexCategory.ext h
    obtain rfl := eq_id_of_epi σ
    exact ⟨_⟩
  · rintro ⟨m, hm, f, hf, y, rfl⟩
    exact ⟨⦋m⦌, f, hf, fun ⟨_⟩ ↦ hm.ne rfl, y, rfl⟩

end SimplexCategory
