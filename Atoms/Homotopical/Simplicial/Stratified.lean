import Atoms.Homotopical.Marked.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

open CategoryTheory Limits Opposite Simplicial

universe u

namespace Atoms.Homotopical

def simplexMarking : MarkingData SimplexCategory where
  markable n := 0 < n.len
  degeneracy := fun _ _ p => Epi p ∧ ¬ IsIso p
  respectsIso := MorphismProperty.RespectsIso.of_respects_arrow_iso _ fun _ _ e ⟨hf, hni⟩ =>
    ⟨((MorphismProperty.epimorphisms _).arrow_mk_iso_iff e).1 hf, fun h =>
      hni (((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 h)⟩
  markable_of_degeneracy a b p hp := by
    obtain ⟨hp, hni⟩ := hp
    refine Nat.pos_of_ne_zero fun h0 => hni ?_
    have := SimplexCategory.len_le_of_epi p
    exact (SimplexCategory.isIso_iff_of_epi p).2 (by omega)
  markable_of_iso a b e h := (SimplexCategory.len_eq_of_isIso e.hom).symm ▸ h

private theorem len_lt_of_degeneracy {m n : SimplexCategory} {p : m ⟶ n}
    (hp : simplexMarking.degeneracy p) : n.len < m.len := by
  obtain ⟨hp, hni⟩ := hp
  exact lt_of_le_of_ne (SimplexCategory.len_le_of_epi p)
    fun h => hni ((SimplexCategory.isIso_iff_of_epi p).2 h.symm)

theorem simplexMarking_degenerate_iff {m n : SimplexCategory} (g : m ⟶ n) :
    simplexMarking.Degenerate g ↔ ¬ Mono g := by
  constructor
  · rintro ⟨c, p, q, hp, rfl⟩ hmono
    have : Mono p := mono_of_mono p q
    have := SimplexCategory.len_le_of_mono p
    have := len_lt_of_degeneracy hp
    omega
  · intro hg
    refine ⟨image g, factorThruImage g, image.ι g, ⟨inferInstance, fun h => hg ?_⟩,
      image.fac g⟩
    rw [← image.fac g]
    infer_instance

abbrev StratifiedSSet : Type (u + 1) := MarkedPresheaf.{u} simplexMarking

namespace StratifiedSSet

@[simp]
theorem marked_zero (X : StratifiedSSet.{u}) : X.marked ⦋0⦌ = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx => (lt_irrefl 0) (X.markable ⦋0⦌ x hx)

theorem degenerate_subset_marked (X : StratifiedSSet.{u}) (n : ℕ) :
    SSet.degenerate X.underlying n ⊆ X.marked ⦋n⦌ := by
  intro x hx
  obtain ⟨m, hm, f, hf, y, rfl⟩ := (SSet.mem_degenerate_iff _ x).1 hx
  exact X.degenerate f ⟨hf, fun h => by
    have : n = m := SimplexCategory.len_eq_of_isIso f
    omega⟩ y

def ofThin (X : SSet.{u}) (T : ∀ n : ℕ, Set (X _⦋n⦌)) (h0 : T 0 = ∅)
    (hd : ∀ n, X.degenerate n ⊆ T n) : StratifiedSSet.{u} :=
  MarkedPresheaf.ofMarking X
    { marked n := T n.len
      markable := by
        rintro ⟨_ | k⟩ x hx
        · change x ∈ T 0 at hx
          rw [h0] at hx
          exact absurd hx (Set.notMem_empty x)
        · exact Nat.succ_pos k
      degenerate a b p hp y := hd a.len ⟨b.len, len_lt_of_degeneracy hp, p, y, rfl⟩
      transport a b e x := by
        obtain rfl : a = b := SimplexCategory.ext (SimplexCategory.len_eq_of_isIso e.hom)
        rw [SimplexCategory.eq_id_of_isIso e.hom, op_id, Functor.map_id_apply] }

@[simp]
theorem mem_marked_ofThin (X : SSet.{u}) (T : ∀ n : ℕ, Set (X _⦋n⦌)) (h0 : T 0 = ∅)
    (hd : ∀ n, X.degenerate n ⊆ T n) {n : ℕ} (x : X _⦋n⦌) :
    x ∈ (ofThin X T h0 hd).marked ⦋n⦌ ↔ x ∈ T n :=
  MarkedPresheaf.mem_marked_ofMarking _ _ _ _

@[simp]
theorem mem_marked_flat_iff_mem_degenerate (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌) :
    x ∈ ((MarkedPresheaf.flat simplexMarking).obj X).marked ⦋n⦌ ↔ x ∈ X.degenerate n := by
  rw [MarkedPresheaf.mem_marked_flat, SSet.mem_degenerate_iff]
  constructor
  · rintro ⟨b, p, hp, y, rfl⟩
    exact ⟨b.len, len_lt_of_degeneracy hp, p, hp.1, y, rfl⟩
  · rintro ⟨m, hm, f, hf, y, rfl⟩
    refine ⟨⦋m⦌, f, ⟨hf, fun h => ?_⟩, y, rfl⟩
    have : n = m := SimplexCategory.len_eq_of_isIso f
    omega

end StratifiedSSet

end Atoms.Homotopical
