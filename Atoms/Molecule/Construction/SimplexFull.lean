import Atoms.Molecule.Construction.SimplexMaps

open Finset Order

universe u

namespace Atoms.Molecule.OGP

private theorem simplexCell_singleton_le_iff (n : ℕ) {x : simplex.{u} n}
    {v : Fin (n + 1)} :
    simplexCell n {v} (singleton_nonempty v) ≤ x ↔ v ∈ simplexVertices n x := by
  rw [← simplexVertices_subset_iff, simplexVertices_simplexCell, singleton_subset_iff]

private theorem le_of_mem_boundary_zero_false {n : ℕ} {y w : simplex.{u} n}
    (hw : w ∈ (simplex.{u} n).boundary (.Iic y) 0 false)
    {t u : Fin (n + 1)} (ht : t ∈ simplexVertices n w) (hu : u ∈ simplexVertices n y) :
    t ≤ u := by
  obtain ⟨z, hz, hwz⟩ := mem_boundary.1 hw
  obtain ⟨hzzy, hzd, hzf⟩ := hz.resolve_right fun h => Nat.not_lt_zero _ h.2
  have hzy : z ≤ y := LowerSet.mem_Iic_iff.1 hzzy
  have hcz : (simplexVertices n z).card = 1 := by
    rw [card_simplexVertices, hzd]
  obtain ⟨t₀, ht₀⟩ := card_eq_one.1 hcz
  have htz : t ∈ simplexVertices n z := (simplexVertices_subset_iff n).2 hwz ht
  rw [ht₀, Finset.mem_singleton] at htz
  subst htz
  by_contra! hlt
  have hty : t ∈ simplexVertices n y :=
    (simplexVertices_subset_iff n).2 hzy (ht₀ ▸ Finset.mem_singleton_self t)
  set y' := simplexCell.{u} n {u, t} (insert_nonempty u {t})
  have hvy' : simplexVertices n y' = {u, t} := simplexVertices_simplexCell n _ _
  have hy'y : y' ≤ y := by
    rw [← simplexVertices_subset_iff, hvy']
    exact insert_subset hu (singleton_subset_iff.2 hty)
  have hzy' : simplexVertices n z = (simplexVertices n y').erase u := by
    rw [hvy', ht₀, erase_insert (by simpa using hlt.ne)]
  have hf := mem_faces_simplex_of_erase n (hvy' ▸ mem_insert_self u {t}) hzy'
  have hfil : (simplexVertices n y').filter (fun w => w < u) = ∅ := by
    rw [hvy', filter_insert, if_neg (lt_irrefl u), filter_singleton, if_neg (lt_asymm hlt)]
  rw [hfil, card_empty] at hf
  exact Set.disjoint_left.1 hzf hf hy'y

theorem simplexMap_injective {m n : ℕ} :
    Function.Injective (simplexMap.{u} : (Fin (m + 1) →o Fin (n + 1)) →
      simplex.{u} m → simplex.{u} n) := by
  intro f f' h
  ext i
  have hc := congrArg (simplexVertices n)
    (congrFun h (simplexCell.{u} m {i} (singleton_nonempty i)))
  rw [simplexVertices_simplexMap, simplexVertices_simplexMap, simplexVertices_simplexCell,
    Finset.image_singleton, Finset.image_singleton, singleton_inj] at hc
  exact congrArg Fin.val hc

theorem exists_simplexMap_eq_of_isMap {m n : ℕ}
    {p : simplex.{u} m → simplex.{u} n} (hp : IsMap p) :
    ∃ f : Fin (m + 1) →o Fin (n + 1), p = simplexMap f := by
  let c : Fin (m + 1) → simplex.{u} m := fun i => simplexCell m {i} (singleton_nonempty i)
  have hc : ∀ i, simplexVertices m (c i) = {i} := fun i => simplexVertices_simplexCell m _ _
  let g : Fin (m + 1) → Fin (n + 1) := fun i =>
    (simplexVertices n (p (c i))).min' (simplexVertices_nonempty n _)
  have hg : ∀ i, simplexVertices n (p (c i)) = {g i} := by
    intro i
    have hd := hp.grade_le (c i)
    have h1 := card_simplexVertices m (c i)
    rw [hc, card_singleton] at h1
    have h2 := card_simplexVertices n (p (c i))
    obtain ⟨a, ha⟩ := card_eq_one.1 (by omega : (simplexVertices n (p (c i))).card = 1)
    have hga : g i = a := by simp only [g, ha, min'_singleton]
    rw [ha, hga]
  have himage : ∀ x, simplexVertices n (p x) = (simplexVertices m x).image g := by
    intro x
    ext t
    rw [Finset.mem_image]
    constructor
    · intro ht
      have hle := (simplexCell_singleton_le_iff n).2 ht
      have hmem : simplexCell n {t} (singleton_nonempty t) ∈ p '' Set.Iic x := by
        rw [hp.image_Iic x]
        exact hle
      obtain ⟨y, hy, hpy⟩ := Set.mem_image _ _ _ |>.1 hmem
      obtain ⟨v, hv⟩ := simplexVertices_nonempty m y
      have hvy : c v ≤ y := (simplexCell_singleton_le_iff m).2 hv
      refine ⟨v, (simplexVertices_subset_iff m).2 hy hv, ?_⟩
      have hsub := (simplexVertices_subset_iff n).2 ((hp.monotone hvy).trans hpy.le)
      rwa [hg, simplexVertices_simplexCell, singleton_subset_iff, Finset.mem_singleton] at hsub
    · rintro ⟨v, hv, rfl⟩
      have hsub := (simplexVertices_subset_iff n).2
        (hp.monotone ((simplexCell_singleton_le_iff m).2 hv))
      rwa [hg, singleton_subset_iff] at hsub
  have hmono : Monotone g := by
    intro i j hij
    by_contra! hlt
    have hne : i ≠ j := ne_of_apply_ne g hlt.ne'
    have hij' : i < j := lt_of_le_of_ne hij hne
    set e := simplexCell.{u} m {i, j} (insert_nonempty i {j})
    have hve : simplexVertices m e = {i, j} := simplexVertices_simplexCell m _ _
    have hcie : simplexVertices m (c i) = (simplexVertices m e).erase j := by
      rw [hc, hve, erase_insert_of_ne hne, erase_singleton, insert_empty]
    have hf := mem_faces_simplex_of_erase m (hve ▸ mem_insert_of_mem (mem_singleton_self j)) hcie
    have hfil : (simplexVertices m e).filter (fun w => w < j) = {i} := by
      rw [hve, filter_insert, if_pos hij', filter_singleton, if_neg (lt_irrefl j), insert_empty]
    rw [hfil, card_singleton] at hf
    have hge : grade ℕ e = 0 + 1 := by
      have hc2 := card_simplexVertices m e
      rw [hve, card_pair hne] at hc2
      omega
    have hbd : c i ∈ (simplex m).boundary (.Iic e) 0 false := by
      rw [boundary_Iic hge]
      exact subset_lowerClosure hf
    have hbd' : p (c i) ∈ (simplex n).boundary (.Iic (p e)) 0 false := by
      rw [← SetLike.mem_coe, ← hp.image_boundary e 0 false]
      exact Set.mem_image_of_mem p hbd
    have hgj : g j ∈ simplexVertices n (p e) := by
      rw [himage, hve]
      exact Finset.mem_image_of_mem g (mem_insert_of_mem (Finset.mem_singleton_self j))
    exact not_le.2 hlt (le_of_mem_boundary_zero_false hbd' (hg i ▸ mem_singleton_self _) hgj)
  exact ⟨⟨g, hmono⟩, funext fun x => ((simplexMap_eq_iff _ x (p x)).2 (himage x)).symm⟩

end Atoms.Molecule.OGP
