import Atoms.Molecule.Cylinder.InvertedMolecule

universe u

open Order Set

namespace Atoms.Molecule.OGP.InvertedCylinder

open PartialCylinder

variable {U : OGP.{u}} {K : LowerSet U} {ε : Bool} {n : ℕ}

section Atom

variable (hU : IsAtom U) (hn : krullDim U = n) (hd : 0 < n) (hKU : K ≤ U.bdry ⊤ ε)
  {t : U} (ht : ∀ x, x ≤ t)

include hKU ht in
theorem top_notMem_K : t ∉ K := fun h => by
  have hIic : LowerSet.Iic t = ⊤ := top_unique fun x _ => ht x
  have h1 := grade_lt_of_mem_bdry (hKU h)
  rw [← hIic, LowerSet.krullDim_Iic] at h1
  exact lt_irrefl _ h1

include hn ht in
private theorem grade_top_eq : grade ℕ t = n := by
  have h1 := LowerSet.krullDim_Iic t
  rw [show LowerSet.Iic t = ⊤ from top_unique fun x _ => ht x, LowerSet.krullDim_top, hn] at h1
  exact_mod_cast h1.symm

include hn ht in
theorem std_eq_erase (htK : t ∉ K) :
    (std K ε n : Set (partialCylinder U K)) =
      (Set.univ \ {mkI K none t htK}) \ {mkI K (some ε) t htK} := by
  have hdt := grade_top_eq hn ht
  have hle (x : U) : n ≤ grade ℕ x ↔ x = t :=
    ⟨fun hx => GradeOrder.eq_of_le_of_grade_le (ht x) (hdt ▸ hx), fun hx => hx ▸ hdt.ge⟩
  ext a
  simp only [SetLike.mem_coe, mem_std, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
  rcases a with ⟨x, hx⟩ | ⟨⟨_ | β⟩, ⟨x, hx⟩⟩
  · exact iff_of_true rfl ⟨Sum.inl_ne_inr, Sum.inl_ne_inr⟩
  · have hne : (mkI K none x hx : partialCylinder U K) ≠ mkI K (some ε) t htK :=
      fun h => by cases h
    change decide (n ≤ grade ℕ x) = false ↔ _
    rw [decide_eq_false_iff_not, hle]
    exact ⟨fun h => ⟨fun he => h (by cases he; rfl), hne⟩,
      fun ⟨h, _⟩ hx' => h (by subst hx'; rfl)⟩
  · have hne : (mkI K (some β) x hx : partialCylinder U K) ≠ mkI K none t htK :=
      fun h => by cases h
    change decide (β = ε ∧ n ≤ grade ℕ x) = false ↔ _
    rw [decide_eq_false_iff_not, hle]
    exact ⟨fun h => ⟨hne, fun he => h (by cases he; exact ⟨rfl, rfl⟩)⟩,
      fun ⟨_, h⟩ ⟨rfl, rfl⟩ => h rfl⟩

include hKU ht in
theorem le_mkI_none_top (a : partialCylinder U K) :
    a ≤ mkI K none t (top_notMem_K hKU ht) :=
  le_mkI_none_of_proj_le _ (ht _)

include hn hKU ht in
theorem mkI_some_top_mem_faceSet_top (β : Bool) :
    mkI K (some β) t (top_notMem_K hKU ht) ∈
      (invertedCylinder U K ε n).faces (!ε) (mkI K none t (top_notMem_K hKU ht)) :=
  ⟨(covBy_mkI_some_mkI_none β _ _).2 rfl, orient_mkI_none_mkI_some_top _ (grade_top_eq hn ht) β _⟩

include hU hn hd hKU ht in
theorem hornSet_closure_mkI_some_top :
    ((invertedCylinder U K ε n).bdryFull ⊤ : Set (invertedCylinder U K ε n)) \
        (invertedCylinder U K ε n).interior
          (LowerSet.Iic (mkI K (some ε) t (top_notMem_K hKU ht))) =
      std K ε n := by
  have htK := top_notMem_K hKU ht
  have hW : IsAtom (invertedCylinder U K ε n) := isAtom_invertedCylinder hU hn hd hKU
  have hx : IsMoleculeIn (invertedCylinder U K ε n) (LowerSet.Iic (mkI K (some ε) t htK)) :=
    (hW.1.isAtomIn_Iic LowerSet.mem_top).1
  have hIic : LowerSet.Iic (mkI K none t htK) = (⊤ : LowerSet (invertedCylinder U K ε n)) :=
    top_unique fun a _ => le_mkI_none_top hKU ht a
  have hbdry : ((invertedCylinder U K ε n).bdryFull ⊤ : Set (partialCylinder U K)) =
      Set.univ \ {mkI K none t htK} := by
    rw [← hIic, bdryFull, coe_bdry_Iic_sup]
    ext a
    simp only [Set.mem_Iio, Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and,
      lt_iff_le_and_ne]
    exact and_iff_right (le_mkI_none_top hKU ht a)
  rw [hbdry, hx.interior_Iic, std_eq_erase hn ht htK]

end Atom

end Atoms.Molecule.OGP.InvertedCylinder
