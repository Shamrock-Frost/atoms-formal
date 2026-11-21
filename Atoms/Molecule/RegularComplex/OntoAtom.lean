import Atoms.Molecule.RegularComplex.Morphism
import Atoms.Molecule.Layering

universe u v

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

variable {P : OGP.{u}} {Q : OGP.{v}} {f : P → Q}

theorem exists_mem_facesIn_mem_cofaces {N : LowerSet P} (hN : IsMoleculeIn P N) {k : ℕ}
    (htop : ∃! t : P, Maximal (· ∈ N) t ∧ k < grade ℕ t) (β : Bool) :
    ∃ x y, x ∈ P.facesIn N k β ∧ y ∈ N ∧ y ∈ P.cofaces β x := by
  obtain ⟨t, ⟨htM, htk⟩, hu⟩ := htop
  have hA := hN.isAtomIn_Iic htM.prop
  have hkt : (k : WithBot ℕ∞) ≤ krullDim (LowerSet.Iic t) := by
    rw [LowerSet.krullDim_Iic]; exact_mod_cast htk.le
  obtain ⟨⟨x, hxB⟩, hxd⟩ := exists_grade_eq_of_krullDim_eq (hA.isMoleculeIn.krullDim_boundary hkt β)
  replace hxd : grade ℕ x = k := hxd
  have hxF : x ∈ P.facesIn (LowerSet.Iic t) k β := mem_facesIn_of_mem_boundary hxB hxd
  obtain ⟨hxt, -, hdisj⟩ := hxF
  obtain ⟨y, hxy, hyt⟩ := exists_covBy_le_of_lt (lt_of_le_of_ne hxt fun e => by
    subst e; omega)
  have hyo : P.orient hxy = β := by
    by_contra hne
    exact Set.disjoint_left.1 hdisj ⟨hxy, by rw [Bool.eq_not_of_ne hne]⟩ hyt
  refine ⟨x, y, ⟨N.lower hxt htM.prop, hxd, Set.disjoint_left.2 fun w ⟨hxw, hwo⟩ hw => ?_⟩,
    N.lower hyt htM.prop, hxy, hyo⟩
  obtain ⟨m, hwm, hm⟩ := hN.exists_le_maximal hw
  have hwd := Nat.covBy_iff_add_one_eq.1 (hxw.grade ℕ)
  obtain rfl : m = t := hu m ⟨hm, by have := grade_mono (𝕆 := ℕ) hwm; omega⟩
  exact Set.disjoint_left.1 hdisj ⟨hxw, hwo⟩ hwm

theorem IsMorphism.not_image_boundary_subset_boundary (hf : IsMorphism f) {N : LowerSet P}
    {V : LowerSet Q} (hN : IsMoleculeIn P N) {k : ℕ}
    (htop : ∃! t : P, Maximal (· ∈ N) t ∧ k < grade ℕ t) (hNV : f '' (N : Set P) ⊆ V)
    (α : Bool) : ¬ f '' P.boundary N k (!α) ⊆ Q.boundary V k α := by
  intro hsub
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_mem_facesIn_mem_cofaces hN htop (!α)
  have hfx := hsub (mem_image_of_mem f (mem_boundary_of_mem_facesIn hx le_rfl))
  obtain ⟨-, -, hdisj⟩ :=
    mem_facesIn_of_mem_boundary hfx (by rw [hf.grade_eq]; exact hx.2.1)
  exact Set.disjoint_left.1 hdisj ((hf.bijOn_faces y (!α)).mapsTo hxy)
    (hNV (mem_image_of_mem f hy))

section Layering

variable {k : ℕ} {U : LowerSet P} {L : List (LowerSet P)}

theorem IsMorphism.eq_zero_of_isLayering (hf : IsMorphism f) (h : IsLayering P k U L)
    {V : LowerSet Q} (hUV : f '' (U : Set P) ⊆ V) {i : ℕ} (hi : i < L.length)
    (hb : f '' P.boundary (L.getD i ⊥) k false ⊆ Q.boundary V k false) : i = 0 := by
  obtain _ | j := i
  · rfl
  rw [h.boundary_false_getD_succ hi] at hb
  exact absurd hb (hf.not_image_boundary_subset_boundary (h.isMoleculeIn_getD (by omega))
    (h.existsUnique_top_getD (by omega)) ((image_mono (h.le (by omega))).trans hUV) false)

theorem IsMorphism.eq_length_sub_one_of_isLayering (hf : IsMorphism f) (h : IsLayering P k U L)
    {V : LowerSet Q} (hUV : f '' (U : Set P) ⊆ V) {i : ℕ} (hi : i < L.length)
    (hb : f '' P.boundary (L.getD i ⊥) k true ⊆ Q.boundary V k true) : i = L.length - 1 := by
  by_contra hne
  have hi' : i + 1 < L.length := by omega
  rw [← h.boundary_false_getD_succ hi'] at hb
  exact hf.not_image_boundary_subset_boundary (h.isMoleculeIn_getD hi')
    (h.existsUnique_top_getD hi') ((image_mono (h.le hi')).trans hUV) true hb

end Layering

theorem IsMorphism.isAtomIn_of_isMoleculeIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) : P.IsAtomIn U := by
  classical
  suffices key : ∀ N (U : LowerSet P) (hU : IsMoleculeIn P U), f '' (U : Set P) ⊆ V →
      krullDim U = krullDim V → P.layeringDim U hU ≤ N → P.IsAtomIn U from
    key _ U hU hUV hd le_rfl
  intro N
  induction N with
  | zero =>
    intro U hU _ _ h0
    exact (layeringDim_eq_zero_iff hU).1 (Nat.le_zero.1 h0)
  | succ k ih =>
    intro U hU hUV hd hk
    by_cases hle : P.layeringDim U hU ≤ k
    · exact ih U hU hUV hd hle
    obtain ⟨n, hn⟩ := hU.exists_krullDim_eq
    have hkn : k + 1 ≤ n := (Nat.lt_of_not_le hle).trans_le (layeringDim_le_of_krullDim_le hU hn.le)
    have hkU : (k : WithBot ℕ∞) < krullDim U := by rw [hn]; exact_mod_cast (by omega)
    obtain ⟨L, hL⟩ := admitsLayering_of_layeringDim_le hU hk hkU
    have hlen : 1 < L.length := (hL.one_lt_length_iff).2 (by omega)
    obtain ⟨⟨x, hxU⟩, hxd⟩ := exists_grade_eq_of_krullDim_eq hn
    replace hxd : grade ℕ x = n := hxd
    obtain ⟨i, hi, hxi⟩ := hL.exists_mem_getD hxU
    have hdi : krullDim (L.getD i ⊥) = krullDim V := by
      refine le_antisymm ((LowerSet.krullDim_mono (hL.le hi)).trans hd.le) ?_
      rw [← hd, hn, ← hxd]
      exact grade_le_krullDim (⟨x, hxi⟩ : ↥(L.getD i ⊥))
    have hiV : f '' (L.getD i ⊥ : Set P) ⊆ V := (image_mono (hL.le hi)).trans hUV
    have hA : P.IsAtomIn (L.getD i ⊥) := ih _ (hL.isMoleculeIn_getD hi) hiV hdi
      (hL.layeringDim_le (getD_mem_of_lt_length hi))
    have hki : (k : WithBot ℕ∞) < krullDim (L.getD i ⊥) := by rw [hdi, ← hd]; exact hkU
    have h0 := hf.eq_zero_of_isLayering hL hUV hi
      (hf.image_boundary_of_isAtomIn hA hV hiV hdi hki false).subset
    have h1 := hf.eq_length_sub_one_of_isLayering hL hUV hi
      (hf.image_boundary_of_isAtomIn hA hV hiV hdi hki true).subset
    omega

theorem IsMorphism.injOn_of_isMoleculeIn_of_isAtomIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) : Set.InjOn f U := fun _ hx _ hy h =>
  hf.eq_of_apply_eq_of_isAtomIn (hf.isAtomIn_of_isMoleculeIn hU hV hUV hd) hV hUV hd hx hy h

theorem IsMorphism.image_eq_of_isMoleculeIn_of_isAtomIn (hf : IsMorphism f) {U : LowerSet P}
    {V : LowerSet Q} (hU : IsMoleculeIn P U) (hV : Q.IsAtomIn V) (hUV : f '' (U : Set P) ⊆ V)
    (hd : krullDim U = krullDim V) : f '' (U : Set P) = V :=
  hf.image_eq_of_isAtomIn (hf.isAtomIn_of_isMoleculeIn hU hV hUV hd) hV hUV hd

theorem isIso_of_isMolecule_of_isAtom {P Q : OGP.{u}} (f : P ⟶ Q) (hP : P.IsMolecule)
    (hQ : Q.IsAtom) (hd : krullDim (⊤ : LowerSet P) = krullDim (⊤ : LowerSet Q)) : IsIso f := by
  have hUV : f '' ((⊤ : LowerSet P) : Set P) ⊆ (⊤ : LowerSet Q) := fun _ _ => LowerSet.mem_top
  have himg := (isMorphism f).image_eq_of_isMoleculeIn_of_isAtomIn hP hQ hUV hd
  refine (isIso_iff_bijective f).2 ⟨fun x y h => ?_, fun y => ?_⟩
  · exact (isMorphism f).injOn_of_isMoleculeIn_of_isAtomIn hP hQ hUV hd LowerSet.mem_top
      LowerSet.mem_top h
  · obtain ⟨x, -, hx⟩ := (Set.ext_iff.1 himg y).2 LowerSet.mem_top
    exact ⟨x, hx⟩

end Atoms.Molecule.OGP
