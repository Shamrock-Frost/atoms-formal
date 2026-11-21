import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.Gluing.Basic
import Atoms.Molecule.Rigidity

universe u

open CategoryTheory Limits

namespace Atoms.Molecule.OGP

variable {U V W W' : OGP.{u}} {k : ℕ}

abbrev PastingIso (U V : OGP.{u}) (k : ℕ) : Type u :=
  U.restrict (U.boundary ⊤ k true) ≅ V.restrict (V.boundary ⊤ k false)

theorem subsingleton_pastingIso (hU : U.IsMolecule) : Subsingleton (PastingIso U V k) :=
  IsMolecule.subsingleton_iso ((isMolecule_restrict_iff _).2 (hU.boundary k true))

theorem IsPasting.of_iso (h : IsPasting U V k W) (e : W ≅ W') : IsPasting U V k W' := by
  obtain ⟨i, j, _, _, hp⟩ := h
  have hp' := (isPastingIn_map_iff e.hom k _ _ ⊤).2 hp
  rw [map_top_of_isIso e.hom, ← map_comp, ← map_comp] at hp'
  exact ⟨i ≫ e.hom, j ≫ e.hom, inferInstance, inferInstance, hp'⟩

theorem IsPastingIn.isPasting_restrict {P : OGP.{u}} {A B C : LowerSet P}
    (hp : P.IsPastingIn k A B C) : IsPasting (P.restrict A) (P.restrict B) k (P.restrict C) := by
  refine ⟨codRestrict (incl A) C fun x => hp.left_le x.2,
    codRestrict (incl B) C fun x => hp.right_le x.2, inferInstance, inferInstance, ?_⟩
  rw [← isPastingIn_map_iff (incl C), ← map_comp, ← map_comp, codRestrict_incl, codRestrict_incl,
    map_incl_top, map_incl_top, map_incl_top]
  exact hp

section GluingIso

variable {i : U ⟶ W} {j : V ⟶ W} [IsInclusion i] [IsInclusion j]
  (hp : W.IsPastingIn k (map i ⊤) (map j ⊤) ⊤)
include hp

theorem IsPastingIn.map_boundary_eq :
    map i (U.boundary ⊤ k true) = map j (V.boundary ⊤ k false) := by
  rw [map_boundary, map_boundary, ← hp.inf_eq_output, hp.inf_eq_input]

theorem IsPastingIn.exists_isPushout : ∃ ψ : PastingIso U V k,
    (∀ x, j (ψ.hom x).1 = i x.1) ∧ IsPushout (incl _) (ψ.hom ≫ incl _) i j := by
  obtain ⟨eU, heU⟩ := exists_iso_restrict_map i (U.boundary ⊤ k true)
  obtain ⟨eV, heV⟩ := exists_iso_restrict_map j (V.boundary ⊤ k false)
  obtain ⟨e, he⟩ := exists_iso_restrict (incl (map i (U.boundary ⊤ k true)))
    (by rw [map_incl_top, hp.map_boundary_eq])
  have key (x : U.restrict (U.boundary ⊤ k true)) :
      j ((eU ≪≫ e ≪≫ eV.symm).hom x).1 = i x.1 := by
    have hV (z : V.restrict (V.boundary ⊤ k false)) : (eV.hom z : W) = j z.1 :=
      ConcreteCategory.congr_hom heV z
    have hE (z : W.restrict (map i (U.boundary ⊤ k true))) : (e.hom z : W) = z.1 :=
      ConcreteCategory.congr_hom he z
    have hU : (eU.hom x : W) = i x.1 := ConcreteCategory.congr_hom heU x
    rw [← hU, ← hE, ← Iso.inv_hom_id_apply eV (e.hom (eU.hom x)), hV]
    rfl
  exact ⟨eU ≪≫ e ≪≫ eV.symm, key, isPushout_of_cover i j (by ext x; exact (key x).symm)
    hp.sup_eq (by rw [hp.inf_eq_output, map_comp, map_incl_top, map_boundary])⟩

end GluingIso

theorem exists_iso_of_cover_pair {P Q A B : OGP.{u}}
    (i₀ : P ⟶ A) (j₀ : Q ⟶ A) [IsInclusion i₀] [IsInclusion j₀]
    (i' : P ⟶ B) (j' : Q ⟶ B) [IsInclusion i'] [IsInclusion j']
    (hcov₀ : map i₀ ⊤ ⊔ map j₀ ⊤ = ⊤) (hcov' : map i' ⊤ ⊔ map j' ⊤ = ⊤)
    (hc : ∀ x y, i₀ x = j₀ y ↔ i' x = j' y) :
    ∃ Θ : A ≅ B, i₀ ≫ Θ.hom = i' ∧ j₀ ≫ Θ.hom = j' ∧
      i' ≫ Θ.inv = i₀ ∧ j' ≫ Θ.inv = j₀ := by
  let S : LowerSet P := comap i₀ (map j₀ ⊤)
  let T : LowerSet Q := comap j₀ (map i₀ ⊤)
  have hS : map i₀ S = map i₀ ⊤ ⊓ map j₀ ⊤ := by
    refine SetLike.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, LowerSet.mem_top, rfl⟩, hx⟩
    · rintro ⟨⟨x, -, rfl⟩, hz⟩
      exact ⟨x, hz, rfl⟩
  have hT : map j₀ T = map i₀ ⊤ ⊓ map j₀ ⊤ := by
    refine SetLike.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, ⟨y, LowerSet.mem_top, rfl⟩⟩
    · rintro ⟨hz, ⟨y, -, rfl⟩⟩
      exact ⟨y, hz, rfl⟩
  obtain ⟨eP, heP⟩ := exists_iso_restrict_map i₀ S
  obtain ⟨eQ, heQ⟩ := exists_iso_restrict_map j₀ T
  obtain ⟨eM, heM⟩ := exists_iso_restrict (incl (map i₀ S))
    (by rw [map_incl_top, hS, ← hT])
  let φ : P.restrict S ≅ Q.restrict T := eP ≪≫ eM ≪≫ eQ.symm
  have hφ₀ (s : P.restrict S) : j₀ (φ.hom s).1 = i₀ s.1 := by
    have h1 (z : Q.restrict T) : (eQ.hom z : A) = j₀ z.1 := ConcreteCategory.congr_hom heQ z
    have h2 (z : A.restrict (map i₀ S)) : (eM.hom z : A) = z.1 :=
      ConcreteCategory.congr_hom heM z
    have h3 : (eP.hom s : A) = i₀ s.1 := ConcreteCategory.congr_hom heP s
    rw [← h3, ← h2, ← Iso.inv_hom_id_apply eQ (eM.hom (eP.hom s)), h1]
    rfl
  have hφ' (s : P.restrict S) : j' (φ.hom s).1 = i' s.1 :=
    ((hc s.1 (φ.hom s).1).1 (hφ₀ s).symm).symm
  have hinf₀ : map i₀ ⊤ ⊓ map j₀ ⊤ = map (incl S ≫ i₀) ⊤ := by
    rw [map_comp, map_incl_top, hS]
  have hinf' : map i' ⊤ ⊓ map j' ⊤ = map (incl S ≫ i') ⊤ := by
    rw [map_comp, map_incl_top]
    refine SetLike.ext fun z => ⟨?_, ?_⟩
    · rintro ⟨⟨x, -, rfl⟩, ⟨y, -, hy⟩⟩
      exact ⟨x, ⟨y, LowerSet.mem_top, ((hc x y).2 hy.symm).symm⟩, rfl⟩
    · rintro ⟨x, ⟨y, -, hy⟩, rfl⟩
      exact ⟨⟨x, LowerSet.mem_top, rfl⟩, ⟨y, LowerSet.mem_top, ((hc x y).1 hy.symm).symm⟩⟩
  have hp₀ := isPushout_of_cover i₀ j₀ (by ext s; exact (hφ₀ s).symm) hcov₀ hinf₀
  have hp' := isPushout_of_cover i' j' (by ext s; exact (hφ' s).symm) hcov' hinf'
  exact ⟨hp₀.isoIsPushout _ _ hp', hp₀.inl_isoIsPushout_hom _ _ hp',
    hp₀.inr_isoIsPushout_hom _ _ hp', hp₀.inl_isoIsPushout_inv _ _ hp',
    hp₀.inr_isoIsPushout_inv _ _ hp'⟩

theorem IsPasting.nonempty_iso (hU : U.IsMolecule) (hW : IsPasting U V k W)
    (hW' : IsPasting U V k W') : Nonempty (W ≅ W') := by
  obtain ⟨i, j, _, _, hp⟩ := hW
  obtain ⟨i', j', _, _, hp'⟩ := hW'
  obtain ⟨ψ, -, h⟩ := hp.exists_isPushout
  obtain ⟨ψ', -, h'⟩ := hp'.exists_isPushout
  have := subsingleton_pastingIso (V := V) (k := k) hU
  obtain rfl := Subsingleton.elim ψ ψ'
  exact ⟨h.isoIsPushout _ _ h'⟩

theorem apply_eq_apply_iff_of_isPastingIn_of_isMolecule (hU : U.IsMolecule) {i : U ⟶ W}
    {j : V ⟶ W} [IsInclusion i] [IsInclusion j] {i' : U ⟶ W'} {j' : V ⟶ W'} [IsInclusion i']
    [IsInclusion j'] (hp : W.IsPastingIn k (map i ⊤) (map j ⊤) ⊤)
    (hp' : W'.IsPastingIn k (map i' ⊤) (map j' ⊤) ⊤) (x : U) (y : V) :
    i x = j y ↔ i' x = j' y := by
  obtain ⟨ψ, hψ, -⟩ := hp.exists_isPushout
  obtain ⟨ψ', hψ', -⟩ := hp'.exists_isPushout
  have := subsingleton_pastingIso (V := V) (k := k) hU
  obtain rfl := Subsingleton.elim ψ ψ'
  have key {W₀ : OGP.{u}} {i₀ : U ⟶ W₀} {j₀ : V ⟶ W₀} [IsInclusion i₀] [IsInclusion j₀]
      (hp₀ : W₀.IsPastingIn k (map i₀ ⊤) (map j₀ ⊤) ⊤)
      (hψ₀ : ∀ s : U.restrict (U.boundary ⊤ k true), j₀ (ψ.hom s).1 = i₀ s.1) :
      i₀ x = j₀ y ↔ ∃ hx : x ∈ U.boundary ⊤ k true, (ψ.hom ⟨x, hx⟩).1 = y := by
    refine ⟨fun hxy => ?_, fun ⟨hx, hy⟩ => (hψ₀ ⟨x, hx⟩).symm.trans (congrArg j₀ hy)⟩
    have hm : i₀ x ∈ map i₀ (U.boundary ⊤ k true) := by
      rw [map_boundary, ← hp₀.inf_eq_output]
      exact ⟨⟨x, LowerSet.mem_top, rfl⟩, ⟨y, LowerSet.mem_top, hxy.symm⟩⟩
    have hx : x ∈ U.boundary ⊤ k true := (apply_mem_map_iff i₀).1 hm
    exact ⟨hx, IsInclusion.injective (f := j₀) ((hψ₀ ⟨x, hx⟩).trans hxy)⟩
  exact (key hp hψ).trans (key hp' hψ').symm

theorem exists_isPasting_unique (hU : U.IsMolecule) (φ : PastingIso U V k) :
    ∃ W, IsPasting U V k W ∧ ∀ W', IsPasting U V k W' → Nonempty (W ≅ W') :=
  ⟨_, isPasting_glue U V k φ, fun _ => (isPasting_glue U V k φ).nonempty_iso hU⟩

end Atoms.Molecule.OGP
