import Atoms.Molecule.Construction.GrayProductMap
import Atoms.Molecule.Construction.Suspension

universe u

open CategoryTheory Order Set Topology

namespace Atoms.Molecule.OGP

open SuspCarrier

variable {U : OGP.{u}}

abbrev cylEndpoint (ε : Bool) (U : OGP.{u}) : U ⟶ grayProduct (globe 1) U :=
  grayProduct.inr (isMin_pole ε)

theorem isRDC_globe_one : IsRDC (globe.{u} 1) :=
  isRDC_globe 1

private theorem exists_mem_boundary_zero_globe_one (v : globe.{u} 1) (α : Bool) :
    ∃ b : globe.{u} 1, b ∈ (globe.{u} 1).boundary (.Iic v) 0 α := by
  rcases v with β | ⟨⟨⟩⟩
  · refine ⟨pole β, ?_⟩
    have h0 : krullDim (LowerSet.Iic (pole β : globe.{u} 1)) ≤ 0 := by
      rw [LowerSet.krullDim_Iic, grade_pole]
      rfl
    rw [boundary_eq_self h0 α]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  · refine ⟨pole α, ?_⟩
    have htop : (LowerSet.Iic (⊤ : globe.{u} 1)) = ⊤ := LowerSet.Iic_top
    rw [susp_unit_eq_top_globe_one, htop, boundary_zero_globe_one]
    exact LowerSet.mem_Iic_iff.2 le_rfl

theorem zigZag_snd_grayProduct_globe_one (hU : IsRDC U)
    (v : globe.{u} 1) (x : U) (n : ℕ) (α : Bool) {b b' : globe.{u} 1} {w : U}
    (hy : ((b, w) : grayProduct (globe.{u} 1) U) ∈
      (grayProduct (globe.{u} 1) U).boundary (.Iic (v, x)) n α)
    (hz : ((b', w) : grayProduct (globe.{u} 1) U) ∈
      (grayProduct (globe.{u} 1) U).boundary (.Iic (v, x)) n α) :
    Relation.ReflTransGen (fun p q : grayProduct (globe.{u} 1) U =>
      p ∈ ((grayProduct (globe.{u} 1) U).boundary (.Iic (v, x)) n α :
        Set (grayProduct (globe.{u} 1) U)) ∩ Prod.snd ⁻¹' Ici w ∧
      q ∈ ((grayProduct (globe.{u} 1) U).boundary (.Iic (v, x)) n α :
        Set (grayProduct (globe.{u} 1) U)) ∩ Prod.snd ⁻¹' Ici w ∧
      (p ≤ q ∨ q ≤ p)) (b, w) (b', w) := by
  have hG : IsRDC (globe.{u} 1) := isRDC_globe_one
  rcases v with β | ⟨⟨⟩⟩
  · have hb : b = pole β := (isMin_pole β).eq_of_le (boundary_le _ n α hy).1
    have hb' : b' = pole β := (isMin_pole β).eq_of_le (boundary_le _ n α hz).1
    rw [hb, hb']
  by_cases hbb : b = b'
  · rw [hbb]
  change ((b, w) : grayProduct (globe.{u} 1) U) ∈
    (grayProduct (globe.{u} 1) U).boundary (.Iic (⊤, x)) n α at hy
  change ((b', w) : grayProduct (globe.{u} 1) U) ∈
    (grayProduct (globe.{u} 1) U).boundary (.Iic (⊤, x)) n α at hz
  have htop : (LowerSet.Iic (⊤ : globe.{u} 1)) = ⊤ := LowerSet.Iic_top
  have key (c : globe.{u} 1)
      (hc : ((c, w) : grayProduct (globe.{u} 1) U) ∈
        (grayProduct (globe.{u} 1) U).boundary (.Iic (⊤, x)) n α) :
      c = pole α ∨ ((⊤, w) : grayProduct (globe.{u} 1) U) ∈
        (grayProduct (globe.{u} 1) U).boundary (.Iic (⊤, x)) n α := by
    obtain ⟨k, hk, hck, hw⟩ :=
      (mem_boundary_Iic_grayProduct hG hU ⊤ x n α c w).1 hc
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [htop, boundary_zero_globe_one] at hck
      exact Or.inl ((isMin_pole α).eq_of_le hck)
    · refine Or.inr ((mem_boundary_Iic_grayProduct hG hU ⊤ x n α ⊤ w).2
        ⟨k, hk, ?_, hw⟩)
      have h1 : krullDim (LowerSet.Iic (⊤ : globe.{u} 1)) ≤ k := by
        rw [LowerSet.krullDim_Iic, grade_top_globe]
        exact_mod_cast hpos
      rw [boundary_eq_self h1 α]
      exact LowerSet.mem_Iic_iff.2 le_rfl
  have hmid : ((⊤, w) : grayProduct (globe.{u} 1) U) ∈
      (grayProduct (globe.{u} 1) U).boundary (.Iic (⊤, x)) n α :=
    (key b hy).elim (fun hb => (key b' hz).resolve_left fun hb' => hbb (hb.trans hb'.symm)) id
  have hle (c : globe.{u} 1) : ((c, w) : grayProduct (globe.{u} 1) U) ≤ (⊤, w) :=
    Prod.mk_le_mk.2 ⟨le_top (a := c), le_rfl⟩
  exact (Relation.ReflTransGen.single
      ⟨⟨hy, le_rfl⟩, ⟨hmid, le_rfl⟩, Or.inl (hle b)⟩).tail
    ⟨⟨hmid, le_rfl⟩, ⟨hz, le_rfl⟩, Or.inr (hle b')⟩

theorem isMap_snd_grayProduct_globe_one (hU : IsRDC U) :
    IsMap (P := grayProduct (globe.{u} 1) U) (Q := U) Prod.snd := by
  have hG : IsRDC (globe.{u} 1) := isRDC_globe_one
  refine ⟨isClosedMap_snd_grayProduct, fun ⟨v, x⟩ n α =>
    finalOn_of_fibration isClosedMap_snd_grayProduct ?_ ?_⟩
  · ext y
    constructor
    · rintro ⟨⟨b, y'⟩, hby, rfl⟩
      obtain ⟨k, hk, -, hy⟩ := (mem_boundary_Iic_grayProduct hG hU v x n α b y').1 hby
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simpa using hy
      · exact (hU x).isGlobular.boundary_le_boundary (by omega) _ α hy
    · intro hy
      obtain ⟨b, hb⟩ := exists_mem_boundary_zero_globe_one v α
      exact ⟨(b, y), (mem_boundary_Iic_grayProduct hG hU v x n α b y).2
        ⟨0, Nat.zero_le n, hb, by simpa using hy⟩, rfl⟩
  · rintro ⟨b, w⟩ hy ⟨b', w'⟩ hz h
    change w = w' at h
    subst h
    exact zigZag_snd_grayProduct_globe_one hU v x n α hy hz

instance functor_isFibered_snd_grayProduct {P U : OGP.{u}}
    (hm : Monotone (α := grayProduct P U) (β := U) Prod.snd) :
    hm.functor.IsFibered := by
  refine (Monotone.functor_isFibered_iff _).2 ?_
  rintro ⟨v, x⟩ y hy
  exact ⟨(v, y), Prod.mk_le_mk.2 ⟨le_rfl, hy⟩, rfl,
    fun ⟨_, _⟩ hle hx' => Prod.mk_le_mk.2 ⟨hle.1, hx'⟩⟩

end Atoms.Molecule.OGP
