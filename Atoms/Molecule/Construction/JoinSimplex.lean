import Atoms.Molecule.Construction.Join
import Atoms.Molecule.MoleculeShape.Basic
import Atoms.Molecule.Vertex

universe u

open Order

namespace Atoms.Molecule

open OGP

namespace OGP

theorem boundary_zero_true_inf_false_eq_bot {P : OGP.{u}} {U : LowerSet P}
    (hU : IsMoleculeIn P U) (hd : 0 < krullDim U) :
    P.boundary U 0 true ⊓ P.boundary U 0 false = ⊥ := by
  induction hU with
  | point x hx =>
    rw [LowerSet.krullDim_Iic_of_isMin hx] at hd
    exact absurd hd (lt_irrefl 0)
  | atom t hround _ _ =>
    rw [inf_comm]
    exact hround.inf_boundary_zero hd
  | paste k V W U hp hV hW hk ihV _ =>
    have hV0 : 0 < krullDim V :=
      (Nat.cast_nonneg' k).trans_lt (hk.trans_le (min_le_left _ _))
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [hp.boundary_output, hp.boundary_input, eq_bot_iff]
      intro v hv
      have hvVW : v ∈ V ⊓ W := ⟨boundary_le V 0 false hv.2, boundary_le W 0 true hv.1⟩
      rw [hp.inf_eq_output] at hvVW
      exact ihV hV0 ▸ ⟨hvVW, hv.2⟩
    · rw [hp.boundary_eq_of_lt_cond false hW.isGlobular hV.isGlobular hk0 true,
        hp.boundary_eq_of_lt_cond false hW.isGlobular hV.isGlobular hk0 false]
      exact ihV hV0

theorem krullDim_eq_zero_of_boundary_zero_eq {P : OGP.{u}} {U : LowerSet P}
    (hU : IsMoleculeIn P U) (h : P.boundary U 0 false = P.boundary U 0 true) :
    krullDim U = 0 := by
  obtain ⟨m, hm⟩ := hU.exists_krullDim_eq
  rcases m.eq_zero_or_pos with rfl | hm0
  · exact hm
  · obtain ⟨v, -, hv⟩ := exists_boundary_zero_eq_Iic hU true
    have he := boundary_zero_true_inf_false_eq_bot hU (by rw [hm]; exact_mod_cast hm0)
    rw [h, hv, inf_idem] at he
    exact False.elim (he ▸ LowerSet.mem_Iic_iff.2 le_rfl : v ∈ (⊥ : LowerSet P))

end OGP

namespace MoleculeShape

def joinSimplexRDC (U : MoleculeShape) (r : ℕ) : RDCpx.{0} :=
  ⟨⟨join U.ogp (simplex r),
    isRDC_of_isMolecule (isMolecule_join _ _ U.isMolecule (isAtom_simplex r).1)⟩⟩

instance (U : MoleculeShape) (r : ℕ) : FinEnum (joinSimplexRDC U r).obj.toOGP :=
  inferInstanceAs (FinEnum (join U.ogp (simplex r)))

instance (U : MoleculeShape) (r : ℕ) : DecidableLE (joinSimplexRDC U r).obj.toOGP :=
  inferInstanceAs (DecidableLE (join U.ogp (simplex r)))

private theorem forall_mem_of_le (U : MoleculeShape) (r : ℕ) (Q : LowerSet U.ogp)
    {p q : (joinSimplexRDC U r).obj.toOGP} (hqp : q ≤ p)
    (hp : ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ Q) :
    ∀ a : U.ogp, q.1.1 = (a : WithBot _) → a ∈ Q := by
  intro a ha
  obtain ⟨b, hb, hab⟩ := WithBot.coe_le_iff.1 (ha ▸ (join_le_iff.1 hqp).1)
  exact Q.lower hab (hp b hb)

def joinSubset (U : MoleculeShape) (r : ℕ) (Q : LowerSet U.ogp) :
    LowerSet (joinSimplexRDC U r).obj.toOGP where
  carrier := {p | ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ Q}
  lower' _ _ hqp hp := forall_mem_of_le U r Q hqp hp

def joinBoxSubset (U : MoleculeShape) (r : ℕ) (P Q : LowerSet U.ogp) :
    LowerSet (joinSimplexRDC U r).obj.toOGP :=
  joinSubset U r Q ⊓
    { carrier := {p |
        (∀ b : simplex.{0} r, p.1.2 = (b : WithBot _) → grade ℕ b < r) ∨
          ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ P}
      lower' := fun p q hqp hp => by
        rcases hp with h | h
        · refine Or.inl fun b hb => ?_
          obtain ⟨c, hc, hbc⟩ := WithBot.coe_le_iff.1 (hb ▸ (join_le_iff.1 hqp).2)
          exact (grade_mono hbc).trans_lt (h c hc)
        · exact Or.inr (forall_mem_of_le U r P hqp h) }

theorem mem_joinSubset (U : MoleculeShape) (r : ℕ) {Q : LowerSet U.ogp}
    {p : (joinSimplexRDC U r).obj.toOGP} :
    p ∈ joinSubset U r Q ↔ ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ Q :=
  Iff.rfl

theorem mem_joinBoxSubset (U : MoleculeShape) (r : ℕ) {P Q : LowerSet U.ogp}
    {p : (joinSimplexRDC U r).obj.toOGP} :
    p ∈ joinBoxSubset U r P Q ↔ (∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ Q) ∧
      ((∀ b : simplex.{0} r, p.1.2 = (b : WithBot _) → grade ℕ b < r) ∨
        ∀ a : U.ogp, p.1.1 = (a : WithBot _) → a ∈ P) :=
  Iff.rfl

end MoleculeShape

end Atoms.Molecule
