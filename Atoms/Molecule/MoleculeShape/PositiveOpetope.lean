import Atoms.Molecule.Construction.Suspension
import Atoms.Molecule.Gluing.Substitution
import Atoms.Molecule.MoleculeShape.Merger

open CategoryTheory Order

namespace Atoms.Molecule.OGP

inductive IsPositiveOpetopeTree : OGP.{0} → Prop
  | point : IsPositiveOpetopeTree point
  | iso {P Q : OGP.{0}} (e : P ≅ Q) (hP : IsPositiveOpetopeTree P) : IsPositiveOpetopeTree Q
  | graft {U V : OGP.{0}} {n : ℕ} {x : V} (hx : x ∈ V.boundary ⊤ n false)
      (φ : U.restrict (U.boundary ⊤ n true) ≅ V.restrict (LowerSet.Iic x))
      (hU : IsPositiveOpetopeTree U) (hV : IsPositiveOpetopeTree V) (hUd : krullDim U = n + 1)
      (hVd : krullDim V = n + 1) : IsPositiveOpetopeTree (pastingAt (α := false) φ)
  | shiftPoint : IsPositiveOpetopeTree (globe 1)
  | shift (U : RoundShape) {n : ℕ} (hd : U.dimension = n + 1)
      (hU : IsPositiveOpetopeTree U.ogp) : IsPositiveOpetopeTree (U.toMerger hd).ogp

def IsPositiveOpetope (P : OGP.{0}) : Prop :=
  IsPositiveOpetopeTree P ∧ ∃ t : P, IsTop t

namespace IsPositiveOpetopeTree

theorem isMolecule_and_isRound {P : OGP.{0}} (h : IsPositiveOpetopeTree P) :
    P.IsMolecule ∧ P.IsRound ⊤ := by
  induction h with
  | point => exact ⟨isAtom_point.isMoleculeIn, isAtom_point.isRound⟩
  | iso e _ ih =>
    refine ⟨(isMolecule_iff_of_iso e).2 ih.1, ?_⟩
    have h := (isRound_map_iff e.hom ⊤).2 ih.2
    rwa [map_top_of_isIso] at h
  | @graft U V n x hx φ _ _ hUd hVd ihU ihV =>
    have hW : V.IsSubmoleculeOf (LowerSet.Iic x) (V.boundary ⊤ n false) :=
      (ihV.1.boundary n false).Iic_isSubmoleculeOf hx
    exact ⟨isMolecule_pastingAt (k := n) (α := false) φ hW ihU.1 ihV.1,
      isRound_pastingAt (n := n) (α := false) hW φ ihU.1 ihV.1 ihV.2 hVd (hUd.trans hVd.symm)⟩
  | shiftPoint => exact ⟨(isAtom_globe.{0} 1).isMoleculeIn, (isAtom_globe.{0} 1).isRound⟩
  | shift U hd _ _ => exact ⟨(U.isAtom_toMerger hd).isMoleculeIn, (U.isAtom_toMerger hd).isRound⟩

theorem isMolecule {P : OGP.{0}} (h : IsPositiveOpetopeTree P) : P.IsMolecule :=
  h.isMolecule_and_isRound.1

theorem isRound {P : OGP.{0}} (h : IsPositiveOpetopeTree P) : P.IsRound ⊤ :=
  h.isMolecule_and_isRound.2

end IsPositiveOpetopeTree

theorem IsPositiveOpetope.isAtom {P : OGP.{0}} (h : IsPositiveOpetope P) : P.IsAtom := by
  obtain ⟨hP, t, ht⟩ := h
  exact ⟨hP.isMolecule, t, SetLike.ext fun x => ⟨fun _ => ht x, fun _ => trivial⟩⟩

theorem isPositiveOpetope_toMerger (U : RoundShape) {n : ℕ} (hd : U.dimension = n + 1)
    (hU : IsPositiveOpetopeTree U.ogp) : IsPositiveOpetope (U.toMerger hd).ogp := by
  obtain ⟨-, t, ht⟩ := U.isAtom_toMerger hd
  exact ⟨.shift U hd hU, t, fun x =>
    LowerSet.mem_Iic_iff.1 (ht ▸ (trivial : x ∈ (⊤ : LowerSet _)))⟩

end Atoms.Molecule.OGP
