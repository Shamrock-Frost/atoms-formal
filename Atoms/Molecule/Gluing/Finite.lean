import Atoms.Molecule.Gluing.Basic

universe u

namespace Atoms.Molecule.OGP

variable {P Q : OGP.{u}} {S : LowerSet P} {T : LowerSet Q} (φ : P.restrict S ≅ Q.restrict T)

namespace GlueCarrier

instance instDecidableEq [DecidableEq P] [DecidableEq Q] [DecidablePred (· ∈ S)] :
    DecidableEq (GlueCarrier φ) := fun x y =>
  Quot.recOnSubsingleton₂ x y fun a b => match a, b with
    | .inl p, .inl p' => decidable_of_iff (p = p') (inl_injective (φ := φ)).eq_iff.symm
    | .inr q, .inr q' => decidable_of_iff (q = q') (inr_injective (φ := φ)).eq_iff.symm
    | .inl p, .inr q =>
      decidable_of_iff (∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) = q) inl_eq_inr_iff.symm
    | .inr q, .inl p =>
      decidable_of_iff (∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) = q)
        (inl_eq_inr_iff.symm.trans eq_comm)

instance instDecidableLE [DecidableLE P] [DecidableLE Q] [DecidablePred (· ∈ S)]
    [DecidablePred (· ∈ T)] : DecidableLE (GlueCarrier φ) := fun x y =>
  Quot.recOnSubsingleton₂ x y fun a b => match a, b with
    | .inl p, .inl p' => decidable_of_iff (p ≤ p') inl_le_inl_iff.symm
    | .inr q, .inr q' => decidable_of_iff (q ≤ q') inr_le_inr_iff.symm
    | .inl p, .inr q =>
      decidable_of_iff (∃ h : p ∈ S, ((φ.hom ⟨p, h⟩ : Q.restrict T) : Q) ≤ q) inl_le_inr_iff.symm
    | .inr q, .inl p =>
      decidable_of_iff (∃ h : q ∈ T, ((φ.inv ⟨q, h⟩ : P.restrict S) : P) ≤ p) inr_le_inl_iff.symm

instance instFinEnum [FinEnum P] [FinEnum Q] [DecidablePred (· ∈ S)] : FinEnum (GlueCarrier φ) :=
  FinEnum.ofSurjective (Sum.elim (inl φ) (inr φ)) fun x =>
    (exists_inl_or_inr x).elim (fun ⟨p, h⟩ => ⟨.inl p, h⟩) fun ⟨q, h⟩ => ⟨.inr q, h⟩

end GlueCarrier

transfer_instances glue φ with DecidableEq DecidableLE FinEnum

end Atoms.Molecule.OGP
