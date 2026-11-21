import Atoms.Molecule.Gluing.Atomic
import Atoms.Molecule.Construction.Basic
import Atoms.Molecule.MoleculeShape.Basic

universe u

open CategoryTheory Limits Order

namespace Atoms.Molecule.OGP

inductive IsGeneratedMolecule : OGP.{u} → Prop
  | point : IsGeneratedMolecule point
  | iso {P Q : OGP.{u}} (e : P ≅ Q) (hP : IsGeneratedMolecule P) : IsGeneratedMolecule Q
  | paste {P Q : OGP.{u}} (k : ℕ) (φ : PastingIso P Q k) (hP : IsGeneratedMolecule P)
      (hQ : IsGeneratedMolecule Q) (hk : (k : WithBot ℕ∞) < min (krullDim P) (krullDim Q)) :
      IsGeneratedMolecule (glue φ)
  | rewrite {P Q : OGP.{u}} (n : ℕ) (φ : P.restrict (P.bdryFull ⊤) ≅ Q.restrict (Q.bdryFull ⊤))
      (hP : IsGeneratedMolecule P) (hQ : IsGeneratedMolecule Q) (hPr : P.IsRound ⊤)
      (hQr : Q.IsRound ⊤) (hPd : krullDim P = n) (hQd : krullDim Q = n) (hφ : φ.IsSigned) :
      IsGeneratedMolecule (rewrite n φ hPr hQr hPd hQd)

theorem IsGeneratedMolecule.isMolecule {P : OGP.{u}} (h : IsGeneratedMolecule P) :
    P.IsMolecule := by
  induction h with
  | point => exact isAtom_point.isMoleculeIn
  | iso e _ ih => exact (isMolecule_iff_of_iso e).2 ih
  | paste k φ _ _ _ ihP ihQ => exact isMolecule_glue k φ ihP ihQ
  | rewrite n φ _ _ hPr hQr hPd hQd hφ ihP ihQ =>
    exact rewrite.isMolecule n φ hPr hQr hPd hQd hφ ihP ihQ

def isoPointRestrictIic {P : OGP.{u}} {x : P} (hx : IsMin x) : point.{u} ≅ P.restrict (.Iic x) :=
  isoMk
    { toFun := fun _ => ⟨x, LowerSet.mem_Iic_iff.2 le_rfl⟩
      invFun := fun _ => PUnit.unit
      left_inv := fun _ => rfl
      right_inv := fun y => Subtype.ext (le_antisymm (hx y.2) y.2)
      map_rel_iff' := iff_of_true le_rfl le_rfl }
    fun {a b} h => (h.ne (by cases a; cases b; rfl)).elim

theorem IsGeneratedMolecule.of_isPushout {P Q R : OGP.{u}} {k : ℕ} (hP : IsGeneratedMolecule P)
    (hQ : IsGeneratedMolecule Q) (φ : PastingIso P Q k) {i : P ⟶ R} {j : Q ⟶ R}
    (h : IsPushout (incl (P.boundary ⊤ k true)) (φ.hom ≫ incl (Q.boundary ⊤ k false)) i j)
    (hk : (k : WithBot ℕ∞) < min (krullDim P) (krullDim Q)) : IsGeneratedMolecule R :=
  .iso ((isPushout_glue φ).isoIsPushout _ _ h) (.paste k φ hP hQ hk)

theorem IsMoleculeIn.isGeneratedMolecule_restrict {P : OGP.{u}} {U : LowerSet P}
    (h : IsMoleculeIn P U) : IsGeneratedMolecule (P.restrict U) := by
  induction h with
  | point x hx => exact .iso (isoPointRestrictIic hx) .point
  | atom t hround hbdry ih =>
    set R := P.restrict (.Iic t)
    have hA : R.IsAtom := IsAtomIn.isAtom_restrict ⟨.atom t hround hbdry, t, rfl⟩
    obtain ⟨n, hn⟩ : ∃ n, grade ℕ t = n + 1 := by
      obtain ⟨y, hy⟩ := (hbdry false).nonempty
      have hyt : y < t := by
        have h : y ∈ ((P.bdry (.Iic t) false ⊔ P.bdry (.Iic t) true : LowerSet P) : Set P) :=
          Or.inl hy
        rwa [coe_bdry_Iic_sup] at h
      have := grade_strictMono (𝕆 := ℕ) hyt
      exact ⟨grade ℕ t - 1, by omega⟩
    have hdim : krullDim (⊤ : LowerSet R) = n + 1 := by
      rw [LowerSet.krullDim_top]
      change krullDim (LowerSet.Iic t) = _
      rw [LowerSet.krullDim_Iic, hn]
      push_cast
      rfl
    obtain ⟨e⟩ := nonempty_iso_rewrite hA hdim
    have hhalf (α : Bool) : IsGeneratedMolecule (R.restrict (R.bdry ⊤ α)) := by
      obtain ⟨e', -⟩ := exists_iso_restrict_map (incl (LowerSet.Iic t)) (R.bdry ⊤ α)
      rw [map_bdry, map_incl_top] at e'
      exact .iso e'.symm (ih α)
    exact .iso e.symm (.rewrite n _ (hhalf false) (hhalf true) (hA.isRound_restrict_bdry hdim false)
      (hA.isRound_restrict_bdry hdim true) (hA.krullDim_restrict_bdry hdim false)
      (hA.krullDim_restrict_bdry hdim true) (isSigned_mergerGluing _ _ _))
  | paste k V W U hp hV hW hk ihV ihW =>
    have hp' : (P.restrict U).IsPastingIn k
        (map (codRestrict (incl V) U fun x => hp.left_le x.2) ⊤)
        (map (codRestrict (incl W) U fun x => hp.right_le x.2) ⊤) ⊤ := by
      rw [← isPastingIn_map_iff (incl U), map_incl_top, ← map_comp, ← map_comp,
        codRestrict_incl, codRestrict_incl, map_incl_top, map_incl_top]
      exact hp
    obtain ⟨ψ, -, h⟩ := hp'.exists_isPushout
    exact .of_isPushout ihV ihW ψ h hk

theorem IsMolecule.isGeneratedMolecule {P : OGP.{u}} (h : P.IsMolecule) :
    IsGeneratedMolecule P := by
  obtain ⟨e, -⟩ := exists_iso_restrict (𝟙 P) (map_top_of_isIso _)
  exact .iso e.symm h.isGeneratedMolecule_restrict

theorem isGeneratedMolecule_iff_isMolecule (P : OGP.{u}) : IsGeneratedMolecule P ↔ P.IsMolecule :=
  ⟨IsGeneratedMolecule.isMolecule, IsMolecule.isGeneratedMolecule⟩

instance decidableIsGeneratedMolecule (P : OGP.{u}) [Fintype P] [DecidableEq P] [DecidableLE P] :
    Decidable (IsGeneratedMolecule P) :=
  decidable_of_iff _ (isGeneratedMolecule_iff_isMolecule P).symm

theorem isGeneratedMolecule_iff_isMoleculeIn_map {P Q : OGP.{u}} (f : P ⟶ Q) [IsInclusion f] :
    IsGeneratedMolecule P ↔ IsMoleculeIn Q (map f ⊤) :=
  (isGeneratedMolecule_iff_isMolecule P).trans (isMoleculeIn_map_iff f ⊤).symm

theorem isGeneratedMolecule_iff_exists_finiteOGP (P : OGP.{0}) :
    IsGeneratedMolecule P ↔ ∃ Q : FiniteOGP, Q.ogp.IsMolecule ∧ Nonempty (P ≅ Q.ogp) := by
  classical
  constructor
  · intro hP
    have hfin : Finite P := Set.finite_univ_iff.1 (by simpa using hP.isMolecule.finite)
    have : Fintype P := Fintype.ofFinite P
    obtain ⟨e⟩ := (Fintype.truncEquivFin P).nonempty
    let : FinEnum P := FinEnum.ofEquiv _ e
    let : DecidableLE P := Classical.decRel _
    exact ⟨FiniteOGP.ofOGP P, (isMolecule_iff_of_iso (FiniteOGP.ofOGPIso P)).2 hP.isMolecule,
      ⟨FiniteOGP.ofOGPIso P⟩⟩
  · rintro ⟨Q, hQ, ⟨e⟩⟩
    exact .iso e.symm hQ.isGeneratedMolecule

end Atoms.Molecule.OGP
