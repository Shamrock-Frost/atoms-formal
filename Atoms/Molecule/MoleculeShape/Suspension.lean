import Atoms.Molecule.MoleculeShape.Basic
import Atoms.Molecule.Construction.SuspensionMap

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

namespace MoleculeShape

variable (P : MoleculeShape)

def suspension : MoleculeShape :=
  ofOGP (OGP.suspension P.ogp) (isMolecule_suspension P.ogp P.isMolecule)

def suspensionIso : OGP.suspension P.ogp ≅ P.suspension.ogp :=
  FiniteOGP.ofOGPIso _

theorem dimension_suspension : P.suspension.dimension = P.dimension + 1 := by
  have h := dimension_ofOGP (OGP.suspension P.ogp) (isMolecule_suspension P.ogp P.isMolecule)
  rw [← LowerSet.krullDim_top, ← susp_top, krullDim_susp P.isMolecule.nonempty,
    LowerSet.krullDim_top, P.krullDim_eq_dimension] at h
  exact_mod_cast h

theorem isRound_suspension {P : MoleculeShape} (hP : P.IsRound) : P.suspension.IsRound :=
  isRound_ofOGP _ _ (by
    rw [← susp_top]
    exact isRound_susp hP fun n α => (P.isMolecule.boundary n α).nonempty)

theorem isRound_suspension_iff : P.suspension.IsRound ↔ P.IsRound := by
  rw [isRound_iff, isRound_iff, isRound_top_iff_of_iso P.suspensionIso, ← susp_top]
  exact isRound_susp_iff fun n α => (P.isMolecule.boundary n α).nonempty

def suspensionRDCIso : RDCpx.suspensionFunctor.obj P.rdc ≅ P.suspension.rdc :=
  RDCpx.isoOfIso (P := RDCpx.suspensionFunctor.obj P.rdc) (Q := P.suspension.rdc) P.suspensionIso

variable {P} {Q : MoleculeShape}

def suspensionMap (f : P.ogp ⟶ Q.ogp) : P.suspension.ogp ⟶ Q.suspension.ogp :=
  P.suspensionIso.inv ≫ OGP.suspension.map f ≫ Q.suspensionIso.hom

instance (f : P.ogp ⟶ Q.ogp) [IsInclusion f] : IsInclusion (suspensionMap f) :=
  inferInstanceAs (IsInclusion (P.suspensionIso.inv ≫ OGP.suspension.map f ≫ Q.suspensionIso.hom))

instance : Nonempty P.ogp :=
  P.isMolecule.nonempty.to_subtype.map Subtype.val

def desuspensionIso (φ : P.suspension.ogp ≅ Q.suspension.ogp) : P.ogp ≅ Q.ogp :=
  OGP.suspension.desuspIso (P.suspensionIso ≪≫ φ ≪≫ Q.suspensionIso.symm)

theorem suspensionMap_desuspensionIso_hom (φ : P.suspension.ogp ≅ Q.suspension.ogp) :
    suspensionMap (desuspensionIso φ).hom = φ.hom := by
  have h : OGP.suspension.map (desuspensionIso φ).hom = _ := congrArg Iso.hom
    (OGP.suspension.mapIso_desuspIso (P.suspensionIso ≪≫ φ ≪≫ Q.suspensionIso.symm))
  rw [suspensionMap, h]
  simp

theorem map_suspensionMap_top (f : P.ogp ⟶ Q.ogp) :
    map (suspensionMap f) ⊤ = map Q.suspensionIso.hom (map f ⊤).susp := by
  rw [suspensionMap, map_comp, map_comp, map_top_of_isIso]
  congr 1
  refine SetLike.ext fun w => ?_
  cases w with
  | pole α => exact iff_of_true ⟨SuspCarrier.pole α, LowerSet.mem_top, rfl⟩ (pole_mem_susp _ α)
  | susp y =>
    refine ⟨?_, ?_⟩
    · rintro ⟨z, -, hz⟩
      cases z with
      | pole β =>
        rw [suspension.map_apply, suspMap_pole] at hz
        exact nomatch hz
      | susp x => exact susp_mem_susp.2 ⟨x, LowerSet.mem_top, SuspCarrier.susp.inj hz⟩
    · intro hy
      obtain ⟨x, -, rfl⟩ := susp_mem_susp.1 hy
      exact ⟨SuspCarrier.susp x, LowerSet.mem_top, rfl⟩

@[reassoc] theorem suspensionRDCIso_hom_comp_ofInclusion_suspensionMap (j : P.ogp ⟶ Q.ogp)
    [IsInclusion j] :
    P.suspensionRDCIso.hom ≫ RDCpx.ofInclusion (P := P.suspension.rdc) (Q := Q.suspension.rdc)
      (suspensionMap j) =
    RDCpx.suspensionFunctor.map (RDCpx.ofInclusion (P := P.rdc) (Q := Q.rdc) j) ≫
      Q.suspensionRDCIso.hom := by
  ext y
  exact congrArg Q.suspensionIso.hom
    (congrArg (OGP.suspension.map j) (ConcreteCategory.congr_hom P.suspensionIso.hom_inv_id y))

variable (P) in
theorem map_boundaryIncl_suspension_top (k : ℕ) (α : Bool) :
    map (P.suspension.boundaryIncl (k + 1) α) ⊤ =
      map (suspensionMap (P.boundaryIncl k α)) ⊤ := by
  rw [map_boundaryIncl_top, map_suspensionMap_top, map_boundaryIncl_top,
    ← boundary_susp_succ (P.isMolecule.boundary k α).nonempty, map_boundary, susp_top,
    map_top_of_isIso]

variable (P) in
theorem nonempty_iso_boundary_suspension (k : ℕ) (α : Bool) :
    Nonempty ((P.suspension.boundary (k + 1) α).ogp ≅ (P.boundary k α).suspension.ogp) := by
  obtain ⟨e, -⟩ := exists_iso_restrict (P.suspension.boundaryIncl (k + 1) α)
    (map_boundaryIncl_suspension_top P k α)
  obtain ⟨e', -⟩ := exists_iso_restrict (suspensionMap (P.boundaryIncl k α)) rfl
  exact ⟨e ≪≫ e'.symm⟩

end MoleculeShape

def RoundShape.suspension (P : RoundShape) : RoundShape :=
  ⟨P.toMoleculeShape.suspension, MoleculeShape.isRound_suspension P.isRound⟩

end Atoms.Molecule
