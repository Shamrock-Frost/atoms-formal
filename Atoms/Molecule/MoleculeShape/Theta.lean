import Atoms.Molecule.Construction.ThetaClassification
import Atoms.Molecule.MoleculeShape.Enumeration
import Atoms.Molecule.Recognition

universe u

open CategoryTheory Order

namespace Atoms.Molecule.OGP

theorem isGlobe_iff_exists_grade (P : OGP.{u}) :
    IsGlobe P ↔ ∃ x : P, Nonempty (P ≅ globe.{u} (grade ℕ x)) := by
  refine ⟨fun ⟨n, ⟨e⟩⟩ => ⟨e.inv ⊤, ?_⟩, fun ⟨x, h⟩ => ⟨grade ℕ x, h⟩⟩
  rw [(isMorphism e.inv).grade_eq, grade_top_globe]
  exact ⟨e⟩

theorem isGlobe_iff_exists_forall_le (P : OGP.{u}) :
    IsGlobe P ↔ ∃ x : P, (∀ y, y ≤ x) ∧ Nonempty (P ≅ globe.{u} (grade ℕ x)) := by
  refine ⟨fun ⟨n, ⟨e⟩⟩ => ⟨e.inv ⊤, fun y => ?_, ?_⟩, fun ⟨x, _, h⟩ => ⟨grade ℕ x, h⟩⟩
  · rw [← e.hom_inv_id_apply y]
    exact (isMorphism e.inv).monotone le_top
  · rw [(isMorphism e.inv).grade_eq, grade_top_globe]
    exact ⟨e⟩

theorem isGlobe_restrict_Iic_iff (P : OGP.{u}) (x : P) :
    IsGlobe (P.restrict (LowerSet.Iic x)) ↔
      Nonempty (P.restrict (LowerSet.Iic x) ≅ globe.{u} (grade ℕ x)) := by
  refine ⟨fun ⟨n, ⟨e⟩⟩ => ?_, fun h => ⟨_, h⟩⟩
  let t : P.restrict (LowerSet.Iic x) := ⟨x, le_rfl⟩
  have h₁ : grade ℕ t ≤ n := by
    rw [← (isMorphism e.hom).grade_eq]
    exact (grade_mono (le_top (a := e.hom t))).trans_eq (grade_top_globe.{u} n)
  have h₂ : n ≤ grade ℕ t := by
    rw [← grade_top_globe.{u} n, ← (isMorphism e.inv).grade_eq]
    exact grade_mono (show e.inv ⊤ ≤ t from (e.inv ⊤).2)
  have : grade ℕ x = n := (LowerSet.grade_coe (LowerSet.Iic x) t).trans (le_antisymm h₁ h₂)
  exact this ▸ ⟨e⟩

theorem isTheta_iff_forall_isMax_isGlobe {P : OGP.{u}} (hP : P.IsMolecule) :
    IsTheta P ↔ ∀ x : P, IsMax x → IsGlobe (P.restrict (LowerSet.Iic x)) := by
  refine ⟨fun h x _ => h.isGlobe_Iic x, fun h => (isTheta_iff_forall_isGlobe hP).2 fun y => ?_⟩
  obtain ⟨x, hyx, hx⟩ := hP.finite.exists_le_maximal (Set.mem_univ y)
  obtain ⟨e, -⟩ := exists_iso_restrict_map (incl (LowerSet.Iic x))
    (LowerSet.Iic (⟨y, hyx⟩ : P.restrict (LowerSet.Iic x)))
  refine ((h x fun z hz => hx.2 (Set.mem_univ z) hz).isGlobe_Iic ⟨y, hyx⟩).iso
    (e ≪≫ restrictCongr ?_)
  rw [map_Iic, incl_apply]

instance decidableIsGlobe (P : OGP.{0}) [FinEnum P] [DecidableLE P] : Decidable (IsGlobe P) :=
  decidable_of_iff _ (isGlobe_iff_exists_forall_le P).symm

instance decidableIsTheta (P : OGP.{0}) [FinEnum P] [DecidableLE P] : Decidable (IsTheta P) :=
  decidable_of_iff (P.IsMolecule ∧ ∀ x : P, (∀ y, x ≤ y → y ≤ x) →
      Nonempty (P.restrict (LowerSet.Iic x) ≅ globe.{0} (grade ℕ x)))
    ⟨fun ⟨hP, h⟩ => (isTheta_iff_forall_isMax_isGlobe hP).2 fun x hx =>
        (isGlobe_restrict_Iic_iff P x).2 (h x hx),
      fun h => ⟨h.isMolecule, fun x _ => (isGlobe_restrict_Iic_iff P x).1 (h.isGlobe_Iic x)⟩⟩

end Atoms.Molecule.OGP
