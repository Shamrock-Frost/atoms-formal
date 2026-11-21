import Atoms.Shape.Rigidity
import Atoms.Molecule.MoleculeShape.Enumeration

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP

namespace Atoms.Shape

instance Atom.decidableNonemptyIso (U V : Atom) : Decidable (Nonempty (U ≅ V)) :=
  decidable_of_iff (Nonempty (U.ogp ≅ V.ogp))
    ⟨fun ⟨e⟩ => ⟨Atom.isoOfOGPIso e⟩, fun ⟨e⟩ => ⟨Atom.isoOGP e⟩⟩

def Atom.enumerate (n b : ℕ) : List Atom :=
  (MoleculeShape.enumerateAtoms n b).attach.map
    fun (P : {P // P ∈ MoleculeShape.enumerateAtoms n b}) => ⟨P.1, by
    have h := P.2
    simp only [MoleculeShape.enumerateAtoms, List.mem_filter, decide_eq_true_eq] at h
    exact h.2⟩

theorem Atom.map_toMoleculeShape_enumerate (n b : ℕ) :
    (Atom.enumerate n b).map Atom.toMoleculeShape = MoleculeShape.enumerateAtoms n b := by
  rw [Atom.enumerate, List.map_map]
  exact List.attach_map_subtype_val _

theorem Atom.exists_iso_mem_enumerate_iff (n b : ℕ) (U : Atom) :
    (∃ V ∈ Atom.enumerate n b, Nonempty (U ≅ V)) ↔
      U.dimension ≤ n ∧ Fintype.card U.ogp ≤ b := by
  constructor
  · rintro ⟨V, hV, ⟨e⟩⟩
    obtain ⟨-, hd, hc⟩ := (MoleculeShape.exists_iso_mem_enumerateAtoms_iff n b U.ogp).1
      ⟨_, Atom.map_toMoleculeShape_enumerate n b ▸ List.mem_map_of_mem hV, ⟨Atom.isoOGP e⟩⟩
    exact ⟨by exact_mod_cast U.krullDim_eq_dimension.symm.le.trans hd, hc⟩
  · rintro ⟨hd, hc⟩
    obtain ⟨Q, hQ, ⟨e⟩⟩ := (MoleculeShape.exists_iso_mem_enumerateAtoms_iff n b U.ogp).2
      ⟨U.isAtom, U.krullDim_eq_dimension.le.trans (by exact_mod_cast hd), hc⟩
    rw [← Atom.map_toMoleculeShape_enumerate] at hQ
    obtain ⟨V, hV, rfl⟩ := List.mem_map.1 hQ
    exact ⟨V, hV, ⟨Atom.isoOfOGPIso e⟩⟩

theorem Atom.pairwise_isEmpty_iso_enumerate (n b : ℕ) :
    (Atom.enumerate n b).Pairwise fun U V => IsEmpty (U ≅ V) := by
  have h := MoleculeShape.pairwise_isEmpty_iso_enumerateAtoms n b
  rw [← Atom.map_toMoleculeShape_enumerate, List.pairwise_map] at h
  exact h.imp fun h' => ⟨fun e => h'.false (Atom.isoOGP e)⟩

end Atoms.Shape
