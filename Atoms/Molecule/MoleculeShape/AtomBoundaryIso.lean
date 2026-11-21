import Atoms.Molecule.MoleculeShape.ParallelAtom
import Atoms.Molecule.Gluing.Atomic

open CategoryTheory Order Atoms.Molecule.OGP

namespace Atoms.Molecule.MoleculeShape

theorem nonempty_iso_of_boundary_iso (V W : MoleculeShape) {n : ℕ}
    (φ : ∀ α : Bool, (V.boundary n α).ogp ≅ (W.boundary n α).ogp)
    (hV : IsAtom V.ogp) (hW : IsAtom W.ogp) (hdV : V.dimension = n + 1)
    (hdW : W.dimension = n + 1) : Nonempty (V.ogp ≅ W.ogp) := by
  obtain ⟨tV, htV⟩ := hV.exists_eq_Iic
  obtain ⟨tW, htW⟩ := hW.exists_eq_Iic
  exact ⟨isoOfBdryIso (fun x => (htV ▸ LowerSet.mem_top : x ∈ LowerSet.Iic tV))
    (fun x => (htW ▸ LowerSet.mem_top : x ∈ LowerSet.Iic tW))
    (bdryIsoOfParallel V W φ hV.isRound hW.isRound hdV hdW)
    (isSigned_bdryIsoOfParallel V W φ hV.isRound hW.isRound hdV hdW)⟩

end Atoms.Molecule.MoleculeShape
