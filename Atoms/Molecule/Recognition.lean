import Atoms.Molecule.ClosedEmbedding
import Atoms.Molecule.MoleculeShape.Basic

open CategoryTheory

namespace Atoms.Molecule.OGP

instance (priority := high) decidableIsMoleculeOfFinEnum (P : OGP.{0}) [FinEnum P]
    [DecidableLE P] : Decidable P.IsMolecule :=
  decidable_of_iff (FiniteOGP.ofOGP P).ogp.IsMolecule
    (isMolecule_iff_of_iso (FiniteOGP.ofOGPIso P))

instance (priority := high) decidableIsSubmoleculeOfOfFinEnum (P : OGP.{0}) [FinEnum P]
    [DecidableLE P] (X U : LowerSet P) [DecidablePred (· ∈ X)] [DecidablePred (· ∈ U)] :
    Decidable (P.IsSubmoleculeOf X U) :=
  letI (V : LowerSet P) [DecidablePred (· ∈ V)] :
      DecidablePred (· ∈ map (FiniteOGP.ofOGPIso P).hom V) := fun y =>
    decidable_of_iff ((FiniteOGP.ofOGPIso P).inv y ∈ V)
      ⟨fun h => ⟨_, h, Iso.inv_hom_id_apply _ y⟩, fun ⟨x, hx, hxy⟩ => by
        rwa [← hxy, Iso.hom_inv_id_apply]⟩
  decidable_of_iff _ (isSubmoleculeOf_map_iff (FiniteOGP.ofOGPIso P).hom)

end Atoms.Molecule.OGP
