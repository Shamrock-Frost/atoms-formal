import Atoms.Molecule.Decidable
import Atoms.Molecule.ShapeData

open CategoryTheory Order

namespace Atoms.Molecule

open OGP

def FiniteOGP.enumerationInvariant (P : FiniteOGP) : Multiset (ℕ × ℕ × ℕ) :=
  letI := decidableCovByOfGrade (P := P.ogp)
  (Finset.univ : Finset P.ogp).val.map fun x =>
    (grade ℕ x, (Finset.univ.filter fun y => ∃ h : y ⋖ x, P.ogp.orient h = false).card,
      (Finset.univ.filter fun y => ∃ h : y ⋖ x, P.ogp.orient h = true).card)

theorem FiniteOGP.enumerationInvariant_eq_of_iso {P Q : FiniteOGP} (e : P.ogp ≅ Q.ogp) :
    P.enumerationInvariant = Q.enumerationInvariant := by
  have hf (α : Bool) (x y : P.ogp) : (∃ h : e.hom y ⋖ e.hom x, Q.ogp.orient h = α) ↔
      ∃ h : y ⋖ x, P.ogp.orient h = α := by
    have hb := (isMorphism e.hom).bijOn_faces x α
    refine ⟨fun h => ?_, fun h => hb.mapsTo h⟩
    obtain ⟨y₀, hy₀, hy⟩ := hb.surjOn h
    rwa [← IsInclusion.injective (f := e.hom) hy]
  have hcard (α : Bool) (x : P.ogp)
      {iP : DecidablePred fun y : P.ogp => ∃ h : y ⋖ x, P.ogp.orient h = α}
      {iQ : DecidablePred fun y : Q.ogp => ∃ h : y ⋖ e.hom x, Q.ogp.orient h = α} :
      (Finset.univ.filter fun y : Q.ogp => ∃ h : y ⋖ e.hom x, Q.ogp.orient h = α).card =
        (Finset.univ.filter fun y : P.ogp => ∃ h : y ⋖ x, P.ogp.orient h = α).card := by
    refine Finset.card_bij' (fun y _ => e.inv y) (fun y _ => e.hom y) (fun y hy => ?_)
      (fun y hy => ?_) (fun y _ => e.inv_hom_id_apply y) (fun y _ => e.hom_inv_id_apply y)
    · rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, (hf α x _).1 (by rw [e.inv_hom_id_apply]; exact hy.2)⟩
    · rw [Finset.mem_filter] at hy ⊢
      exact ⟨Finset.mem_univ _, (hf α x y).2 hy.2⟩
  have hu : (Finset.univ : Finset Q.ogp).val =
      (Finset.univ : Finset P.ogp).val.map (orderIsoOfIso e).toEquiv.toEmbedding := by
    rw [← Finset.map_val, Finset.map_univ_equiv]
  rw [enumerationInvariant, enumerationInvariant, hu, Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => Prod.ext ((isMorphism e.hom).grade_eq x).symm
    (Prod.ext (hcard false x).symm (hcard true x).symm)

end Atoms.Molecule
