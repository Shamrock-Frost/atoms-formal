import Atoms.Diagrammatic.Equivalence.PastingCriterion

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

private theorem exists_within_mem_equivalences_iff {m : PastingDiagram X} {n : ℕ} {α : Bool}
    {P Q : RoundPastingDiagram X} (hP : P.dim = n + 1) (hQ : Q.dim = n + 1)
    (wP : Within P.toPastingDiagram m) (wQ : Within Q.toPastingDiagram m)
    {R : LowerSet m.shape.ogp} (hc : m.shape.ogp.IsPastingAtIn n α wP.image wQ.image R)
    (he : P ∈ equivalences X) :
    ∃ (r : RoundPastingDiagram X) (wr : Within r.toPastingDiagram m), wr.image = R ∧
      r.dim = n + 1 ∧ (r ∈ equivalences X ↔ Q ∈ equivalences X) := by
  obtain ⟨D, wD, hwD, -, -, -⟩ := exists_pasteAtData_of_isPastingAtIn hP hQ wP wQ hc
  exact ⟨D.round, wD, hwD, D.dim_pasting, pasteAt_mem_equivalences_iff D he⟩

theorem mem_equivalences_of_isGenPastingIn {m u v : RoundPastingDiagram X} {k : ℕ}
    (wu : PastingDiagram.Within u.toPastingDiagram m.toPastingDiagram)
    (wv : PastingDiagram.Within v.toPastingDiagram m.toPastingDiagram)
    (hdu : u.dim = k + 1) (hdv : v.dim = k + 1)
    (hg : m.shape.ogp.IsGenPastingIn k wu.image wv.image) (hsup : wu.image ⊔ wv.image = ⊤)
    (iU : wu.image ⊓ m.shape.ogp.boundary ⊤ k false ≤ m.shape.ogp.boundary wu.image k false)
    (iV : wv.image ⊓ m.shape.ogp.boundary ⊤ k true ≤ m.shape.ogp.boundary wv.image k true)
    (hu : u ∈ equivalences X) (hv : v ∈ equivalences X) : m ∈ equivalences X := by
  classical
  have hdm : m.dim = k + 1 := by
    have h := (Within.refl m.toPastingDiagram).krullDim_image
    rw [Within.image_refl, ← hsup, LowerSet.krullDim_sup, wu.krullDim_image, wv.krullDim_image,
      hdu, hdv, max_self] at h
    exact_mod_cast h.symm
  have hz := isRound_boundary_of_isRound m.isRound k true
  have hdz : (m.toPastingDiagram.boundary k true).dim = k := dim_boundary _ (by omega) _
  have hpu : m.toPastingDiagram.Pastable (m.toPastingDiagram.boundary k true).unit k :=
    ⟨(boundary_unit hdz false).symm, by rw [dim_unit, hdz, hdm]; omega⟩
  have hdε : hz.unit.dim = k + 1 := by rw [dim_unit, hdz]
  have hr := isRound_paste_of_dim m hz.unit hdm hdε hpu
  refine mem_equivalences_of_equivalent (equivalent_paste_unit_cond true m hdm hpu hr) ?_
  let iM := Within.pasteInl m.toPastingDiagram _ k hpu
  let iE := Within.pasteInr m.toPastingDiagram _ k hpu
  have eU : (wu.trans iM).image = OGP.map iM.emb wu.image := Within.image_trans _ _
  have eV : (wv.trans iM).image = OGP.map iM.emb wv.image := Within.image_trans _ _
  have hg' : OGP.IsGenPastingIn _ k (wu.trans iM).image (wv.trans iM).image := by
    rw [eU, eV]
    exact hg.map iM.emb
  have iU' : (wu.trans iM).image ⊓ OGP.boundary _ ((wu.trans iM).image ⊔ (wv.trans iM).image) k
      false ≤ OGP.boundary _ (wu.trans iM).image k false := by
    rw [eU, eV, ← map_sup, hsup, ← map_boundary, ← map_boundary, ← map_inf]
    exact map_mono _ iU
  have iV' : (wv.trans iM).image ⊓ OGP.boundary _ ((wu.trans iM).image ⊔ (wv.trans iM).image) k
      true ≤ OGP.boundary _ (wv.trans iM).image k true := by
    rw [eU, eV, ← map_sup, hsup, ← map_boundary, ← map_boundary, ← map_inf]
    exact map_mono _ iV
  have hp : (m.toPastingDiagram.paste _ k hpu).shape.ogp.IsPastingIn k
      ((wu.trans iM).image ⊔ (wv.trans iM).image) iE.image ⊤ := by
    rw [eU, eV, ← map_sup, hsup]
    exact Within.isPastingIn_paste m.toPastingDiagram _ k hpu
  have hkU : (k : WithBot ℕ∞) ≤ krullDim (wu.trans iM).image := by
    rw [Within.krullDim_image, hdu]
    exact_mod_cast Nat.le_succ k
  obtain ⟨r, wr, hwr, hdr, hr₁⟩ := exists_within_mem_equivalences_iff hdv hdε (wv.trans iM) iE
    (hg'.isPastingAtIn_right_of_isPastingIn iV' iE.isMoleculeIn_image hp) hv
  have c₂ := hg'.isPastingAtIn_left_of_isPastingIn iU' iV' iE.isMoleculeIn_image hp hkU
  rw [← hwr] at c₂
  obtain ⟨r', wr', hwr', -, hr₂⟩ := exists_within_mem_equivalences_iff hdu hdr (wu.trans iM) wr
    c₂ hu
  exact mem_equivalences_of_equiv
    (Within.equiv_of_image_eq wr' (Within.refl _) (hwr'.trans (Within.image_refl _).symm))
    (hr₂.2 (hr₁.2 (unit_mem_equivalences ⟨_, hz⟩)))

end Atoms.Diagrammatic
