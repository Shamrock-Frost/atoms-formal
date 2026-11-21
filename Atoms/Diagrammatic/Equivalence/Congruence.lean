import Atoms.Diagrammatic.Equivalence.TopCells

universe u

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure SubstituteData (u w : RoundPastingDiagram X) where
  sub : PastingDiagram X
  occ : Within sub u.toPastingDiagram
  rewritable : u.toPastingDiagram.shape.ogp.IsRewritableSubmolecule occ.image ⊤
  rewrite : RoundPastingDiagram X
  dim_rewrite : rewrite.dim = u.dim + 1
  source : (rewrite.boundary u.dim false).Equiv sub
  target : (rewrite.boundary u.dim true).Equiv w.toPastingDiagram

namespace SubstituteData

variable {u w : RoundPastingDiagram X} (D : SubstituteData u w)

noncomputable def unitOcc : Within D.sub (u.isRound.unit.boundary u.dim true) :=
  D.occ.trans (Within.ofEquiv (PastingDiagram.boundary_unit rfl true).symm)

theorem isRewritableSubmolecule_image_unitOcc :
    (u.isRound.unit.boundary u.dim true).shape.ogp.IsRewritableSubmolecule D.unitOcc.image ⊤ :=
  (D.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff _).2 D.rewritable

noncomputable def pasteData : PasteAtData true u.dim D.rewrite u.isRound.unit :=
  ⟨D.dim_rewrite, u.dim_unit, D.sub, D.unitOcc, D.isRewritableSubmolecule_image_unitOcc,
    D.source⟩

theorem equiv_source : (D.pasteData.pasting.boundary u.dim false).Equiv u.toPastingDiagram :=
  D.pasteData.equiv_boundary_not.trans
    (PastingDiagram.boundary_unit rfl false)

noncomputable def withinU : Within u.toPastingDiagram D.pasteData.pasting :=
  (Within.ofEquiv ((PastingDiagram.boundary_unit rfl true).symm)).trans
    ((Within.boundary u.isRound.unit.toPastingDiagram u.dim true).trans D.pasteData.pasteAtInr)

theorem image_withinU :
    D.withinU.image =
      D.pasteData.pasting.shape.ogp.boundary D.pasteData.pasteAtInr.image u.dim true := by
  change ((Within.ofEquiv
    ((PastingDiagram.boundary_unit rfl true).symm)).trans
      ((Within.boundary u.isRound.unit.toPastingDiagram u.dim true).trans
        D.pasteData.pasteAtInr)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary_trans _ _ _

theorem image_occ_withinU :
    (D.occ.trans D.withinU).image =
      D.pasteData.pasteAtInl.image ⊓ D.pasteData.pasteAtInr.image := by
  rw [← D.pasteData.image_occ_pasteAtInr]
  rfl

noncomputable def withinW : Within w.toPastingDiagram D.pasteData.pasting :=
  (Within.ofEquiv (D.target.symm)).trans
    ((Within.boundary D.rewrite.toPastingDiagram u.dim true).trans D.pasteData.pasteAtInl)

theorem image_withinW :
    D.withinW.image =
      D.pasteData.pasting.shape.ogp.boundary D.pasteData.pasteAtInl.image u.dim true := by
  change ((Within.ofEquiv (D.target.symm)).trans
    ((Within.boundary D.rewrite.toPastingDiagram u.dim true).trans
      D.pasteData.pasteAtInl)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary_trans _ _ _

theorem isMoleculeIn_output :
    IsMoleculeIn D.pasteData.pasting.shape.ogp
      (D.pasteData.pasting.shape.ogp.boundary ⊤ u.dim true) :=
  D.pasteData.pasting.shape.isMolecule.boundary _ _

theorem equiv_target_restrictTo :
    (D.pasteData.pasting.boundary u.dim true).Equiv
      (D.pasteData.pasting.restrictTo D.isMoleculeIn_output) :=
  Within.equiv_restrictTo_of_eq (Within.boundary D.pasteData.pasting u.dim true)
    (Within.image_boundary _ _ _) D.isMoleculeIn_output

theorem isSubstitutionIn :
    IsSubstitutionIn D.pasteData.pasting.shape.ogp D.withinU.image
      (D.occ.trans D.withinU).image D.withinW.image
      (D.pasteData.pasting.shape.ogp.boundary ⊤ u.dim true) := by
  rw [image_withinU, image_occ_withinU, image_withinW]
  exact D.pasteData.isPastingAtIn_pasteAtInl.isSubstitutionIn_boundary
    (D.pasteData.pasteAtInl.round_image_iff.2 D.rewrite.isRound) D.pasteData.krullDim_pasteAtInl
    (by rw [D.pasteData.krullDim_pasteAtInr]; exact_mod_cast u.dim.le_succ)

theorem equiv_target_substitute
    (hp : Parallel ⟨D.sub, D.occ.round_image_iff.1 D.rewritable.isRound⟩ w) :
    (D.pasteData.pasting.boundary u.dim true).Equiv
      (u.toPastingDiagram.substitute D.occ D.rewritable w hp) :=
  D.equiv_target_restrictTo.trans
    ((equiv_substitute_of_within D.occ D.rewritable w hp D.withinU
      D.withinW D.isSubstitutionIn D.isMoleculeIn_output).symm)

end SubstituteData

section Paste

noncomputable abbrev pasteRound {u v : PastingDiagram X} {k : ℕ} (hp : u.Pastable v k)
    (hr : (u.paste v k hp).IsRound) : RoundPastingDiagram X :=
  ⟨u.paste v k hp, hr⟩

variable {c h : RoundPastingDiagram X} {k : ℕ} (α : Bool)
  (hp : (cond α c.toPastingDiagram h.toPastingDiagram).Pastable
    (cond α h.toPastingDiagram c.toPastingDiagram) k)

theorem isSubmoleculeOf_pasteIn : IsSubmoleculeOf _ (Within.pasteIn α hp).image ⊤ := by
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn α hp
  exact (hpst.isPastingFactorOf α (Within.pasteIn α hp).isMoleculeIn_image
    wc.isMoleculeIn_image).isSubmoleculeOf

theorem dim_paste_of_dim_eq (hd : c.dim = h.dim) :
    ((cond α c.toPastingDiagram h.toPastingDiagram).paste
      (cond α h.toPastingDiagram c.toPastingDiagram) k hp).dim = h.dim := by
  rw [dim_paste_cond, hd, max_self]

theorem isRewritableSubmolecule_image_pasteIn (hd : c.dim = h.dim) :
    IsRewritableSubmolecule _ (Within.pasteIn α hp).image ⊤ :=
  (Within.pasteIn α hp).isRewritableSubmolecule_image_iff.2
    ⟨isSubmoleculeOf_pasteIn α hp, h.isRound, (dim_paste_of_dim_eq α hp hd).symm⟩

variable (hr : ((cond α c.toPastingDiagram h.toPastingDiagram).paste
    (cond α h.toPastingDiagram c.toPastingDiagram) k hp).IsRound)

theorem EquivalenceData.hasBdry {u v : RoundPastingDiagram X} (E : EquivalenceData u v) :
    HasBdry false u.dim E.equivalence.toPastingDiagram u.toPastingDiagram v.toPastingDiagram :=
  ⟨E.dim_equivalence, rfl, E.dim_eq.symm, E.source, E.target⟩

namespace SubstituteData

noncomputable def ofPaste {h' r : RoundPastingDiagram X}
    (hb : HasBdry false h.dim r.toPastingDiagram h.toPastingDiagram h'.toPastingDiagram)
    (hd : c.dim = h.dim) : SubstituteData (pasteRound hp hr) h' where
  sub := h.toPastingDiagram
  occ := Within.pasteIn α hp
  rewritable := isRewritableSubmolecule_image_pasteIn α hp hd
  rewrite := r
  dim_rewrite := by
    rw [hb.dim_h]
    exact congrArg (· + 1) (dim_paste_of_dim_eq α hp hd).symm
  source := by
    rw [PastingDiagram.boundary_congr r.toPastingDiagram (dim_paste_of_dim_eq α hp hd)]
    exact hb.side
  target := by
    rw [PastingDiagram.boundary_congr r.toPastingDiagram (dim_paste_of_dim_eq α hp hd)]
    exact hb.other

theorem equiv_target_ofPaste {h' r : RoundPastingDiagram X}
    (hb : HasBdry false h.dim r.toPastingDiagram h.toPastingDiagram h'.toPastingDiagram)
    (hd : c.dim = h.dim)
    (hp' : (cond α c.toPastingDiagram h'.toPastingDiagram).Pastable
      (cond α h'.toPastingDiagram c.toPastingDiagram) k) :
    ((ofPaste α hp hr hb hd).pasteData.pasting.boundary (pasteRound hp hr).dim true).Equiv
      ((cond α c.toPastingDiagram h'.toPastingDiagram).paste
        (cond α h'.toPastingDiagram c.toPastingDiagram) k hp') := by
  let D := ofPaste α hp hr hb hd
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn α hp
  have hq : D.pasteData.pasting.shape.ogp.IsPastingIn k
      (cond α (wc.trans D.withinU).image ((Within.pasteIn α hp).trans D.withinU).image)
      (cond α ((Within.pasteIn α hp).trans D.withinU).image (wc.trans D.withinU).image)
      D.withinU.image := by
    rw [Within.image_trans, Within.image_trans, ← Bool.apply_cond (OGP.map D.withinU.emb),
      ← Bool.apply_cond (OGP.map D.withinU.emb)]
    exact (isPastingIn_map_iff D.withinU.emb k _ _ _).2 hpst
  have hkh : k < h.dim := by
    rw [← dim_paste_of_dim_eq α hp hd, dim_paste]
    exact lt_max_of_lt_left (lt_min_iff.1 hp.2).1
  have hk : (k : WithBot ℕ∞) < krullDim ((Within.pasteIn α hp).trans D.withinU).image := by
    rw [Within.krullDim_image]; exact_mod_cast hkh
  exact D.equiv_target_restrictTo.trans ((equiv_paste_cond_of_within α (wc.trans D.withinU)
    D.withinW (D.isSubstitutionIn.isPastingIn_self_cond α (wc.trans D.withinU).isMoleculeIn_image
      hk hq) D.isMoleculeIn_output hp').symm)

end SubstituteData

end Paste

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem PasteAtData.equiv_boundary_pasting_of_image_univ {α : Bool} {n : ℕ}
    {P Q : RoundPastingDiagram X} (d : PasteAtData α n P Q) (h : d.occ.image = ⊤) :
    (d.pasting.boundary n α).Equiv (P.boundary n α) :=
  Within.equiv_of_image_eq (Within.boundary d.pasting n α)
    ((Within.boundary P.toPastingDiagram n α).trans d.pasteAtInl) (by
      rw [Within.image_boundary, Within.image_boundary_trans]
      exact d.isPastingAtIn_pasteAtInl.boundary_eq_left_of_inf_eq
        (inter_eq_boundary_pasteAt_of_image_univ _ _ n α d.occ d.rewritable.isSubmoleculeOf h
          d.equiv))

def pasteData (u v : RoundPastingDiagram X) {k : ℕ} (hu : u.dim = k + 1) (hv : v.dim = k + 1)
    (hp : u.toPastingDiagram.Pastable v.toPastingDiagram k) : PasteAtData false k u v :=
  PasteAtData.ofBoundary hu hv hp.1

theorem equivalent_of_equiv {u v : RoundPastingDiagram X} (h : u.Equiv v.toPastingDiagram) :
    Equivalent u v :=
  EquivalenceData.equivalent
    { dim_eq := dim_eq_of_equiv h
      equivalence := u.isRound.unit
      mem := unit_mem_equivalences u
      dim_equivalence := u.dim_unit
      source := PastingDiagram.boundary_unit rfl false
      target := (PastingDiagram.boundary_unit rfl true).trans h }

theorem equivalent_symm {u v : RoundPastingDiagram X} (h : Equivalent u v) : Equivalent v u := by
  obtain ⟨hd, e, he, hde, hs, ht⟩ := h.data
  obtain ⟨e', he', ht'⟩ := exists_inverse_mem_equivalences he hde
  refine EquivalenceData.equivalent ⟨hd.symm, e', he', ?_, ?_, ?_⟩
  · rw [ht'.dim_h, hd]
  · rw [← hd]; exact ht'.side.trans ht
  · rw [← hd]; exact ht'.other.trans hs

theorem equivalent_of_mem_equivalences_cond (α : Bool) {z u v : RoundPastingDiagram X}
    (hz : z ∈ equivalences X) {k : ℕ} (hu : u.dim = k) (hv : v.dim = k) (hzd : z.dim = k + 1)
    (h₁ : (z.boundary k α).Equiv u.toPastingDiagram)
    (h₂ : (z.boundary k (!α)).Equiv v.toPastingDiagram) : Equivalent u v := by
  have key : ∀ u v : RoundPastingDiagram X, u.dim = k → v.dim = k →
      (z.boundary k false).Equiv u.toPastingDiagram →
      (z.boundary k true).Equiv v.toPastingDiagram → Equivalent u v := by
    intro u v hu hv h₁ h₂
    subst hu
    exact EquivalenceData.equivalent ⟨hv.symm, z, hz, hzd, h₁, h₂⟩
  cases α
  · exact key u v hu hv h₁ h₂
  · exact equivalent_symm (key v u hv hu h₂ h₁)

theorem equivalent_trans {u v w : RoundPastingDiagram X} (h : Equivalent u v)
    (h' : Equivalent v w) : Equivalent u w := by
  obtain ⟨hd, e, he, hde, hs, ht⟩ := h.data
  obtain ⟨hd', e', he', hde', hs', ht'⟩ := h'.data
  have hde'' : e'.dim = u.dim + 1 := by rw [hde', hd]
  let d : PasteAtData false u.dim e e' :=
    PasteAtData.ofBoundary hde hde'' (by
      change (e.boundary u.dim true).Equiv (e'.boundary u.dim false)
      rw [PastingDiagram.boundary_congr e'.toPastingDiagram hd false]
      exact ht.trans (hs'.symm))
  refine EquivalenceData.equivalent
    ⟨hd.trans hd', d.round, (pasteAt_mem_equivalences_iff d he).2 he', d.dim_pasting, ?_, ?_⟩
  · exact PastingDiagram.Equiv.trans
      (d.equiv_boundary_pasting_of_image_univ (Within.image_refl _)) hs
  · have h2 := d.equiv_boundary_not
    rw [PastingDiagram.boundary_congr e'.toPastingDiagram hd] at h2
    exact h2.trans ht'

instance : IsEquiv (RoundPastingDiagram X) Equivalent where
  refl := equivalent_refl
  symm _ _ := equivalent_symm
  trans _ _ _ := equivalent_trans

theorem mem_equivalences_of_equivalent {u v : RoundPastingDiagram X} (h : Equivalent u v)
    (hv : v ∈ equivalences X) : u ∈ equivalences X := by
  rw [← eqvSolutions_eq_equivalences] at hv ⊢
  obtain ⟨hd, k, hk, hdk, hs, ht⟩ := h.data
  rw [← eqvSolutions_eq_equivalences] at hk
  obtain ⟨k', hk', ht'⟩ := exists_inverse_mem_eqvSolutions hk hdk
  rw [← solutionOperator_eqvSolutions]
  refine ⟨by rw [hd]; exact pos_dim_of_mem_eqvSolutions hv, fun α n u' eq => ?_⟩
  have hn : u.dim = n + 1 := eq.dim_e
  have hvn : v.dim = n + 1 := by rw [← hd]; exact hn
  have pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure (eqvSolutions X) kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram u.toPastingDiagram v.toPastingDiagram := by
    intro β
    cases β
    · refine ⟨k, .base hk, ⟨by rw [hdk, hn], hn, hvn, ?_, ?_⟩⟩
      · rw [← PastingDiagram.boundary_congr k.toPastingDiagram hn false]; exact hs
      · rw [Bool.not_false, ← PastingDiagram.boundary_congr k.toPastingDiagram hn true]
        exact ht
    · refine ⟨k', .base hk', HasBdry.symm (β := false) ⟨by rw [ht'.dim_h, hn], hvn, hn, ?_, ?_⟩⟩
      · rw [← PastingDiagram.boundary_congr k'.toPastingDiagram hn false]
        exact ht'.side.trans ht
      · rw [Bool.not_false, ← PastingDiagram.boundary_congr k'.toPastingDiagram hn true]
        exact ht'.other.trans hs
  obtain ⟨k₀, -, hk₀⟩ := pair false
  let eq' : Equation α n v u' :=
    eq.ofEquiv hvn (hk₀.equiv_boundary (Nat.lt_succ_self n) α)
  obtain ⟨s'⟩ := unbiased_tClosure_eqvSolutions hv α n u' eq'
  obtain ⟨s⟩ := nonempty_unbiasedSolution_of_pair (fun _ hd => isDegenerate_mem_eqvSolutions hd)
    eq hvn (hk₀.equiv_boundary (Nat.lt_succ_self n) α) pair s'
  exact ⟨s.toLax.mono fun _ ha => mem_eqvSolutions_of_tClosure ha⟩

theorem mem_equivalences_iff_of_equivalent {u v : RoundPastingDiagram X} (h : Equivalent u v) :
    u ∈ equivalences X ↔ v ∈ equivalences X :=
  ⟨mem_equivalences_of_equivalent (equivalent_symm h), mem_equivalences_of_equivalent h⟩

theorem Equivalent.equiv_boundary {u v : RoundPastingDiagram X} (h : Equivalent u v) {k : ℕ}
    (hk : k < u.dim) (β : Bool) : (u.boundary k β).Equiv (v.boundary k β) := by
  obtain ⟨-, e, -, -, hs, ht⟩ := h.data
  exact (hs.boundary k β).symm.trans
    ((equiv_boundary_boundary e.toPastingDiagram hk false β).trans
      (PastingDiagram.Equiv.trans
        ((equiv_boundary_boundary e.toPastingDiagram hk true β).symm)
        (ht.boundary k β)))

theorem pastable_of_equivalent_left {u u' v : RoundPastingDiagram X} (hu : Equivalent u u')
    {k : ℕ} (hp : u.Pastable v.toPastingDiagram k) : u'.Pastable v.toPastingDiagram k :=
  ⟨PastingDiagram.Equiv.trans
    ((hu.equiv_boundary (lt_min_iff.1 hp.2).1 true).symm) hp.1,
    by rw [← hu.data.dim_eq]; exact hp.2⟩

theorem SubstituteData.equivalent {u w w' : RoundPastingDiagram X} (D : SubstituteData u w)
    (hh : D.rewrite ∈ equivalences X)
    (ht : (D.pasteData.pasting.boundary u.dim true).Equiv w'.toPastingDiagram) :
    Equivalent u w' :=
  EquivalenceData.equivalent
    ⟨(dim_boundary D.pasteData.pasting (by rw [D.pasteData.dim_pasting]; omega) true).symm.trans
        (dim_eq_of_equiv ht),
      D.pasteData.round, (pasteAt_mem_equivalences_iff _ hh).2 (unit_mem_equivalences u),
      D.pasteData.dim_pasting, D.equiv_source, ht⟩

theorem equivalent_substitute (u : RoundPastingDiagram X) {v : PastingDiagram X}
    (ι : PastingDiagram.Within v u.toPastingDiagram)
    (hι : u.toPastingDiagram.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (w : RoundPastingDiagram X) (hp : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)
    (he : Equivalent ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)
    (hr : (u.substitute ι hι w hp).IsRound) :
    Equivalent u ⟨u.substitute ι hι w hp, hr⟩ := by
  obtain ⟨-, h, hh, hdh, hs, ht⟩ := he.data
  have hdim : (⟨v, ι.round_image_iff.1 hι.isRound⟩ : RoundPastingDiagram X).dim = u.dim :=
    (ι.isRewritableSubmolecule_image_iff.1 hι).2.2
  rw [PastingDiagram.boundary_congr h.toPastingDiagram hdim] at hs ht
  let D : SubstituteData u w := ⟨v, ι, hι, h, hdh.trans (congrArg (· + 1) hdim), hs, ht⟩
  exact D.equivalent hh (D.equiv_target_substitute hp)

theorem equivalent_paste_cond (α : Bool) {c h h' : RoundPastingDiagram X} (hh : Equivalent h h')
    {k k' : ℕ} (hkk : k = k') (hd : c.dim = h.dim)
    (hp : (cond α c.toPastingDiagram h.toPastingDiagram).Pastable
      (cond α h.toPastingDiagram c.toPastingDiagram) k)
    (hp' : (cond α c.toPastingDiagram h'.toPastingDiagram).Pastable
      (cond α h'.toPastingDiagram c.toPastingDiagram) k')
    (hr : ((cond α c.toPastingDiagram h.toPastingDiagram).paste
      (cond α h.toPastingDiagram c.toPastingDiagram) k hp).IsRound)
    (hr' : ((cond α c.toPastingDiagram h'.toPastingDiagram).paste
      (cond α h'.toPastingDiagram c.toPastingDiagram) k' hp').IsRound) :
    Equivalent ⟨_, hr⟩ ⟨_, hr'⟩ := by
  subst hkk
  exact (SubstituteData.ofPaste α hp hr hh.data.hasBdry hd).equivalent hh.data.mem
    (SubstituteData.equiv_target_ofPaste α hp hr hh.data.hasBdry hd hp')

theorem equivalent_paste_left {u u' v : RoundPastingDiagram X} (hu : Equivalent u u') {k : ℕ}
    (hd : u.dim = v.dim) (hp : u.Pastable v.toPastingDiagram k)
    (hp' : u'.Pastable v.toPastingDiagram k) (hr : (u.paste v.toPastingDiagram k hp).IsRound)
    (hr' : (u'.paste v.toPastingDiagram k hp').IsRound) :
    Equivalent ⟨u.paste v.toPastingDiagram k hp, hr⟩ ⟨u'.paste v.toPastingDiagram k hp', hr'⟩ :=
  equivalent_paste_cond false hu rfl hd.symm hp hp' hr hr'

theorem equivalent_paste_right {u v v' : RoundPastingDiagram X} (hv : Equivalent v v')
    {k k' : ℕ} (hkk : k = k') (hd : u.dim = v.dim) (hp : u.Pastable v.toPastingDiagram k)
    (hp' : u.Pastable v'.toPastingDiagram k') (hr : (u.paste v.toPastingDiagram k hp).IsRound)
    (hr' : (u.paste v'.toPastingDiagram k' hp').IsRound) :
    Equivalent ⟨u.paste v.toPastingDiagram k hp, hr⟩ ⟨u.paste v'.toPastingDiagram k' hp', hr'⟩ :=
  equivalent_paste_cond true hv hkk hd hp hp' hr hr'

theorem equivalent_paste (u u' v v' : RoundPastingDiagram X)
    (hu : Equivalent u u') (hv : Equivalent v v')
    (hd : u.dim = v.dim)
    (h : u.Pastable v.toPastingDiagram (u.dim - 1))
    (h' : u'.Pastable v'.toPastingDiagram (u'.dim - 1))
    (hr : (u.paste v.toPastingDiagram (u.dim - 1) h).IsRound)
    (hr' : (u'.paste v'.toPastingDiagram (u'.dim - 1) h').IsRound) :
    Equivalent ⟨u.paste v.toPastingDiagram (u.dim - 1) h, hr⟩
      ⟨u'.paste v'.toPastingDiagram (u'.dim - 1) h', hr'⟩ := by
  have hpos : 0 < u.dim := by have := (lt_min_iff.1 h.2).1; omega
  have hdu : u.dim = u'.dim := hu.data.dim_eq
  have h₁ : u'.Pastable v.toPastingDiagram (u.dim - 1) := pastable_of_equivalent_left hu h
  have hr₁ : (u'.paste v.toPastingDiagram (u.dim - 1) h₁).IsRound :=
    isRound_paste_of_dim u' v (by omega) (by omega) h₁
  exact equivalent_trans (equivalent_paste_left hu hd h h₁ hr hr₁)
    (equivalent_paste_right hv (by rw [hdu]) (hdu.symm.trans hd) h₁ h' hr₁ hr')

theorem mem_equivalences_of_topCells (u : RoundPastingDiagram X) (hd : 0 < u.dim)
    (h : ∀ (U : Atom) (x : diagram X U), U.dimension = u.dim →
      (∃ (v : PastingDiagram X) (ι : PastingDiagram.Within v u.toPastingDiagram),
        IsSubmoleculeOf u.toPastingDiagram.shape.ogp ι.image ⊤ ∧
          v.Equiv (PastingDiagram.ofCell x)) →
      IsEquivalence X x) : u ∈ equivalences X :=
  mem_equivalences_of_forall_cellAt u hd fun t ht => h _ (u.cellAt t)
    (by
      have h1 := dim_restrictTo u.toPastingDiagram
        ((u.shape.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := t))).1)
      rw [← dim_eq_of_equiv (u.equiv_ofCell_cellAt t), LowerSet.krullDim_Iic, ht] at h1
      exact_mod_cast h1)
    ⟨_, Within.restrictTo u.toPastingDiagram
      (u.shape.isMolecule.Iic_isSubmoleculeOf (LowerSet.mem_top (a := t))).isMoleculeIn,
      Within.isSubmoleculeOf_image_restrictTo _
        (u.shape.isMolecule.Iic_isSubmoleculeOf (LowerSet.mem_top (a := t))),
      (u.equiv_ofCell_cellAt t).symm⟩

end Atoms.Diagrammatic
