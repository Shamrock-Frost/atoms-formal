import Atoms.Diagrammatic.Equivalence.WeakInverse

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

inductive PastingClosure (A : Set (RoundPastingDiagram X)) : Set (RoundPastingDiagram X)
  | base {a : RoundPastingDiagram X} (ha : a ∈ A) : PastingClosure A a
  | equivalence {e : RoundPastingDiagram X} (he : e ∈ equivalences X) : PastingClosure A e
  | pasteAt {u v : RoundPastingDiagram X} {n : ℕ} {α : Bool} (d : PasteAtData α n u v)
      (hu : PastingClosure A u) (hv : PastingClosure A v) : PastingClosure A d.round

def ArrowIn (S : Set (RoundPastingDiagram X)) (u v : RoundPastingDiagram X) : Prop :=
  ∃ h ∈ S, HasBdry false u.dim h.toPastingDiagram u.toPastingDiagram v.toPastingDiagram

def HasSideInverse (S : Set (RoundPastingDiagram X)) (α : Bool) (u : RoundPastingDiagram X) :
    Prop :=
  ∃ (n : ℕ) (u' : RoundPastingDiagram X) (d : PasteAtData false n (cond α u' u) (cond α u u')),
    HasBdry false n u'.toPastingDiagram (u.boundary n true) (u.boundary n false) ∧
    d.occ.image = ⊤ ∧
    cond α (ArrowIn S (isRound_boundary_of_isRound u.isRound n true).unit d.round)
      (ArrowIn S d.round (isRound_boundary_of_isRound u.isRound n false).unit)

theorem subset_pastingClosure (A : Set (RoundPastingDiagram X)) : A ⊆ PastingClosure A :=
  fun _ ha => .base ha

theorem equivalences_subset_pastingClosure (A : Set (RoundPastingDiagram X)) :
    equivalences X ⊆ PastingClosure A :=
  fun _ he => .equivalence he

theorem ArrowIn.mono {S T : Set (RoundPastingDiagram X)} (hST : S ⊆ T)
    {u v : RoundPastingDiagram X} (h : ArrowIn S u v) : ArrowIn T u v :=
  h.elim fun k hk => ⟨k, hST hk.1, hk.2⟩

theorem HasSideInverse.mono {S T : Set (RoundPastingDiagram X)} (hST : S ⊆ T) {α : Bool}
    {u : RoundPastingDiagram X} (h : HasSideInverse S α u) : HasSideInverse T α u := by
  obtain ⟨n, u', d, hb, hocc, ha⟩ := h
  refine ⟨n, u', d, hb, hocc, ?_⟩
  cases α
  exacts [ha.mono hST, ha.mono hST]

private theorem dim_unit_boundary (u : RoundPastingDiagram X) {n : ℕ} (hn : u.dim = n + 1)
    (β : Bool) : (isRound_boundary_of_isRound u.isRound n β).unit.dim = n + 1 :=
  (dim_unit _).trans (congrArg (· + 1) (dim_boundary _ (by omega) _))

private theorem BiInvData.hasSideInverse {S : Set (RoundPastingDiagram X)}
    {u : RoundPastingDiagram X} (D : BiInvData S u) (α : Bool) : HasSideInverse S α u := by
  have hn : u.dim = u.dim - 1 + 1 := (Nat.sub_add_cancel D.dim_pos).symm
  have hi : (D.inverse α).dim = u.dim - 1 + 1 := (D.dim_inverse α).trans hn
  have hb : HasBdry false (u.dim - 1) (D.inverse α).toPastingDiagram (u.boundary (u.dim - 1) true)
      (u.boundary (u.dim - 1) false) :=
    ⟨hi, dim_boundary _ (Nat.sub_le _ _) _, dim_boundary _ (Nat.sub_le _ _) _,
      D.equiv_boundary_inverse α false, D.equiv_boundary_inverse α true⟩
  have hz := D.dim_invertor α
  have hc := D.boundary_invertor_composite α
  have hu := D.boundary_invertor_unit α
  cases α
  · let d : PasteAtData false (u.dim - 1) u (D.inverse false) :=
      PasteAtData.ofBoundary hn hi (D.pastable false).1
    have hp := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf
      (Within.image_refl _) d.equiv (D.pastable false)
    exact ⟨u.dim - 1, D.inverse false, d, hb, Within.image_refl _, D.invertor false,
      D.invertor_mem false, HasBdry.of_dim_eq (hn.trans d.dim_pasting.symm) hz rfl
        ((dim_unit_boundary u hn false).trans d.dim_pasting.symm) (hc.trans hp) hu⟩
  · let d : PasteAtData false (u.dim - 1) (D.inverse true) u :=
      PasteAtData.ofBoundary hi hn (D.pastable true).1
    have hp := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf
      (Within.image_refl _) d.equiv (D.pastable true)
    exact ⟨u.dim - 1, D.inverse true, d, hb, Within.image_refl _, D.invertor true,
      D.invertor_mem true, HasBdry.of_dim_eq (hn.trans (dim_unit_boundary u hn true).symm) hz
        rfl (d.dim_pasting.trans (dim_unit_boundary u hn true).symm) hu (hc.trans hp)⟩

private theorem HasSideInverse.exists_invertor {S : Set (RoundPastingDiagram X)} {α : Bool}
    {u : RoundPastingDiagram X} (h : HasSideInverse S α u) :
    ∃ (u' z : RoundPastingDiagram X), z ∈ S ∧ 0 < u.dim ∧ u'.dim = u.dim ∧
      (∀ γ, (u'.boundary (u.dim - 1) γ).Equiv (u.boundary (u.dim - 1) (!γ))) ∧
      z.dim = u.dim + 1 ∧
      ∃ hp : (cond α u'.toPastingDiagram u.toPastingDiagram).Pastable
        (cond α u.toPastingDiagram u'.toPastingDiagram) (u.dim - 1),
        (z.boundary u.dim α).Equiv ((cond α u'.toPastingDiagram u.toPastingDiagram).paste
          (cond α u.toPastingDiagram u'.toPastingDiagram) (u.dim - 1) hp) ∧
        (z.boundary u.dim (!α)).Equiv (u.boundary (u.dim - 1) α).unit := by
  obtain ⟨n, u', d, hb, hocc, ha⟩ := h
  have hpst : (cond α u' u).toPastingDiagram.Pastable (cond α u u').toPastingDiagram n :=
    ⟨d.equiv.trans (Within.equiv_of_image_eq d.occ (Within.refl _)
      (by rw [hocc, Within.image_refl])), by rw [d.dim_e, d.dim_u']; omega⟩
  have hp := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf hocc
    d.equiv hpst
  have hun : u.dim = n + 1 := by cases α; exacts [d.dim_e, d.dim_u']
  have hn : u.dim - 1 = n := by omega
  have hbi : ∀ γ, (u'.boundary n γ).Equiv (u.boundary n (!γ)) := fun γ => by
    cases γ; exacts [hb.side, hb.other]
  rw [hn]
  cases α
  · obtain ⟨z, hz, hzb⟩ := ha
    rw [show d.round.dim = u.dim from d.dim_pasting.trans hun.symm] at hzb
    exact ⟨u', z, hz, by omega, hb.dim_h.trans hun.symm, hbi, hzb.dim_h, hpst,
      hzb.side.trans hp.symm, hzb.other⟩
  · obtain ⟨z, hz, hzb⟩ := ha
    rw [show _ = u.dim from (dim_unit_boundary u hun true).trans hun.symm] at hzb
    exact ⟨u', z, hz, by omega, hb.dim_h.trans hun.symm, hbi, hzb.dim_h, hpst,
      hzb.other.trans hp.symm, hzb.side⟩

theorem mem_biInvOperator_iff {S : Set (RoundPastingDiagram X)} {u : RoundPastingDiagram X} :
    u ∈ biInvOperator X S ↔ HasSideInverse S false u ∧ HasSideInverse S true u := by
  refine ⟨fun h => ⟨BiInvData.hasSideInverse (BiInvWitness.data h) false,
    BiInvData.hasSideInverse (BiInvWitness.data h) true⟩, fun ⟨hL, hR⟩ => ?_⟩
  obtain ⟨uL, zL, hzL, hd, hdL, hbL, hdzL, hpL, hcL, huL⟩ := hL.exists_invertor
  obtain ⟨uR, zR, hzR, -, hdR, hbR, hdzR, hpR, hcR, huR⟩ := hR.exists_invertor
  exact BiInvData.witness
    { dim_pos := hd
      inverse := fun α => cond α uR uL
      invertor := fun α => cond α zR zL
      invertor_mem := fun α => by cases α; exacts [hzL, hzR]
      dim_inverse := fun α => by cases α; exacts [hdL, hdR]
      dim_invertor := fun α => by cases α; exacts [hdzL, hdzR]
      equiv_boundary_inverse := fun α => by cases α; exacts [hbL, hbR]
      pastable := fun α => by cases α; exacts [hpL, hpR]
      boundary_invertor_composite := fun α => by cases α; exacts [hcL, hcR]
      boundary_invertor_unit := fun α => by cases α; exacts [huL, huR] }

theorem arrowIn_equivalences_iff {u v : RoundPastingDiagram X} :
    ArrowIn (equivalences X) u v ↔ Equivalent u v := by
  refine ⟨fun ⟨h, hh, hb⟩ => EquivalenceData.equivalent
    ⟨hb.dim_b.symm, h, hh, hb.dim_h, hb.side, hb.other⟩, fun h => ?_⟩
  obtain ⟨hd, e, he, hde, hs, ht⟩ := h.data
  exact ⟨e, he, hde, rfl, hd.symm, hs, ht⟩

theorem Equivalent.arrowIn_pastingClosure (A : Set (RoundPastingDiagram X))
    {u v : RoundPastingDiagram X} (h : Equivalent u v) : ArrowIn (PastingClosure A) u v :=
  (arrowIn_equivalences_iff.2 h).mono (equivalences_subset_pastingClosure A)

theorem arrowIn_pastingClosure_refl (A : Set (RoundPastingDiagram X)) (u : RoundPastingDiagram X) :
    ArrowIn (PastingClosure A) u u :=
  (equivalent_refl u).arrowIn_pastingClosure A

theorem ArrowIn.trans_pastingClosure {A : Set (RoundPastingDiagram X)}
    {u v w : RoundPastingDiagram X} (h₁ : ArrowIn (PastingClosure A) u v)
    (h₂ : ArrowIn (PastingClosure A) v w) : ArrowIn (PastingClosure A) u w := by
  obtain ⟨h, hh, hb⟩ := h₁
  obtain ⟨z, hz, hb'⟩ := h₂
  rw [hb.dim_b] at hb'
  let d : PasteAtData false u.dim h z :=
    PasteAtData.ofBoundary hb.dim_h hb'.dim_h (hb.other.trans hb'.side.symm)
  exact ⟨d.round, .pasteAt d hh hz, d.dim_pasting, rfl, hb'.dim_b,
    (d.equiv_boundary_pasting_of_image_univ (Within.image_refl _)).trans hb.side,
    d.equiv_boundary_not.trans hb'.other⟩

theorem SubstituteData.arrowIn {A : Set (RoundPastingDiagram X)}
    {u w w' : RoundPastingDiagram X} (D : SubstituteData u w) (hh : D.rewrite ∈ PastingClosure A)
    (ht : (D.pasteData.pasting.boundary u.dim true).Equiv w'.toPastingDiagram) :
    ArrowIn (PastingClosure A) u w' :=
  ⟨D.pasteData.round, .pasteAt _ hh (.equivalence (unit_mem_equivalences u)),
    D.pasteData.dim_pasting, rfl,
    ((dim_boundary D.pasteData.pasting (by rw [D.pasteData.dim_pasting]; omega) true).symm.trans
      (dim_eq_of_equiv ht)).symm, D.equiv_source, ht⟩

theorem arrowIn_pastingClosure_substitute {A : Set (RoundPastingDiagram X)}
    (u : RoundPastingDiagram X) {v : PastingDiagram X}
    (ι : PastingDiagram.Within v u.toPastingDiagram)
    (hι : u.toPastingDiagram.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (w : RoundPastingDiagram X) (hp : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)
    (hvw : ArrowIn (PastingClosure A) ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)
    (hr : (u.substitute ι hι w hp).IsRound) :
    ArrowIn (PastingClosure A) u ⟨u.substitute ι hι w hp, hr⟩ := by
  obtain ⟨h, hh, hb⟩ := hvw
  have hdim : (⟨v, ι.round_image_iff.1 hι.isRound⟩ : RoundPastingDiagram X).dim = u.dim :=
    (ι.isRewritableSubmolecule_image_iff.1 hι).2.2
  rw [hdim] at hb
  let D : SubstituteData u w := ⟨v, ι, hι, h, hb.dim_h, hb.side, hb.other⟩
  exact D.arrowIn hh (D.equiv_target_substitute hp)

theorem arrowIn_pastingClosure_paste_cond (α : Bool) {A : Set (RoundPastingDiagram X)}
    {c h h' : RoundPastingDiagram X} (hh : ArrowIn (PastingClosure A) h h')
    {k k' : ℕ} (hkk : k = k') (hd : c.dim = h.dim)
    (hp : (cond α c.toPastingDiagram h.toPastingDiagram).Pastable
      (cond α h.toPastingDiagram c.toPastingDiagram) k)
    (hp' : (cond α c.toPastingDiagram h'.toPastingDiagram).Pastable
      (cond α h'.toPastingDiagram c.toPastingDiagram) k')
    (hr : ((cond α c.toPastingDiagram h.toPastingDiagram).paste
      (cond α h.toPastingDiagram c.toPastingDiagram) k hp).IsRound)
    (hr' : ((cond α c.toPastingDiagram h'.toPastingDiagram).paste
      (cond α h'.toPastingDiagram c.toPastingDiagram) k' hp').IsRound) :
    ArrowIn (PastingClosure A) ⟨_, hr⟩ ⟨_, hr'⟩ := by
  subst hkk
  obtain ⟨r, hrA, hb⟩ := hh
  exact (SubstituteData.ofPaste α hp hr hb hd).arrowIn hrA
    (SubstituteData.equiv_target_ofPaste α hp hr hb hd hp')

theorem arrowIn_pastingClosure_pasteAt {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e e' w : RoundPastingDiagram X} (d : PasteAtData α n e w) (d' : PasteAtData α n e' w)
    (hocc : d'.occ.image = d.occ.image) (he : ArrowIn (PastingClosure A) e e') :
    ArrowIn (PastingClosure A) d.round d'.round := by
  obtain ⟨h, hh, hb⟩ := he
  have hde : e.dim = d.round.dim := d.dim_e.trans d.dim_pasting.symm
  rw [hde] at hb
  let D : SubstituteData d.round e' := ⟨e.toPastingDiagram, d.pasteAtInl,
    d.pasteAtInl.isRewritableSubmolecule_image_iff.2
      ⟨d.isPastingAtIn_pasteAtInl.isSubmoleculeOf_left, e.isRound, hde⟩, h, hb.dim_h, hb.side,
    hb.other⟩
  refine D.arrowIn hh (D.equiv_target_restrictTo.trans (PastingDiagram.Equiv.symm ?_))
  have hpst := d.isPastingAtIn_trans D.withinU
  have hs := D.isSubstitutionIn
  have hkS : (n : WithBot ℕ∞) < krullDim (d.pasteAtInl.trans D.withinU).image := by
    rw [Within.krullDim_image, d.dim_e]; exact_mod_cast n.lt_succ_self
  have hc := hpst.subst_left_self hs hkS
  have hW : krullDim D.withinW.image = n + 1 := by
    rw [Within.krullDim_image]; exact_mod_cast d'.dim_e
  have hmeet : (d'.occ.trans ((Within.boundary w.toPastingDiagram n α).trans
      (d.pasteAtInr.trans D.withinU))).image = D.withinW.image ⊓
        (d.pasteAtInr.trans D.withinU).image := by
    have hS : D.occ.trans D.withinU = d.pasteAtInl.trans D.withinU := rfl
    have hU : ∀ {V : PastingDiagram X} (o : Within V (w.boundary n α)),
        (o.trans ((Within.boundary w.toPastingDiagram n α).trans
          (d.pasteAtInr.trans D.withinU))).image =
        OGP.map D.withinU.emb (o.trans ((Within.boundary w.toPastingDiagram n α).trans
          d.pasteAtInr)).image := fun o =>
      Within.image_trans_assoc (o.trans (Within.boundary w.toPastingDiagram n α)) d.pasteAtInr
        D.withinU
    rw [hc.inf_eq, ← bdry_eq_boundary hW, hs.bdry_eq, bdry_eq_boundary
      (hs.krullDim_target.symm.trans hW), hS, ← hpst.inf_eq, hU, Within.image_trans, hocc,
      ← Within.image_trans, d.image_occ_pasteAtInr]
    exact (OGP.map_inf _ _ _).trans
      (congrArg₂ (· ⊓ ·) (Within.image_trans _ _).symm (Within.image_trans _ _).symm)
  exact equiv_pasteAtBoundary_of_within D.withinW (d.pasteAtInr.trans D.withinU) hc d'.occ
    d'.rewritable.isSubmoleculeOf hmeet d'.equiv

end Atoms.Diagrammatic
