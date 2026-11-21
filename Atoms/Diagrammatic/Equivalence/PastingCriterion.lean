import Atoms.Diagrammatic.Equivalence.PastingClosure

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem ArrowIn.of_equiv_left {S : Set (RoundPastingDiagram X)} {u u' v : RoundPastingDiagram X}
    (h : ArrowIn S u v) (e : u.Equiv u'.toPastingDiagram) : ArrowIn S u' v := by
  obtain ⟨k, hk, hb⟩ := h
  refine ⟨k, hk, ?_⟩
  rw [← dim_eq_of_equiv e]
  exact hb.of_equiv_side e

theorem ArrowIn.of_equiv_right {S : Set (RoundPastingDiagram X)} {u v v' : RoundPastingDiagram X}
    (h : ArrowIn S u v) (e : v.Equiv v'.toPastingDiagram) : ArrowIn S u v' :=
  h.elim fun k hk => ⟨k, hk.1, hk.2.of_equiv_other e⟩

theorem ArrowIn.equiv_boundary {S : Set (RoundPastingDiagram X)} {u v : RoundPastingDiagram X}
    (h : ArrowIn S u v) {k : ℕ} (hk : k < u.dim) (γ : Bool) :
    (u.boundary k γ).Equiv (v.boundary k γ) :=
  h.elim fun _ hh => hh.2.equiv_boundary hk γ

private theorem image_trans_ofEquiv_trans_eq {A D D' m V : PastingDiagram X} (o : Within V A)
    (e : A.Equiv D) (e' : A.Equiv D') (w : Within D m) (w' : Within D' m)
    (h : w.image = w'.image) :
    (o.trans ((Within.ofEquiv e).trans w)).image = (o.trans ((Within.ofEquiv e').trans w')).image :=
  by rw [Within.ext_of_image_eq ((Within.ofEquiv e).trans w) ((Within.ofEquiv e').trans w')
    (by rw [Within.image_ofEquiv_trans, Within.image_ofEquiv_trans, h])]

private theorem OGP.IsPastingAtIn.flip {P : OGP.{u}} {k : ℕ} {α : Bool} {S T R : LowerSet P}
    (h : P.IsPastingAtIn k α S T R) (he : S ⊓ T = P.boundary T k α) :
    P.IsPastingAtIn k (!α) T S R :=
  ⟨h.isMoleculeIn_right, h.isMoleculeIn_left, h.eq_sup.trans (sup_comm _ _),
    by rw [inf_comm, he, Bool.not_not], by
      rw [inf_comm, h.inf_eq]
      exact IsSubmoleculeOf.refl (h.isMoleculeIn_left.boundary k (!α))⟩

private theorem krullDim_eq_of_le {m a : PastingDiagram X} {n : ℕ} (hm : m.dim = n + 1)
    (w : Within a m) (ha : a.dim = n + 1) {S : LowerSet m.shape.ogp} (hS : w.image ≤ S) :
    krullDim S = n + 1 := by
  refine le_antisymm ?_ ?_
  · have h : krullDim S ≤ krullDim (Within.refl m).image :=
      LowerSet.krullDim_mono (le_top.trans (Within.image_refl m).symm.le)
    rw [Within.krullDim_image, hm] at h
    exact_mod_cast h
  · have h : krullDim w.image ≤ krullDim S := LowerSet.krullDim_mono hS
    rw [Within.krullDim_image, ha] at h
    exact_mod_cast h

theorem PasteAtData.exists_within {α : Bool} {n : ℕ} {e w : RoundPastingDiagram X}
    (d : PasteAtData α n e w) {m : PastingDiagram X} (we : Within e.toPastingDiagram m)
    (ww : Within w.toPastingDiagram m) {R : LowerSet m.shape.ogp}
    (hc : IsPastingAtIn m.shape.ogp n α we.image ww.image R)
    (hmeet : (d.occ.trans ((Within.boundary w.toPastingDiagram n α).trans ww)).image =
      we.image ⊓ ww.image) :
    ∃ wd : Within d.round.toPastingDiagram m, wd.image = R := by
  classical
  exact ⟨(Within.ofEquiv (equiv_pasteAtBoundary_of_within we ww hc d.occ
      d.rewritable.isSubmoleculeOf hmeet d.equiv)).trans (Within.restrictTo m hc.isMoleculeIn),
    (Within.image_ofEquiv_trans _ _).trans (Within.image_restrictTo _ _)⟩

private theorem exists_within_of_isRound {m : PastingDiagram X} {n : ℕ} {S : LowerSet m.shape.ogp}
    (hS : IsMoleculeIn m.shape.ogp S) (hr : m.shape.ogp.IsRound S)
    (hd : krullDim S = (n : WithBot ℕ∞) + 1) :
    ∃ (w : RoundPastingDiagram X) (ww : Within w.toPastingDiagram m), ww.image = S ∧
      w.dim = n + 1 := by
  classical
  refine ⟨⟨m.restrictTo hS, (isRound_restrictTo_iff m hS).2 hr⟩, Within.restrictTo m hS,
    Within.image_restrictTo m hS, ?_⟩
  have h := dim_restrictTo m hS
  rw [hd] at h
  exact_mod_cast h

private theorem exists_pasteAtData_of_within {m : PastingDiagram X} {n : ℕ}
    {P Q : RoundPastingDiagram X} (hP : P.dim = n + 1) (hQ : Q.dim = n + 1)
    (wP : Within P.toPastingDiagram m) (wQ : Within Q.toPastingDiagram m)
    (hc : IsPastingAtIn m.shape.ogp n false wP.image wQ.image ⊤)
    (he : wP.image ⊓ wQ.image = m.shape.ogp.boundary wQ.image n false) :
    ∃ D : PasteAtData false n P Q, D.occ.image = ⊤ ∧ D.pasting.Equiv m ∧
      (P.boundary n true).Equiv (Q.boundary n false) := by
  classical
  have hb : (P.boundary n (!false)).Equiv (Q.boundary n false) :=
    Within.equiv_of_image_eq ((Within.boundary _ n true).trans wP)
      ((Within.boundary _ n false).trans wQ) (by
        rw [Within.image_boundary_trans, Within.image_boundary_trans, ← he, hc.inf_eq]; rfl)
  refine ⟨PasteAtData.ofBoundary hP hQ hb, Within.image_refl _,
    (equiv_pasteAtBoundary_of_within wP wQ hc (Within.refl _) (Within.isSubmoleculeOf_image_refl _)
      ?_ hb).trans (Within.equiv_restrictTo_of_eq (Within.refl m) (Within.image_refl m) _).symm, hb⟩
  rw [Within.image_trans, Within.image_refl]
  exact (Within.image_boundary_trans _ _ _).trans he.symm

private theorem Within.ofEquiv_trans_ofEquiv {a b c : PastingDiagram X} (e : a.Equiv b)
    (e' : b.Equiv c) (e'' : a.Equiv c) :
    (Within.ofEquiv e).trans (Within.ofEquiv e') = Within.ofEquiv e'' :=
  Within.ext_of_image_eq _ _ (by
    rw [Within.image_ofEquiv_trans, Within.image_ofEquiv, Within.image_ofEquiv])

private theorem OGP.IsPastingAtIn.of_eq {P : OGP.{u}} {k k' : ℕ} {α : Bool} {S T R : LowerSet P}
    (h : k = k') (hc : P.IsPastingAtIn k α S T R) : P.IsPastingAtIn k' α S T R :=
  h ▸ hc

private theorem OGP.IsPastingIn.isPastingAtIn {P : OGP.{u}} {k : ℕ} {S T R : LowerSet P}
    (h : P.IsPastingIn k S T R) (hS : IsMoleculeIn P S) (hT : IsMoleculeIn P T) :
    P.IsPastingAtIn k false S T R :=
  ⟨hS, hT, h.sup_eq.symm, h.inf_eq_output, by
    rw [h.inf_eq_input]; exact IsSubmoleculeOf.refl (hT.boundary k false)⟩

theorem exists_pasteAtData_of_isPastingAtIn {m : PastingDiagram X} {n : ℕ} {α : Bool}
    {P Q : RoundPastingDiagram X} (hP : P.dim = n + 1) (hQ : Q.dim = n + 1)
    (wP : Within P.toPastingDiagram m) (wQ : Within Q.toPastingDiagram m)
    {R : LowerSet m.shape.ogp} (hc : IsPastingAtIn m.shape.ogp n α wP.image wQ.image R) :
    ∃ (D : PasteAtData α n P Q) (wD : Within D.round.toPastingDiagram m), wD.image = R ∧
      (D.occ.trans ((Within.boundary Q.toPastingDiagram n α).trans wQ)).image =
        wP.image ⊓ wQ.image ∧
      (D.pasteAtInl.trans wD).image = wP.image ∧ (D.pasteAtInr.trans wD).image = wQ.image := by
  classical
  have hV := hc.isSubmoleculeOf_inf
  have hbP : (P.boundary n (!α)).Equiv (occurrenceDiagram wQ n α hV) :=
    equiv_boundary_occurrence wQ n α hV wP hc.inf_eq.symm
  have hrw : (Q.boundary n α).shape.ogp.IsRewritableSubmolecule (occurrence wQ n α hV).image ⊤ :=
    (occurrence wQ n α hV).isRewritableSubmolecule_image_iff.2
      ⟨isSubmoleculeOf_image_occurrence wQ n α hV,
        hbP.isRound_iff.1 (isRound_boundary_of_isRound P.isRound n (!α)),
        (dim_eq_of_equiv hbP).symm.trans ((dim_boundary _ (by omega) _).trans
          (dim_boundary _ (by omega) _).symm)⟩
  let D : PasteAtData α n P Q := ⟨hP, hQ, _, occurrence wQ n α hV, hrw, hbP⟩
  have hmeet : (D.occ.trans ((Within.boundary Q.toPastingDiagram n α).trans wQ)).image =
      wP.image ⊓ wQ.image := image_occurrence wQ n α hV
  have eD := equiv_pasteAtBoundary_of_within wP wQ hc D.occ D.rewritable.isSubmoleculeOf hmeet
    D.equiv
  obtain ⟨hl, hr⟩ := apply_iso_pasteAtInl_and_pasteAtInr_of_within wP wQ hc D.occ
    D.rewritable.isSubmoleculeOf hmeet hc.isMoleculeIn D.equiv eD
  let wD : Within D.round.toPastingDiagram m :=
    (Within.ofEquiv eD).trans (Within.restrictTo m hc.isMoleculeIn)
  have el : (D.pasteAtInl.trans wD).emb = wP.emb := by ext x; exact hl x
  have er : (D.pasteAtInr.trans wD).emb = wQ.emb := by ext y; exact hr y
  refine ⟨D, wD, (Within.image_ofEquiv_trans _ _).trans (Within.image_restrictTo _ _), hmeet, ?_,
    ?_⟩
  · change OGP.map _ ⊤ = OGP.map _ ⊤
    rw [el]
  · change OGP.map _ ⊤ = OGP.map _ ⊤
    rw [er]

private theorem equivalent_pasteAt_unit {α : Bool} {k : ℕ} {e x : RoundPastingDiagram X}
    (D : PasteAtData α k e x) (hocc : D.occ.image = ⊤)
    (he : e.Equiv (x.toPastingDiagram.boundary k α).unit) : Equivalent x D.round := by
  have hb : (e.boundary k (!α)).Equiv (x.boundary k α) :=
    D.equiv.trans (Within.equiv_of_image_eq D.occ (Within.refl _) (by rw [hocc, Within.image_refl]))
  have hdx : x.dim = k + 1 := D.dim_u'
  have hde : e.dim = k + 1 := D.dim_e
  have hdu : (x.toPastingDiagram.boundary k α).unit.dim = k + 1 := by
    rw [dim_unit, dim_boundary _ (by omega)]
  have hp : (cond α x.toPastingDiagram e.toPastingDiagram).Pastable
      (cond α e.toPastingDiagram x.toPastingDiagram) k := by
    cases α
    · exact ⟨hb, by simp only [cond_false, hde, hdx]; omega⟩
    · exact ⟨hb.symm, by simp only [cond_true, hde, hdx]; omega⟩
  have hpu : (cond α x.toPastingDiagram (x.toPastingDiagram.boundary k α).unit).Pastable
      (cond α (x.toPastingDiagram.boundary k α).unit x.toPastingDiagram) k := by
    cases α
    · exact ⟨boundary_unit (dim_boundary x.toPastingDiagram (by omega) false) true,
        by simp only [cond_false, hdu, hdx]; omega⟩
    · exact ⟨(boundary_unit (dim_boundary x.toPastingDiagram (by omega) true) false).symm,
        by simp only [cond_true, hdu, hdx]; omega⟩
  have e₂ := equiv_paste_pasteAtBoundary e.toPastingDiagram x.toPastingDiagram k α D.occ
    D.rewritable.isSubmoleculeOf hocc D.equiv hp
  have e₁ : ((cond α x.toPastingDiagram (x.toPastingDiagram.boundary k α).unit).paste
      (cond α (x.toPastingDiagram.boundary k α).unit x.toPastingDiagram) k hpu).Equiv
      ((cond α x.toPastingDiagram e.toPastingDiagram).paste
        (cond α e.toPastingDiagram x.toPastingDiagram) k hp) := by
    cases α
    · exact PastingDiagram.Equiv.paste he.symm (.refl _) hpu hp
    · exact PastingDiagram.Equiv.paste (.refl _) he.symm hpu hp
  exact equivalent_trans (equivalent_paste_unit_cond α x hdx hpu
    ((e₁.trans e₂).isRound_iff.2 D.isRound_pasting)) (equivalent_of_equiv (e₁.trans e₂))

private theorem equivalent_pasteAt_unit_right {k : ℕ} {e x : RoundPastingDiagram X}
    (D : PasteAtData false k x e) (hocc : D.occ.image = ⊤)
    (he : e.Equiv (x.toPastingDiagram.boundary k true).unit) : Equivalent x D.round := by
  have hb : (x.boundary k true).Equiv (e.boundary k false) :=
    D.equiv.trans (Within.equiv_of_image_eq D.occ (Within.refl _) (by rw [hocc, Within.image_refl]))
  have hdx : x.dim = k + 1 := D.dim_e
  have hde : e.dim = k + 1 := D.dim_u'
  have hdu : (x.toPastingDiagram.boundary k true).unit.dim = k + 1 := by
    rw [dim_unit, dim_boundary _ (by omega)]
  have hp : x.toPastingDiagram.Pastable e.toPastingDiagram k := ⟨hb, by rw [hde, hdx]; omega⟩
  have hpu : x.toPastingDiagram.Pastable (x.toPastingDiagram.boundary k true).unit k :=
    ⟨(boundary_unit (dim_boundary x.toPastingDiagram (by omega) true) false).symm,
      by rw [hdu, hdx]; omega⟩
  have e₂ := equiv_paste_pasteAtBoundary x.toPastingDiagram e.toPastingDiagram k false D.occ
    D.rewritable.isSubmoleculeOf hocc D.equiv hp
  have e₁ : (x.toPastingDiagram.paste (x.toPastingDiagram.boundary k true).unit k hpu).Equiv
      (x.toPastingDiagram.paste e.toPastingDiagram k hp) :=
    PastingDiagram.Equiv.paste (.refl _) he.symm hpu hp
  exact equivalent_trans (equivalent_paste_unit_cond true x hdx hpu
    ((e₁.trans e₂).isRound_iff.2 D.isRound_pasting)) (equivalent_of_equiv (e₁.trans e₂))

theorem arrowIn_pastingClosure_pasteAt_host {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e w w' : RoundPastingDiagram X} (d : PasteAtData α n e w) (d' : PasteAtData α n e w')
    (f : (w.boundary n α).Equiv (w'.boundary n α))
    (hocc : d'.occ.image = (d.occ.trans (Within.ofEquiv f)).image)
    (hw : ArrowIn (PastingClosure A) w w') : ArrowIn (PastingClosure A) d.round d'.round := by
  obtain ⟨h, hh, hb⟩ := hw
  have hdw : w.dim = d.round.dim := d.dim_u'.trans d.dim_pasting.symm
  rw [hdw] at hb
  let D : SubstituteData d.round w' := ⟨w.toPastingDiagram, d.pasteAtInr,
    d.pasteAtInr.isRewritableSubmolecule_image_iff.2
      ⟨d.isPastingAtIn_pasteAtInl.isSubmoleculeOf_right, w.isRound, hdw⟩, h, hb.dim_h, hb.side,
    hb.other⟩
  refine D.arrowIn hh (D.equiv_target_restrictTo.trans (PastingDiagram.Equiv.symm ?_))
  have hpst := d.isPastingAtIn_trans D.withinU
  have hs := D.isSubstitutionIn
  have hS : D.occ.trans D.withinU = d.pasteAtInr.trans D.withinU := rfl
  rw [hS] at hs
  have hkT : (n : WithBot ℕ∞) < krullDim (d.pasteAtInr.trans D.withinU).image := by
    rw [Within.krullDim_image, d.dim_u']; exact_mod_cast n.lt_succ_self
  have hc := hpst.subst_right_self hs hkT
  have hW : krullDim D.withinW.image = n + 1 := by
    rw [Within.krullDim_image]; exact_mod_cast d'.dim_u'
  have hT : krullDim (d.pasteAtInr.trans D.withinU).image = n + 1 := by
    rw [Within.krullDim_image]; exact_mod_cast d.dim_u'
  have hL : (Within.ofEquiv f).trans ((Within.boundary w'.toPastingDiagram n α).trans D.withinW) =
      (Within.boundary w.toPastingDiagram n α).trans (d.pasteAtInr.trans D.withinU) :=
    Within.ext_of_image_eq _ _ (by
      rw [Within.image_ofEquiv_trans, Within.image_boundary_trans, Within.image_boundary_trans,
        ← bdry_eq_boundary hW, hs.bdry_eq, bdry_eq_boundary hT])
  have hmeet : (d'.occ.trans ((Within.boundary w'.toPastingDiagram n α).trans D.withinW)).image =
      (d.pasteAtInl.trans D.withinU).image ⊓ D.withinW.image := by
    have h1 : (d.occ.trans ((Within.boundary w.toPastingDiagram n α).trans
        (d.pasteAtInr.trans D.withinU))).image = OGP.map D.withinU.emb
          (d.occ.trans ((Within.boundary w.toPastingDiagram n α).trans d.pasteAtInr)).image :=
      Within.image_trans_assoc (d.occ.trans (Within.boundary w.toPastingDiagram n α))
        d.pasteAtInr D.withinU
    rw [hc.inf_eq, ← hpst.inf_eq, Within.image_trans, hocc, ← Within.image_trans,
      Within.trans_assoc, hL, h1, d.image_occ_pasteAtInr]
    exact (OGP.map_inf _ _ _).trans
      (congrArg₂ (· ⊓ ·) (Within.image_trans _ _).symm (Within.image_trans _ _).symm)
  exact equiv_pasteAtBoundary_of_within (d.pasteAtInl.trans D.withinU) D.withinW hc d'.occ
    d'.rewritable.isSubmoleculeOf hmeet d'.equiv

theorem hasSideInverse_pasteAt_false_true {A : Set (RoundPastingDiagram X)} {n : ℕ}
    {u v : RoundPastingDiagram X} (d : PasteAtData false n u v)
    (hu : HasSideInverse (PastingClosure A) true u)
    (hv : HasSideInverse (PastingClosure A) true v) :
    HasSideInverse (PastingClosure A) true d.round := by
  classical
  obtain ⟨nu, uR, du, hbu, hou, hau⟩ := hu
  obtain ⟨nv, vR, dv, hbv, hov, hav⟩ := hv
  change PasteAtData false nu uR u at du
  change PasteAtData false nv vR v at dv
  change ArrowIn _ _ du.round at hau
  change ArrowIn _ _ dv.round at hav
  have hnu : nu = n := by have := du.dim_u'; have := d.dim_e; omega
  have hnv : nv = n := by have := dv.dim_u'; have := d.dim_u'; omega
  subst nu nv
  have hdv : v.dim = n + 1 := d.dim_u'
  obtain rfl : n = v.dim - 1 := by omega
  have hd : 0 < v.dim := by omega
  let d₂ : PasteAtData false (v.dim - 1) du.round v :=
    ⟨du.dim_pasting, d.dim_u', d.sub, d.occ, d.rewritable, du.equiv_boundary_not.trans d.equiv⟩
  have hε : ArrowIn (PastingClosure A) (unitData v hd false d.occ d.rewritable).round d₂.round :=
    arrowIn_pastingClosure_pasteAt _ d₂ rfl (hau.of_equiv_left (Equiv.unit d.equiv))
  have hlb := hasBdry_unitorRound v hd false d.occ d.rewritable
  rw [← hdv] at hlb
  have hl : Equivalent v (unitData v hd false d.occ d.rewritable).round :=
    EquivalenceData.equivalent ⟨hdv.trans (unitData v hd false d.occ d.rewritable).dim_pasting.symm,
      unitorRound v hd false d.occ d.rewritable,
      mem_equivalences_of_isDegenerate _ (isDegenerate_unitorRound v hd false d.occ d.rewritable),
      dim_unitorRound v hd false d.occ d.rewritable, hlb.other, hlb.side⟩
  have h₂ : ArrowIn (PastingClosure A) v d₂.round :=
    (hl.arrowIn_pastingClosure A).trans_pastingClosure hε
  have hdR : vR.dim = v.dim - 1 + 1 := hbv.dim_h
  let dM : PasteAtData true (v.dim - 1) d₂.round vR := PasteAtData.ofBoundary d₂.dim_pasting hdR
    ((h₂.equiv_boundary (by omega) false).symm.trans hbv.other.symm)
  let d₀ : PasteAtData true (v.dim - 1) v vR := PasteAtData.ofBoundary hdv hdR hbv.other.symm
  have hp₀ : vR.toPastingDiagram.Pastable v.toPastingDiagram (v.dim - 1) :=
    ⟨hbv.other, by rw [hdR]; omega⟩
  have e₀ : dv.pasting.Equiv d₀.pasting :=
    (equiv_paste_pasteAtBoundary _ _ _ false dv.occ dv.rewritable.isSubmoleculeOf hov dv.equiv
      hp₀).symm.trans (equiv_paste_pasteAtBoundary _ _ _ true d₀.occ d₀.rewritable.isSubmoleculeOf
      (Within.image_refl _) d₀.equiv hp₀)
  have hM : ArrowIn (PastingClosure A) (isRound_boundary_of_isRound v.isRound (v.dim - 1) true).unit
      dM.round :=
    (hav.of_equiv_right (v' := d₀.round) e₀).trans_pastingClosure
      (arrowIn_pastingClosure_pasteAt d₀ dM rfl h₂)
  let M := dM.pasting
  let wY := dM.pasteAtInl
  let wVR := dM.pasteAtInr
  let wUU := d₂.pasteAtInl.trans wY
  let wV := d₂.pasteAtInr.trans wY
  let wUR := du.pasteAtInl.trans wUU
  let wU := du.pasteAtInr.trans wUU
  have c0 : IsPastingAtIn M.shape.ogp (v.dim - 1) true wY.image wVR.image ⊤ :=
    dM.isPastingAtIn_pasteAtInl
  have c0e : wY.image ⊓ wVR.image = M.shape.ogp.boundary wVR.image (v.dim - 1) true :=
    inter_eq_boundary_pasteAt_of_image_univ _ _ _ true dM.occ dM.rewritable.isSubmoleculeOf
      (Within.image_refl _) dM.equiv
  have c1 : IsPastingAtIn M.shape.ogp (v.dim - 1) false wUU.image wV.image wY.image :=
    d₂.isPastingAtIn_trans wY
  have c2 : IsPastingAtIn M.shape.ogp (v.dim - 1) false wUR.image wU.image wUU.image :=
    du.isPastingAtIn_trans wUU
  have e₂ := c2.eq_sup
  rw [e₂] at c1 c2
  obtain ⟨cB, c4⟩ := c2.assoc_right c1
  have e₄ := c4.eq_sup
  rw [e₄] at c0 c0e c4
  have hUR : krullDim wUR.image = (v.dim - 1 : ℕ) + 1 := by
    rw [Within.krullDim_image, hbu.dim_h]; push_cast; rfl
  have hVR : krullDim wVR.image = (v.dim - 1 : ℕ) + 1 := by
    rw [Within.krullDim_image, hdR]; push_cast; rfl
  have hUV : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤
      krullDim (wU.image ⊔ wV.image : LowerSet M.shape.ogp) := by
    have h : krullDim wV.image ≤ krullDim (wU.image ⊔ wV.image : LowerSet M.shape.ogp) :=
      LowerSet.krullDim_mono le_sup_right
    refine le_trans ?_ h
    rw [Within.krullDim_image]
    exact_mod_cast Nat.sub_le v.dim 1
  have hkVR : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim wVR.image := by
    rw [hVR]; exact_mod_cast (v.dim - 1).le_succ
  have hrUR : M.shape.ogp.IsRound wUR.image := wUR.round_image_iff.2 uR.isRound
  obtain ⟨cA, c5⟩ := c4.assoc_mixed_right (α := true) c0 hrUR hUR hUV hkVR
  have c6 := cA.assoc_mixed_left (α := false) c4 (OGP.IsPastingAtIn.flip c0 c0e) hrUR hUR hkVR hUV
  have hmeet :
      (d.occ.trans ((Within.boundary v.toPastingDiagram (v.dim - 1) false).trans wV)).image =
      wU.image ⊓ wV.image := by
    have h1 :
        (d.occ.trans ((Within.boundary v.toPastingDiagram (v.dim - 1) false).trans wV)).image =
        OGP.map wY.emb (d₂.occ.trans
          ((Within.boundary v.toPastingDiagram (v.dim - 1) false).trans d₂.pasteAtInr)).image :=
      Within.image_trans_assoc (d.occ.trans (Within.boundary v.toPastingDiagram (v.dim - 1) false))
        d₂.pasteAtInr wY
    rw [h1, d₂.image_occ_pasteAtInr]
    refine ((OGP.map_inf _ _ _).trans (congrArg₂ (· ⊓ ·) (Within.image_trans _ _).symm
      (Within.image_trans _ _).symm)).trans ?_
    change wUU.image ⊓ wV.image = _
    rw [e₂, c1.inf_eq, c2.boundary_not, cB.inf_eq]
  obtain ⟨wW, hW⟩ := d.exists_within wU wV cB hmeet
  have hMd : M.dim = v.dim - 1 + 1 := dM.dim_pasting
  obtain ⟨w', ww', hww', hw'⟩ := exists_within_of_isRound cA.isMoleculeIn
    (cA.isRound (wVR.round_image_iff.2 vR.isRound) hVR (krullDim_eq_of_le hMd wVR hdR le_sup_right))
    (krullDim_eq_of_le hMd wVR hdR le_sup_right)
  rw [← hww', ← hW] at c6
  have hC : ww'.image ⊓ wW.image = M.shape.ogp.boundary wW.image (v.dim - 1) false := by
    rw [hww', hW]; exact (inf_comm _ _).trans c5.inf_eq
  obtain ⟨D, hDo, eD, hb₁⟩ :=
    exists_pasteAtData_of_within (P := w') (Q := d.round) hw' d.dim_pasting ww' wW c6 hC
  have hwd : d.round.dim = v.dim - 1 + 1 := d.dim_pasting
  have hb₀ : (w'.boundary (v.dim - 1) false).Equiv (d.round.boundary (v.dim - 1) true) :=
    (Within.equiv_of_image_eq ((Within.boundary _ _ false).trans ww')
      ((Within.boundary vR.toPastingDiagram _ false).trans wVR) (by
        rw [Within.image_boundary_trans, Within.image_boundary_trans, hww']
        exact cA.boundary_not)).trans (hbv.side.trans d.equiv_boundary_not.symm)
  refine ⟨v.dim - 1, w', D,
    ⟨hw', dim_boundary _ (by omega) _, dim_boundary _ (by omega) _, hb₀, hb₁⟩, hDo, ?_⟩
  exact (hM.of_equiv_right (v' := D.round) eD.symm).of_equiv_left
    (Equiv.unit d.equiv_boundary_not.symm)

theorem hasSideInverse_pasteAt_true_false {A : Set (RoundPastingDiagram X)} {n : ℕ}
    {u v : RoundPastingDiagram X} (d : PasteAtData true n u v)
    (hu : HasSideInverse (PastingClosure A) false u)
    (hv : HasSideInverse (PastingClosure A) false v) :
    HasSideInverse (PastingClosure A) false d.round := by
  classical
  obtain ⟨nu, uL, du, hbu, hou, hau⟩ := hu
  obtain ⟨nv, vL, dv, hbv, hov, hav⟩ := hv
  change PasteAtData false nu u uL at du
  change PasteAtData false nv v vL at dv
  change ArrowIn _ du.round _ at hau
  change ArrowIn _ dv.round _ at hav
  have hnu : nu = n := by have := du.dim_e; have := d.dim_e; omega
  have hnv : nv = n := by have := dv.dim_e; have := d.dim_u'; omega
  subst nu nv
  have hdv : v.dim = n + 1 := d.dim_u'
  obtain rfl : n = v.dim - 1 := by omega
  have hd : 0 < v.dim := by omega
  let d₂ : PasteAtData true (v.dim - 1) du.round v :=
    ⟨du.dim_pasting, d.dim_u', d.sub, d.occ, d.rewritable,
      (du.equiv_boundary_pasting_of_image_univ hou).trans d.equiv⟩
  have hε : ArrowIn (PastingClosure A) d₂.round (unitData v hd true d.occ d.rewritable).round :=
    arrowIn_pastingClosure_pasteAt d₂ _ rfl (hau.of_equiv_right (Equiv.unit d.equiv))
  have hrb := hasBdry_unitorReverseRound v hd true d.occ d.rewritable
  rw [← hdv] at hrb
  have hr : Equivalent v (unitData v hd true d.occ d.rewritable).round :=
    EquivalenceData.equivalent ⟨hdv.trans (unitData v hd true d.occ d.rewritable).dim_pasting.symm,
      unitorReverseRound v hd true d.occ d.rewritable,
      mem_equivalences_of_isDegenerate _
        (isDegenerate_unitorReverseRound v hd true d.occ d.rewritable),
      by rw [unitorReverseRound, dim_reverse, dim_unitorRound], hrb.other, hrb.side⟩
  have h₂ : ArrowIn (PastingClosure A) d₂.round v :=
    hε.trans_pastingClosure ((equivalent_symm hr).arrowIn_pastingClosure A)
  have hdL : vL.dim = v.dim - 1 + 1 := hbv.dim_h
  let dM : PasteAtData false (v.dim - 1) d₂.round vL := PasteAtData.ofBoundary d₂.dim_pasting hdL
    ((h₂.equiv_boundary (lt_of_lt_of_eq (Nat.lt_succ_self _) d₂.dim_pasting.symm) true).trans
      hbv.side.symm)
  let d₀ : PasteAtData false (v.dim - 1) v vL := PasteAtData.ofBoundary hdv hdL hbv.side.symm
  have hp₀ : v.toPastingDiagram.Pastable vL.toPastingDiagram (v.dim - 1) :=
    ⟨hbv.side.symm, by rw [hdL]; omega⟩
  have e₀ : dv.pasting.Equiv d₀.pasting :=
    (equiv_paste_pasteAtBoundary _ _ _ false dv.occ dv.rewritable.isSubmoleculeOf hov dv.equiv
      hp₀).symm.trans (equiv_paste_pasteAtBoundary _ _ _ false d₀.occ
        d₀.rewritable.isSubmoleculeOf (Within.image_refl _) d₀.equiv hp₀)
  have hM : ArrowIn (PastingClosure A) dM.round
      (isRound_boundary_of_isRound v.isRound (v.dim - 1) false).unit :=
    (arrowIn_pastingClosure_pasteAt dM d₀ rfl h₂).trans_pastingClosure
      (hav.of_equiv_left (u' := d₀.round) e₀)
  let M := dM.pasting
  let wX := dM.pasteAtInl
  let wVL := dM.pasteAtInr
  let wUU := d₂.pasteAtInl.trans wX
  let wV := d₂.pasteAtInr.trans wX
  let wU := du.pasteAtInl.trans wUU
  let wUL := du.pasteAtInr.trans wUU
  have c0 : IsPastingAtIn M.shape.ogp (v.dim - 1) false wX.image wVL.image ⊤ :=
    dM.isPastingAtIn_pasteAtInl
  have c0e : wX.image ⊓ wVL.image = M.shape.ogp.boundary wVL.image (v.dim - 1) false :=
    inter_eq_boundary_pasteAt_of_image_univ _ _ _ false dM.occ dM.rewritable.isSubmoleculeOf
      (Within.image_refl _) dM.equiv
  have c1 : IsPastingAtIn M.shape.ogp (v.dim - 1) true wUU.image wV.image wX.image :=
    d₂.isPastingAtIn_trans wX
  have c2 : IsPastingAtIn M.shape.ogp (v.dim - 1) false wU.image wUL.image wUU.image :=
    du.isPastingAtIn_trans wUU
  have he : wU.image ⊓ wUL.image = M.shape.ogp.boundary wUL.image (v.dim - 1) false :=
    (congrArg₂ (· ⊓ ·) (Within.image_trans _ _) (Within.image_trans _ _)).trans
      ((OGP.map_inf wUU.emb _ _).symm.trans ((congrArg (OGP.map wUU.emb)
        (inter_eq_boundary_pasteAt_of_image_univ _ _ _ false du.occ du.rewritable.isSubmoleculeOf
          hou du.equiv)).trans ((map_boundary wUU.emb _ _ _).trans
            (congrArg (M.shape.ogp.boundary · (v.dim - 1) false) (Within.image_trans _ _).symm))))
  have e₂ := c2.eq_sup
  rw [e₂] at c1 c2
  have hU : krullDim wU.image = (v.dim - 1 : ℕ) + 1 := by
    rw [Within.krullDim_image, d.dim_e]; push_cast; rfl
  have hUL : krullDim wUL.image = (v.dim - 1 : ℕ) + 1 := by
    rw [Within.krullDim_image, hbu.dim_h]; push_cast; rfl
  have hVL : krullDim wVL.image = (v.dim - 1 : ℕ) + 1 := by
    rw [Within.krullDim_image, hdL]; push_cast; rfl
  have hkUL : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim wUL.image := by
    rw [hUL]; exact_mod_cast (v.dim - 1).le_succ
  have hkVL : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim wVL.image := by
    rw [hVL]; exact_mod_cast (v.dim - 1).le_succ
  have hkV : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤ krullDim wV.image := by
    rw [Within.krullDim_image]; exact_mod_cast Nat.sub_le v.dim 1
  have hUV : ((v.dim - 1 : ℕ) : WithBot ℕ∞) ≤
      krullDim (wU.image ⊔ wV.image : LowerSet M.shape.ogp) :=
    hkV.trans (LowerSet.krullDim_mono le_sup_right)
  obtain ⟨cB, c4⟩ := c2.assoc_mixed_right (α := true) c1 (wU.round_image_iff.2 u.isRound) hU hkUL
    hkV
  have e₄ := c4.eq_sup
  rw [e₄] at c0 c0e c4
  have hrUL : M.shape.ogp.IsRound wUL.image := wUL.round_image_iff.2 uL.isRound
  obtain ⟨cA, c5⟩ := c4.assoc_mixed_right (α := false) c0 hrUL hUL hUV hkVL
  have c6 := cA.assoc_mixed_left (α := true) c4 (OGP.IsPastingAtIn.flip c0 c0e) hrUL hUL hkVL hUV
  have hmeet :
      (d.occ.trans ((Within.boundary v.toPastingDiagram (v.dim - 1) true).trans wV)).image =
      wU.image ⊓ wV.image := by
    have h1 : (d.occ.trans ((Within.boundary v.toPastingDiagram (v.dim - 1) true).trans wV)).image =
        OGP.map wX.emb (d₂.occ.trans
          ((Within.boundary v.toPastingDiagram (v.dim - 1) true).trans d₂.pasteAtInr)).image :=
      Within.image_trans_assoc (d.occ.trans (Within.boundary v.toPastingDiagram (v.dim - 1) true))
        d₂.pasteAtInr wX
    rw [h1, d₂.image_occ_pasteAtInr]
    refine ((OGP.map_inf _ _ _).trans (congrArg₂ (· ⊓ ·) (Within.image_trans _ _).symm
      (Within.image_trans _ _).symm)).trans ?_
    change wUU.image ⊓ wV.image = _
    rw [e₂, c1.inf_eq, Bool.not_true, c2.boundary_eq_left_of_inf_eq he, cB.inf_eq]
    rfl
  obtain ⟨wW, hW⟩ := d.exists_within wU wV cB hmeet
  have hMd : M.dim = v.dim - 1 + 1 := dM.dim_pasting
  obtain ⟨w', ww', hww', hw'⟩ := exists_within_of_isRound cA.isMoleculeIn
    (cA.isRound (wVL.round_image_iff.2 vL.isRound) hVL (krullDim_eq_of_le hMd wVL hdL le_sup_right))
    (krullDim_eq_of_le hMd wVL hdL le_sup_right)
  rw [← hww', ← hW] at c5
  have hC : wW.image ⊓ ww'.image = M.shape.ogp.boundary ww'.image (v.dim - 1) false := by
    rw [hww', hW]; exact (inf_comm _ _).trans c6.inf_eq
  have hwd : d.round.dim = v.dim - 1 + 1 := d.dim_pasting
  obtain ⟨D, hDo, eD, hb₁⟩ :=
    exists_pasteAtData_of_within (P := d.round) (Q := w') hwd hw' wW ww' c5 hC
  have hb₀ : (w'.boundary (v.dim - 1) true).Equiv (d.round.boundary (v.dim - 1) false) :=
    (Within.equiv_of_image_eq ((Within.boundary _ _ true).trans ww')
      ((Within.boundary vL.toPastingDiagram _ true).trans wVL) (by
        rw [Within.image_boundary_trans, Within.image_boundary_trans, hww']
        exact cA.boundary_not)).trans (hbv.other.trans d.equiv_boundary_not.symm)
  refine ⟨v.dim - 1, w', D, ⟨hw', dim_boundary _ (by omega) _, dim_boundary _ (by omega) _,
    hb₁.symm, hb₀⟩, hDo, ?_⟩
  exact (hM.of_equiv_left (u' := D.round) eD.symm).of_equiv_right
    (Equiv.unit d.equiv_boundary_not.symm)

theorem hasSideInverse_pasteAt_false_false {A : Set (RoundPastingDiagram X)} {n : ℕ}
    {u v : RoundPastingDiagram X} (d : PasteAtData false n u v)
    (hu : HasSideInverse (PastingClosure A) false u)
    (hv : HasSideInverse (PastingClosure A) false v) :
    HasSideInverse (PastingClosure A) false d.round := by
  classical
  obtain ⟨nu, uL, du, hbu, hou, hau⟩ := hu
  obtain ⟨nv, vL, dv, hbv, hov, hav⟩ := hv
  change PasteAtData false nu u uL at du
  change PasteAtData false nv v vL at dv
  change ArrowIn _ du.round _ at hau
  change ArrowIn _ dv.round _ at hav
  have hnu : nu = n := by have := du.dim_e; have := d.dim_e; omega
  have hnv : nv = n := by have := dv.dim_e; have := d.dim_u'; omega
  subst nu nv
  have hdu : u.dim = n + 1 := d.dim_e
  have hdv : v.dim = n + 1 := d.dim_u'
  have huL : uL.dim = n + 1 := hbu.dim_h
  have hvL : vL.dim = n + 1 := hbv.dim_h
  have f₁ : (v.boundary n false).Equiv (dv.round.boundary n true) :=
    hbv.other.symm.trans dv.equiv_boundary_not.symm
  let dY : PasteAtData true n uL dv.round := ⟨huL, dv.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₁), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₁).2
      d.rewritable, hbu.side.trans d.equiv⟩
  have f₂ : (v.boundary n false).Equiv (dY.round.boundary n false) :=
    (dv.equiv_boundary_pasting_of_image_univ hov).symm.trans dY.equiv_boundary_not.symm
  let dM : PasteAtData false n u dY.round := ⟨hdu, dY.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₂), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₂).2
      d.rewritable, d.equiv⟩
  let E := (isRound_boundary_of_isRound v.isRound n false).unit
  have hE : E.dim = n + 1 := by
    change (v.boundary n false).unit.dim = _
    rw [dim_unit, dim_boundary _ (by omega)]
  have bE (β : Bool) : (E.boundary n β).Equiv (v.boundary n false) :=
    boundary_unit (dim_boundary _ (by omega) _) β
  let dY₁ : PasteAtData true n uL E := ⟨huL, hE, d.sub,
    d.occ.trans (Within.ofEquiv (bE true).symm),
    (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff _).2 d.rewritable,
    hbu.side.trans d.equiv⟩
  have hYY₁ : ArrowIn (PastingClosure A) dY.round dY₁.round :=
    arrowIn_pastingClosure_pasteAt_host dY dY₁ (f₁.symm.trans (bE true).symm) (by
      change (d.occ.trans (Within.ofEquiv (bE true).symm)).image =
        ((d.occ.trans (Within.ofEquiv f₁)).trans (Within.ofEquiv _)).image
      rw [Within.trans_assoc, Within.ofEquiv_trans_ofEquiv]) hav
  have hY₁ : dY₁.round.dim = n + 1 := dY₁.dim_pasting
  let Ea := (isRound_boundary_of_isRound dY₁.round.isRound n true).unit
  have hEa : Ea.dim = n + 1 := by
    change (dY₁.round.boundary n true).unit.dim = _
    rw [dim_unit, dim_boundary _ (by omega)]
  let dN : PasteAtData true n Ea dY₁.round := PasteAtData.ofBoundary hEa hY₁
    (boundary_unit (dim_boundary _ (by omega) _) false)
  have hY₁N : Equivalent dY₁.round dN.round :=
    equivalent_pasteAt_unit dN (Within.image_refl _) (.refl _)
  let wEa := dN.pasteAtInl
  let wY₁ := dN.pasteAtInr
  let yL : Within uL.toPastingDiagram dY₁.round.toPastingDiagram := dY₁.pasteAtInl
  let yE : Within E.toPastingDiagram dY₁.round.toPastingDiagram := dY₁.pasteAtInr
  have hoY₁ : (dY₁.occ.trans ((Within.boundary E.toPastingDiagram n true).trans yE)).image =
      yL.image ⊓ yE.image := dY₁.image_occ_pasteAtInr
  let wE := yE.trans wY₁
  let wUL := yL.trans wY₁
  have n0 : IsPastingAtIn dN.pasting.shape.ogp n true wEa.image wY₁.image ⊤ :=
    dN.isPastingAtIn_pasteAtInl
  have n0e : wEa.image ⊓ wY₁.image = dN.pasting.shape.ogp.boundary wY₁.image n true :=
    inter_eq_boundary_pasteAt_of_image_univ _ _ _ true dN.occ dN.rewritable.isSubmoleculeOf
      (Within.image_refl _) dN.equiv
  have n1 : IsPastingAtIn dN.pasting.shape.ogp n true wUL.image wE.image wY₁.image :=
    dY₁.isPastingAtIn_trans wY₁
  have f₃ := n1.eq_sup
  rw [f₃] at n0 n0e n1
  have hdUL : krullDim wUL.image = (n : WithBot ℕ∞) + 1 := by
    rw [Within.krullDim_image, huL]; push_cast; rfl
  have hkE : (n : WithBot ℕ∞) ≤ krullDim wE.image := by
    rw [Within.krullDim_image, hE]; exact_mod_cast n.le_succ
  have hkEa : (n : WithBot ℕ∞) ≤ krullDim wEa.image := by
    rw [Within.krullDim_image, hEa]; exact_mod_cast n.le_succ
  have hrUL : dN.pasting.shape.ogp.IsRound wUL.image := wUL.round_image_iff.2 uL.isRound
  obtain ⟨n2, n3⟩ := n1.assoc_mixed_right (α := false)
    (OGP.IsPastingAtIn.flip n0 n0e) hrUL hdUL hkE hkEa
  have n4 := n2.assoc_mixed_left (α := true) n1 n0 hrUL hdUL hkEa hkE
  obtain ⟨dY₂, wY₂, hwY₂, -, hlY₂, -⟩ := exists_pasteAtData_of_isPastingAtIn huL hEa wUL wEa n2
  let zL : Within uL.toPastingDiagram dY₂.round.toPastingDiagram := dY₂.pasteAtInl
  let zEa : Within Ea.toPastingDiagram dY₂.round.toPastingDiagram := dY₂.pasteAtInr
  have hlY₂' : (zL.trans wY₂).image = wUL.image := hlY₂
  rw [← hwY₂] at n3
  have hC₂ : wE.image ⊓ wY₂.image = dN.pasting.shape.ogp.boundary wY₂.image n false := by
    rw [hwY₂]; exact (inf_comm _ _).trans n4.inf_eq
  obtain ⟨dEY, hEYo, eEY, hbEY⟩ :=
    exists_pasteAtData_of_within (P := E) (Q := dY₂.round) hE dY₂.dim_pasting wE wY₂ n3 hC₂
  have hY₂ : Equivalent dY₂.round dEY.round :=
    equivalent_pasteAt_unit dEY hEYo (Equiv.unit (hbEY.symm.trans (bE true)).symm)
  have hY₁Y₂ : Equivalent dY₁.round dY₂.round := equivalent_trans hY₁N
    (equivalent_trans (equivalent_of_equiv (v := dEY.round) eEY.symm) (equivalent_symm hY₂))
  have f₄ : (v.boundary n false).Equiv (dY₂.round.boundary n false) := (bE true).symm.trans hbEY
  let dK : PasteAtData false n u dY₂.round := ⟨hdu, dY₂.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₄), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₄).2
      d.rewritable, d.equiv⟩
  have hMK : ArrowIn (PastingClosure A) dM.round dK.round :=
    arrowIn_pastingClosure_pasteAt_host dM dK (f₂.symm.trans f₄) (by
      change (d.occ.trans (Within.ofEquiv f₄)).image =
        ((d.occ.trans (Within.ofEquiv f₂)).trans (Within.ofEquiv _)).image
      rw [Within.trans_assoc, Within.ofEquiv_trans_ofEquiv])
      (hYY₁.trans_pastingClosure (hY₁Y₂.arrowIn_pastingClosure A))
  have hT : (dK.occ.trans (Within.boundary dY₂.round.toPastingDiagram n false)).image =
      ((Within.boundary uL.toPastingDiagram n false).trans zL).image := by
    refine map_injective wY₂.emb ?_
    have h1 : OGP.map wY₂.emb
        (dK.occ.trans (Within.boundary dY₂.round.toPastingDiagram n false)).image =
        (d.occ.trans ((Within.ofEquiv f₄).trans
          ((Within.boundary dY₂.round.toPastingDiagram n false).trans wY₂))).image :=
      (Within.image_trans_assoc _ _ _).symm
    have h2 : (d.occ.trans ((Within.ofEquiv (bE true).symm).trans
        ((Within.boundary E.toPastingDiagram n true).trans wE))).image =
        OGP.map wY₁.emb (dY₁.occ.trans
          ((Within.boundary E.toPastingDiagram n true).trans yE)).image :=
      Within.image_trans_assoc (dY₁.occ.trans (Within.boundary E.toPastingDiagram n true)) yE wY₁
    have h3 : OGP.map wY₂.emb ((Within.boundary uL.toPastingDiagram n false).trans zL).image =
        dN.pasting.shape.ogp.boundary wUL.image n false := by
      rw [← Within.image_trans, Within.trans_assoc, Within.image_boundary_trans, hlY₂']
    have h4 : OGP.map wY₁.emb (yL.image ⊓ yE.image) =
        dN.pasting.shape.ogp.boundary wUL.image n false := by
      rw [OGP.map_inf wY₁.emb, ← Within.image_trans, ← Within.image_trans]
      exact n1.inf_eq
    rw [h1, image_trans_ofEquiv_trans_eq d.occ f₄ (bE true).symm _ _ (by
      rw [Within.image_boundary_trans, Within.image_boundary_trans, ← hC₂, n3.inf_eq]; rfl), h2,
      hoY₁, h4, h3]
  let kU := dK.pasteAtInl
  let kY := dK.pasteAtInr
  let kUL := zL.trans kY
  let kEa := zEa.trans kY
  have k0 : IsPastingAtIn dK.pasting.shape.ogp n false kU.image kY.image ⊤ :=
    dK.isPastingAtIn_pasteAtInl
  have k1 : IsPastingAtIn dK.pasting.shape.ogp n false kUL.image kEa.image kY.image :=
    dY₂.isPastingAtIn_trans kY
  have hmK : kU.image ⊓ kY.image = dK.pasting.shape.ogp.boundary kUL.image n false := by
    rw [← dK.image_occ_pasteAtInr]
    refine (Within.image_trans_assoc _ _ _).trans ?_
    rw [hT]
    exact (Within.image_trans _ _).symm.trans ((congrArg Within.image
      (Within.trans_assoc _ _ _)).trans (Within.image_boundary_trans _ _ _))
  have hB : dK.pasting.shape.ogp.boundary kU.image n true =
      dK.pasting.shape.ogp.boundary kUL.image n false :=
    k0.inf_eq.symm.trans hmK
  have hUUL : kU.image ⊓ kUL.image = dK.pasting.shape.ogp.boundary kU.image n true :=
    le_antisymm ((inf_le_inf_left _ k1.left_le).trans k0.inf_eq.le)
      (le_inf (boundary_le _ _ _) (hB ▸ boundary_le _ _ _))
  have k2 : IsPastingAtIn dK.pasting.shape.ogp n false kU.image kUL.image (kU.image ⊔ kUL.image) :=
    ⟨kU.isMoleculeIn_image, kUL.isMoleculeIn_image, rfl, hUUL, by
      rw [hUUL, hB]; exact IsSubmoleculeOf.refl (kUL.isMoleculeIn_image.boundary n false)⟩
  obtain ⟨kUU, hkUU⟩ := du.exists_within kU kUL k2 (by
    rw [Within.image_trans, hou, ← Within.image, Within.image_boundary_trans, hUUL, hB])
  have e₁ := k1.eq_sup
  rw [e₁] at k0 k1
  have k3 := k2.assoc_left k1 k0
  rw [← hkUU] at k3
  have hn' : n = Ea.dim - 1 := by omega
  obtain ⟨d₃, w₃, hw₃, -, -, -⟩ := exists_pasteAtData_of_isPastingAtIn (n := Ea.dim - 1)
    (du.dim_pasting.trans (by omega)) (by omega) kUU kEa (OGP.IsPastingAtIn.of_eq hn' k3)
  have e₃ : d₃.pasting.Equiv dK.pasting :=
    Within.equiv_of_image_eq w₃ (Within.refl dK.pasting)
      (hw₃.trans (Within.image_refl dK.pasting).symm)
  have hd₃ : (u.boundary n false).Equiv d₃.sub := by
    have h := d₃.equiv
    rw [boundary_congr _ hn'.symm] at h
    exact hbu.other.symm.trans (du.equiv_boundary_not.symm.trans h)
  have hEa₀ : 0 < Ea.dim := by omega
  have h₃₄ : ArrowIn (PastingClosure A) d₃.round
      (unitData Ea hEa₀ false d₃.occ d₃.rewritable).round :=
    arrowIn_pastingClosure_pasteAt d₃ _ rfl (hau.of_equiv_right (Equiv.unit hd₃))
  have hdEa : Ea.dim = Ea.dim - 1 + 1 := by omega
  have hlb := hasBdry_unitorRound Ea hEa₀ false d₃.occ d₃.rewritable
  rw [← hdEa] at hlb
  have hl : Equivalent Ea (unitData Ea hEa₀ false d₃.occ d₃.rewritable).round :=
    EquivalenceData.equivalent ⟨hdEa.trans
        (unitData Ea hEa₀ false d₃.occ d₃.rewritable).dim_pasting.symm,
      unitorRound Ea hEa₀ false d₃.occ d₃.rewritable,
      mem_equivalences_of_isDegenerate _
        (isDegenerate_unitorRound Ea hEa₀ false d₃.occ d₃.rewritable),
      dim_unitorRound Ea hEa₀ false d₃.occ d₃.rewritable, hlb.other, hlb.side⟩
  have hchain : ArrowIn (PastingClosure A) dM.round Ea :=
    ((hMK.of_equiv_right (v' := d₃.round) e₃.symm).trans_pastingClosure h₃₄).trans_pastingClosure
      ((equivalent_symm hl).arrowIn_pastingClosure A)
  let wU := dM.pasteAtInl
  let wY := dM.pasteAtInr
  let yUL : Within uL.toPastingDiagram dY.round.toPastingDiagram := dY.pasteAtInl
  let yVV : Within dv.round.toPastingDiagram dY.round.toPastingDiagram := dY.pasteAtInr
  let vV : Within v.toPastingDiagram dv.round.toPastingDiagram := dv.pasteAtInl
  let vVL : Within vL.toPastingDiagram dv.round.toPastingDiagram := dv.pasteAtInr
  let wVV := yVV.trans wY
  let mUL := yUL.trans wY
  let wV := vV.trans wVV
  let wVL := vVL.trans wVV
  have m0 : IsPastingAtIn dM.pasting.shape.ogp n false wU.image wY.image ⊤ :=
    dM.isPastingAtIn_pasteAtInl
  have m1 : IsPastingAtIn dM.pasting.shape.ogp n true mUL.image wVV.image wY.image :=
    dY.isPastingAtIn_trans wY
  have m2 : IsPastingAtIn dM.pasting.shape.ogp n false wV.image wVL.image wVV.image :=
    dv.isPastingAtIn_trans wVV
  have m2e : wV.image ⊓ wVL.image = dM.pasting.shape.ogp.boundary wVL.image n false :=
    (congrArg₂ (· ⊓ ·) (Within.image_trans _ _) (Within.image_trans _ _)).trans
      ((OGP.map_inf wVV.emb _ _).symm.trans ((congrArg (OGP.map wVV.emb)
        (inter_eq_boundary_pasteAt_of_image_univ _ _ _ false dv.occ dv.rewritable.isSubmoleculeOf
          hov dv.equiv)).trans ((map_boundary wVV.emb _ _ _).trans
            (congrArg (dM.pasting.shape.ogp.boundary · n false) (Within.image_trans _ _).symm))))
  have m2p : IsPastingIn dM.pasting.shape.ogp n wV.image wVL.image wVV.image :=
    m2.isPastingIn_of_inf_eq m2e
  obtain ⟨-, mA, mP⟩ := isPastingAtIn_of_isPastingIn_not m1 wVL.isMoleculeIn_image m2p
  have mP' : IsPastingIn dM.pasting.shape.ogp n wV.image (mUL.image ⊔ wVL.image) wY.image := mP
  obtain ⟨hUV, mB, mP₂⟩ := isPastingAtIn_of_isPastingIn_not m0 wV.isMoleculeIn_image mP'
  have mP₂' : IsPastingIn dM.pasting.shape.ogp n (wU.image ⊔ wV.image) (mUL.image ⊔ wVL.image) ⊤ :=
    mP₂
  have hL : (Within.boundary v.toPastingDiagram n false).trans wV =
      (Within.ofEquiv f₂).trans ((Within.boundary dY.round.toPastingDiagram n false).trans wY) :=
    Within.ext_of_image_eq _ _ (by
      rw [Within.image_boundary_trans, Within.image_ofEquiv_trans, Within.image_boundary_trans,
        mP'.boundary_input])
  have hmeet : (d.occ.trans ((Within.boundary v.toPastingDiagram n false).trans wV)).image =
      wU.image ⊓ wV.image := by
    rw [hL, ← Within.trans_assoc]
    exact dM.image_occ_pasteAtInr.trans hUV.symm
  obtain ⟨wW, hW⟩ := d.exists_within wU wV mB hmeet
  have hMd : dM.pasting.dim = n + 1 := dM.dim_pasting
  have hVLd : krullDim wVL.image = (n : WithBot ℕ∞) + 1 := by
    rw [Within.krullDim_image, hvL]; push_cast; rfl
  obtain ⟨w', ww', hww', hw'⟩ := exists_within_of_isRound mA.isMoleculeIn
    (mA.isRound (wVL.round_image_iff.2 vL.isRound) hVLd
      (krullDim_eq_of_le hMd wVL hvL le_sup_right))
    (krullDim_eq_of_le hMd wVL hvL le_sup_right)
  have mC : IsPastingAtIn dM.pasting.shape.ogp n false wW.image ww'.image ⊤ := by
    rw [hW, hww']; exact OGP.IsPastingIn.isPastingAtIn mP₂' mB.isMoleculeIn mA.isMoleculeIn
  have hC : wW.image ⊓ ww'.image = dM.pasting.shape.ogp.boundary ww'.image n false := by
    rw [hW, hww']; exact mP₂'.inf_eq_input
  have hwd : d.round.dim = n + 1 := d.dim_pasting
  obtain ⟨D, hDo, eD, hb₁⟩ :=
    exists_pasteAtData_of_within (P := d.round) (Q := w') hwd hw' wW ww' mC hC
  have eM : (dM.pasting.boundary n false).Equiv (d.round.boundary n false) :=
    Within.equiv_of_image_eq (Within.boundary dM.pasting n false)
      ((Within.boundary d.round.toPastingDiagram n false).trans wW) (by
        rw [Within.image_boundary, Within.image_boundary_trans, hW, mP₂'.boundary_input])
  have eM' : (dM.pasting.boundary n true).Equiv (w'.boundary n true) :=
    Within.equiv_of_image_eq (Within.boundary dM.pasting n true)
      ((Within.boundary w'.toPastingDiagram n true).trans ww') (by
        rw [Within.image_boundary, Within.image_boundary_trans, hww', mP₂'.boundary_output])
  have bEa (β : Bool) : (Ea.boundary n β).Equiv (dY₁.round.boundary n true) :=
    boundary_unit (dim_boundary _ (by omega) _) β
  have hlt : n < dM.round.dim := lt_of_lt_of_eq n.lt_succ_self hMd.symm
  have hEw : (dY₁.round.boundary n true).Equiv (d.round.boundary n false) :=
    (bEa false).symm.trans ((hchain.equiv_boundary hlt false).symm.trans eM)
  have hb₀ : (w'.boundary n true).Equiv (d.round.boundary n false) :=
    eM'.symm.trans ((hchain.equiv_boundary hlt true).trans ((bEa true).trans hEw))
  exact ⟨n, w', D, ⟨hw', dim_boundary _ (by omega) _, dim_boundary _ (by omega) _, hb₁.symm, hb₀⟩,
    hDo, (hchain.of_equiv_left (u' := D.round) eD.symm).of_equiv_right (Equiv.unit hEw)⟩

theorem hasSideInverse_pasteAt_true_true {A : Set (RoundPastingDiagram X)} {n : ℕ}
    {u v : RoundPastingDiagram X} (d : PasteAtData true n u v)
    (hu : HasSideInverse (PastingClosure A) true u)
    (hv : HasSideInverse (PastingClosure A) true v) :
    HasSideInverse (PastingClosure A) true d.round := by
  classical
  obtain ⟨nu, uR, du, hbu, hou, hau⟩ := hu
  obtain ⟨nv, vR, dv, hbv, hov, hav⟩ := hv
  change PasteAtData false nu uR u at du
  change PasteAtData false nv vR v at dv
  change ArrowIn _ _ du.round at hau
  change ArrowIn _ _ dv.round at hav
  have hnu : nu = n := by have := du.dim_u'; have := d.dim_e; omega
  have hnv : nv = n := by have := dv.dim_u'; have := d.dim_u'; omega
  subst nu nv
  have hdu : u.dim = n + 1 := d.dim_e
  have hdv : v.dim = n + 1 := d.dim_u'
  have huR : uR.dim = n + 1 := hbu.dim_h
  have hvR : vR.dim = n + 1 := hbv.dim_h
  have f₁ : (v.boundary n true).Equiv (dv.round.boundary n false) :=
    hbv.side.symm.trans (dv.equiv_boundary_pasting_of_image_univ hov).symm
  let dY : PasteAtData false n uR dv.round := ⟨huR, dv.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₁), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₁).2
      d.rewritable, hbu.other.trans d.equiv⟩
  have f₂ : (v.boundary n true).Equiv (dY.round.boundary n true) :=
    dv.equiv_boundary_not.symm.trans dY.equiv_boundary_not.symm
  let dM : PasteAtData true n u dY.round := ⟨hdu, dY.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₂), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₂).2
      d.rewritable, d.equiv⟩
  let E := (isRound_boundary_of_isRound v.isRound n true).unit
  have hE : E.dim = n + 1 := by
    change (v.boundary n true).unit.dim = _
    rw [dim_unit, dim_boundary _ (by omega)]
  have bE (β : Bool) : (E.boundary n β).Equiv (v.boundary n true) :=
    boundary_unit (dim_boundary _ (by omega) _) β
  let dY₁ : PasteAtData false n uR E := ⟨huR, hE, d.sub,
    d.occ.trans (Within.ofEquiv (bE false).symm),
    (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff _).2 d.rewritable,
    hbu.other.trans d.equiv⟩
  have hY₁Y : ArrowIn (PastingClosure A) dY₁.round dY.round :=
    arrowIn_pastingClosure_pasteAt_host dY₁ dY ((bE false).trans f₁) (by
      change (d.occ.trans (Within.ofEquiv f₁)).image =
        ((d.occ.trans (Within.ofEquiv (bE false).symm)).trans (Within.ofEquiv _)).image
      rw [Within.trans_assoc, Within.ofEquiv_trans_ofEquiv]) hav
  have hY₁ : dY₁.round.dim = n + 1 := dY₁.dim_pasting
  let Ea := (isRound_boundary_of_isRound dY₁.round.isRound n false).unit
  have hEa : Ea.dim = n + 1 := by
    change (dY₁.round.boundary n false).unit.dim = _
    rw [dim_unit, dim_boundary _ (by omega)]
  let dN : PasteAtData false n Ea dY₁.round := PasteAtData.ofBoundary hEa hY₁
    (boundary_unit (dim_boundary _ (by omega) _) true)
  have hY₁N : Equivalent dY₁.round dN.round :=
    equivalent_pasteAt_unit dN (Within.image_refl _) (.refl _)
  let wEa := dN.pasteAtInl
  let wY₁ := dN.pasteAtInr
  let yR : Within uR.toPastingDiagram dY₁.round.toPastingDiagram := dY₁.pasteAtInl
  let yE : Within E.toPastingDiagram dY₁.round.toPastingDiagram := dY₁.pasteAtInr
  have hoY₁ : (dY₁.occ.trans ((Within.boundary E.toPastingDiagram n false).trans yE)).image =
      yR.image ⊓ yE.image := dY₁.image_occ_pasteAtInr
  let wE := yE.trans wY₁
  let wUR := yR.trans wY₁
  have n0 : IsPastingAtIn dN.pasting.shape.ogp n false wEa.image wY₁.image ⊤ :=
    dN.isPastingAtIn_pasteAtInl
  have n0e : wEa.image ⊓ wY₁.image = dN.pasting.shape.ogp.boundary wY₁.image n false :=
    inter_eq_boundary_pasteAt_of_image_univ _ _ _ false dN.occ dN.rewritable.isSubmoleculeOf
      (Within.image_refl _) dN.equiv
  have n1 : IsPastingAtIn dN.pasting.shape.ogp n false wUR.image wE.image wY₁.image :=
    dY₁.isPastingAtIn_trans wY₁
  have f₃ := n1.eq_sup
  rw [f₃] at n0 n0e n1
  have hdUR : krullDim wUR.image = (n : WithBot ℕ∞) + 1 := by
    rw [Within.krullDim_image, huR]; push_cast; rfl
  have hkE : (n : WithBot ℕ∞) ≤ krullDim wE.image := by
    rw [Within.krullDim_image, hE]; exact_mod_cast n.le_succ
  have hkEa : (n : WithBot ℕ∞) ≤ krullDim wEa.image := by
    rw [Within.krullDim_image, hEa]; exact_mod_cast n.le_succ
  have hrUR : dN.pasting.shape.ogp.IsRound wUR.image := wUR.round_image_iff.2 uR.isRound
  obtain ⟨n2, n3⟩ := n1.assoc_mixed_right (α := true)
    (OGP.IsPastingAtIn.flip n0 n0e) hrUR hdUR hkE hkEa
  have n4 := n2.assoc_mixed_left (α := false) n1 n0 hrUR hdUR hkEa hkE
  obtain ⟨dY₂, wY₂, hwY₂, -, hlY₂, -⟩ := exists_pasteAtData_of_isPastingAtIn huR hEa wUR wEa n2
  let zR : Within uR.toPastingDiagram dY₂.round.toPastingDiagram := dY₂.pasteAtInl
  let zEa : Within Ea.toPastingDiagram dY₂.round.toPastingDiagram := dY₂.pasteAtInr
  have hlY₂' : (zR.trans wY₂).image = wUR.image := hlY₂
  rw [← hwY₂] at n4
  have hC₂ : wY₂.image ⊓ wE.image = dN.pasting.shape.ogp.boundary wE.image n false := by
    rw [hwY₂]; exact (inf_comm _ _).trans n3.inf_eq
  obtain ⟨dYE, hYEo, eYE, hbYE⟩ :=
    exists_pasteAtData_of_within (P := dY₂.round) (Q := E) dY₂.dim_pasting hE wY₂ wE n4 hC₂
  have hY₂ : Equivalent dY₂.round dYE.round :=
    equivalent_pasteAt_unit_right dYE hYEo (Equiv.unit (hbYE.trans (bE false)).symm)
  have hY₂Y₁ : Equivalent dY₂.round dY₁.round := equivalent_trans hY₂
    (equivalent_trans (equivalent_of_equiv (v := dN.round) eYE) (equivalent_symm hY₁N))
  have f₄ : (v.boundary n true).Equiv (dY₂.round.boundary n true) := (bE false).symm.trans hbYE.symm
  let dK : PasteAtData true n u dY₂.round := ⟨hdu, dY₂.dim_pasting, d.sub,
    d.occ.trans (Within.ofEquiv f₄), (d.occ.isRewritableSubmolecule_image_trans_ofEquiv_iff f₄).2
      d.rewritable, d.equiv⟩
  have hKM : ArrowIn (PastingClosure A) dK.round dM.round :=
    arrowIn_pastingClosure_pasteAt_host dK dM (f₄.symm.trans f₂) (by
      change (d.occ.trans (Within.ofEquiv f₂)).image =
        ((d.occ.trans (Within.ofEquiv f₄)).trans (Within.ofEquiv _)).image
      rw [Within.trans_assoc, Within.ofEquiv_trans_ofEquiv])
      ((hY₂Y₁.arrowIn_pastingClosure A).trans_pastingClosure hY₁Y)
  have hT : (dK.occ.trans (Within.boundary dY₂.round.toPastingDiagram n true)).image =
      ((Within.boundary uR.toPastingDiagram n true).trans zR).image := by
    refine map_injective wY₂.emb ?_
    have h1 : OGP.map wY₂.emb
        (dK.occ.trans (Within.boundary dY₂.round.toPastingDiagram n true)).image =
        (d.occ.trans ((Within.ofEquiv f₄).trans
          ((Within.boundary dY₂.round.toPastingDiagram n true).trans wY₂))).image :=
      (Within.image_trans_assoc _ _ _).symm
    have h2 : (d.occ.trans ((Within.ofEquiv (bE false).symm).trans
        ((Within.boundary E.toPastingDiagram n false).trans wE))).image =
        OGP.map wY₁.emb (dY₁.occ.trans
          ((Within.boundary E.toPastingDiagram n false).trans yE)).image :=
      Within.image_trans_assoc (dY₁.occ.trans (Within.boundary E.toPastingDiagram n false)) yE wY₁
    have h3 : OGP.map wY₂.emb ((Within.boundary uR.toPastingDiagram n true).trans zR).image =
        dN.pasting.shape.ogp.boundary wUR.image n true := by
      rw [← Within.image_trans, Within.trans_assoc, Within.image_boundary_trans, hlY₂']
    have h4 : OGP.map wY₁.emb (yR.image ⊓ yE.image) =
        dN.pasting.shape.ogp.boundary wUR.image n true := by
      rw [OGP.map_inf wY₁.emb, ← Within.image_trans, ← Within.image_trans]
      exact n1.inf_eq
    rw [h1, image_trans_ofEquiv_trans_eq d.occ f₄ (bE false).symm _ _ (by
      rw [Within.image_boundary_trans, Within.image_boundary_trans, ← hC₂, n4.inf_eq]; rfl), h2,
      hoY₁, h4, h3]
  let kU := dK.pasteAtInl
  let kY := dK.pasteAtInr
  let kUR := zR.trans kY
  let kEa := zEa.trans kY
  have k0 : IsPastingAtIn dK.pasting.shape.ogp n true kU.image kY.image ⊤ :=
    dK.isPastingAtIn_pasteAtInl
  have k1 : IsPastingAtIn dK.pasting.shape.ogp n true kUR.image kEa.image kY.image :=
    dY₂.isPastingAtIn_trans kY
  have hmK : kU.image ⊓ kY.image = dK.pasting.shape.ogp.boundary kUR.image n true := by
    rw [← dK.image_occ_pasteAtInr]
    refine (Within.image_trans_assoc _ _ _).trans ?_
    rw [hT]
    exact (Within.image_trans _ _).symm.trans ((congrArg Within.image
      (Within.trans_assoc _ _ _)).trans (Within.image_boundary_trans _ _ _))
  have hB : dK.pasting.shape.ogp.boundary kU.image n false =
      dK.pasting.shape.ogp.boundary kUR.image n true :=
    k0.inf_eq.symm.trans hmK
  have hURU : kUR.image ⊓ kU.image = dK.pasting.shape.ogp.boundary kUR.image n true :=
    le_antisymm ((inf_comm _ _).le.trans ((inf_le_inf_left _ k1.left_le).trans
      (k0.inf_eq.trans hB).le)) (le_inf (boundary_le _ _ _) (hB ▸ boundary_le _ _ _))
  have k2 : IsPastingAtIn dK.pasting.shape.ogp n false kUR.image kU.image
      (kUR.image ⊔ kU.image) :=
    ⟨kUR.isMoleculeIn_image, kU.isMoleculeIn_image, rfl, hURU, by
      rw [hURU, ← hB]; exact IsSubmoleculeOf.refl (kU.isMoleculeIn_image.boundary n false)⟩
  have k2' : IsPastingAtIn dK.pasting.shape.ogp n true kU.image kUR.image
      (kU.image ⊔ kUR.image) :=
    ⟨kU.isMoleculeIn_image, kUR.isMoleculeIn_image, rfl, (inf_comm _ _).trans (hURU.trans hB.symm),
      by rw [inf_comm, hURU]; exact IsSubmoleculeOf.refl (kUR.isMoleculeIn_image.boundary n true)⟩
  obtain ⟨kUU, hkUU⟩ := du.exists_within kUR kU k2 (by
    rw [Within.image_trans, hou, ← Within.image, Within.image_boundary_trans, hURU, hB])
  have e₁ := k1.eq_sup
  rw [e₁] at k0 k1
  have k3 := k2'.assoc_left k1 k0
  rw [sup_comm, ← hkUU] at k3
  have hn' : n = Ea.dim - 1 := by omega
  obtain ⟨d₃, w₃, hw₃, -, -, -⟩ := exists_pasteAtData_of_isPastingAtIn (n := Ea.dim - 1)
    (du.dim_pasting.trans (by omega)) (by omega) kUU kEa (OGP.IsPastingAtIn.of_eq hn' k3)
  have e₃ : d₃.pasting.Equiv dK.pasting :=
    Within.equiv_of_image_eq w₃ (Within.refl dK.pasting)
      (hw₃.trans (Within.image_refl dK.pasting).symm)
  have hd₃ : (u.boundary n true).Equiv d₃.sub := by
    have h := d₃.equiv
    rw [boundary_congr _ hn'.symm] at h
    exact hbu.side.symm.trans ((du.equiv_boundary_pasting_of_image_univ hou).symm.trans h)
  have hEa₀ : 0 < Ea.dim := by omega
  have h₄₃ : ArrowIn (PastingClosure A)
      (unitData Ea hEa₀ true d₃.occ d₃.rewritable).round d₃.round :=
    arrowIn_pastingClosure_pasteAt _ d₃ rfl (hau.of_equiv_left (Equiv.unit hd₃))
  have hdEa : Ea.dim = Ea.dim - 1 + 1 := by omega
  have hrb := hasBdry_unitorReverseRound Ea hEa₀ true d₃.occ d₃.rewritable
  rw [← hdEa] at hrb
  have hr : Equivalent Ea (unitData Ea hEa₀ true d₃.occ d₃.rewritable).round :=
    EquivalenceData.equivalent ⟨hdEa.trans
        (unitData Ea hEa₀ true d₃.occ d₃.rewritable).dim_pasting.symm,
      unitorReverseRound Ea hEa₀ true d₃.occ d₃.rewritable,
      mem_equivalences_of_isDegenerate _
        (isDegenerate_unitorReverseRound Ea hEa₀ true d₃.occ d₃.rewritable),
      by rw [unitorReverseRound, dim_reverse, dim_unitorRound], hrb.other, hrb.side⟩
  have hchain : ArrowIn (PastingClosure A) Ea dM.round :=
    (((hr.arrowIn_pastingClosure A).trans_pastingClosure h₄₃).of_equiv_right
      (v' := dK.round) e₃).trans_pastingClosure hKM
  let wU := dM.pasteAtInl
  let wY := dM.pasteAtInr
  let yUR : Within uR.toPastingDiagram dY.round.toPastingDiagram := dY.pasteAtInl
  let yVV : Within dv.round.toPastingDiagram dY.round.toPastingDiagram := dY.pasteAtInr
  let vVR : Within vR.toPastingDiagram dv.round.toPastingDiagram := dv.pasteAtInl
  let vV : Within v.toPastingDiagram dv.round.toPastingDiagram := dv.pasteAtInr
  let wVV := yVV.trans wY
  let mUR := yUR.trans wY
  let wVR := vVR.trans wVV
  let wV := vV.trans wVV
  have m0 : IsPastingAtIn dM.pasting.shape.ogp n true wU.image wY.image ⊤ :=
    dM.isPastingAtIn_pasteAtInl
  have m1 : IsPastingAtIn dM.pasting.shape.ogp n false mUR.image wVV.image wY.image :=
    dY.isPastingAtIn_trans wY
  have m2 : IsPastingAtIn dM.pasting.shape.ogp n false wVR.image wV.image wVV.image :=
    dv.isPastingAtIn_trans wVV
  have m2e : wVR.image ⊓ wV.image = dM.pasting.shape.ogp.boundary wV.image n false :=
    (congrArg₂ (· ⊓ ·) (Within.image_trans _ _) (Within.image_trans _ _)).trans
      ((OGP.map_inf wVV.emb _ _).symm.trans ((congrArg (OGP.map wVV.emb)
        (inter_eq_boundary_pasteAt_of_image_univ _ _ _ false dv.occ dv.rewritable.isSubmoleculeOf
          hov dv.equiv)).trans ((map_boundary wVV.emb _ _ _).trans
            (congrArg (dM.pasting.shape.ogp.boundary · n false) (Within.image_trans _ _).symm))))
  have m2p : IsPastingIn dM.pasting.shape.ogp n wVR.image wV.image wVV.image :=
    m2.isPastingIn_of_inf_eq m2e
  obtain ⟨-, mA, mP⟩ := isPastingAtIn_of_isPastingIn_not m1 wVR.isMoleculeIn_image m2p
  have mP' : IsPastingIn dM.pasting.shape.ogp n (mUR.image ⊔ wVR.image) wV.image wY.image := mP
  obtain ⟨hUV, mB, mP₂⟩ := isPastingAtIn_of_isPastingIn_not m0 wV.isMoleculeIn_image mP'
  have mP₂' : IsPastingIn dM.pasting.shape.ogp n (mUR.image ⊔ wVR.image) (wU.image ⊔ wV.image) ⊤ :=
    mP₂
  have hL : (Within.boundary v.toPastingDiagram n true).trans wV =
      (Within.ofEquiv f₂).trans ((Within.boundary dY.round.toPastingDiagram n true).trans wY) :=
    Within.ext_of_image_eq _ _ (by
      rw [Within.image_boundary_trans, Within.image_ofEquiv_trans, Within.image_boundary_trans,
        mP'.boundary_output])
  have hmeet : (d.occ.trans ((Within.boundary v.toPastingDiagram n true).trans wV)).image =
      wU.image ⊓ wV.image := by
    rw [hL, ← Within.trans_assoc]
    exact dM.image_occ_pasteAtInr.trans hUV.symm
  obtain ⟨wW, hW⟩ := d.exists_within wU wV mB hmeet
  have hMd : dM.pasting.dim = n + 1 := dM.dim_pasting
  have hVRd : krullDim wVR.image = (n : WithBot ℕ∞) + 1 := by
    rw [Within.krullDim_image, hvR]; push_cast; rfl
  obtain ⟨w', ww', hww', hw'⟩ := exists_within_of_isRound mA.isMoleculeIn
    (mA.isRound (wVR.round_image_iff.2 vR.isRound) hVRd
      (krullDim_eq_of_le hMd wVR hvR le_sup_right))
    (krullDim_eq_of_le hMd wVR hvR le_sup_right)
  have mC : IsPastingAtIn dM.pasting.shape.ogp n false ww'.image wW.image ⊤ := by
    rw [hW, hww']; exact OGP.IsPastingIn.isPastingAtIn mP₂' mA.isMoleculeIn mB.isMoleculeIn
  have hC : ww'.image ⊓ wW.image = dM.pasting.shape.ogp.boundary wW.image n false := by
    rw [hW, hww']; exact mP₂'.inf_eq_input
  have hwd : d.round.dim = n + 1 := d.dim_pasting
  obtain ⟨D, hDo, eD, hb₁⟩ :=
    exists_pasteAtData_of_within (P := w') (Q := d.round) hw' hwd ww' wW mC hC
  have eM : (dM.pasting.boundary n true).Equiv (d.round.boundary n true) :=
    Within.equiv_of_image_eq (Within.boundary dM.pasting n true)
      ((Within.boundary d.round.toPastingDiagram n true).trans wW) (by
        rw [Within.image_boundary, Within.image_boundary_trans, hW, mP₂'.boundary_output])
  have eM' : (dM.pasting.boundary n false).Equiv (w'.boundary n false) :=
    Within.equiv_of_image_eq (Within.boundary dM.pasting n false)
      ((Within.boundary w'.toPastingDiagram n false).trans ww') (by
        rw [Within.image_boundary, Within.image_boundary_trans, hww', mP₂'.boundary_input])
  have bEa (β : Bool) : (Ea.boundary n β).Equiv (dY₁.round.boundary n false) :=
    boundary_unit (dim_boundary _ (by omega) _) β
  have hlt : n < Ea.dim := by omega
  have hEw : (dY₁.round.boundary n false).Equiv (d.round.boundary n true) :=
    (bEa true).symm.trans ((hchain.equiv_boundary hlt true).trans eM)
  have hb₀ : (w'.boundary n false).Equiv (d.round.boundary n true) :=
    eM'.symm.trans ((hchain.equiv_boundary hlt false).symm.trans ((bEa false).trans hEw))
  exact ⟨n, w', D, ⟨hw', dim_boundary _ (by omega) _, dim_boundary _ (by omega) _, hb₀, hb₁⟩,
    hDo, (hchain.of_equiv_right (v' := D.round) eD.symm).of_equiv_left (Equiv.unit hEw)⟩

theorem hasSideInverse_pasteAt {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {u v : RoundPastingDiagram X} (d : PasteAtData α n u v) (β : Bool)
    (hu : HasSideInverse (PastingClosure A) β u) (hv : HasSideInverse (PastingClosure A) β v) :
    HasSideInverse (PastingClosure A) β d.round := by
  cases α <;> cases β
  · exact hasSideInverse_pasteAt_false_false d hu hv
  · exact hasSideInverse_pasteAt_false_true d hu hv
  · exact hasSideInverse_pasteAt_true_false d hu hv
  · exact hasSideInverse_pasteAt_true_true d hu hv

theorem pastingClosure_subset_biInvOperator {A : Set (RoundPastingDiagram X)}
    (hA : A ⊆ biInvOperator X (PastingClosure A)) :
    PastingClosure A ⊆ biInvOperator X (PastingClosure A) := by
  intro w hw
  induction hw with
  | base ha => exact hA ha
  | equivalence he =>
    exact (biInvOperator X).monotone (equivalences_subset_pastingClosure A)
      ((mem_equivalences_iff _).1 he)
  | pasteAt d _ _ ihu ihv =>
    exact mem_biInvOperator_iff.2
      ⟨hasSideInverse_pasteAt d false (mem_biInvOperator_iff.1 ihu).1
        (mem_biInvOperator_iff.1 ihv).1,
      hasSideInverse_pasteAt d true (mem_biInvOperator_iff.1 ihu).2
        (mem_biInvOperator_iff.1 ihv).2⟩

theorem pastingClosure_subset_equivalences {A : Set (RoundPastingDiagram X)}
    (hA : A ⊆ biInvOperator X (PastingClosure A)) : PastingClosure A ⊆ equivalences X :=
  subset_equivalences (pastingClosure_subset_biInvOperator hA)

end Atoms.Diagrammatic
