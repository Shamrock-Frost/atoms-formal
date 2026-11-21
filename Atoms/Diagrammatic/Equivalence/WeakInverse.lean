import Atoms.Diagrammatic.Context.Trim
import Atoms.Diagrammatic.Equivalence.Congruence
import Atoms.Diagrammatic.Context.HigherUnitor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def IsWeakInverse (e e' : PastingDiagram X) : Prop :=
  ∃ (he : e.IsRound) (D : BiInvData (equivalences X) ⟨e, he⟩),
    (D.inverse false).toPastingDiagram = e' ∧ (D.inverse true).toPastingDiagram = e'

theorem IsWeakInverse.mem_equivalences {e e' : PastingDiagram X} (h : IsWeakInverse e e')
    (he : ∀ hr : e.IsRound, (⟨e, hr⟩ : RoundPastingDiagram X) ∈ equivalences X) :
    ∃ hr' : e'.IsRound, (⟨e', hr'⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  obtain ⟨hr, D, hL, -⟩ := h
  subst hL
  exact ⟨(D.inverse false).isRound, D.leftInverse_mem (he hr)⟩

theorem IsWeakInverse.hasBdry {e e' x y : PastingDiagram X} {n : ℕ} (h : IsWeakInverse e e')
    (ht : HasBdry false n e x y) : ∃ _ : e'.IsRound, HasBdry false n e' y x := by
  obtain ⟨hre, D, hL, -⟩ := h
  subst hL
  have hd : (⟨e, hre⟩ : RoundPastingDiagram X).dim = n + 1 := ht.dim_h
  have hd1 : (⟨e, hre⟩ : RoundPastingDiagram X).dim - 1 = n := by rw [hd]; rfl
  have hs := D.equiv_boundary_inverse false false
  have hta := D.equiv_boundary_inverse false true
  rw [hd1] at hs hta
  exact ⟨(D.inverse false).isRound, (D.dim_inverse false).trans hd, ht.dim_b, ht.dim_a,
    hs.trans ht.other, hta.trans ht.side⟩

theorem equivalent_paste_unit_cond (α : Bool) (x : RoundPastingDiagram X) {n : ℕ}
    (hd : x.dim = n + 1)
    (hp : (cond α x.toPastingDiagram (x.toPastingDiagram.boundary n α).unit).Pastable
      (cond α (x.toPastingDiagram.boundary n α).unit x.toPastingDiagram) n)
    (hr : ((cond α x.toPastingDiagram (x.toPastingDiagram.boundary n α).unit).paste
      (cond α (x.toPastingDiagram.boundary n α).unit x.toPastingDiagram) n hp).IsRound) :
    Equivalent x ⟨_, hr⟩ := by
  let z := x.toPastingDiagram.boundary n α
  have hz : z.IsRound := isRound_boundary_of_isRound x.isRound n α
  have hdz : z.dim = n := dim_boundary _ (by omega) α
  have hι : z.shape.ogp.IsRewritableSubmolecule (Within.refl z).image ⊤ :=
    (Within.refl z).isRewritableSubmolecule_image_iff.2
        ⟨Within.isSubmoleculeOf_image_refl z, hz, rfl⟩
  have hu : (z.unit.boundary n (!α)).Equiv z := boundary_unit hdz (!α)
  let d : CylSpec X := ⟨n, α, z, some ⟨z, Within.refl z, hι⟩⟩
  have hdx : x.toPastingDiagram.dim = n + 1 := hd
  have hf : d.Fits x.toPastingDiagram :=
    ⟨x.isRound, show n < x.toPastingDiagram.dim by rw [hdx]; omega, .refl _⟩
  obtain ⟨hr', he, hdf⟩ := hf.fam_spec
  exact equivalent_of_mem_equivalences_cond α (z := ⟨d.fam x.toPastingDiagram, hr'⟩) he hd
    (by rw [dim_paste_cond, dim_unit, hdz, hdx, max_self]) (hdf.trans (congrArg (· + 1) hdx))
    ((hf.atEnd_self (β := α) (Or.inl rfl)).equiv_boundary hd).symm
    (((hf.atEnd_sidePaste_unit (ι := ⟨z, Within.refl z, hι⟩) rfl hu).equiv_boundary hd).symm.trans
      (CtxExpr.sidePaste_equiv_paste α (Within.image_refl _) hu (.refl _) hp))

theorem BiInvData.equivalent_invertor {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) (α : Bool)
    (hr : ((cond α (D.inverse α).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (D.inverse α).toPastingDiagram) (e.dim - 1)
      (D.pastable α)).IsRound) :
    Equivalent ⟨_, hr⟩ (isRound_boundary_of_isRound e.isRound (e.dim - 1) α).unit := by
  have hpos := D.dim_pos
  refine equivalent_of_mem_equivalences_cond α (D.invertor_mem α) (k := e.dim) ?_ ?_
    (D.dim_invertor α) (D.boundary_invertor_composite α) (D.boundary_invertor_unit α)
  · change ((cond α (D.inverse α).toPastingDiagram e.toPastingDiagram).paste
      (cond α e.toPastingDiagram (D.inverse α).toPastingDiagram) (e.dim - 1)
      (D.pastable α)).dim = _
    rw [dim_paste_cond, D.dim_inverse, max_self]
  · change (PastingDiagram.unit _).dim = _
    rw [PastingDiagram.dim_unit, dim_boundary _ (Nat.sub_le _ _)]
    omega

theorem BiInvData.equivalent_inverses {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) : Equivalent (D.inverse false) (D.inverse true) := by
  set m := e.dim - 1
  have hm : e.dim = m + 1 := by have := D.dim_pos; omega
  let u := e.toPastingDiagram.boundary m false
  let v := e.toPastingDiagram.boundary m true
  have hur : u.IsRound := isRound_boundary_of_isRound e.isRound m false
  have hvr : v.IsRound := isRound_boundary_of_isRound e.isRound m true
  have hdu : u.dim = m := dim_boundary _ (by omega) false
  have hdv : v.dim = m := dim_boundary _ (by omega) true
  let eL := (D.inverse false)
  let eR := (D.inverse true)
  have hdL : eL.dim = m + 1 := (D.dim_inverse false).trans hm
  have hdR : eR.dim = m + 1 := (D.dim_inverse true).trans hm
  have hLs : (eL.toPastingDiagram.boundary m false).Equiv v :=
    (D.equiv_boundary_inverse false false)
  have hRt : (eR.toPastingDiagram.boundary m true).Equiv u := (D.equiv_boundary_inverse true true)
  have pLe : e.toPastingDiagram.Pastable eL.toPastingDiagram m := (D.pastable false)
  have pRe : eR.toPastingDiagram.Pastable e.toPastingDiagram m := (D.pastable true)
  have hdU : u.unit.dim = m + 1 := by rw [dim_unit, hdu]
  have hdV : v.unit.dim = m + 1 := by rw [dim_unit, hdv]
  let εu : RoundPastingDiagram X := hur.unit
  let εv : RoundPastingDiagram X := hvr.unit
  have hRe : (eR.toPastingDiagram.paste e.toPastingDiagram m pRe).IsRound :=
    isRound_paste_of_dim eR e hdR hm pRe
  have hRedim : (eR.toPastingDiagram.paste e.toPastingDiagram m pRe).dim = m + 1 := by
    rw [dim_paste, hdR, hm, max_self]
  have Eh : Equivalent εv ⟨_, hRe⟩ := equivalent_symm (D.equivalent_invertor true hRe)
  have heL : (e.toPastingDiagram.paste eL.toPastingDiagram m pLe).IsRound :=
    isRound_paste_of_dim e eL hm hdL pLe
  have heLdim : (e.toPastingDiagram.paste eL.toPastingDiagram m pLe).dim = m + 1 := by
    rw [dim_paste, hdL, hm, max_self]
  have Ez : Equivalent ⟨_, heL⟩ εu := D.equivalent_invertor false heL
  have p1 : (eL.toPastingDiagram.boundary m false).unit.Pastable eL.toPastingDiagram m :=
    ⟨boundary_unit
      (dim_boundary _ (by omega) false) true, by
      rw [dim_unit, dim_boundary _ (by omega) false, hdL]; omega⟩
  have hdLb : (eL.toPastingDiagram.boundary m false).unit.dim = m + 1 := by
    rw [dim_unit, dim_boundary _ (by omega) false]
  have hdRb : (eR.toPastingDiagram.boundary m true).unit.dim = m + 1 := by
    rw [dim_unit, dim_boundary _ (by omega) true]
  have r1 := isRound_paste_of_dim
    (isRound_boundary_of_isRound eL.isRound m false).unit eL hdLb hdL p1
  have p2 : v.unit.Pastable eL.toPastingDiagram m :=
    ⟨(boundary_unit hdv true).trans
      (hLs.symm), by rw [hdV, hdL]; omega⟩
  have r2 := isRound_paste_of_dim εv eL hdV hdL p2
  have p3 : (eR.toPastingDiagram.paste e.toPastingDiagram m pRe).Pastable eL.toPastingDiagram m :=
    ⟨(equiv_boundary_paste pRe true).trans (hLs.symm), by
      rw [hRedim, hdL]; omega⟩
  have r3 := isRound_paste_of_dim ⟨_, hRe⟩ eL hRedim hdL p3
  obtain ⟨h₃, h₄, hA⟩ := equiv_paste_assoc pRe p3
  have r4 := isRound_paste_of_dim eR ⟨_, heL⟩ hdR heLdim h₄
  have p5 : eR.toPastingDiagram.Pastable u.unit m :=
    ⟨hRt.trans ((boundary_unit hdu false).symm),
      by rw [hdR, hdU]; omega⟩
  have r5 := isRound_paste_of_dim eR εu hdR hdU p5
  have p6 : eR.toPastingDiagram.Pastable (eR.toPastingDiagram.boundary m true).unit m :=
    ⟨(boundary_unit (dim_boundary _ (by omega) true)
        false).symm, by
      rw [hdR, dim_unit, dim_boundary _ (by omega) true]; omega⟩
  have r6 := isRound_paste_of_dim eR
    (isRound_boundary_of_isRound eR.isRound m true).unit hdR hdRb p6
  calc Equivalent eL ⟨_, r1⟩ := equivalent_paste_unit_cond false eL hdL p1 r1
    Equivalent _ ⟨_, r2⟩ :=
      equivalent_of_equiv (Equiv.paste (Equiv.unit hLs) (.refl _) p1 p2)
    Equivalent _ ⟨_, r3⟩ := equivalent_paste_left Eh (hdV.trans hdL.symm) p2 p3 r2 r3
    Equivalent _ ⟨_, r4⟩ := equivalent_of_equiv hA
    Equivalent _ ⟨_, r5⟩ := equivalent_paste_right Ez rfl (hdR.trans heLdim.symm) h₄ p5 r4 r5
    Equivalent _ ⟨_, r6⟩ :=
      equivalent_of_equiv (Equiv.paste (.refl _) (Equiv.unit hRt.symm) p5 p6)
    Equivalent _ eR := equivalent_symm (equivalent_paste_unit_cond true eR hdR p6 r6)

theorem BiInvData.rightInverse_mem {e : RoundPastingDiagram X}
    (D : BiInvData (equivalences X) e) (he : e ∈ equivalences X) :
    (D.inverse true) ∈ equivalences X :=
  (mem_equivalences_iff_of_equivalent D.equivalent_inverses).1 (D.leftInverse_mem he)

theorem exists_isWeakInverse {e : RoundPastingDiagram X} (he : e ∈ equivalences X) :
    ∃ e' : RoundPastingDiagram X, IsWeakInverse e.toPastingDiagram e'.toPastingDiagram := by
  let D := ((mem_equivalences_iff e).1 he).data
  set m := e.dim - 1
  have hm : e.dim = m + 1 := by have := D.dim_pos; omega
  let v := e.toPastingDiagram.boundary m true
  have hvr : v.IsRound := isRound_boundary_of_isRound e.isRound m true
  have hdV : v.unit.dim = m + 1 := by rw [dim_unit, dim_boundary _ (by omega) true]
  let εv : RoundPastingDiagram X := hvr.unit
  have hdεv : εv.dim = e.dim := hdV.trans hm.symm
  let eL := (D.inverse false)
  let eR := (D.inverse true)
  have hdL : eL.dim = m + 1 := (D.dim_inverse false).trans hm
  have hdR : eR.dim = m + 1 := (D.dim_inverse true).trans hm
  have pRe : eR.toPastingDiagram.Pastable e.toPastingDiagram m := (D.pastable true)
  have pEl : eL.toPastingDiagram.Pastable e.toPastingDiagram m :=
    ⟨(D.equiv_boundary_inverse false true), by rw [hdL]; omega⟩
  have hRe : (eR.toPastingDiagram.paste e.toPastingDiagram m pRe).IsRound :=
    isRound_paste_of_dim eR e hdR hm pRe
  have Eh : Equivalent εv ⟨_, hRe⟩ := equivalent_symm (D.equivalent_invertor true hRe)
  have rLe := isRound_paste_of_dim eL e hdL hm pEl
  have B1 : Equivalent ⟨_, hRe⟩ ⟨_, rLe⟩ :=
    equivalent_paste_left (equivalent_symm D.equivalent_inverses) (hdR.trans hm.symm) pRe pEl
      hRe rLe
  let H := (equivalent_trans Eh B1).data
  let D' : BiInvData (equivalences X) e :=
    { D with
      inverse := fun _ => eL
      invertor := fun α => cond α H.equivalence (D.invertor false)
      invertor_mem := fun α => by cases α; exacts [D.invertor_mem false, H.mem]
      dim_inverse := fun _ => D.dim_inverse false
      dim_invertor := fun α => by
        cases α
        exacts [D.dim_invertor false, H.dim_equivalence.trans (congrArg (· + 1) hdεv)]
      equiv_boundary_inverse := fun _ γ => D.equiv_boundary_inverse false γ
      pastable := fun α => by cases α; exacts [D.pastable false, pEl]
      boundary_invertor_composite := fun α => by
        cases α
        · exact D.boundary_invertor_composite false
        · change (H.equivalence.toPastingDiagram.boundary e.dim true).Equiv _
          rw [PastingDiagram.boundary_congr H.equivalence.toPastingDiagram hdεv.symm true]
          exact H.target
      boundary_invertor_unit := fun α => by
        cases α
        · exact D.boundary_invertor_unit false
        · change (H.equivalence.toPastingDiagram.boundary e.dim false).Equiv _
          rw [PastingDiagram.boundary_congr H.equivalence.toPastingDiagram hdεv.symm false]
          exact H.source }
  exact ⟨eL, e.isRound, D', rfl, rfl⟩

theorem IsWeakInverse.spec {e e' x y : PastingDiagram X} {n : ℕ} (h : IsWeakInverse e e')
    (ht : HasBdry false n e x y) :
    ∃ _ : e'.IsRound, HasBdry false n e' y x ∧
      (∃ (z : PastingDiagram X) (hz : z.IsRound),
        (⟨z, hz⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
          HasBdry false (n + 1) z (e.pasteOr e' n) x.unit) ∧
      (∃ (z : PastingDiagram X) (hz : z.IsRound),
        (⟨z, hz⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
          HasBdry false (n + 1) z y.unit (e'.pasteOr e n)) := by
  obtain ⟨-, te'⟩ := h.hasBdry ht
  obtain ⟨hre, D, hL, hR⟩ := h
  subst hL
  have hd : (⟨e, hre⟩ : RoundPastingDiagram X).dim = n + 1 := ht.dim_h
  have hd1 : (⟨e, hre⟩ : RoundPastingDiagram X).dim - 1 = n := by rw [hd]; rfl
  have zs := (D.boundary_invertor_composite false)
  have zt := (D.boundary_invertor_unit false)
  rw [PastingDiagram.paste_eq_pasteOr (D.pastable false) hd1 rfl rfl] at zs
  rw [hd1] at zt
  rw [hd] at zs zt
  have hs' := (D.boundary_invertor_unit true)
  have ht' := (D.boundary_invertor_composite true)
  rw [PastingDiagram.paste_eq_pasteOr (D.pastable true) hd1 hR rfl] at ht'
  rw [hd1] at hs'
  rw [hd] at hs' ht'
  refine ⟨(D.inverse false).isRound, te',
    ⟨_, (D.invertor false).isRound, (D.invertor_mem false), ⟨by rw [D.dim_invertor false, hd],
      (ht.pasteOr te' (.refl _)).dim_h, by rw [dim_unit, ht.dim_a], zs,
      zt.trans (Equiv.unit ht.side)⟩⟩,
    ⟨_, (D.invertor true).isRound, (D.invertor_mem true), ⟨by rw [D.dim_invertor true, hd],
      by rw [dim_unit, ht.dim_b], (te'.pasteOr ht (.refl _)).dim_h,
      hs'.trans (Equiv.unit ht.other), ht'⟩⟩⟩

theorem mem_equivalences_of_equivalent_unit {e e' : RoundPastingDiagram X}
    {a b : PastingDiagram X} {n : ℕ} (he : HasBdry false n e.toPastingDiagram a b)
    (he' : HasBdry false n e'.toPastingDiagram b a) (ha : a.IsRound) (hb : b.IsRound)
    (h₁ : Equivalent ⟨e.paste e'.toPastingDiagram n (he.pastable he' (.refl _)),
      isRound_paste_of_dim e e' he.dim_h he'.dim_h _⟩ ha.unit)
    (h₂ : Equivalent hb.unit ⟨e'.paste e.toPastingDiagram n (he'.pastable he (.refl _)),
      isRound_paste_of_dim e' e he'.dim_h he.dim_h _⟩) :
    e ∈ equivalences X := by
  have hm : e.dim - 1 = n := by rw [he.dim_h]; rfl
  have hp : e.Pastable e'.toPastingDiagram n := he.pastable he' (.refl _)
  have hq : e'.Pastable e.toPastingDiagram n := he'.pastable he (.refl _)
  let D₁ := h₁.data
  let D₂ := h₂.data
  have hd₁ : (⟨e.paste e'.toPastingDiagram n hp, isRound_paste_of_dim e e' he.dim_h he'.dim_h _⟩ :
      RoundPastingDiagram X).dim = e.dim :=
    (dim_paste e.toPastingDiagram e'.toPastingDiagram n hp).trans
      ((congrArg₂ max he.dim_h he'.dim_h).trans ((max_self _).trans he.dim_h.symm))
  have hd₂ : hb.unit.dim = e.dim := ((dim_unit b).trans (congrArg (· + 1) he.dim_b)).trans
    he.dim_h.symm
  refine (mem_equivalences_iff e).2 (BiInvData.witness
    { dim_pos := by rw [he.dim_h]; exact Nat.succ_pos n
      inverse := fun _ => e'
      invertor := fun α => cond α D₂.equivalence D₁.equivalence
      invertor_mem := fun α => by cases α; exacts [D₁.mem, D₂.mem]
      dim_inverse := fun _ => he'.dim_h.trans he.dim_h.symm
      dim_invertor := fun α => by
        cases α
        exacts [D₁.dim_equivalence.trans (congrArg (· + 1) hd₁),
          D₂.dim_equivalence.trans (congrArg (· + 1) hd₂)]
      equiv_boundary_inverse := fun _ γ => by
        rw [hm]
        cases γ
        exacts [he'.side.trans he.other.symm, he'.other.trans he.side.symm]
      pastable := fun α => by
        rw [hm]
        cases α
        exacts [hp, hq]
      boundary_invertor_composite := fun α => by
        cases α
        · have h := D₁.source
          rw [PastingDiagram.boundary_congr _ hd₁] at h
          have key : ∀ p, (cond false e'.toPastingDiagram e.toPastingDiagram).paste
              (cond false e.toPastingDiagram e'.toPastingDiagram) (e.dim - 1) p =
                e.paste e'.toPastingDiagram n hp := fun p =>
            (PastingDiagram.paste_eq_pasteOr p hm rfl rfl).trans (PastingDiagram.pasteOr_of hp)
          rw [key]
          exact h
        · have h := D₂.target
          rw [PastingDiagram.boundary_congr _ hd₂] at h
          have key : ∀ p, (cond true e'.toPastingDiagram e.toPastingDiagram).paste
              (cond true e.toPastingDiagram e'.toPastingDiagram) (e.dim - 1) p =
                e'.paste e.toPastingDiagram n hq := fun p =>
            (PastingDiagram.paste_eq_pasteOr p hm rfl rfl).trans (PastingDiagram.pasteOr_of hq)
          rw [key]
          exact h
      boundary_invertor_unit := fun α => by
        rw [hm]
        cases α
        · have h := D₁.target
          rw [PastingDiagram.boundary_congr _ hd₁] at h
          exact h.trans he.side.symm.unit
        · have h := D₂.source
          rw [PastingDiagram.boundary_congr _ hd₂] at h
          exact h.trans he.other.symm.unit })

end Atoms.Diagrammatic
