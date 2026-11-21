import Atoms.Diagrammatic.InftyCategory
import Atoms.Diagrammatic.Context.OfFrames

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem IsRoundIn.of_hasBdry {β : Bool} {H : PdHom X} {e a b : PastingDiagram X}
    (ha : IsRoundIn H a) (ht : HasBdry β (H.k + 1) e a b) (he : e.IsRound) : IsRoundIn H b :=
  ⟨((InHom.of_hasBdry ht ha.inHom).boundary (Nat.lt_succ_self H.k)
      (by rw [ht.dim_h]; omega) (!β)).of_equiv ht.other, ht.dim_b,
    ht.other.isRound_iff.1 (isRound_boundary_of_isRound he _ (!β))⟩

theorem natSim_frames_rounded {H H' : PdHom X} {F : CtxExpr X} (hF : IsRoundCtxOn H H' F)
    {v w : PastingDiagram X} (hv : IsRoundIn H v) (hw : IsRoundIn H w) {D : PdHom X}
    (hD : D.k = H.k + 1) {ℓ r : PastingDiagram X} (hℓ : ℓ.IsRound)
    (tℓ : HasBdry false D.k ℓ D.v (F.app v)) (hr : r.IsRound)
    (tr : HasBdry false D.k r (F.app w) D.w) :
    NatSim X (RoundHom.ofIsRoundIn hv hw) D
      (fun c => (CtxExpr.paste false ℓ D.k).app ((CtxExpr.paste true r D.k).app (F.app c)))
      (fun c => (CtxExpr.paste false ℓ D.k).app
        ((CtxExpr.paste true r D.k).app ((F.rounded w H.k).app c))) := by
  obtain ⟨k', v', w'⟩ := H'
  obtain rfl : H.k = k' := hF.typed.k_eq.symm
  obtain ⟨k, x₀, y₀⟩ := D
  change k = H.k + 1 at hD
  subst hD
  have hFv := hF.isRoundIn hv
  have hFw := hF.isRoundIn hw
  have hx₀ := hFv.of_hasBdry tℓ.symm hℓ
  set D := RoundHom.ofIsRoundIn hv hw
  set DK := RoundHom.ofIsRoundIn hx₀ hFw
  have uFw := hasType_unit hFw.dim_eq
  have hFp := hF.typed.promote_of_inHom trivial hv.inHom hw.inHom
  have hRF := isRoundCtxOn_rounded hF hv hw
  have hK : IsRoundCtxOn D DK (.comp (CtxExpr.paste false ℓ (H.k + 1)) F) :=
    (isRoundCtxOn_comp_paste false hFp hℓ tℓ.dim_h tℓ.other.symm).congr (.refl _)
      ⟨rfl, tℓ.side, .refl _⟩
  have hR : IsRoundCtxOn DK ⟨H.k + 1, x₀, y₀⟩ (CtxExpr.paste true r (H.k + 1)) :=
    (isRoundCtxOn_paste true DK.toPdHom hr tr.dim_h tr.side.symm).congr (.refl _)
      ⟨rfl, .refl _, tr.other⟩
  refine (NatSim.symm ((NatSim.unit_right D DK
    (T := .comp (CtxExpr.paste false ℓ (H.k + 1)) F) hK).left hR)).of_equiv
    (fun c hc => ?_) (fun c hc => ?_)
  · have hFc := hFp.mapsInto c hc
    exact CtxExpr.pasteRight_app_pasteLeft (tℓ.pastable_inHom hFc (.refl _))
      (hFc.pastable_hasType tr (.refl _))
  · have hFc := hFp.mapsInto c hc
    have hRFc := hRF.typed.mapsInto c hc
    exact (CtxExpr.app_equiv (CtxExpr.paste true r (H.k + 1))
      (((CtxExpr.paste_app_pasteOr true
        ((hK.typed.mapsInto c hc).pastable_hasType uFw (.refl _))).symm).trans
        (CtxExpr.pasteRight_app_pasteLeft (tℓ.pastable_inHom hFc (.refl _))
          (hFc.pastable_hasType uFw (.refl _))))).trans
      (CtxExpr.pasteRight_app_pasteLeft (tℓ.pastable_inHom hRFc (.refl _))
        (hRFc.pastable_hasType tr (.refl _)))

theorem exists_isWeakInvCtx_frames {H H₁ H' : RoundHom X} {ℓ r : PastingDiagram X}
    (hℓ : ℓ.IsRound) (hℓe : (⟨ℓ, hℓ⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (tℓ : HasBdry false H.k ℓ H'.v H₁.v) (hr : r.IsRound)
    (hre : (⟨r, hr⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (tr : HasBdry false H.k r H.w H₁.w) (he₁ : (H.setSide true H₁.w).Equiv H₁)
    (he : (H₁.setSide false H'.v).Equiv H') :
    ∃ E' : CtxExpr X, IsWeakInvCtx H H'
      (.comp (CtxExpr.paste false ℓ H.k) (CtxExpr.paste true r H.k)) E' ∧ PresEqv H' E' := by
  obtain ⟨⟨k₁, v₁, w₁⟩, hv₁, hw₁, hd₁, hp₁⟩ := H₁
  obtain rfl : H.k = k₁ := he₁.k_eq
  obtain ⟨r', hr', hr'e⟩ := exists_isWeakInvCtx_pasteRight hr hre tr he₁
  obtain ⟨ℓ', hℓ', hℓ'e⟩ := exists_isWeakInvCtx_pasteLeft hℓ hℓe tℓ he
  exact ⟨_, hr'.comp hℓ', hℓ'e.comp hℓ'.round' hr'e⟩

theorem IsWeakInvCtx.exists_frames {H H' : RoundHom X} {F F' : CtxExpr X}
    (hF : IsWeakInvCtx H H' F F') {v w : PastingDiagram X} (hv : IsRoundIn H v)
    (hw : IsRoundIn H w) {D : RoundHom X} (hD : D.k = H.k + 1) {ℓ r : PastingDiagram X}
    (hℓ : ℓ.IsRound) (hℓe : (⟨ℓ, hℓ⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (tℓ : HasBdry false D.k ℓ D.v (F.app v)) (hr : r.IsRound)
    (hre : (⟨r, hr⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (tr : HasBdry false D.k r (F.app w) D.w) :
    ∃ E' : CtxExpr X, IsWeakInvCtx (.ofIsRoundIn hv hw) D
      (.comp (CtxExpr.paste false ℓ D.k) (.comp (CtxExpr.paste true r D.k) F)) E' ∧
      PresEqv D E' := by
  obtain ⟨⟨k', v', w'⟩, hv', hw', hdv', hp'⟩ := H'
  obtain rfl : H.k = k' := hF.round.typed.k_eq.symm
  have hS := natSim_frames_rounded hF.round hv hw hD hℓ tℓ hr tr
  rw [hD] at tℓ tr hS ⊢
  have hFv := hF.round.isRoundIn hv
  have hFw := hF.round.isRoundIn hw
  have hy₀ := hFw.of_hasBdry tr hr
  obtain ⟨K, hK, hKe⟩ := hF.exists_rounded hv hw
  obtain ⟨T', hT, hT'e⟩ := exists_isWeakInvCtx_frames (H := .ofIsRoundIn hFv hFw)
    (H₁ := .ofIsRoundIn hFv hy₀) (H' := D) hℓ hℓe tℓ hr hre tr (.refl _) ⟨hD.symm, .refl _, .refl _⟩
  have hFp := hF.round.typed.promote_of_inHom trivial hv.inHom hw.inHom
  have hE : IsRoundCtxOn (RoundHom.ofIsRoundIn hv hw) D (.comp (CtxExpr.paste false ℓ (H.k + 1))
      (.comp (CtxExpr.paste true r (H.k + 1)) F)) :=
    (isRoundCtxOn_comp_paste false (hFp.comp (CtxExpr.typed_paste true (u := ⟨r, hr⟩)
      (H := ⟨H.k + 1, F.app v, F.app w⟩) (Set.mem_univ _) tr.dim_h tr.side.symm)) hℓ tℓ.dim_h
      tℓ.other.symm).congr (.refl _) ⟨hD.symm, tℓ.side, tr.other⟩
  exact ⟨_, (hK.comp hT).of_natSim hS hE, hT'e.comp hT.round' hKe⟩

theorem IsWeakInvCtx.exists_solution {H H' : RoundHom X} {E E' : CtxExpr X}
    (h : IsWeakInvCtx H H' E E') (he : PresEqv H' E') {b : PastingDiagram X}
    (hb : IsRoundIn H' b) :
    ∃ (a : PastingDiagram X) (ha : IsRoundIn H a),
      Equivalent ⟨E.app a, (h.round.isRoundIn ha).isRound⟩ ⟨b, hb.isRound⟩ ∧
        ((⟨b, hb.isRound⟩ : RoundPastingDiagram X) ∈ equivalences X →
          (⟨a, ha.isRound⟩ : RoundPastingDiagram X) ∈ equivalences X) :=
  ⟨E'.app b, h.round'.isRoundIn hb, h.right.equivalent_app hb _ _,
    fun hbe => he b hb hbe _⟩

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem mem_equivalences_app_of_trim {H H' : PdHom X} {t : CtxExpr X}
    (ht : t.Typed (equivalences X) False H H') :
    ∀ a, InHom H a → a.dim = H.k + 1 → ∀ har : a.IsRound,
      (⟨a, har⟩ : RoundPastingDiagram X) ∈ equivalences X →
        ∀ hr : (t.app a).IsRound, (⟨t.app a, hr⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs₀ =>
    intro a ha hda har hae _
    have hs : (a.boundary H.k α).Equiv v₀ := (ha.side α).trans hs₀.symm
    let d : PasteAtData α H.k u ⟨a, har⟩ :=
      ⟨hdu, hda, V, sideOcc α H.k ι hs,
          (ι.isRewritableSubmolecule_image_trans_ofEquiv_iff hs.symm).2 hι,
        h⟩
    have e : d.pasting = sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h a :=
      (sidePaste_of hs).symm
    exact mem_equivalences_of_equiv (e := d.round)
      (by change d.pasting.Equiv _; rw [e]; exact .refl _)
      ((pasteAt_mem_equivalences_iff d hu).2 hae)
  | id => exact fun a _ _ _ hae _ => hae
  | comp ht₁ _ ih₁ ih₂ =>
    exact fun a ha hda har hae hr => ih₂ _ (ht₁.mapsInto a ha)
      ((ht₁.ctxLaws.dim_eq a ha).trans (hda.trans (by rw [ht₁.k_eq])))
      (isRound_app_of_trim ht₁ a ha hda har) (ih₁ a ha hda har hae _) hr
  | promote hp => exact hp.elim

theorem PastingDiagram.topCells_subset_equivalences (ℓ : PastingDiagram X) {k : ℕ}
    (h : ∀ (U : Atom) (x : diagram X U), U.dimension = k + 1 →
      (∃ (v : PastingDiagram X) (ι : PastingDiagram.Within v ℓ),
        ℓ.shape.ogp.IsSubmoleculeOf ι.image ⊤ ∧ v.Equiv (PastingDiagram.ofCell x)) →
        IsEquivalence X x) :
    ℓ.topCells k ⊆ equivalences X := by
  rintro u ⟨t, ht, hu⟩
  have hsub := ℓ.shape.isMolecule.Iic_isSubmoleculeOf (LowerSet.mem_top (a := t))
  have hx := h _ (ℓ.cellAt t) ((dimension_principalAtomRDC ℓ.shape.rdc t).trans ht)
    ⟨_, Within.restrictTo ℓ hsub.isMoleculeIn, Within.isSubmoleculeOf_image_restrictTo _ hsub,
      (ℓ.equiv_ofCell_cellAt t).symm⟩
  exact mem_equivalences_of_equiv (e := cellRound (ℓ.cellAt t))
    (by rw [hu]; exact ℓ.equiv_ofCell_cellAt t) hx

namespace CtxExpr

theorem frameOf_app_equiv (α : Bool) {ℓ z : PastingDiagram X} {k : ℕ} (hdl : ℓ.dim = k + 1)
    (hp : (cond α z ℓ).Pastable (cond α ℓ z) k) :
    ((frameOf α ℓ k).app z).Equiv ((paste α ℓ k).app z) := by
  rw [frameOf_of_eq α hdl]
  exact (ℓ.frameCtx_app α hdl z hp).trans (paste_app α hp).symm

theorem frameOf_app_paste (α : Bool) {ℓ y u : PastingDiagram X} {k : ℕ}
    (hℓy : (y.boundary k α).Equiv (ℓ.boundary k (!α)))
    (hyu : (cond α u y).Pastable (cond α y u) k) :
    ((frameOf α ℓ k).app ((paste (!α) u k).app y)).Equiv
      ((paste (!α) u k).app ((frameOf α ℓ k).app y)) := by
  by_cases hdl : ℓ.dim = k + 1
  · cases α
    · have hp : ℓ.Pastable y k := ⟨hℓy.symm, lt_min (by omega) (lt_min_iff.1 hyu.2).1⟩
      exact (frameOf_app_equiv false hdl (Pastable.of_equiv
        (Pastable.paste_right hp hyu) (.refl _) ((paste_app true hyu).symm))).trans
        ((pasteRight_app_pasteLeft hp hyu).symm.trans
          (app_equiv (paste true u k) ((frameOf_app_equiv false hdl hp).symm)))
    · have hp : y.Pastable ℓ k := ⟨hℓy, lt_min (lt_min_iff.1 hyu.2).2 (by omega)⟩
      exact (frameOf_app_equiv true hdl (Pastable.of_equiv
        (Pastable.paste_left hyu hp) ((paste_app false hyu).symm) (.refl _))).trans
        ((pasteRight_app_pasteLeft hyu hp).trans
          (app_equiv (paste false u k) ((frameOf_app_equiv true hdl hp).symm)))
  · rw [frameOf_of_not α hdl]
    exact .refl _

theorem frameOf_app_frameOf {ℓ r y : PastingDiagram X} {k : ℕ} (hdℓ : ℓ.dim ≤ k + 1)
    (hℓy : (ℓ.boundary k true).Equiv (y.boundary k false))
    (hyr : (y.boundary k true).Equiv (r.boundary k false)) (hdy : k < y.dim) :
    ((frameOf false ℓ k).app ((frameOf true r k).app y)).Equiv
      ((frameOf true r k).app ((frameOf false ℓ k).app y)) := by
  by_cases hdr' : r.dim = k + 1
  · have hp : y.Pastable r k := ⟨hyr, lt_min hdy (by omega)⟩
    have hL := (typed_frameOf false (H := ⟨k, y.boundary k false, y.boundary k true⟩) hdℓ
      hℓy.symm).mapsInto y ⟨hdy, .refl _, .refl _⟩
    exact (app_equiv (frameOf false ℓ k) (frameOf_app_equiv true hdr' hp)).trans
      ((frameOf_app_paste false hℓy.symm hp).trans
        ((frameOf_app_equiv true hdr'
          ⟨hL.target.trans hyr, lt_min hL.lt_dim (by change k < r.dim; omega)⟩).symm))
  · rw [frameOf_of_not true hdr']
    exact .refl _

end CtxExpr

private theorem pad_frameOf_unit (β : Bool) {ℓ : PastingDiagram X} {k : ℕ} (hd : ℓ.dim ≤ k + 1)
    (hk : k ≤ ℓ.dim) (hr : (ℓ.boundary k β).IsRound) :
    ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit).IsRound ∧
      HasBdry false k ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit)
        (ℓ.boundary k false) (ℓ.boundary k true) ∧
      ∀ z, (z.boundary k β).Equiv (ℓ.boundary k (!β)) → k < z.dim →
        ((CtxExpr.paste β ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit) k).app z).Equiv
          ((CtxExpr.paste β (ℓ.boundary k β).unit k).app ((CtxExpr.frameOf β ℓ k).app z)) := by
  have hdx : (ℓ.boundary k β).dim = k := dim_boundary ℓ hk β
  have u₀ := hasType_unit hdx
  have ht := CtxExpr.typed_frameOf (!β) (H := ⟨k, ℓ.boundary k β, ℓ.boundary k β⟩) hd
    (by rw [Bool.not_not]; cases β <;> exact .refl _)
  have hin : InHom ⟨k, ℓ.boundary k β, ℓ.boundary k β⟩ (ℓ.boundary k β).unit :=
    ⟨by rw [u₀.dim_h]; exact Nat.lt_succ_self k, u₀.side, u₀.other⟩
  have hv := ht.mapsInto _ hin
  have hdℓ' := ht.ctxLaws.dim_eq _ hin
  have hb : ∀ γ, (((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit).boundary k γ).Equiv
      (ℓ.boundary k γ) := fun γ => by cases β <;> cases γ <;> exact hv.side _
  refine ⟨isRound_app_of_trim ht _ hin u₀.dim_h (isRound_unit hr), ⟨hdℓ'.trans u₀.dim_h,
    dim_boundary ℓ hk false, dim_boundary ℓ hk true, hb false, hb true⟩, fun z hz hkz => ?_⟩
  by_cases hdl : ℓ.dim = k + 1
  · have hpε : (cond (!β) (ℓ.boundary k β).unit ℓ).Pastable (cond (!β) ℓ (ℓ.boundary k β).unit)
        k := .of_side (!β) (by rw [Bool.not_not]; exact boundary_unit hdx (!β))
          (by rw [u₀.dim_h]; omega) (by omega)
    have huv : (cond β ℓ (ℓ.boundary k β).unit).Pastable (cond β (ℓ.boundary k β).unit ℓ) k := by
      have := hpε
      rwa [Bool.cond_not, Bool.cond_not] at this
    have hpz : (cond β z ℓ).Pastable (cond β ℓ z) k := .of_side β hz hkz (by omega)
    have eP : ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit).Equiv
        ((cond β ℓ (ℓ.boundary k β).unit).pasteOr (cond β (ℓ.boundary k β).unit ℓ) k) := by
      rw [pasteOr_of huv]
      exact (CtxExpr.frameOf_app_equiv (!β) hdl hpε).trans ((CtxExpr.paste_app (!β) hpε).trans
        (by cases β <;> exact .refl _))
    have hpz' : (cond β z ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit)).Pastable
        (cond β ((CtxExpr.frameOf (!β) ℓ k).app (ℓ.boundary k β).unit) z) k :=
      .of_side β (hz.trans (hb (!β)).symm) hkz (by rw [hdℓ', u₀.dim_h]; omega)
    have hpzP : (cond β z ((cond β ℓ (ℓ.boundary k β).unit).pasteOr
        (cond β (ℓ.boundary k β).unit ℓ) k)).Pastable
          (cond β ((cond β ℓ (ℓ.boundary k β).unit).pasteOr (cond β (ℓ.boundary k β).unit ℓ) k) z)
          k :=
      .of_side β (hz.trans ((hb (!β)).symm.trans (eP.boundary k (!β)))) hkz
        (by rw [← dim_eq_of_equiv eP, hdℓ', u₀.dim_h]; omega)
    exact (CtxExpr.paste_app_not β hpz').trans ((CtxExpr.app_equiv _ eP).trans
      ((CtxExpr.paste_app_not β hpzP).symm.trans ((CtxExpr.paste_app_paste β hpz huv).symm.trans
        (CtxExpr.app_equiv _ (CtxExpr.frameOf_app_equiv β hdl hpz).symm))))
  · rw [CtxExpr.frameOf_of_not (!β) hdl, CtxExpr.frameOf_of_not β hdl]
    exact .refl _

theorem exists_pad_round (β : Bool) {ℓ : PastingDiagram X} {k : ℕ} (hd : ℓ.dim ≤ k + 1)
    (hk : k ≤ ℓ.dim) (hr : (ℓ.boundary k β).IsRound) :
    ∃ ℓ' : PastingDiagram X, ℓ'.IsRound ∧
      HasBdry false k ℓ' (ℓ.boundary k false) (ℓ.boundary k true) ∧
      ∀ z, (z.boundary k β).Equiv (ℓ.boundary k (!β)) → k < z.dim →
        ((CtxExpr.paste β ℓ' k).app z).Equiv
          ((CtxExpr.paste β (ℓ.boundary k β).unit k).app ((CtxExpr.frameOf β ℓ k).app z)) :=
  ⟨_, pad_frameOf_unit β hd hk hr⟩

theorem exists_pad (β : Bool) {ℓ : PastingDiagram X} {k : ℕ} (hd : ℓ.dim ≤ k + 1)
    (hk : k ≤ ℓ.dim) (hr : (ℓ.boundary k β).IsRound) (he : ℓ.topCells k ⊆ equivalences X) :
    ∃ (ℓ' : PastingDiagram X) (hℓ' : ℓ'.IsRound),
      (⟨ℓ', hℓ'⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
      HasBdry false k ℓ' (ℓ.boundary k false) (ℓ.boundary k true) ∧
      ∀ z, (z.boundary k β).Equiv (ℓ.boundary k (!β)) → k < z.dim →
        ((CtxExpr.paste β ℓ' k).app z).Equiv
          ((CtxExpr.paste β (ℓ.boundary k β).unit k).app ((CtxExpr.frameOf β ℓ k).app z)) := by
  obtain ⟨hround, hb, hz⟩ := pad_frameOf_unit β hd hk hr
  have u₀ := hasType_unit (dim_boundary ℓ hk β)
  refine ⟨_, hround, mem_equivalences_app_of_trim
    ((CtxExpr.typed_frameOf (!β) (H := ⟨k, ℓ.boundary k β, ℓ.boundary k β⟩) hd
      (by rw [Bool.not_not]; cases β <;> exact .refl _)).mono he fun h => h) _
    ⟨by rw [u₀.dim_h]; exact Nat.lt_succ_self k, u₀.side, u₀.other⟩ u₀.dim_h (isRound_unit hr)
    (unit_mem_equivalences ⟨_, hr⟩) hround, hb, hz⟩

theorem natSim_frame_padded {H H' : RoundHom X} {ℓ r ℓ' r' : PastingDiagram X} {G : CtxExpr X}
    (hH' : H'.toPdHom = ⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩)
    (hG : G.Typed Set.univ True H ⟨H.k, G.app H.v, G.app H.w⟩) (hdℓ : ℓ.dim ≤ H.k + 1)
    (hdr : r.dim ≤ H.k + 1) (hv : (G.app H.v).Equiv (ℓ.boundary H.k true))
    (hw : (G.app H.w).Equiv (r.boundary H.k false))
    (hE : IsRoundCtxOn H H' (.comp (CtxExpr.frame ℓ r H.k) G))
    (hℓ' : ∀ z, (z.boundary H.k false).Equiv (ℓ.boundary H.k true) → H.k < z.dim →
      ((CtxExpr.paste false ℓ' H.k).app z).Equiv
        ((CtxExpr.paste false (ℓ.boundary H.k false).unit H.k).app
          ((CtxExpr.frameOf false ℓ H.k).app z)))
    (hr' : ∀ z, (z.boundary H.k true).Equiv (r.boundary H.k false) → H.k < z.dim →
      ((CtxExpr.paste true r' H.k).app z).Equiv
        ((CtxExpr.paste true (r.boundary H.k true).unit H.k).app
          ((CtxExpr.frameOf true r H.k).app z)))
    (hr'r : r'.IsRound) (tr' : HasBdry false H.k r' (r.boundary H.k false) (r.boundary H.k true)) :
    NatSim X H H' (CtxExpr.comp (CtxExpr.frame ℓ r H.k) G).app
      (fun c => (CtxExpr.paste false ℓ' H.k).app ((CtxExpr.paste true r' H.k).app (G.app c))) := by
  obtain ⟨⟨k', v', w'⟩, hv', hw', hdv', hp'⟩ := H'
  cases hH'
  set H' : RoundHom X := ⟨⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩, hv', hw', hdv', hp'⟩
  have u₀ := hasType_unit H'.dim_v
  have u₁ := hasType_unit H'.dim_w
  have hK : IsRoundCtxOn H H' (.comp (CtxExpr.paste false (ℓ.boundary H.k false).unit H.k)
      (.comp (CtxExpr.frame ℓ r H.k) G)) :=
    (isRoundCtxOn_comp_paste false hE.typed (isRound_unit H'.isRound_v) u₀.dim_h
      u₀.other.symm).congr (.refl _) ⟨rfl, u₀.side, .refl _⟩
  have hR' : IsRoundCtxOn ⟨H.k, G.app H.v, G.app H.w⟩ ⟨H.k, G.app H.v, r.boundary H.k true⟩
      (CtxExpr.paste true r' H.k) :=
    (isRoundCtxOn_paste true ⟨H.k, G.app H.v, G.app H.w⟩ hr'r tr'.dim_h
      (hw.trans tr'.side.symm)).congr (.refl _) ⟨rfl, .refl _, tr'.other⟩
  refine ((NatSim.unit_left H H' (T := .comp (CtxExpr.frame ℓ r H.k) G) hE).trans_of_equiv
    (NatSim.unit_right H H' (T := .comp (CtxExpr.paste false (ℓ.boundary H.k false).unit H.k)
      (.comp (CtxExpr.frame ℓ r H.k) G)) hK).symm fun c hc => ?_).of_equiv
    (fun _ _ => .refl _) fun c hc => ?_
  · exact (CtxExpr.paste_app_pasteOr false
      (u₀.pastable_inHom (hE.typed.mapsInto c hc) (.refl _))).symm
  · have hGc := hG.mapsInto c hc
    have hℓy : (ℓ.boundary H.k true).Equiv ((G.app c).boundary H.k false) :=
      (hGc.source.trans hv).symm
    have hyr : ((G.app c).boundary H.k true).Equiv (r.boundary H.k false) :=
      hGc.target.trans hw
    have hRc := (CtxExpr.typed_frameOf true (H := ⟨H.k, G.app H.v, G.app H.w⟩) hdr
      hw).mapsInto _ hGc
    have hEc := hE.typed.mapsInto c hc
    have hr'c := hR'.typed.mapsInto _ hGc
    exact ((CtxExpr.paste_app_pasteOr true
      ((hK.typed.mapsInto c hc).pastable_hasType u₁ (.refl _))).symm).trans
      ((CtxExpr.pasteRight_app_pasteLeft
        (u₀.pastable_inHom hEc (.refl _))
        (hEc.pastable_hasType u₁ (.refl _))).trans
      ((CtxExpr.app_equiv (CtxExpr.paste false (ℓ.boundary H.k false).unit H.k)
        (CtxExpr.app_equiv (CtxExpr.paste true (r.boundary H.k true).unit H.k)
          ((CtxExpr.frameOf_app_frameOf hdℓ hℓy hyr hGc.lt_dim).symm))).trans
      ((CtxExpr.app_equiv (CtxExpr.paste false (ℓ.boundary H.k false).unit H.k)
        ((CtxExpr.frameOf_app_paste false
          (hRc.source.trans hv)
          (hRc.pastable_hasType u₁ (.refl _))).symm)).trans
      ((CtxExpr.app_equiv (CtxExpr.paste false (ℓ.boundary H.k false).unit H.k)
        (CtxExpr.app_equiv (CtxExpr.frameOf false ℓ H.k)
          ((hr' _ hyr hGc.lt_dim).symm))).trans
        ((hℓ' _ (hr'c.source.trans hv) hr'c.lt_dim).symm)))))

def FrameEqvRev : ContextFrames X → Prop
  | [] => True
  | (ℓ, r) :: fs => ℓ.topCells fs.length ⊆ equivalences X ∧
      r.topCells fs.length ⊆ equivalences X ∧ FrameEqvRev fs

theorem frameEqvRev_of_frameEquivalences : ∀ fs : ContextFrames X,
    FrameEquivalences fs.reverse → FrameEqvRev fs
  | [] => fun _ => trivial
  | (ℓ, r) :: fs => fun h => by
    rw [List.reverse_cons] at h
    have hlen : fs.reverse.length < (fs.reverse ++ [(ℓ, r)]).length := by simp
    have h₁ : ∀ p, (p = ℓ ∨ p = r) → p.topCells fs.length ⊆ equivalences X := fun p hp =>
      p.topCells_subset_equivalences fun U x hU hx => by
        refine h ⟨fs.reverse.length, hlen⟩ p ?_ U x (by simpa using hU) hx
        simpa [List.get_eq_getElem, List.getElem_concat_length] using hp
    refine ⟨h₁ ℓ (Or.inl rfl), h₁ r (Or.inr rfl), frameEqvRev_of_frameEquivalences fs fun i p hp =>
      ?_⟩
    have hi := i.isLt
    have h₂ := h ⟨i.val, by simp only [List.length_append, List.length_singleton]; omega⟩ p
    simp only [List.get_eq_getElem] at h₂ hp
    rw [List.getElem_append_left hi] at h₂
    exact h₂ hp

theorem exists_isWeakInvCtx_ofFramesRev : ∀ (ℓ r : PastingDiagram X) (fs : ContextFrames X)
    {H H' : RoundHom X}, H.k = fs.length →
    H'.toPdHom = ⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩ →
    FramesOn ((ℓ, r) :: fs) H → IsRoundCtx H (CtxExpr.ofFramesRev ((ℓ, r) :: fs)) →
    FrameEqvRev ((ℓ, r) :: fs) →
      ∃ E' : CtxExpr X, IsWeakInvCtx H H' (CtxExpr.ofFramesRev ((ℓ, r) :: fs)) E' ∧
        PresEqv H' E'
  | ℓ, r, fs, H, H', hk, hH', hfo, hr, ⟨heℓ, her, hfe⟩ => by
    have hE : IsRoundCtxOn H H' (CtxExpr.ofFramesRev ((ℓ, r) :: fs)) :=
      ⟨(typed_ofFramesRev ℓ r fs hk hfo).congr_codomain (by rw [hH']), hr⟩
    have hE' : IsRoundCtxOn H H' (.comp (CtxExpr.frame ℓ r H.k) (CtxExpr.ofFramesRev fs)) := by
      rw [hk]; exact hE
    obtain ⟨hdℓ, hdr, hv, hw, hf⟩ := hfo
    have hG := typed_inner hk hf
    obtain ⟨⟨k', v', w'⟩, hv', hw', hdv', hp'⟩ := H'
    cases hH'
    set H' : RoundHom X :=
      ⟨⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩, hv', hw', hdv', hp'⟩
    rw [← hk] at heℓ her
    obtain ⟨ℓ', hℓ'r, hℓ'e, tℓ', hℓ'⟩ := exists_pad false hdℓ (ℓ.le_dim_of_dim_boundary hdv')
      hv' heℓ
    obtain ⟨r', hr'r, hr'e, tr', hr'⟩ := exists_pad true hdr
      (r.le_dim_of_dim_boundary (hp'.1.symm.trans hdv')) hw' her
    have hS := natSim_frame_padded rfl hG hdℓ hdr hv hw hE' hℓ' hr' hr'r tr'
    clear hE'
    match fs, hk, hf, hfe, hr, hG, hv, hw, hS, hE with
    | [], hk, _, _, _, _, hv, hw, hS, hE =>
      obtain ⟨E', hW, hP⟩ := exists_isWeakInvCtx_frames
        (H₁ := ⟨⟨H.k, H.v, r.boundary H.k true⟩, H.isRound_v, hw', H.dim_v,
          ⟨H.dim_v.trans (hp'.1.symm.trans hdv').symm, Or.inl (H.dim_v.trans hk)⟩⟩) (H' := H')
        hℓ'r hℓ'e (tℓ'.of_equiv_other hv.symm) hr'r hr'e (tr'.of_equiv_side hw.symm)
        (.refl _) (.refl _)
      obtain ⟨⟨k, v, w⟩, hrv, hrw, hdv, hpar⟩ := H
      change k = 0 at hk
      subst hk
      exact ⟨E', hW.of_natSim (hS.of_equiv (fun _ _ => .refl _)
        fun _ _ => .refl _) hE, hP⟩
    | (ℓ₁, r₁) :: fs', hk, hf, hfe, hr, _, hv, hw, hS, hE =>
      have hGr := isRoundCtx_inner ℓ r ℓ₁ r₁ fs' hk ⟨hdℓ, hdr, hv, hw, hf⟩ hr
      rw [hk] at hf
      have hGt := typed_ofFramesRev ℓ₁ r₁ fs' (H := H.pred fs'.length hk) rfl hf
      have hvIn := H.isRoundIn_v hk
      have hwIn := H.isRoundIn_w hk
      obtain ⟨G', hW, -⟩ := exists_isWeakInvCtx_ofFramesRev ℓ₁ r₁ fs' (H := H.pred fs'.length hk)
        (H' := (IsRoundCtxOn.isRoundIn ⟨hGt, hGr⟩ hvIn).roundHom) rfl rfl hf hGr hfe
      obtain ⟨E', hW', hP⟩ := hW.exists_frames hvIn hwIn (D := H') hk hℓ'r hℓ'e
        (tℓ'.of_equiv_other hv.symm) hr'r hr'e (tr'.of_equiv_side hw.symm)
      obtain ⟨⟨k, v, w⟩, hrv, hrw, hdv, hpar⟩ := H
      change k = _ at hk
      subst hk
      exact ⟨E', hW'.of_natSim hS hE, hP⟩

def RoundHom.ofParallel {v w : RoundPastingDiagram X} (h : Parallel v w) : RoundHom X :=
  ⟨⟨v.dim, v.toPastingDiagram, w.toPastingDiagram⟩, v.isRound, w.isRound, rfl, h⟩

theorem InHom.of_hasRoundType {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    (h : HasRoundType a v w) (hp : Parallel v w) : InHom (RoundHom.ofParallel hp) a :=
  ⟨by change v.dim < a.dim; rw [h.dim_eq]; omega, h.source, h.target⟩

theorem HasRoundType.of_isRoundIn {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    {hp : Parallel v w} (ha : IsRoundIn (RoundHom.ofParallel hp) a) : HasRoundType a v w where
  dim_eq := ha.dim_eq
  dim_eq_dim := hp.1
  source := ha.inHom.source
  target := ha.inHom.target

theorem RoundContextEquation.spec {fs : ContextFrames X} {v w b : RoundPastingDiagram X}
    (h : RoundContextEquation fs v w b) :
    ∃ (ℓ r : PastingDiagram X) (rest : ContextFrames X),
      fs = ((ℓ, r) :: rest).reverse ∧ v.dim = rest.length ∧
      FramesOn ((ℓ, r) :: rest) (RoundHom.ofParallel h.1) ∧
      IsRoundCtx (RoundHom.ofParallel h.1) (CtxExpr.ofFramesRev ((ℓ, r) :: rest)) ∧
      IsRoundIn ⟨v.dim, ℓ.boundary v.dim false, r.boundary v.dim true⟩ b.toPastingDiagram := by
  obtain ⟨hpar, hlen, hbd, Y, f, hmono, U, a₀, c₀, hty, hev, hpc⟩ := h
  have := hmono
  obtain ⟨⟨ℓ, r⟩, rest, hrev⟩ : ∃ x rest, fs.reverse = x :: rest := by
    match hm : fs.reverse with
    | [] =>
      exfalso
      have := congrArg List.length hm
      rw [List.length_reverse, hlen] at this
      simp at this
    | x :: rest => exact ⟨x, rest, rfl⟩
  have hfs : fs = ((ℓ, r) :: rest).reverse := by rw [← hrev, List.reverse_reverse]
  subst hfs
  have hdv : v.dim = rest.length := by
    have := hlen; rw [List.length_reverse, List.length_cons] at this; omega
  set H := RoundHom.ofParallel hpar
  have ha₀ : IsRoundIn (H.mapTo f) (PastingDiagram.ofCell a₀) :=
    ⟨InHom.of_hasRoundType hty (hpar.mapTo f), hty.dim_eq, U.isAtom.isRound⟩
  obtain ⟨hfo, hval⟩ := framesOn_of_evalFrames f ℓ r rest hdv
    (boundedRev_of_boundedFrames _ hbd) ha₀.inHom hev
  have hr := isRoundCtx_ofFramesRev_of_hole f ℓ r rest hdv hfo ha₀ hval c₀.isRound
  have hEt := typed_ofFramesRev ℓ r rest hdv hfo
  have hc := ((hEt.mapTo f (B := Set.univ) fun _ _ => trivial).mapsInto _ ha₀.inHom).of_equiv hval
  have hdc : c₀.dim = v.dim + 1 :=
    (dim_eq_of_equiv hval).symm.trans
      (((hEt.mapTo f (B := Set.univ) fun _ _ => trivial).ctxLaws.dim_eq _ ha₀.inHom).trans
        ha₀.dim_eq)
  have hb₀ := hpc.equiv_boundary_pred hdc false
  have hb₁ := hpc.equiv_boundary_pred hdc true
  rw [boundary_mapTo] at hb₀ hb₁
  have hbdim : b.dim = v.dim + 1 := hpc.1.symm.trans hdc
  refine ⟨ℓ, r, rest, rfl, hdv, hfo, hr, ⟨⟨by dsimp only; omega,
    PastingDiagram.Equiv.of_mapTo f ?_, PastingDiagram.Equiv.of_mapTo f ?_⟩, hbdim, b.isRound⟩⟩
  · rw [← boundary_mapTo]
    exact hb₀.symm.trans hc.source
  · rw [← boundary_mapTo]
    exact hb₁.symm.trans hc.target

theorem roundContext_solution (fs : ContextFrames X) (v w b : RoundPastingDiagram X)
    (hE : FrameEquivalences fs) (h : RoundContextEquation fs v w b) :
    ∃ a c : RoundPastingDiagram X, HasRoundType a.toPastingDiagram v w ∧
      EvalFrames fs 0 a.toPastingDiagram c.toPastingDiagram ∧ Equivalent c b ∧
        (b ∈ equivalences X → a ∈ equivalences X) := by
  obtain ⟨ℓ, r, rest, rfl, hdv, hfo, hr, hb⟩ := h.spec
  obtain ⟨E', hW, hP⟩ := exists_isWeakInvCtx_ofFramesRev ℓ r rest (H' := hb.roundHom) hdv rfl hfo
    hr (frameEqvRev_of_frameEquivalences _ hE)
  obtain ⟨a, ha, heq, hcond⟩ := hW.exists_solution hP hb
  exact ⟨⟨a, ha.isRound⟩, ⟨_, (hW.round.isRoundIn ha).isRound⟩,
    HasRoundType.of_isRoundIn ha, evalFrames_ofFramesRev ℓ r rest hdv hfo a ha.inHom, heq,
    hcond⟩

theorem Equivalent.app {H H' : PdHom X} {E : CtxExpr X} (hE : IsRoundCtxOn H H' E)
    {a c : PastingDiagram X} (ha : IsRoundIn H a) (hc : IsRoundIn H c)
    (h : Equivalent ⟨a, ha.isRound⟩ ⟨c, hc.isRound⟩) :
    Equivalent ⟨E.app a, (hE.isRoundIn ha).isRound⟩ ⟨E.app c, (hE.isRoundIn hc).isRound⟩ := by
  obtain ⟨k', v', w'⟩ := H'
  obtain rfl : H.k = k' := hE.typed.k_eq.symm
  obtain ⟨-, e, he, hde, hs, ht⟩ := h.data
  have hda : (⟨a, ha.isRound⟩ : RoundPastingDiagram X).dim = H.k + 1 := ha.dim_eq
  rw [hda] at hde hs ht
  have hin : InHom H e.toPastingDiagram :=
    InHom.of_hasBdry (β := false) ⟨hde, ha.dim_eq, hc.dim_eq, hs, ht⟩ ha.inHom
  obtain ⟨hp, hround, hmem⟩ := mem_equivalences_app_paste_unit hE.typed hE.round he hin hde ht
  have L := hE.typed.ctxLaws
  have hEa := hE.isRoundIn ha
  have hEc := hE.isRoundIn hc
  have hdEa : (⟨E.app a, hEa.isRound⟩ : RoundPastingDiagram X).dim = H.k + 1 := hEa.dim_eq
  refine EquivalenceData.equivalent
    ⟨hEa.dim_eq.trans hEc.dim_eq.symm, ⟨_, hround⟩, hmem, ?_, ?_, ?_⟩
  · rw [hdEa]
    change ((E.app e.toPastingDiagram).paste (E.app c).unit (H.k + 1) hp).dim = H.k + 1 + 1
    rw [dim_paste, L.dim_eq _ hin, hde, dim_unit, hEc.dim_eq, max_self]
  · rw [hdEa]
    exact (equiv_boundary_paste hp false).trans
      ((L.boundary _ hin (Nat.lt_succ_self H.k) (by rw [hde]; omega) false).trans
        (CtxExpr.app_equiv E hs))
  · rw [hdEa]
    exact (equiv_boundary_paste hp true).trans
      (boundary_unit hEc.dim_eq true)

theorem roundContext_solution_cell (hX : HasWeakComposites X)
    (fs : ContextFrames X) (v w b : RoundPastingDiagram X)
    (hE : FrameEquivalences fs) (h : RoundContextEquation fs v w b) :
    ∃ (U : Atom) (a : diagram X U) (c : RoundPastingDiagram X),
      HasRoundType (PastingDiagram.ofCell a) v w ∧
      EvalFrames fs 0 (PastingDiagram.ofCell a) c.toPastingDiagram ∧ Equivalent c b ∧
        (b ∈ equivalences X → IsEquivalence X a) := by
  obtain ⟨ℓ, r, rest, rfl, hdv, hfo, hr, hb⟩ := h.spec
  obtain ⟨E', hW, hP⟩ := exists_isWeakInvCtx_ofFramesRev ℓ r rest (H' := hb.roundHom) hdv rfl hfo
    hr (frameEqvRev_of_frameEquivalences _ hE)
  obtain ⟨a, ha, heq, hcond⟩ := hW.exists_solution hP hb
  obtain ⟨x, hx⟩ := hX ⟨a, ha.isRound⟩
  have hdx : (PastingDiagram.ofCell x).dim = v.dim + 1 := hx.data.dim_eq.symm.trans ha.dim_eq
  have hxIn : IsRoundIn (RoundHom.ofParallel h.1) (PastingDiagram.ofCell x) :=
    ⟨⟨by change v.dim < _; omega, PastingDiagram.Equiv.trans
        ((hx.equiv_boundary (by rw [ha.dim_eq]; change v.dim < v.dim + 1; omega) false).symm)
        ha.inHom.source,
      PastingDiagram.Equiv.trans
        ((hx.equiv_boundary (by rw [ha.dim_eq]; change v.dim < v.dim + 1; omega) true).symm)
        ha.inHom.target⟩, hdx, (cellRound x).isRound⟩
  have hEx := Equivalent.app hW.round ha hxIn hx
  exact ⟨_, x, ⟨_, (hW.round.isRoundIn hxIn).isRound⟩, HasRoundType.of_isRoundIn hxIn,
    evalFrames_ofFramesRev ℓ r rest hdv hfo _ hxIn.inHom,
    equivalent_trans (equivalent_symm hEx) heq,
    fun hbe => (mem_equivalences_iff_of_equivalent hx).1 (hcond hbe)⟩

end Atoms.Diagrammatic
