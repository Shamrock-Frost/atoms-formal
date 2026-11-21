import Atoms.Diagrammatic.Context.NaturalClosure

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure IsWeakInvCtx (H H' : RoundHom X) (E E' : CtxExpr X) : Prop where
  round : IsRoundCtxOn H H' E
  round' : IsRoundCtxOn H' H E'
  left : NatSim X H H (fun c => E'.app (E.app c)) (fun c => c)
  right : NatSim X H' H' (fun c => E.app (E'.app c)) (fun c => c)

def PresEqv (H : PdHom X) (E : CtxExpr X) : Prop :=
  ∀ a (ha : IsRoundIn H a), (⟨a, ha.isRound⟩ : RoundPastingDiagram X) ∈ equivalences X →
    ∀ hr : (E.app a).IsRound, (⟨E.app a, hr⟩ : RoundPastingDiagram X) ∈ equivalences X

theorem PresEqv.comp {H H' : PdHom X} {E F : CtxExpr X} (hE : PresEqv H E)
    (hEr : IsRoundCtxOn H H' E) (hF : PresEqv H' F) : PresEqv H (.comp F E) := fun a ha he hr =>
  hF _ (hEr.isRoundIn ha) (hE a ha he _) hr

theorem presEqv_paste (α : Bool) {H : PdHom X} {x : PastingDiagram X} (hx : x.IsRound)
    (hxe : (⟨x, hx⟩ : RoundPastingDiagram X) ∈ equivalences X) (hdx : x.dim = H.k + 1)
    (hxs : (x.boundary H.k (!α)).Equiv (H.side α)) : PresEqv H (CtxExpr.paste α x H.k) :=
  fun a ha he hr => by
    have hp := Pastable.of_side α ((ha.inHom.side α).trans hxs.symm) ha.inHom.lt_dim
      (by rw [hdx]; omega)
    have e := (CtxExpr.paste_app α hp).symm
    cases α
    · exact mem_equivalences_of_equiv e ((paste_mem_equivalences_iff_right (u := ⟨x, hx⟩)
        (v := ⟨a, ha.isRound⟩) hxe hdx ha.dim_eq hp).2 he)
    · exact mem_equivalences_of_equiv e ((paste_mem_equivalences_iff_right (u := ⟨a, ha.isRound⟩)
        (v := ⟨x, hx⟩) he ha.dim_eq hdx hp).2 hxe)

namespace IsWeakInvCtx

variable {H H' H'' : RoundHom X} {E E' F F' : CtxExpr X}

theorem symm (h : IsWeakInvCtx H H' E E') : IsWeakInvCtx H' H E' E :=
  ⟨h.round', h.round, h.right, h.left⟩

theorem comp (h₁ : IsWeakInvCtx H H' E E') (h₂ : IsWeakInvCtx H' H'' F F') :
    IsWeakInvCtx H H'' (.comp F E) (.comp E' F') :=
  ⟨h₁.round.comp h₂.round, h₂.round'.comp h₁.round',
    ((h₂.left.right H h₁.round).left h₁.round').trans h₁.left,
    ((h₁.right.right H'' h₂.round').left h₂.round).trans h₂.right⟩

theorem of_natSim (hF : IsWeakInvCtx H H' F F') (h : NatSim X H H' E.app F.app)
    (hE : IsRoundCtxOn H H' E) : IsWeakInvCtx H H' E F' :=
  ⟨hE, hF.round', (h.left hF.round').trans hF.left, (h.right H' hF.round').trans hF.right⟩

theorem of_left (hE : IsRoundCtxOn H H' E) {K K' : CtxExpr X} (hK : IsRoundCtxOn H' H K)
    (hK' : IsRoundCtxOn H H' K') (hl : NatSim X H H (fun c => K.app (E.app c)) (fun c => c))
    (hl' : NatSim X H' H' (fun c => K'.app (K.app c)) (fun c => c)) : IsWeakInvCtx H H' E K :=
  ⟨hE, hK, hl,
    ((NatSim.symm (hl'.right H' (hK.comp hE))).trans ((hl.right H' hK).left hK')).trans hl'⟩

end IsWeakInvCtx

theorem exists_isWeakInvCtx_pasteLeft {H H' : RoundHom X} {x : PastingDiagram X}
    (hx : x.IsRound) (hxe : (⟨x, hx⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (ht : HasBdry false H.k x H'.v H.v) (he : (H.setSide false H'.v).Equiv H') :
    ∃ x' : PastingDiagram X, IsWeakInvCtx H H' (CtxExpr.paste false x H.k)
      (CtxExpr.paste false x' H.k) ∧ PresEqv H' (CtxExpr.paste false x' H.k) := by
  obtain ⟨⟨k', p, w'⟩, hp, hw', hdp, hpp⟩ := H'
  obtain rfl : H.k = k' := he.k_eq
  set H' : RoundHom X := ⟨⟨H.k, p, w'⟩, hp, hw', hdp, hpp⟩
  have hw : H.w.Equiv H'.w := he.equiv_w
  obtain ⟨e', hwi⟩ := exists_isWeakInverse hxe
  obtain ⟨hr', he'⟩ := hwi.mem_equivalences fun _ => hxe
  obtain ⟨-, tx', ⟨z, hz, hmz, tz⟩, ⟨h, hh, hmh, th⟩⟩ := hwi.spec ht
  set x' := e'.toPastingDiagram
  have hE : IsRoundCtxOn H H' (CtxExpr.paste false x H.k) :=
    (isRoundCtxOn_paste false H.toPdHom hx ht.dim_h ht.other.symm).congr (.refl _)
      ⟨rfl, ht.side, hw⟩
  have hE' : IsRoundCtxOn H' H (CtxExpr.paste false x' H.k) :=
    (isRoundCtxOn_paste false H'.toPdHom hr' tx'.dim_h tx'.other.symm).congr (.refl _)
      ⟨rfl, tx'.side, hw.symm⟩
  have tq := hasType_unit H.dim_v
  have tp := hasType_unit H'.dim_v
  have t₁ := tx'.pasteOr ht (.refl _)
  have t₂ := ht.pasteOr tx' (.refl _)
  have hσ₁ : ctxPfw false H H.v.unit (x'.pasteOr x H.k) h ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨false, H, _, _, _, ⟨hh, hmh, th⟩, tq.other, rfl⟩
  have hσ₂ : ctxPfw false H' (x.pasteOr x' H.k) H'.v.unit z ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨false, H', _, _, _, ⟨hz, hmz, tz⟩, t₂.other, rfl⟩
  have S₁ : NatSim X H H (CtxExpr.paste false (x'.pasteOr x H.k) H.k).app
      (CtxExpr.paste false H.v.unit H.k).app :=
    (NatSim.symm (CtxTriple.Sim.of_mem hσ₁)).congr (.refl _)
      (PdHom.equiv_setSide H.toPdHom (α := false) tq.side.symm).symm
  have S₂ : NatSim X H' H' (CtxExpr.paste false (x.pasteOr x' H.k) H.k).app
      (CtxExpr.paste false H'.v.unit H.k).app :=
    (CtxTriple.Sim.of_mem hσ₂).congr (.refl _)
      (PdHom.equiv_setSide H'.toPdHom (α := false) t₂.side.symm).symm
  have U₁ : NatSim X H H (fun c => H.v.unit.pasteOr c H.k) (fun c => c) :=
    (NatSim.unit_left H H (T := .id) isRoundCtxOn_id).symm
  have U₂ : NatSim X H' H' (fun c => H'.v.unit.pasteOr c H.k) (fun c => c) :=
    (NatSim.unit_left H' H' (T := .id) isRoundCtxOn_id).symm
  refine ⟨x', ⟨hE, hE', ?_, ?_⟩, presEqv_paste false hr' he' tx'.dim_h tx'.other⟩
  · refine (S₁.trans_of_equiv U₁ fun c hc => CtxExpr.paste_app_pasteOr false
      (tq.pastable_inHom hc (.refl _))).of_equiv (fun c hc =>
        (CtxExpr.paste_app_paste false
          (ht.pastable_inHom hc (.refl _))
          (tx'.pastable ht (.refl _))).symm) (fun _ _ => .refl _)
  · refine (S₂.trans_of_equiv U₂ fun c hc => CtxExpr.paste_app_pasteOr false
      (tp.pastable_inHom hc (.refl _))).of_equiv (fun c hc =>
        (CtxExpr.paste_app_paste false
          (tx'.pastable_inHom hc (.refl _))
          (ht.pastable tx' (.refl _))).symm) (fun _ _ => .refl _)

theorem exists_isWeakInvCtx_pasteRight {H H' : RoundHom X} {x : PastingDiagram X}
    (hx : x.IsRound) (hxe : (⟨x, hx⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (ht : HasBdry false H.k x H.w H'.w) (he : (H.setSide true H'.w).Equiv H') :
    ∃ x' : PastingDiagram X, IsWeakInvCtx H H' (CtxExpr.paste true x H.k)
      (CtxExpr.paste true x' H.k) ∧ PresEqv H' (CtxExpr.paste true x' H.k) := by
  obtain ⟨⟨k', v', q⟩, hv', hq, hdv', hpq⟩ := H'
  obtain rfl : H.k = k' := he.k_eq
  set H' : RoundHom X := ⟨⟨H.k, v', q⟩, hv', hq, hdv', hpq⟩
  have hv : H.v.Equiv H'.v := he.equiv_v
  obtain ⟨e', hwi⟩ := exists_isWeakInverse hxe
  obtain ⟨hr', he'⟩ := hwi.mem_equivalences fun _ => hxe
  obtain ⟨-, tx', ⟨z, hz, hmz, tz⟩, ⟨h, hh, hmh, th⟩⟩ := hwi.spec ht
  set x' := e'.toPastingDiagram
  have hE : IsRoundCtxOn H H' (CtxExpr.paste true x H.k) :=
    (isRoundCtxOn_paste true H.toPdHom hx ht.dim_h ht.side.symm).congr (.refl _) ⟨rfl, hv, ht.other⟩
  have hE' : IsRoundCtxOn H' H (CtxExpr.paste true x' H.k) :=
    (isRoundCtxOn_paste true H'.toPdHom hr' tx'.dim_h tx'.side.symm).congr (.refl _)
      ⟨rfl, hv.symm, tx'.other⟩
  have tq := hasType_unit H'.dim_w
  have tp := hasType_unit H.dim_w
  have t₁ := tx'.pasteOr ht (.refl _)
  have t₂ := ht.pasteOr tx' (.refl _)
  have hσ₁ : ctxPfw true H (x.pasteOr x' H.k) H.w.unit z ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨true, H, _, _, _, ⟨hz, hmz, tz⟩, t₂.side, rfl⟩
  have hσ₂ : ctxPfw true H' H'.w.unit (x'.pasteOr x H.k) h ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨true, H', _, _, _, ⟨hh, hmh, th⟩, tq.side, rfl⟩
  have S₁ : NatSim X H H (CtxExpr.paste true (x.pasteOr x' H.k) H.k).app
      (CtxExpr.paste true H.w.unit H.k).app :=
    (CtxTriple.Sim.of_mem hσ₁).congr (.refl _)
      (PdHom.equiv_setSide H.toPdHom (α := true) t₂.other.symm).symm
  have S₂ : NatSim X H' H' (CtxExpr.paste true (x'.pasteOr x H.k) H.k).app
      (CtxExpr.paste true H'.w.unit H.k).app :=
    (NatSim.symm (CtxTriple.Sim.of_mem hσ₂)).congr (.refl _)
      (PdHom.equiv_setSide H'.toPdHom (α := true) tq.other.symm).symm
  have U₁ : NatSim X H H (fun c => c.pasteOr H.w.unit H.k) (fun c => c) :=
    NatSim.unit_right H H (T := .id) isRoundCtxOn_id
  have U₂ : NatSim X H' H' (fun c => c.pasteOr H'.w.unit H.k) (fun c => c) :=
    NatSim.unit_right H' H' (T := .id) isRoundCtxOn_id
  refine ⟨x', ⟨hE, hE', ?_, ?_⟩, presEqv_paste true hr' he' tx'.dim_h tx'.side⟩
  · refine (S₁.trans_of_equiv U₁ fun c hc => CtxExpr.paste_app_pasteOr true
      (hc.pastable_hasType tp (.refl _))).of_equiv (fun c hc =>
        (CtxExpr.paste_app_paste true
          (hc.pastable_hasType ht (.refl _))
          (ht.pastable tx' (.refl _))).symm) (fun _ _ => .refl _)
  · refine (S₂.trans_of_equiv U₂ fun c hc => CtxExpr.paste_app_pasteOr true
      (hc.pastable_hasType tq (.refl _))).of_equiv (fun c hc =>
        (CtxExpr.paste_app_paste true
          (hc.pastable_hasType tx' (.refl _))
          (tx'.pastable ht (.refl _))).symm) (fun _ _ => .refl _)

noncomputable def CtxExpr.rounded (F : CtxExpr X) (b : PastingDiagram X) (n : ℕ) : CtxExpr X :=
  .comp (CtxExpr.paste true (F.app b).unit (n + 1)) F

theorem isRoundCtxOn_rounded {H H' : PdHom X} {a b : PastingDiagram X} {F : CtxExpr X}
    (hF : IsRoundCtxOn H H' F) (ha : IsRoundIn H a) (hb : IsRoundIn H b) :
    IsRoundCtxOn (RoundHom.ofIsRoundIn ha hb)
      (RoundHom.ofIsRoundIn (hF.isRoundIn ha) (hF.isRoundIn hb)) (F.rounded b H.k) := by
  have hk : H'.k + 1 = H.k + 1 := by rw [hF.typed.k_eq]
  have hFb := hF.isRoundIn hb
  have tu := hasType_unit (hFb.dim_eq.trans hk)
  exact (isRoundCtxOn_comp_paste true (hF.typed.promote_of_inHom trivial ha.inHom hb.inHom)
    (isRound_unit hFb.isRound) tu.dim_h tu.side.symm).congr (.refl _) ⟨hk.symm, .refl _, tu.other⟩

theorem presEqv_rounded {H H' : PdHom X} {a b : PastingDiagram X} {F : CtxExpr X}
    (hF : IsRoundCtxOn H H' F) (ha : IsRoundIn H a) (hb : IsRoundIn H b) :
    PresEqv (RoundHom.ofIsRoundIn ha hb) (F.rounded b H.k) := fun c hc he _ => by
  obtain ⟨hp, hround, hmem⟩ := mem_equivalences_app_paste_unit hF.typed hF.round
    (e := ⟨c, hc.isRound⟩) he (InHom.of_inHom_succ hc.inHom ha.inHom hb.inHom) hc.dim_eq
    hc.inHom.target
  exact mem_equivalences_of_equiv (e := ⟨_, hround⟩)
    ((CtxExpr.paste_app true hp).symm) hmem

theorem exists_natSim_rounded_of_natEqv {H : RoundHom X} {H' : PdHom X} {F G : CtxExpr X}
    {ϑ : PastingDiagram X → PastingDiagram X}
    (hσ : (⟨H, H', F, G, ϑ⟩ : CtxTriple X) ∈ natEqv X) (hF : IsRoundCtxOn H H' F)
    (hG : IsRoundCtxOn H H' G) {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) :
    ∃ C C' : CtxExpr X,
      IsWeakInvCtx (.ofIsRoundIn (hG.isRoundIn ha) (hG.isRoundIn hb))
        (.ofIsRoundIn (hF.isRoundIn ha) (hF.isRoundIn hb)) C C' ∧
      PresEqv (RoundHom.ofIsRoundIn (hF.isRoundIn ha) (hF.isRoundIn hb)) C' ∧
      NatSim X (RoundHom.ofIsRoundIn ha hb) (RoundHom.ofIsRoundIn (hF.isRoundIn ha)
        (hF.isRoundIn hb)) (F.rounded b H.k).app (fun c => C.app ((G.rounded b H.k).app c)) := by
  obtain ⟨k', v', w'⟩ := H'
  obtain rfl : H.k = k' := hF.typed.k_eq.symm
  rw [← natOp_natEqv] at hσ
  obtain ⟨hv, N⟩ := hσ
  have hFa := hF.isRoundIn ha
  have hFb := hF.isRoundIn hb
  have hGa := hG.isRoundIn ha
  have hGb := hG.isRoundIn hb
  obtain ⟨hra, hea, tϑa⟩ := hv.comp a ha
  obtain ⟨hrb, heb, tϑb⟩ := hv.comp b hb
  change HasBdry false (H.k + 1) (ϑ a) (F.app a) (G.app a) at tϑa
  change HasBdry false (H.k + 1) (ϑ b) (F.app b) (G.app b) at tϑb
  obtain ⟨e', hwi⟩ := exists_isWeakInverse heb
  obtain ⟨hr', -⟩ := hwi.mem_equivalences fun _ => heb
  obtain ⟨-, tϑ', ⟨z, hz, hmz, tz⟩, -⟩ := hwi.spec tϑb
  set ϑ' := e'.toPastingDiagram
  set D := RoundHom.ofIsRoundIn ha hb
  set DFF := RoundHom.ofIsRoundIn hFa hFb
  have uFa := hasType_unit hFa.dim_eq
  have uFb := hasType_unit hFb.dim_eq
  have uGb := hasType_unit hGb.dim_eq
  have tx := tϑb.pasteOr tϑ' (.refl _)
  have hFp := hF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGp := hG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  obtain ⟨x₁, h₁, he₁⟩ := exists_isWeakInvCtx_pasteRight (H := .ofIsRoundIn hGa hGb)
    (H' := .ofIsRoundIn hGa hFb) hr' (hwi.mem_equivalences fun _ => heb).2 tϑ' (.refl _)
  obtain ⟨x₂, h₂, he₂⟩ := exists_isWeakInvCtx_pasteLeft (H := .ofIsRoundIn hGa hFb)
    (H' := DFF) hra hea tϑa (.refl _)
  refine ⟨.comp (CtxExpr.paste false (ϑ a) (H.k + 1)) (CtxExpr.paste true ϑ' (H.k + 1)),
    .comp (CtxExpr.paste true x₁ (H.k + 1)) (CtxExpr.paste false x₂ (H.k + 1)), h₁.comp h₂,
    he₂.comp h₂.round' he₁, ?_⟩
  have hT₁ : IsRoundCtxOn D (RoundHom.ofIsRoundIn hFa hGb)
      (.comp (CtxExpr.paste false (ϑ a) (H.k + 1)) G) :=
    (isRoundCtxOn_comp_paste false hGp hra tϑa.dim_h tϑa.other.symm).congr (.refl _)
      ⟨rfl, tϑa.side, .refl _⟩
  have hR' : IsRoundCtxOn (RoundHom.ofIsRoundIn hFa hGb) DFF (CtxExpr.paste true ϑ' (H.k + 1)) :=
    (isRoundCtxOn_paste true (RoundHom.ofIsRoundIn hFa hGb).toPdHom hr' tϑ'.dim_h
      tϑ'.side.symm).congr (.refl _) ⟨rfl, .refl _, tϑ'.other⟩
  have hT₃ : IsRoundCtxOn D DFF (.comp (CtxExpr.paste true ϑ' (H.k + 1))
      (.comp (CtxExpr.paste true (ϑ b) (H.k + 1)) F)) :=
    (hv.isRoundCtxOn_nextF ha hb).comp hR'
  have hK : IsRoundCtxOn D DFF (.comp (CtxExpr.paste false (F.app a).unit (H.k + 1)) F) :=
    (isRoundCtxOn_comp_paste false hFp (isRound_unit hFa.isRound) uFa.dim_h
      uFa.other.symm).congr (.refl _) ⟨rfl, uFa.side, .refl _⟩
  have hRF : IsRoundCtxOn D DFF (F.rounded b H.k) := isRoundCtxOn_rounded hF ha hb
  have hRG := isRoundCtxOn_rounded hG ha hb
  have hσ₄ : ctxPfw true DFF ((ϑ b).pasteOr ϑ' (H.k + 1)) (F.app b).unit z ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨true, DFF, _, _, _, ⟨hz, hmz, tz⟩, tx.side, rfl⟩
  have S₁ := (NatSim.unit_right D (.ofIsRoundIn hFa hGb)
    (T := .comp (CtxExpr.paste false (ϑ a) (H.k + 1)) G) hT₁).left hR'
  have S₂ := (NatSim.symm (CtxTriple.Sim.mono (fun _ h => CtxTriple.Closure.base h)
    (N a b ha hb))).left hR'
  have S₃ := NatSim.unit_left D DFF (T := .comp (CtxExpr.paste true ϑ' (H.k + 1))
    (.comp (CtxExpr.paste true (ϑ b) (H.k + 1)) F)) hT₃
  have S₄ := ((CtxTriple.Sim.of_mem hσ₄).congr (.refl _)
    (PdHom.equiv_setSide DFF.toPdHom (α := true) tx.other.symm).symm).right D hK
  have S₅ := (NatSim.unit_left D DFF (T := F.rounded b H.k) hRF).symm
  refine (NatSim.symm ((((S₁.trans S₂).trans S₃).trans_of_equiv S₄ fun c hc => ?_).trans_of_equiv S₅
    fun c hc => ?_)).of_equiv (fun _ _ => .refl _) fun c hc => ?_
  · have hFc := hFp.mapsInto c hc
    exact ((CtxExpr.paste_app_pasteOr false
      (uFa.pastable_inHom (hT₃.typed.mapsInto c hc) (.refl _))).symm).trans
      ((CtxExpr.app_equiv (CtxExpr.paste false (F.app a).unit (H.k + 1))
        (CtxExpr.paste_app_paste true (hFc.pastable_hasType tϑb (.refl _))
          (tϑb.pastable tϑ' (.refl _)))).trans
        ((CtxExpr.pasteRight_app_pasteLeft
          (uFa.pastable_inHom hFc (.refl _))
          (hFc.pastable_hasType tx (.refl _))).symm))
  · have hFc := hFp.mapsInto c hc
    exact (CtxExpr.pasteRight_app_pasteLeft
      (uFa.pastable_inHom hFc (.refl _))
      (hFc.pastable_hasType uFb (.refl _))).trans
      (CtxExpr.paste_app_pasteOr false (uFa.pastable_inHom (hRF.typed.mapsInto c hc)
        (.refl _)))
  · have hGc := hGp.mapsInto c hc
    have hRGc := hRG.typed.mapsInto c hc
    exact (CtxExpr.app_equiv (CtxExpr.paste true ϑ' (H.k + 1))
      (((CtxExpr.paste_app_pasteOr true
        ((hT₁.typed.mapsInto c hc).pastable_hasType uGb (.refl _))).symm).trans
        (CtxExpr.pasteRight_app_pasteLeft (tϑa.pastable_inHom hGc (.refl _))
          (hGc.pastable_hasType uGb (.refl _))))).trans
      (CtxExpr.pasteRight_app_pasteLeft (tϑa.pastable_inHom hRGc (.refl _))
        (hRGc.pastable_hasType tϑ' (.refl _)))

theorem natSim_rounded_comp {H H' H'' : PdHom X} {F G : CtxExpr X} (hF : IsRoundCtxOn H H' F)
    (hG : IsRoundCtxOn H' H'' G) {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) :
    NatSim X (RoundHom.ofIsRoundIn ha hb)
      (RoundHom.ofIsRoundIn (hG.isRoundIn (hF.isRoundIn ha)) (hG.isRoundIn (hF.isRoundIn hb)))
      ((CtxExpr.comp G F).rounded b H.k).app
      (fun c => (G.rounded (F.app b) H'.k).app ((F.rounded b H.k).app c)) := by
  obtain ⟨k', v', w'⟩ := H'
  obtain rfl : H.k = k' := hF.typed.k_eq.symm
  obtain ⟨k'', v'', w''⟩ := H''
  obtain rfl : H.k = k'' := hG.typed.k_eq.symm
  have hGF := hF.comp hG
  have hFa := hF.isRoundIn ha
  have hFb := hF.isRoundIn hb
  have hGFa := hG.isRoundIn hFa
  have hGFb := hG.isRoundIn hFb
  set D := RoundHom.ofIsRoundIn ha hb
  set D₀ := RoundHom.ofIsRoundIn hGFa hGFb
  have uFb := hasType_unit hFb.dim_eq
  have uGFa := hasType_unit hGFa.dim_eq
  have uGFb := hasType_unit hGFb.dim_eq
  have hT₀ : IsRoundCtxOn D D₀ ((CtxExpr.comp G F).rounded b H.k) :=
    isRoundCtxOn_rounded hGF ha hb
  have hRF := isRoundCtxOn_rounded hF ha hb
  have hT₁ : IsRoundCtxOn D D₀ (.comp (G.rounded (F.app b) H.k) (F.rounded b H.k)) :=
    hRF.comp (isRoundCtxOn_rounded hG hFa hFb)
  have hFp := hF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGFp := hGF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGp := hG.typed.promote_of_inHom trivial hFa.inHom hFb.inHom
  have tGu := hG.typed.hasType_app uFb hFb.inHom hFb.inHom
  have hK : IsRoundCtxOn D D₀
      (.comp (CtxExpr.paste false (G.app (F.app a)).unit (H.k + 1)) (.comp G F)) :=
    (isRoundCtxOn_comp_paste false hGFp (isRound_unit hGFa.isRound) uGFa.dim_h
      uGFa.other.symm).congr (.refl _) ⟨rfl, uGFa.side, .refl _⟩
  have hE : IsRoundCtxOn D₀ D₀ (CtxExpr.paste true (G.app (F.app b)).unit (H.k + 1)) :=
    (isRoundCtxOn_paste true D₀.toPdHom (isRound_unit hGFb.isRound) uGFb.dim_h
      uGFb.side.symm).congr (.refl _) ⟨rfl, .refl _, uGFb.other⟩
  have S₁ := NatSim.unit_left D D₀ (T := (CtxExpr.comp G F).rounded b H.k) hT₀
  have S₂ := (CtxTriple.Sim.paste_app_unit (fun _ => valid_of_mem_natEqv) cylTriples_subset_natEqv
    D D₀ hG.typed hFb rfl (.refl _) hK : NatSim X D D₀ _ _).left hE
  have S₃ := (NatSim.unit_left D D₀ (T := .comp (G.rounded (F.app b) H.k) (F.rounded b H.k))
    hT₁).symm
  refine (S₁.trans_of_equiv S₂ fun c hc => ?_).trans_of_equiv S₃ fun c hc => ?_
  · have hGFc := hGFp.mapsInto c hc
    exact ((CtxExpr.paste_app_pasteOr false
      (uGFa.pastable_inHom (hT₀.typed.mapsInto c hc) (.refl _))).symm).trans
      ((CtxExpr.pasteRight_app_pasteLeft
        (uGFa.pastable_inHom hGFc (.refl _))
        (hGFc.pastable_hasType uGFb (.refl _))).symm)
  · have hGFc := hGFp.mapsInto c hc
    have hFc := hFp.mapsInto c hc
    have hRFc := hRF.typed.mapsInto c hc
    have hGRFc := hGp.mapsInto _ hRFc
    have hKc := hK.typed.mapsInto c hc
    exact (CtxExpr.app_equiv
      (CtxExpr.paste true (G.app (F.app b)).unit (H.k + 1)) (PastingDiagram.Equiv.trans
        ((CtxExpr.paste_app_pasteOr true
          (hKc.pastable_hasType tGu (.refl _))).symm)
        ((CtxExpr.pasteRight_app_pasteLeft
          (uGFa.pastable_inHom hGFc (.refl _))
          (hGFc.pastable_hasType tGu (.refl _))).trans
          (CtxExpr.app_equiv (CtxExpr.paste false (G.app (F.app a)).unit (H.k + 1))
            ((hG.typed.app_paste true
              (InHom.of_inHom_succ hFc hFa.inHom hFb.inHom)
              (hFc.pastable_hasType uFb (.refl _))).symm))))).trans
      ((CtxExpr.pasteRight_app_pasteLeft
        (uGFa.pastable_inHom hGRFc (.refl _))
        (hGRFc.pastable_hasType uGFb (.refl _))).trans
        (CtxExpr.paste_app_pasteOr false (uGFa.pastable_inHom (hT₁.typed.mapsInto c hc)
          (.refl _))))

theorem IsWeakInvCtx.exists_left_rounded {H H' : RoundHom X} {F F' : CtxExpr X}
    (hF : IsWeakInvCtx H H' F F') {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) :
    ∃ J J' : CtxExpr X, IsWeakInvCtx (.ofIsRoundIn ha hb)
        (.ofIsRoundIn (hF.round'.isRoundIn (hF.round.isRoundIn ha))
          (hF.round'.isRoundIn (hF.round.isRoundIn hb))) J J' ∧
      PresEqv (RoundHom.ofIsRoundIn (hF.round'.isRoundIn (hF.round.isRoundIn ha))
        (hF.round'.isRoundIn (hF.round.isRoundIn hb))) J' ∧
      NatSim X (RoundHom.ofIsRoundIn ha hb)
        (RoundHom.ofIsRoundIn (hF.round'.isRoundIn (hF.round.isRoundIn ha))
          (hF.round'.isRoundIn (hF.round.isRoundIn hb)))
        (fun c => (F'.rounded (F.app b) H'.k).app ((F.rounded b H.k).app c)) J.app := by
  obtain ⟨σ, hσ, r⟩ := hF.left
  have hσ' : σ ∈ natEqv X := by rw [← closure_natEqv]; exact hσ
  have hFF := hF.round.comp hF.round'
  have hτ := mem_natEqv_of_realizes (F := .comp F' F) (G := .id) hσ' r hFF isRoundCtxOn_id
  obtain ⟨C, C', hC, hC'e, hCs⟩ :=
    exists_natSim_rounded_of_natEqv hτ hFF isRoundCtxOn_id ha hb
  have ub := hasType_unit hb.dim_eq
  obtain ⟨y, hy, hye⟩ := exists_isWeakInvCtx_pasteRight (H := .ofIsRoundIn ha hb)
    (H' := .ofIsRoundIn ha hb) (isRound_unit hb.isRound)
    (unit_mem_equivalences ⟨b, hb.isRound⟩) ub (.refl _)
  have hI : IsWeakInvCtx (.ofIsRoundIn ha hb) (.ofIsRoundIn ha hb)
      ((CtxExpr.id : CtxExpr X).rounded b H.k) (CtxExpr.paste true y (H.k + 1)) :=
    hy.of_natSim ((NatSim.refl (.ofIsRoundIn ha hb) hy.round).of_equiv (fun _ _ => .refl _)
      (fun _ _ => .refl _)) (isRoundCtxOn_rounded isRoundCtxOn_id ha hb)
  refine ⟨.comp C ((CtxExpr.id : CtxExpr X).rounded b H.k),
    .comp (CtxExpr.paste true y (H.k + 1)) C', hI.comp hC, hC'e.comp hC.round' hye, ?_⟩
  exact (natSim_rounded_comp hF.round hF.round' ha hb).symm.trans hCs

theorem IsWeakInvCtx.exists_rounded {H H' : RoundHom X} {F F' : CtxExpr X}
    (hF : IsWeakInvCtx H H' F F') {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) :
    ∃ K : CtxExpr X, IsWeakInvCtx (.ofIsRoundIn ha hb)
        (.ofIsRoundIn (hF.round.isRoundIn ha) (hF.round.isRoundIn hb)) (F.rounded b H.k) K ∧
      PresEqv (RoundHom.ofIsRoundIn (hF.round.isRoundIn ha) (hF.round.isRoundIn hb)) K := by
  have hFa := hF.round.isRoundIn ha
  have hFb := hF.round.isRoundIn hb
  obtain ⟨J, J', hJ, hJe, hJs⟩ := hF.exists_left_rounded ha hb
  obtain ⟨J₂, J₂', hJ₂, -, hJ₂s⟩ := hF.symm.exists_left_rounded hFa hFb
  have hRF := isRoundCtxOn_rounded hF.round ha hb
  have hRF' := isRoundCtxOn_rounded hF.round' hFa hFb
  have hRF₂ := isRoundCtxOn_rounded hF.round (hF.round'.isRoundIn hFa) (hF.round'.isRoundIn hFb)
  refine ⟨.comp J' (F'.rounded (F.app b) H'.k), IsWeakInvCtx.of_left hRF (hRF'.comp hJ.round')
    (K' := .comp (.comp J₂' (F.rounded (F'.app (F.app b)) H.k)) J)
    (hJ.round.comp (hRF₂.comp hJ₂.round')) ((hJs.left hJ.round').trans hJ.left) ?_,
    (presEqv_rounded hF.round' hFa hFb).comp hRF' hJe⟩
  exact ((hJ.right.right (.ofIsRoundIn hFa hFb) hRF').left (hRF₂.comp hJ₂.round')).trans
    ((hJ₂s.left hJ₂.round').trans hJ₂.left)

end Atoms.Diagrammatic
