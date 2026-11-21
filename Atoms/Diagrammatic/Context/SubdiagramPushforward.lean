import Atoms.Diagrammatic.Context.NaturalClosure

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem equivalent_of_hasBdry {k : ℕ} {h x y : RoundPastingDiagram X} (hh : h ∈ equivalences X)
    (ht : HasBdry false (k + 1) h.toPastingDiagram x.toPastingDiagram y.toPastingDiagram) :
    Equivalent x y := by
  have hx : x.dim = k + 1 := ht.dim_a
  exact EquivalenceData.equivalent ⟨hx.trans ht.dim_b.symm, h, hh,
    by rw [ht.dim_h, hx], by rw [hx]; exact ht.side, by rw [hx]; exact ht.other⟩

structure CtxSubdiagram (H : RoundHom X) where
  side : Bool
  innerCod : RoundHom X
  inner : CtxExpr X
  isRoundCtxOn_inner : IsRoundCtxOn H innerCod inner
  factor : RoundPastingDiagram X
  dim_factor : factor.dim = innerCod.k + 1
  boundary_factor : (factor.boundary innerCod.k (!side)).Equiv (innerCod.side side)
  sub : PastingDiagram X
  occ : Within sub factor.toPastingDiagram
  rewritable : factor.toPastingDiagram.shape.ogp.IsRewritableSubmolecule occ.image ⊤

namespace CtxSubdiagram

variable {H : RoundHom X} (s : CtxSubdiagram H)

def ctx : CtxExpr X :=
  .comp (CtxExpr.paste s.side s.factor.toPastingDiagram s.innerCod.k) s.inner

def cod : PdHom X :=
  s.innerCod.setSide s.side (s.factor.boundary s.innerCod.k s.side)

theorem isRoundCtxOn_ctx : IsRoundCtxOn H s.cod s.ctx :=
  s.isRoundCtxOn_inner.comp
    (isRoundCtxOn_paste s.side s.innerCod.toPdHom s.factor.isRound s.dim_factor
      s.boundary_factor.symm)

theorem isRound_sub : s.sub.IsRound :=
  s.occ.round_image_iff.1 s.rewritable.isRound

noncomputable def substCtx (z' : RoundPastingDiagram X) (hz : Parallel ⟨s.sub, s.isRound_sub⟩ z') :
    CtxExpr X :=
  .comp (CtxExpr.paste s.side (s.factor.toPastingDiagram.substitute s.occ s.rewritable z' hz)
    s.innerCod.k) s.inner

noncomputable def pfw (y e : PastingDiagram X) : CtxTriple X :=
  ⟨H, s.cod, s.ctx, .comp (CtxExpr.paste s.side y s.innerCod.k) s.inner,
    fun a => (ctxPfw s.side s.innerCod s.factor.toPastingDiagram y e).ϑ (s.inner.app a)⟩

def substituteData {h z' : RoundPastingDiagram X}
    (ht : HasBdry false (s.innerCod.k + 1) h.toPastingDiagram s.sub z'.toPastingDiagram) :
    SubstituteData s.factor z' :=
  ⟨s.sub, s.occ, s.rewritable, h, by rw [ht.dim_h, s.dim_factor],
    by rw [s.dim_factor]; exact ht.side, by rw [s.dim_factor]; exact ht.other⟩

theorem pfwSpec_substituteData {h z' : RoundPastingDiagram X} (hh : h ∈ equivalences X)
    (ht : HasBdry false (s.innerCod.k + 1) h.toPastingDiagram s.sub z'.toPastingDiagram)
    (hz : Parallel ⟨s.sub, s.isRound_sub⟩ z') :
    PfwSpec s.innerCod.k s.factor.toPastingDiagram
      (s.factor.toPastingDiagram.substitute s.occ s.rewritable z' hz)
      (s.substituteData ht).pasteData.pasting := by
  set D := s.substituteData ht
  have hd : D.pasteData.pasting.dim = s.innerCod.k + 1 + 1 := by
    rw [D.pasteData.dim_pasting, s.dim_factor]
  have hT := D.equiv_target_substitute hz
  have hS := D.equiv_source
  rw [PastingDiagram.boundary_congr _ s.dim_factor] at hT hS
  exact ⟨D.pasteData.isRound_pasting,
    (pasteAt_mem_equivalences_iff D.pasteData hh).2 (unit_mem_equivalences s.factor),
    ⟨hd, s.dim_factor, (dim_eq_of_equiv hT).symm.trans
      (dim_boundary D.pasteData.pasting (by rw [hd]; omega) true), hS, hT⟩⟩

end CtxSubdiagram

def ctxPfwTriples (X : DiagSet.{u}) : Set (CtxTriple X) :=
  {τ | ∃ (H : RoundHom X) (s : CtxSubdiagram H) (z' : RoundPastingDiagram X)
    (hz : Parallel ⟨s.sub, s.isRound_sub⟩ z') (y e : PastingDiagram X),
    Equivalent ⟨s.sub, s.isRound_sub⟩ z' ∧
      y.Equiv (s.factor.toPastingDiagram.substitute s.occ s.rewritable z' hz) ∧
      PfwSpec s.innerCod.k s.factor.toPastingDiagram y e ∧ τ = s.pfw y e}

theorem CtxSubdiagram.pfw_mem_ctxPfwTriples {H : RoundHom X} (s : CtxSubdiagram H)
    {h z' : RoundPastingDiagram X} (hh : h ∈ equivalences X)
    (ht : HasBdry false (s.innerCod.k + 1) h.toPastingDiagram s.sub z'.toPastingDiagram)
    (hz : Parallel ⟨s.sub, s.isRound_sub⟩ z') :
    s.pfw (s.factor.toPastingDiagram.substitute s.occ s.rewritable z' hz)
      (s.substituteData ht).pasteData.pasting ∈ ctxPfwTriples X :=
  ⟨H, s, z', hz, _, _,
    equivalent_of_hasBdry hh ht,
    .refl _, s.pfwSpec_substituteData hh ht hz, rfl⟩

theorem exists_mem_ctxPfwTriples_of_mem_pfwTriples {τ : CtxTriple X} (hτ : τ ∈ pfwTriples X) :
    ∃ σ ∈ ctxPfwTriples X, σ.ϑ = τ.ϑ ∧ σ.Realizes τ.dom τ.cod τ.F.app τ.G.app := by
  obtain ⟨α, H, x, x', h, hs, hx, rfl⟩ := hτ
  have hrx := hs.isRound_x
  have hι : x.shape.ogp.IsRewritableSubmolecule (Within.refl x).image ⊤ :=
    (Within.refl x).isRewritableSubmolecule_image_iff.2
      ⟨Within.isSubmoleculeOf_image_refl x, hrx, rfl⟩
  let s : CtxSubdiagram H :=
    ⟨α, H, .id, isRoundCtxOn_id, ⟨x, hrx⟩, hs.hasType.dim_a, hx, x, Within.refl x, hι⟩
  have he : Equivalent ⟨x, hrx⟩ ⟨x', hs.isRound_x'⟩ :=
    equivalent_of_hasBdry (h := ⟨h, hs.isRound_h⟩) hs.mem hs.hasType
  have hz : Parallel ⟨s.sub, s.isRound_sub⟩ ⟨x', hs.isRound_x'⟩ :=
    (Equivalent.spec hs.hasType.dim_a he).1
  exact ⟨s.pfw x' h, ⟨H, s, _, hz, x', h, he,
    (equiv_substitute_of_image_eq_univ (Within.refl x) hι _ hz (Within.image_refl x)).symm,
    hs, rfl⟩, rfl, ⟨.refl _, .refl _, fun _ _ => .refl _, fun _ _ => .refl _⟩⟩

theorem cylTriples_union_ctxPfwTriples_subset_natEqv :
    cylTriples X ∪ ctxPfwTriples X ⊆ natEqv X := by
  rintro τ (hτ | ⟨H, s, z', hz, y, e, -, -, hs, rfl⟩)
  · exact cylTriples_subset_natEqv hτ
  have hσ : ctxPfw s.side s.innerCod s.factor.toPastingDiagram y e ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨s.side, s.innerCod, _, _, _, hs, s.boundary_factor, rfl⟩
  rw [← closure_natEqv]
  exact CtxTriple.Closure.right (.base hσ) s.isRoundCtxOn_inner

theorem CtxSubdiagram.ctxEquivalent_substCtx {H : RoundHom X} (s : CtxSubdiagram H)
    {h z' : RoundPastingDiagram X} (hh : h ∈ equivalences X)
    (ht : HasBdry false (s.innerCod.k + 1) h.toPastingDiagram s.sub z'.toPastingDiagram)
    (hz : Parallel ⟨s.sub, s.isRound_sub⟩ z') :
    CtxEquivalent H s.cod s.ctx (s.substCtx z' hz) :=
  ⟨_, cylTriples_union_ctxPfwTriples_subset_natEqv (Or.inr (s.pfw_mem_ctxPfwTriples hh ht hz))⟩

theorem NatSim.paste_typed (α : Bool) (D C E : RoundHom X) {K : CtxExpr X}
    (hK : K.Typed Set.univ True D C) {x x' e : PastingDiagram X} (hs : PfwSpec C.k x x' e)
    (hx : (x.boundary C.k (!α)).Equiv (C.side α))
    (hE : (C.setSide α (x.boundary C.k α)).Equiv E.toPdHom) :
    NatSim X D E (fun c => (CtxExpr.paste α x C.k).app (K.app c))
      (fun c => (CtxExpr.paste α x' C.k).app (K.app c)) := by
  obtain ⟨⟨kE, vE, wE⟩, hvE, hwE, hdv, hpE⟩ := E
  obtain rfl : C.k = kE := hE.k_eq
  have hdw : wE.dim = C.k := hpE.1.symm.trans hdv
  have hT := (isRoundCtxOn_comp_paste α hK hs.isRound_x hs.hasType.dim_a hx.symm).congr
    (.refl _) hE
  have hT' := (isRoundCtxOn_comp_paste α hK hs.isRound_x' hs.hasType.dim_b
    ((hs.equiv_boundary_x (!α)).symm.trans hx).symm).congr (.refl _)
    (((PdHom.Equiv.refl C.toPdHom).setSide α (hs.equiv_boundary_x α).symm).trans hE)
  have hσ : ctxPfw α C x x' e ∈ natEqv X :=
    pfwTriples_subset_natEqv ⟨α, C, x, x', e, hs, hx, rfl⟩
  have tx : HasBdry false C.k x (x.boundary C.k false) (x.boundary C.k true) :=
    ⟨hs.hasType.dim_a, dim_boundary x (by rw [hs.hasType.dim_a]; omega) false,
      dim_boundary x (by rw [hs.hasType.dim_a]; omega) true, .refl _, .refl _⟩
  have tx' : HasBdry false C.k x' (x'.boundary C.k false) (x'.boundary C.k true) :=
    ⟨hs.hasType.dim_b, dim_boundary x' (by rw [hs.hasType.dim_b]; omega) false,
      dim_boundary x' (by rw [hs.hasType.dim_b]; omega) true, .refl _, .refl _⟩
  dsimp only at hdv hT hT' ⊢
  cases α
  · simp only [Bool.not_false, PdHom.side_false] at hx
    have hw : C.w.Equiv wE := hE.equiv_w
    have hu := hasType_unit hdw
    have hR : IsRoundCtxOn D C (.comp (CtxExpr.paste true wE.unit C.k) K) :=
      (isRoundCtxOn_comp_paste true hK (isRound_unit hwE) (by rw [dim_unit, hdw])
        (hw.trans (boundary_unit hdw false).symm)).congr (.refl _)
        ⟨rfl, .refl _, (boundary_unit hdw true).trans hw.symm⟩
    have S₁ : NatSim X D ⟨C.k, vE, wE⟩ (fun c => (CtxExpr.paste false x C.k).app (K.app c))
        (fun c => ((CtxExpr.paste false x C.k).app (K.app c)).pasteOr wE.unit C.k) :=
      NatSim.symm (by
        have r := CtxTriple.Sim.unit true cylTriples_subset_natEqv D
          ⟨⟨C.k, vE, wE⟩, hvE, hwE, hdv, hpE⟩ hT
        simp only [cond_true, PdHom.side_true] at r
        exact r)
    have S₃ : NatSim X D ⟨C.k, vE, wE⟩
        (fun c => ((CtxExpr.paste false x' C.k).app (K.app c)).pasteOr wE.unit C.k)
        (fun c => (CtxExpr.paste false x' C.k).app (K.app c)) :=
      by
        have r := CtxTriple.Sim.unit true cylTriples_subset_natEqv D
          ⟨⟨C.k, vE, wE⟩, hvE, hwE, hdv, hpE⟩ hT'
        simp only [cond_true, PdHom.side_true] at r
        exact r
    have S₂ := ((CtxTriple.Sim.of_mem (A := natEqv X) hσ).right D hR).congr (.refl _) hE
    refine (S₁.trans_of_equiv S₂ (fun c hc => ?_)).trans_of_equiv S₃ (fun c hc => ?_)
    · have hy := hK.mapsInto c hc
      exact (CtxExpr.paste_app_pasteOr true (u := wE.unit)
        ((hT.typed.mapsInto c hc).pastable_hasType hu (.refl _))).symm.trans
        (CtxExpr.pasteRight_app_pasteLeft (tx.pastable_inHom hy hx) (hy.pastable_hasType hu hw))
    · have hy := hK.mapsInto c hc
      exact (CtxExpr.pasteRight_app_pasteLeft
        (tx'.pastable_inHom hy ((hs.equiv_boundary_x true).symm.trans hx))
        (hy.pastable_hasType hu hw)).symm.trans
        (CtxExpr.paste_app_pasteOr true (u := wE.unit)
          ((hT'.typed.mapsInto c hc).pastable_hasType hu (.refl _)))
  · simp only [Bool.not_true, PdHom.side_true] at hx
    have hv : C.v.Equiv vE := hE.equiv_v
    have hu := hasType_unit hdv
    have hR : IsRoundCtxOn D C (.comp (CtxExpr.paste false vE.unit C.k) K) :=
      (isRoundCtxOn_comp_paste false hK (isRound_unit hvE) (by rw [dim_unit, hdv])
        (hv.trans (boundary_unit hdv true).symm)).congr (.refl _)
        ⟨rfl, (boundary_unit hdv false).trans hv.symm, .refl _⟩
    have S₁ : NatSim X D ⟨C.k, vE, wE⟩ (fun c => (CtxExpr.paste true x C.k).app (K.app c))
        (fun c => vE.unit.pasteOr ((CtxExpr.paste true x C.k).app (K.app c)) C.k) :=
      by
        have r := CtxTriple.Sim.unit false cylTriples_subset_natEqv D
          ⟨⟨C.k, vE, wE⟩, hvE, hwE, hdv, hpE⟩ hT
        simp only [cond_false, PdHom.side_false] at r
        exact r
    have S₃ : NatSim X D ⟨C.k, vE, wE⟩
        (fun c => vE.unit.pasteOr ((CtxExpr.paste true x' C.k).app (K.app c)) C.k)
        (fun c => (CtxExpr.paste true x' C.k).app (K.app c)) :=
      NatSim.symm (by
        have r := CtxTriple.Sim.unit false cylTriples_subset_natEqv D
          ⟨⟨C.k, vE, wE⟩, hvE, hwE, hdv, hpE⟩ hT'
        simp only [cond_false, PdHom.side_false] at r
        exact r)
    have S₂ := ((CtxTriple.Sim.of_mem (A := natEqv X) hσ).right D hR).congr (.refl _) hE
    refine (S₁.trans_of_equiv S₂ (fun c hc => ?_)).trans_of_equiv S₃ (fun c hc => ?_)
    · have hy := hK.mapsInto c hc
      exact (CtxExpr.paste_app_pasteOr false (u := vE.unit)
        (hu.pastable_inHom (hT.typed.mapsInto c hc) (.refl _))).symm.trans
        (CtxExpr.pasteRight_app_pasteLeft (hu.pastable_inHom hy hv.symm)
          (hy.pastable_hasType tx hx.symm)).symm
    · have hy := hK.mapsInto c hc
      exact (CtxExpr.pasteRight_app_pasteLeft (hu.pastable_inHom hy hv.symm)
        (hy.pastable_hasType tx' ((hs.equiv_boundary_x false).symm.trans hx).symm)).trans
        (CtxExpr.paste_app_pasteOr false (u := vE.unit)
          (hu.pastable_inHom (hT'.typed.mapsInto c hc) (.refl _)))

theorem mem_natEqv_of_pfwSpec {τ : CtxTriple X} (hτ : τ ∈ natEqv X)
    {ϑ' : PastingDiagram X → PastingDiagram X}
    (hϑ' : ∀ a, IsRoundIn τ.dom a → ∃ e, PfwSpec (τ.dom.k + 1) (ϑ' a) (τ.ϑ a) e) :
    (⟨τ.dom, τ.cod, τ.F, τ.G, ϑ'⟩ : CtxTriple X) ∈ natEqv X := by
  obtain ⟨D, ⟨k', v', w'⟩, F, G, ϑ⟩ := τ
  rw [← natOp_natEqv] at hτ ⊢
  obtain ⟨hv, N⟩ := hτ
  obtain rfl : k' = D.k := hv.ctxF.typed.k_eq
  have hcomp : ∀ a, IsRoundIn D a → ∃ e, PfwSpec (D.k + 1) (ϑ' a) (ϑ a) e ∧
      ∃ hr : (ϑ' a).IsRound, (⟨ϑ' a, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
        HasBdry false (D.k + 1) (ϑ' a) (F.app a) (G.app a) := fun a ha => by
    obtain ⟨e, hs⟩ := hϑ' a ha
    obtain ⟨hr, hm, ht⟩ := hv.comp a ha
    have he : Equivalent ⟨ϑ' a, hs.isRound_x⟩ ⟨ϑ a, hr⟩ :=
      equivalent_of_hasBdry (h := ⟨e, hs.isRound_h⟩) hs.mem hs.hasType
    exact ⟨e, hs, hs.isRound_x, (mem_equivalences_iff_of_equivalent he).2 hm,
      ⟨hs.hasType.dim_a, ht.dim_a, ht.dim_b, (hs.equiv_boundary_x false).trans ht.side,
        (hs.equiv_boundary_x true).trans ht.other⟩⟩
  refine ⟨⟨hv.ctxF, hv.ctxG, fun a ha => by
    obtain ⟨-, -, h⟩ := hcomp a ha
    exact h⟩, fun a b ha hb => ?_⟩
  change IsRoundIn D a at ha
  change IsRoundIn D b at hb
  obtain ⟨ea, hsa, -, -, ta⟩ := hcomp a ha
  obtain ⟨eb, hsb, -, -, tb⟩ := hcomp b hb
  have hFa := hv.ctxF.isRoundIn ha
  have hFb := hv.ctxF.isRoundIn hb
  have hGa := hv.ctxG.isRoundIn ha
  have hGb := hv.ctxG.isRoundIn hb
  have S₁ := NatSim.paste_typed true (RoundHom.ofIsRoundIn ha hb) (RoundHom.ofIsRoundIn hFa hFb)
    (RoundHom.ofIsRoundIn hFa hGb) (hv.ctxF.typed.promote_of_inHom trivial ha.inHom hb.inHom) hsb
    tb.side ⟨rfl, .refl _, tb.other⟩
  have S₃ := NatSim.paste_typed false (RoundHom.ofIsRoundIn ha hb)
    (RoundHom.ofIsRoundIn hGa hGb) (RoundHom.ofIsRoundIn hFa hGb)
    (hv.ctxG.typed.promote_of_inHom trivial ha.inHom hb.inHom) hsa ta.other ⟨rfl, ta.side, .refl _⟩
  obtain ⟨σ, hσ, hr⟩ := N a b ha hb
  have S₂ : NatSim X ⟨D.k + 1, a, b⟩ ⟨D.k + 1, F.app a, G.app b⟩
      (fun c => (CtxExpr.paste true (ϑ b) (D.k + 1)).app (F.app c))
      (fun c => (CtxExpr.paste false (ϑ a) (D.k + 1)).app (G.app c)) := ⟨σ, .base hσ, hr⟩
  obtain ⟨σ', hσ', hr'⟩ := CtxTriple.Sim.trans S₁ (CtxTriple.Sim.trans S₂ (NatSim.symm S₃))
  refine ⟨σ', ?_, hr'⟩
  rw [← closure_natEqv]
  exact hσ'

end Atoms.Diagrammatic
