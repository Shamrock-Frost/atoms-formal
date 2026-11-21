import Atoms.Diagrammatic.Context.RoundBicategoryCoherence
import Atoms.Diagrammatic.Context.TrimSideInverse

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure UnitCrossing (X : DiagSet.{u}) where
  a : RoundBicat X 0
  b : RoundBicat X 0
  γ : Bool
  β : Bool
  g : RoundPastingDiagram X
  dim_g : g.dim = 2
  unit_g : (g.boundary 1 β).Equiv (cond γ b.diag.toPastingDiagram a.diag.toPastingDiagram).unit

namespace UnitCrossing

open RoundBicat

variable (c : UnitCrossing X)

open Classical in
noncomputable def unitorFam (t : PastingDiagram X) : PastingDiagram X :=
  if c.β = c.γ then (unitorSpec c.γ c.a c.b).fam t
  else if h : ∃ e', IsWeakInverse ((unitorSpec c.γ c.a c.b).fam t) e' then h.choose else t

noncomputable def unitorTriple {Q : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q) : CtxTriple X :=
  ⟨hQ.roundHom, hQ.roundHom, cond c.β (unitCtx c.γ c.a c.b) .id,
    cond c.β .id (unitCtx c.γ c.a c.b), c.unitorFam⟩

private theorem unitorTriple_eq {Q : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hβ : c.β = c.γ) :
    c.unitorTriple hQ = ⟨hQ.roundHom, hQ.roundHom, cond c.γ (unitCtx c.γ c.a c.b) .id,
      cond c.γ .id (unitCtx c.γ c.a c.b), (unitorSpec c.γ c.a c.b).fam⟩ := by
  unfold unitorTriple
  rw [hβ]
  congr 1
  funext t
  exact if_pos hβ

theorem unitorTriple_mem_natEqv {Q : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q) :
    c.unitorTriple hQ ∈ natEqv X := by
  have h := isCylTriple_unitorSpec c.γ hQ
  by_cases hβ : c.β = c.γ
  · rw [c.unitorTriple_eq hQ hβ]
    exact cylTriples_subset_natEqv ⟨_, h⟩
  · have hinv : ∀ t, IsRoundIn hQ.roundHom t →
        IsWeakInverse ((unitorSpec c.γ c.a c.b).fam t) (c.unitorFam t) := by
      intro t ht
      obtain ⟨_, he, -⟩ := h.valid.comp t ht
      have hex : ∃ e', IsWeakInverse ((unitorSpec c.γ c.a c.b).fam t) e' :=
        let ⟨_, h'⟩ := exists_isWeakInverse he; ⟨_, h'⟩
      rw [unitorFam, if_neg hβ, dif_pos hex]
      exact hex.choose_spec
    have hm := closure_natEqv.subset
      (CtxTriple.Closure.inv (.base (cylTriples_subset_natEqv ⟨_, h⟩)) hinv)
    have hβ' : c.β = !c.γ := by
      cases hb : c.β <;> cases hg : c.γ <;> simp only [hb, hg, not_true_eq_false] at hβ ⊢ <;> rfl
    unfold unitorTriple
    rw [hβ']
    revert hm
    cases c.γ <;> exact id

private theorem exists_mem_natEqv_next {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    ∃ ϑ : PastingDiagram X → PastingDiagram X,
      (⟨RoundHom.ofIsRoundIn hQ hQ', ⟨(c.unitorTriple hQ).dom.k + 1, (c.unitorTriple hQ).F.app Q,
        (c.unitorTriple hQ).G.app Q'⟩, (c.unitorTriple hQ).nextF Q', (c.unitorTriple hQ).nextG Q,
        ϑ⟩ : CtxTriple X) ∈ natEqv X := by
  have hm := c.unitorTriple_mem_natEqv hQ
  have hv := valid_of_mem_natEqv hm
  rw [← natOp_natEqv] at hm
  obtain ⟨σ, hσ, hr⟩ := hm.2 Q Q' hQ hQ'
  exact ⟨σ.ϑ, mem_natEqv_of_realizes hσ hr (hv.isRoundCtxOn_nextF hQ hQ')
    (hv.isRoundCtxOn_nextG hQ hQ')⟩

open Classical in
noncomputable def higherFam {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    PastingDiagram X → PastingDiagram X :=
  if c.β = c.γ then (unitorSpec c.γ c.a c.b).fam else (c.exists_mem_natEqv_next hQ hQ').choose

noncomputable def higherTriple {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    CtxTriple X :=
  ⟨RoundHom.ofIsRoundIn hQ hQ', ⟨(c.unitorTriple hQ).dom.k + 1, (c.unitorTriple hQ).F.app Q,
    (c.unitorTriple hQ).G.app Q'⟩, (c.unitorTriple hQ).nextF Q', (c.unitorTriple hQ).nextG Q,
    c.higherFam hQ hQ'⟩

theorem higherTriple_mem_natEqv {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    c.higherTriple hQ hQ' ∈ natEqv X := by
  unfold higherTriple
  by_cases hβ : c.β = c.γ
  · have h := (isCylTriple_unitorSpec c.γ hQ).next hQ hQ'
    rw [show c.higherFam hQ hQ' = _ from if_pos hβ, c.unitorTriple_eq hQ hβ]
    exact cylTriples_subset_natEqv ⟨_, h⟩
  · rw [show c.higherFam hQ hQ' = _ from if_neg hβ]
    exact (c.exists_mem_natEqv_next hQ hQ').choose_spec

private theorem isRoundIn_cond (β : Bool) {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ (cond β Q Q') := by
  cases β <;> assumption

theorem pastable_unit {R : PastingDiagram X}
    (hR : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ R) :
    (cond c.γ R (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit).Pastable
      (cond c.γ (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit R) 0 :=
  Pastable.of_side c.γ ((hR.inHom.side c.γ).trans
      (boundary_unit (dim_cond_diag c.γ c.a c.b) (!c.γ)).symm)
    (by rw [hR.dim_eq]; omega) (by rw [dim_unit, dim_cond_diag]; omega)

noncomputable def unitPath {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    PastingDiagram X :=
  (cond c.γ (cond c.β Q Q')
      (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit).paste
    (cond c.γ (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit (cond c.β Q Q'))
    0 (c.pastable_unit (c.isRoundIn_cond c.β hQ hQ'))

noncomputable def unitOcc {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    Within (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit
      (c.unitPath hQ hQ') :=
  Within.pasteIn c.γ (c.pastable_unit (c.isRoundIn_cond c.β hQ hQ'))

theorem isRewritableSubmolecule_image_unitOcc {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    (c.unitPath hQ hQ').shape.ogp.IsRewritableSubmolecule (c.unitOcc hQ hQ').image ⊤ :=
  isRewritableSubmolecule_image_pasteIn (c := ⟨_, (c.isRoundIn_cond c.β hQ hQ').isRound⟩)
    (h := ⟨_, isRound_unit (isRound_cond_diag c.γ c.a c.b)⟩) c.γ _
    (by change (cond c.β Q Q').dim = (cond c.γ c.b.diag.toPastingDiagram
          c.a.diag.toPastingDiagram).unit.dim
        rw [dim_unit, dim_cond_diag, (c.isRoundIn_cond c.β hQ hQ').dim_eq])

private theorem boundary_g_not_not :
    (c.g.boundary 1 (!!c.β)).Equiv
      (cond c.γ c.b.diag.toPastingDiagram c.a.diag.toPastingDiagram).unit := by
  rw [Bool.not_not]
  exact c.unit_g

noncomputable def sideCtx {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    CtxExpr X :=
  .side (!c.β) c.g.toPastingDiagram 1 (c.unitOcc hQ hQ')
    (c.isRewritableSubmolecule_image_unitOcc hQ hQ').isSubmoleculeOf c.boundary_g_not_not

noncomputable def sideHom {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    PdHom X :=
  (c.higherTriple hQ hQ').cod.setSide (!c.β)
    ((sidePaste (!c.β) c.g.toPastingDiagram (c.higherTriple hQ hQ').cod.k (c.unitOcc hQ hQ')
      (c.isRewritableSubmolecule_image_unitOcc hQ hQ').isSubmoleculeOf c.boundary_g_not_not
      (c.unitPath hQ hQ')).boundary (c.higherTriple hQ hQ').cod.k (!c.β))

private theorem side_cod_higherTriple {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    (c.higherTriple hQ hQ').cod.side (!c.β) = (unitCtx c.γ c.a c.b).app (cond c.β Q Q') := by
  unfold higherTriple unitorTriple
  cases c.β <;> rfl

theorem unitPath_equiv_side {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    (c.unitPath hQ hQ').Equiv ((c.higherTriple hQ hQ').cod.side (!c.β)) := by
  rw [c.side_cod_higherTriple hQ hQ']
  exact (CtxExpr.sidePaste_equiv_paste c.γ (Within.image_refl _)
    (boundary_unit (dim_cond_diag c.γ c.a c.b) (!c.γ))
    ((c.isRoundIn_cond c.β hQ hQ').inHom.side c.γ) _).symm

private theorem typed_sideCtx {p : Prop} {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    (c.sideCtx hQ hQ').Typed Set.univ p (c.higherTriple hQ hQ').cod (c.sideHom hQ hQ') := by
  have hk : (c.higherTriple hQ hQ').cod.k = 1 := rfl
  have T := CtxExpr.Typed.side (A := Set.univ) (p := p) (H := (c.higherTriple hQ hQ').cod)
    (H' := c.sideHom hQ hQ') (!c.β) c.g (Set.mem_univ _) (by rw [c.dim_g, hk])
    (c.unitOcc hQ hQ') (c.isRewritableSubmolecule_image_unitOcc hQ hQ') ?_ ?_ ?_
  · exact T
  · exact c.unitPath_equiv_side hQ hQ'
  · exact .refl _

theorem isRoundCtxOn_sideCtx {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    IsRoundCtxOn (c.higherTriple hQ hQ').cod (c.sideHom hQ hQ') (c.sideCtx hQ hQ') :=
  ⟨c.typed_sideCtx hQ hQ', isRoundCtx_of_trim (c.typed_sideCtx (p := False) hQ hQ')⟩

noncomputable def triple {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    CtxTriple X :=
  ⟨(c.higherTriple hQ hQ').dom, c.sideHom hQ hQ',
    .comp (c.sideCtx hQ hQ') (c.higherTriple hQ hQ').F,
    .comp (c.sideCtx hQ hQ') (c.higherTriple hQ hQ').G,
    fun t => ((c.sideCtx hQ hQ').app ((c.higherTriple hQ hQ').ϑ t)).pasteOr
      ((c.sideCtx hQ hQ').app ((c.higherTriple hQ hQ').G.app t)).unit
      ((c.higherTriple hQ hQ').dom.k + 1)⟩

theorem triple_mem_natEqv {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    c.triple hQ hQ' ∈ natEqv X :=
  closure_natEqv.subset (CtxTriple.Closure.left (.base (c.higherTriple_mem_natEqv hQ hQ'))
    (c.isRoundCtxOn_sideCtx hQ hQ'))

theorem mem_equivalences_triple {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q')
    {t : PastingDiagram X} (ht : IsRoundIn ⟨1, Q, Q'⟩ t) :
    ∃ hr : ((c.triple hQ hQ').ϑ t).IsRound,
      (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
        HasBdry false 2 ((c.triple hQ hQ').ϑ t) ((c.triple hQ hQ').F.app t)
          ((c.triple hQ hQ').G.app t) :=
  (valid_of_mem_natEqv (c.triple_mem_natEqv hQ hQ')).comp t ht

theorem equivalent_square {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q')
    {t t' α : PastingDiagram X} (ht : IsRoundIn ⟨1, Q, Q'⟩ t) (ht' : IsRoundIn ⟨1, Q, Q'⟩ t')
    (hα : IsRoundIn ⟨2, t, t'⟩ α)
    (h₁ : (((c.triple hQ hQ').nextF t').app α).IsRound)
    (h₂ : (((c.triple hQ hQ').nextG t).app α).IsRound) :
    Equivalent ⟨_, h₁⟩ ⟨_, h₂⟩ := by
  have hm := c.triple_mem_natEqv hQ hQ'
  rw [← natOp_natEqv] at hm
  obtain ⟨σ, hσ, hr⟩ := hm.2 t t' ht ht'
  exact NatSim.equivalent_app ⟨σ, .base hσ, hr⟩ hα h₁ h₂

theorem exists_inv_mem_natEqv {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    ∃ ϑ' : PastingDiagram X → PastingDiagram X,
      (∀ t, IsRoundIn ⟨1, Q, Q'⟩ t → IsWeakInverse ((c.triple hQ hQ').ϑ t) (ϑ' t)) ∧
      (⟨(c.triple hQ hQ').dom, (c.triple hQ hQ').cod, (c.triple hQ hQ').G,
        (c.triple hQ hQ').F, ϑ'⟩ : CtxTriple X) ∈ natEqv X := by
  have hm := c.triple_mem_natEqv hQ hQ'
  have hv := valid_of_mem_natEqv hm
  have hex : ∀ t, IsRoundIn ⟨1, Q, Q'⟩ t → ∃ e', IsWeakInverse ((c.triple hQ hQ').ϑ t) e' :=
    fun t ht => by
      obtain ⟨_, he, -⟩ := hv.comp t ht
      obtain ⟨e', he'⟩ := exists_isWeakInverse he
      exact ⟨_, he'⟩
  choose! ϑ' hϑ' using hex
  exact ⟨ϑ', hϑ', closure_natEqv.subset (CtxTriple.Closure.inv (.base hm) hϑ')⟩

private theorem dim_unitPath {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    (c.unitPath hQ hQ').dim = 1 := by
  unfold unitPath
  rw [dim_paste_cond, dim_unit, dim_cond_diag, (c.isRoundIn_cond c.β hQ hQ').dim_eq, max_self]

noncomputable def whiskered {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    PastingDiagram X :=
  (c.sideCtx hQ hQ').app (c.unitPath hQ hQ')

theorem exists_equiv_sideCtx_app {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q')
    {y : PastingDiagram X} (hy : InHom (c.higherTriple hQ hQ').cod y) (hdy : 1 < y.dim) :
    ∃ hp : (cond (!c.β) y (c.whiskered hQ hQ')).Pastable
        (cond (!c.β) (c.whiskered hQ hQ') y) 1,
      ((c.sideCtx hQ hQ').app y).Equiv
        ((cond (!c.β) y (c.whiskered hQ hQ')).paste (cond (!c.β) (c.whiskered hQ hQ') y) 1 hp) :=
  sidePaste_equiv_paste_sidePaste c.dim_g
    (c.dim_unitPath hQ hQ')
    ((hy.side (!c.β)).trans (c.unitPath_equiv_side hQ hQ').symm) hdy

theorem exists_equiv_F_app {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q')
    {t : PastingDiagram X} (ht : IsRoundIn ⟨1, Q, Q'⟩ t) :
    ∃ (hp₁ : ((c.unitorTriple hQ).F.app t).Pastable (c.unitorFam Q') 1)
      (hp₂ : (cond (!c.β) (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁)
          (c.whiskered hQ hQ')).Pastable
        (cond (!c.β) (c.whiskered hQ hQ')
          (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁)) 1),
      ((c.triple hQ hQ').F.app t).Equiv
        ((cond (!c.β) (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁)
          (c.whiskered hQ hQ')).paste
          (cond (!c.β) (c.whiskered hQ hQ')
            (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁)) 1 hp₂) := by
  have hv := valid_of_mem_natEqv (c.unitorTriple_mem_natEqv hQ)
  have hv₁ := valid_of_mem_natEqv (c.higherTriple_mem_natEqv hQ hQ')
  have hFt : InHom ⟨1, (c.unitorTriple hQ).F.app Q, (c.unitorTriple hQ).F.app Q'⟩
      ((c.unitorTriple hQ).F.app t) :=
    (hv.ctxF.typed.promote_of_inHom trivial hQ.inHom hQ'.inHom).mapsInto t ht.inHom
  obtain ⟨-, -, hb⟩ := hv.comp Q' hQ'
  have hp₁ : ((c.unitorTriple hQ).F.app t).Pastable (c.unitorFam Q') 1 :=
    InHom.pastable_hasType hFt hb (.refl _)
  have e : ((CtxExpr.paste true (c.unitorFam Q') 1).app ((c.unitorTriple hQ).F.app t)).Equiv
      (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁) :=
    CtxExpr.paste_app true hp₁
  have hy := (hv₁.ctxF.typed.mapsInto t ht.inHom).of_equiv e
  have hdy : 1 < (((c.unitorTriple hQ).F.app t).paste (c.unitorFam Q') 1 hp₁).dim := by
    have hd : ((c.higherTriple hQ hQ').F.app t).dim = 1 + 1 :=
      (hv₁.ctxF.typed.ctxLaws.dim_eq t ht.inHom).trans ht.dim_eq
    rw [← dim_eq_of_equiv e]
    exact hd ▸ Nat.lt_succ_self 1
  obtain ⟨hp₂, e₂⟩ := c.exists_equiv_sideCtx_app hQ hQ' hy hdy
  exact ⟨hp₁, hp₂, (CtxExpr.app_equiv (c.sideCtx hQ hQ') e).trans e₂⟩

theorem exists_equiv_G_app {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q')
    {t : PastingDiagram X} (ht : IsRoundIn ⟨1, Q, Q'⟩ t) :
    ∃ (hp₁ : (c.unitorFam Q).Pastable ((c.unitorTriple hQ).G.app t) 1)
      (hp₂ : (cond (!c.β) ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁)
          (c.whiskered hQ hQ')).Pastable
        (cond (!c.β) (c.whiskered hQ hQ')
          ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁)) 1),
      ((c.triple hQ hQ').G.app t).Equiv
        ((cond (!c.β) ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁)
          (c.whiskered hQ hQ')).paste
          (cond (!c.β) (c.whiskered hQ hQ')
            ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁)) 1 hp₂) := by
  have hv := valid_of_mem_natEqv (c.unitorTriple_mem_natEqv hQ)
  have hv₁ := valid_of_mem_natEqv (c.higherTriple_mem_natEqv hQ hQ')
  have hGt : InHom ⟨1, (c.unitorTriple hQ).G.app Q, (c.unitorTriple hQ).G.app Q'⟩
      ((c.unitorTriple hQ).G.app t) :=
    (hv.ctxG.typed.promote_of_inHom trivial hQ.inHom hQ'.inHom).mapsInto t ht.inHom
  obtain ⟨-, -, hb⟩ := hv.comp Q hQ
  have hp₁ : (c.unitorFam Q).Pastable ((c.unitorTriple hQ).G.app t) 1 :=
    HasBdry.pastable_inHom hGt hb (.refl _)
  have e : ((CtxExpr.paste false (c.unitorFam Q) 1).app ((c.unitorTriple hQ).G.app t)).Equiv
      ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁) :=
    CtxExpr.paste_app false hp₁
  have hy := (hv₁.ctxG.typed.mapsInto t ht.inHom).of_equiv e
  have hdy : 1 < ((c.unitorFam Q).paste ((c.unitorTriple hQ).G.app t) 1 hp₁).dim := by
    have hd : ((c.higherTriple hQ hQ').G.app t).dim = 1 + 1 :=
      (hv₁.ctxG.typed.ctxLaws.dim_eq t ht.inHom).trans ht.dim_eq
    rw [← dim_eq_of_equiv e]
    exact hd ▸ Nat.lt_succ_self 1
  obtain ⟨hp₂, e₂⟩ := c.exists_equiv_sideCtx_app hQ hQ' hy hdy
  exact ⟨hp₁, hp₂, (CtxExpr.app_equiv (c.sideCtx hQ hQ') e).trans e₂⟩

private theorem isPastingIn_map_cond {P R : OGP.{u}} (f : P ⟶ R) [IsInclusion f] (k : ℕ) (γ : Bool)
    (A B U : LowerSet P) (h : P.IsPastingIn k (cond γ A B) (cond γ B A) U) :
    R.IsPastingIn k (cond γ (map f A) (map f B)) (cond γ (map f B) (map f A)) (map f U) := by
  cases γ <;> exact (isPastingIn_map_iff f k _ _ _).2 h

private theorem isPastingIn_cond_of_isPastingAtIn {P : OGP.{u}} {k n : ℕ} {α γ : Bool}
    {G V T R E : LowerSet P} (h : P.IsPastingAtIn n α G V T)
    (hp : P.IsPastingIn k (cond γ R E) (cond γ E R) V) (hE : G ⊓ V = E) (hkn : k < n) :
    P.IsPastingIn k (cond γ R G) (cond γ G R) T := by
  obtain ⟨hRE, h₁, h₂⟩ := (isPastingIn_cond_iff γ).1 hp
  have hRV : R ≤ V := hRE ▸ le_sup_left
  have hEG : E ≤ G := hE ▸ inf_le_left
  have hRG : R ⊓ G = R ⊓ E := by
    rw [← hE, inf_comm G V, ← inf_assoc, inf_eq_left.2 hRV]
  have hbE : P.boundary E k (!γ) = P.boundary G k (!γ) := by
    rw [← hE, h.inf_eq]
    exact h.isMoleculeIn_left.isGlobular k n hkn (!γ) (!α)
  refine (isPastingIn_cond_iff γ).2 ⟨?_, hRG.trans (h₁.trans hbE), hRG.trans h₂⟩
  rw [h.eq_sup, ← hRE, sup_comm R E, ← sup_assoc, sup_eq_left.2 hEG, sup_comm]

theorem exists_equiv_whiskered {Q Q' : PastingDiagram X}
    (hQ : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q)
    (hQ' : IsRoundIn ⟨0, c.a.diag.toPastingDiagram, c.b.diag.toPastingDiagram⟩ Q') :
    ∃ hp : (cond c.γ (cond c.β Q Q') c.g.toPastingDiagram).Pastable
        (cond c.γ c.g.toPastingDiagram (cond c.β Q Q')) 0,
      ((cond c.γ (cond c.β Q Q') c.g.toPastingDiagram).paste
        (cond c.γ c.g.toPastingDiagram (cond c.β Q Q')) 0 hp).Equiv (c.whiskered hQ hQ') := by
  classical
  have hR := c.isRoundIn_cond c.β hQ hQ'
  have hdv := c.dim_unitPath hQ hQ'
  have hs : ((c.unitPath hQ hQ').boundary 1 (!c.β)).Equiv (c.unitPath hQ hQ') :=
    equiv_boundary_dim _ hdv.le _
  have hιs := isSubmoleculeOf_image_sideOcc (!c.β) 1 (c.unitOcc hQ hQ')
    (c.isRewritableSubmolecule_image_unitOcc hQ hQ').isSubmoleculeOf hs
  have e₀ : c.whiskered hQ hQ' = pasteAtBoundary c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
      (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not :=
    sidePaste_of (hι := (c.isRewritableSubmolecule_image_unitOcc hQ hQ').isSubmoleculeOf) hs
  set s := pasteAtBoundary c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
    (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not
  set wL := Within.pasteAtInl c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
    (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not
  set wR := Within.pasteAtInr c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
    (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not
  have hc := Within.isPastingAtIn_pasteAt c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
    (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not
  have hW : sideWithin wR 1 (!c.β) hs = wR := Within.ext_of_image_eq _ _ (by
    rw [image_sideWithin]
    exact boundary_eq_self (by rw [Within.krullDim_image, hdv]) _)
  have hmeet : ((c.unitOcc hQ hQ').trans wR).image = wL.image ⊓ wR.image := by
    have e := image_occurrence_pasteAt c.g.toPastingDiagram (c.unitPath hQ hQ') 1 (!c.β)
      (sideOcc (!c.β) 1 (c.unitOcc hQ hQ') hs) hιs c.boundary_g_not_not
    rw [image_sideOcc_trans_boundary, hW] at e
    exact e
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn c.γ
    (c.pastable_unit (c.isRoundIn_cond c.β hQ hQ'))
  have hpst' : s.shape.ogp.IsPastingIn 0 (cond c.γ (wc.trans wR).image
      ((c.unitOcc hQ hQ').trans wR).image)
      (cond c.γ ((c.unitOcc hQ hQ').trans wR).image (wc.trans wR).image) wR.image := by
    have h₁ : (wc.trans wR).image = OGP.map wR.emb wc.image := Within.image_trans wc wR
    have h₂ : ((c.unitOcc hQ hQ').trans wR).image = OGP.map wR.emb (c.unitOcc hQ hQ').image :=
      Within.image_trans _ _
    rw [h₁, h₂]
    exact isPastingIn_map_cond wR.emb 0 c.γ _ _ _ hpst
  have hpG := isPastingIn_cond_of_isPastingAtIn hc hpst' hmeet.symm Nat.zero_lt_one
  have hp := pastable_cond_of_isPastingIn c.γ (wc.trans wR) wL hpG
    (by rw [hR.dim_eq]; omega) (by rw [c.dim_g]; omega)
  refine ⟨hp, ?_⟩
  rw [e₀]
  exact (equiv_paste_cond_of_within c.γ (wc.trans wR) wL hpG s.shape.isMolecule hp).trans
    (equiv_restrictTo_univ s)

end UnitCrossing

end Atoms.Diagrammatic
