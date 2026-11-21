import Atoms.Diagrammatic.Context.Decomposition
import Atoms.Diagrammatic.Context.Division

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem IsWeakInvCtx.equivalent_of_equivalent_app {H H' : RoundHom X} {E E' : CtxExpr X}
    (h : IsWeakInvCtx H H' E E') {a a' : PastingDiagram X} (ha : IsRoundIn H a)
    (ha' : IsRoundIn H a')
    (he : Equivalent ⟨E.app a, (h.round.isRoundIn ha).isRound⟩
      ⟨E.app a', (h.round.isRoundIn ha').isRound⟩) :
    Equivalent ⟨a, ha.isRound⟩ ⟨a', ha'.isRound⟩ :=
  have hEa := h.round.isRoundIn ha
  have hEa' := h.round.isRoundIn ha'
  equivalent_trans (equivalent_symm (h.left.equivalent_app ha (h.round'.isRoundIn hEa).isRound
      ha.isRound))
    (equivalent_trans (Equivalent.app h.round' hEa hEa' he)
      (h.left.equivalent_app ha' (h.round'.isRoundIn hEa').isRound ha'.isRound))

def RoundHom.ofEquiv (H : RoundHom X) {H₀ : PdHom X} (e : H.toPdHom.Equiv H₀) : RoundHom X :=
  ⟨H₀, e.equiv_v.isRound_iff.1 H.isRound_v, e.equiv_w.isRound_iff.1 H.isRound_w,
    (dim_eq_of_equiv e.equiv_v).symm.trans (H.dim_v.trans e.k_eq),
    (H.parallel.of_equiv_left (u' := ⟨H₀.v, e.equiv_v.isRound_iff.1 H.isRound_v⟩)
      e.equiv_v.symm).of_equiv_right (v' := ⟨H₀.w, e.equiv_w.isRound_iff.1 H.isRound_w⟩)
      e.equiv_w.symm⟩

theorem RoundHom.isRound_side (H : RoundHom X) (α : Bool) : (H.side α).IsRound := by
  cases α
  · exact H.isRound_v
  · exact H.isRound_w

theorem exists_isWeakInvCtx_paste (α : Bool) {H H' : RoundHom X} {x : PastingDiagram X}
    (hx : x.IsRound) (hxe : (⟨x, hx⟩ : RoundPastingDiagram X) ∈ equivalences X)
    (ht : HasBdry α H.k x (H'.side α) (H.side α)) (he : (H.setSide α (H'.side α)).Equiv H') :
    ∃ E' : CtxExpr X, IsWeakInvCtx H H' (CtxExpr.paste α x H.k) E' ∧ PresEqv H' E' := by
  cases α
  · obtain ⟨x', h, h'⟩ := exists_isWeakInvCtx_pasteLeft hx hxe ht he
    exact ⟨_, h, h'⟩
  · obtain ⟨x', h, h'⟩ := exists_isWeakInvCtx_pasteRight hx hxe
      ⟨ht.dim_h, ht.dim_b, ht.dim_a, ht.other, ht.side⟩ he
    exact ⟨_, h, h'⟩

section Side

variable {H : RoundHom X} (α : Bool) {v₀ : PastingDiagram X} (u : RoundPastingDiagram X)
  (hu : u ∈ equivalences X) (hdu : u.dim = H.k + 1) {V : PastingDiagram X} (ι : Within V v₀)
  (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤) (h : (u.boundary H.k (!α)).Equiv V)
  (hs : v₀.Equiv (H.side α))

include hu hdu hs in
theorem sidePaste_unit_spec :
    ∃ hr : (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h (H.side α).unit).IsRound,
      (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
      HasBdry α H.k (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h (H.side α).unit)
        ((sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary H.k α)
        (H.side α) := by
  have hdv₀ := CtxExpr.Typed.dim_side_of_isRewritable u hdu ι hι h
  have hdH : (H.side α).dim = H.k := (dim_eq_of_equiv hs).symm.trans hdv₀
  have tε := hasType_unit hdH
  have hsε : ((H.side α).unit.boundary H.k α).Equiv v₀ :=
    (boundary_unit hdH α).trans hs.symm
  have ht : (CtxExpr.side α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h).Typed (equivalences X)
      False ⟨H.k, H.side α, H.side α⟩ ((PdHom.mk H.k (H.side α) (H.side α)).setSide α
        ((sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary H.k α)) :=
    .side (H := ⟨H.k, H.side α, H.side α⟩) α u hu hdu ι hι h (by cases α <;> exact hs) (.refl _)
  have hin : InHom ⟨H.k, H.side α, H.side α⟩ (H.side α).unit :=
    ⟨by rw [tε.dim_h]; exact Nat.lt_succ_self _, tε.side, tε.other⟩
  have hr := isRound_app_of_trim ht _ hin tε.dim_h (isRound_unit (H.isRound_side α))
  have hdx := (dim_sidePaste (ι := ι) (hι := hι.isSubmoleculeOf) (h := h) hsε
    (by rw [tε.dim_h, hdu])).trans tε.dim_h
  have hbα := equiv_boundary_sidePaste_of_side (ι := ι) (hι := hι.isSubmoleculeOf) (h := h)
    u.isRound hdu hι hsε (equiv_boundary_dim v₀ hdv₀.le α) (by rw [tε.dim_h]; omega) hdv₀.ge
  refine ⟨hr, mem_equivalences_app_of_trim ht _ hin tε.dim_h _
    (unit_mem_equivalences ⟨_, H.isRound_side α⟩) hr, ⟨hdx, ?_, hdH, hbα, ?_⟩⟩
  · exact (dim_eq_of_equiv hbα).symm.trans (dim_boundary _ (by omega) α)
  · exact (equiv_boundary_not_sidePaste hsε).trans (boundary_unit hdH (!α))

include hu hdu hs in
theorem exists_isWeakInvCtx_side {H' : RoundHom X}
    (e : (H.setSide α ((sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary
      H.k α)).Equiv H'.toPdHom) :
    ∃ E' : CtxExpr X, IsWeakInvCtx H H' (.side α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h) E' ∧
      PresEqv H'.toPdHom E' := by
  obtain ⟨hr, hxe, tx⟩ := sidePaste_unit_spec α u hu hdu ι hι h hs
  set E := CtxExpr.side α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h
  have hdH := tx.dim_b
  have tε := hasType_unit hdH
  have hsε : ((H.side α).unit.boundary H.k α).Equiv v₀ := (boundary_unit hdH α).trans hs.symm
  have hs' := e.side α
  rw [PdHom.side_setSide_self] at hs'
  obtain ⟨E', hW, hP⟩ := exists_isWeakInvCtx_paste α hr hxe (tx.of_equiv_side hs')
    (((PdHom.Equiv.refl _).setSide α hs'.symm).trans e)
  have hEt : E.Typed (equivalences X) False H.toPdHom H'.toPdHom := .side α u hu hdu ι hι h hs e
  have hE : IsRoundCtxOn H H' E :=
    ⟨hEt.mono (Set.subset_univ _) fun h => h.elim, isRoundCtx_of_trim hEt⟩
  have U : NatSim X H H (fun c => c)
      (fun c => (cond α c (H.side α).unit).pasteOr (cond α (H.side α).unit c) H.k) := by
    cases α
    · exact NatSim.unit_left H H (T := .id) isRoundCtxOn_id
    · exact (NatSim.unit_right H H (T := .id) isRoundCtxOn_id).symm
  refine ⟨E', hW.of_natSim ((U.left hE).of_equiv (fun _ _ => .refl _) fun c hc => ?_) hE, hP⟩
  have hpc : (cond α c (H.side α).unit).Pastable (cond α (H.side α).unit c) H.k :=
    .of_side α ((hc.side α).trans (boundary_unit hdH (!α)).symm) hc.lt_dim
      (by rw [tε.dim_h]; omega)
  have hpε : (cond (!α) (H.side α).unit c).Pastable (cond (!α) c (H.side α).unit) H.k := by
    rw [Bool.cond_not, Bool.cond_not]
    exact hpc
  have hpx : (cond α c (E.app (H.side α).unit)).Pastable (cond α (E.app (H.side α).unit) c) H.k :=
    .of_side α ((hc.side α).trans tx.other.symm) hc.lt_dim (by
      change H.k < (sidePaste _ _ _ _ _ _ _).dim
      rw [tx.dim_h]; omega)
  exact (CtxExpr.app_equiv E ((CtxExpr.paste_app_pasteOr α hpc).symm.trans
    (CtxExpr.paste_app_not α hpc))).trans
      ((CtxExpr.side_app_paste_not hdu hsε hpε).trans (CtxExpr.paste_app_not α hpx).symm)

end Side

theorem RoundHom.exists_setSide (H : RoundHom X) (α : Bool) {x s : PastingDiagram X}
    (hx : x.IsRound) (tx : HasBdry α H.k x s (H.side α)) :
    ∃ H' : RoundHom X, H'.toPdHom = H.setSide α s := by
  have hs := tx.side.isRound_iff.1 (isRound_boundary_of_isRound hx H.k α)
  have hp : Parallel ⟨s, hs⟩ ⟨H.side (!α), H.isRound_side (!α)⟩ := by
    have h₁ := ((parallel_boundary hx tx.dim_h α (!α)).of_equiv_left
      (u' := ⟨s, hs⟩) tx.side.symm).of_equiv_right
      (v' := ⟨H.side α, H.isRound_side α⟩) tx.other.symm
    refine Parallel.trans h₁ ?_
    cases α
    · exact H.parallel
    · exact H.parallel.symm
  cases α
  · exact ⟨⟨H.setSide false s, hs, H.isRound_w, tx.dim_a, hp⟩, rfl⟩
  · exact ⟨⟨H.setSide true s, H.isRound_v, hs, H.dim_v, hp.symm⟩, rfl⟩

theorem exists_roundHom_of_typed_trim {H₀ H₀' : PdHom X} {t : CtxExpr X}
    (ht : t.Typed (equivalences X) False H₀ H₀') :
    ∀ H : RoundHom X, H.toPdHom = H₀ → ∃ H' : RoundHom X, H'.toPdHom = H₀' := by
  induction ht with
  | side α u hu hdu ι hι h hs e =>
    rintro H rfl
    obtain ⟨hr, -, tx⟩ := sidePaste_unit_spec α u hu hdu ι hι h hs
    obtain ⟨H₁, hH₁⟩ := H.exists_setSide α hr tx
    exact ⟨H₁.ofEquiv (hH₁ ▸ e), rfl⟩
  | id e =>
    rintro H rfl
    exact ⟨H.ofEquiv e, rfl⟩
  | comp _ _ ih₁ ih₂ =>
    intro H hH
    obtain ⟨H₁, hH₁⟩ := ih₁ H hH
    exact ih₂ H₁ hH₁
  | promote hp => exact hp.elim

theorem exists_isWeakInvCtx_of_typed_trim {H H' : RoundHom X} {E : CtxExpr X}
    (hE : E.Typed (equivalences X) False H.toPdHom H'.toPdHom) :
    ∃ E' : CtxExpr X, IsWeakInvCtx H H' E E' ∧ PresEqv H'.toPdHom E' := by
  suffices key : ∀ {H₀ H₀' : PdHom X} {t : CtxExpr X}, t.Typed (equivalences X) False H₀ H₀' →
      ∀ H H' : RoundHom X, H.toPdHom = H₀ → H'.toPdHom = H₀' →
        ∃ E' : CtxExpr X, IsWeakInvCtx H H' t E' ∧ PresEqv H'.toPdHom E' from
    key hE H H' rfl rfl
  intro H₀ H₀' t ht
  induction ht with
  | side α u hu hdu ι hι h hs e =>
    rintro H H' rfl rfl
    exact exists_isWeakInvCtx_side α u hu hdu ι hι h hs e
  | id e =>
    rintro H H' rfl rfl
    refine ⟨.id, ⟨isRoundCtxOn_id.congr (.refl _) e, isRoundCtxOn_id.congr (.refl _) e.symm,
      NatSim.refl H isRoundCtxOn_id, NatSim.refl H' isRoundCtxOn_id⟩, fun a _ he _ => he⟩
  | comp ht₁ _ ih₁ ih₂ =>
    rintro H H' rfl rfl
    obtain ⟨H₁, hH₁⟩ := exists_roundHom_of_typed_trim ht₁ H rfl
    obtain ⟨E₁, W₁, P₁⟩ := ih₁ H H₁ rfl hH₁
    obtain ⟨E₂, W₂, P₂⟩ := ih₂ H₁ H' hH₁ rfl
    exact ⟨.comp E₁ E₂, W₁.comp W₂, P₂.comp W₂.round' P₁⟩
  | promote hp => exact hp.elim

namespace CtxExpr

section SideFrame

variable {α : Bool} {u : PastingDiagram X} {k : ℕ} {v V : PastingDiagram X} {ι : Within V v}
  {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤} {h : (u.boundary k (!α)).Equiv V}

theorem side_app_frameOf (hdu : u.dim = k + 1) {ℓ z : PastingDiagram X} (hdℓ : ℓ.dim ≤ k + 1)
    (hkℓ : k ≤ ℓ.dim) (hsℓ : (ℓ.boundary k α).Equiv v)
    (hz : (z.boundary k α).Equiv (ℓ.boundary k (!α))) (hkz : k < z.dim) :
    ((side α u k ι hι h).app ((frameOf α ℓ k).app z)).Equiv
      ((frameOf α ((side α u k ι hι h).app ℓ) k).app z) := by
  have hdℓ' : ((side α u k ι hι h).app ℓ).dim = k + 1 := by
    change (sidePaste α u k ι hι h ℓ).dim = k + 1
    rw [sidePaste_of hsℓ, dim_pasteAtBoundary, hdu]
    omega
  have hz' : (z.boundary k α).Equiv (((side α u k ι hι h).app ℓ).boundary k (!α)) :=
    hz.trans (equiv_boundary_not_sidePaste hsℓ).symm
  have hp' : (cond α z ((side α u k ι hι h).app ℓ)).Pastable
      (cond α ((side α u k ι hι h).app ℓ) z) k := .of_side α hz' hkz (by omega)
  refine PastingDiagram.Equiv.trans ?_ ((paste_app_not α hp').symm.trans
    (frameOf_app_equiv α hdℓ' hp').symm)
  by_cases hd : ℓ.dim = k + 1
  · have hp : (cond α z ℓ).Pastable (cond α ℓ z) k := .of_side α hz hkz (by omega)
    have hpn : (cond (!α) ℓ z).Pastable (cond (!α) z ℓ) k := by
      rw [Bool.cond_not, Bool.cond_not]
      exact hp
    exact (app_equiv _ ((frameOf_app_equiv α hd hp).trans (paste_app_not α hp))).trans
      (side_app_paste_not hdu hsℓ hpn)
  · rw [frameOf_of_not α hd]
    have hle : ℓ.dim ≤ k := by omega
    have hdv : v.dim = k := (dim_eq_of_equiv hsℓ).symm.trans (dim_boundary ℓ hkℓ α)
    have hℓv : ℓ.Equiv v := (equiv_boundary_dim ℓ hle α).symm.trans hsℓ
    have hsz : (z.boundary k α).Equiv v :=
      hz.trans ((equiv_boundary_dim ℓ hle (!α)).trans hℓv)
    have hsv : (v.boundary k α).Equiv v := equiv_boundary_dim v hdv.le α
    have hdP : ((side α u k ι hι h).app v).dim = k + 1 := by
      change (sidePaste α u k ι hι h v).dim = k + 1
      rw [sidePaste_of hsv, dim_pasteAtBoundary, hdu]
      omega
    have hpv : (cond α z ((side α u k ι hι h).app v)).Pastable
        (cond α ((side α u k ι hι h).app v) z) k :=
      .of_side α (hsz.trans ((equiv_boundary_dim v hdv.le (!α)).symm.trans
        (equiv_boundary_not_sidePaste hsv).symm)) hkz (by omega)
    exact (side_app_equiv_paste hdu hdv hsz hkz).trans ((paste_app_not α hpv).trans
      (app_equiv _ (sidePaste_equiv hsv hℓv.symm)))

theorem side_app_frameOf_not (hdu : u.dim = k + 1) {r z : PastingDiagram X}
    (hsz : (z.boundary k α).Equiv v)
    (hz : (z.boundary k (!α)).Equiv (r.boundary k α)) (hkz : k < z.dim) :
    ((side α u k ι hι h).app ((frameOf (!α) r k).app z)).Equiv
      ((frameOf (!α) r k).app ((side α u k ι hι h).app z)) := by
  by_cases hd : r.dim = k + 1
  · have hp : (cond (!α) z r).Pastable (cond (!α) r z) k :=
      .of_side (!α) (by rw [Bool.not_not]; exact hz) hkz (by omega)
    have hp' : (cond (!α) ((side α u k ι hι h).app z) r).Pastable
        (cond (!α) r ((side α u k ι hι h).app z)) k :=
      .of_side (!α) (by rw [Bool.not_not]; exact (equiv_boundary_not_sidePaste hsz).trans hz)
        (by rw [show (side α u k ι hι h).app z = sidePaste α u k ι hι h z from rfl,
          dim_sidePaste hsz (by omega)]; exact hkz) (by omega)
    exact (app_equiv _ (frameOf_app_equiv (!α) hd hp)).trans
      ((side_app_paste_not hdu hsz hp).trans (frameOf_app_equiv (!α) hd hp').symm)
  · rw [frameOf_of_not (!α) hd]
    exact .refl _

end SideFrame

end CtxExpr

structure IsFrameOn (H₁ H : PdHom X) (f : Bool → PastingDiagram X) : Prop where
  k_eq : H.k = H₁.k
  dim_le : ∀ α, (f α).dim ≤ H₁.k + 1
  le_dim : ∀ α, H₁.k ≤ (f α).dim
  inner : ∀ α, ((f α).boundary H₁.k (!α)).Equiv (H₁.side α)
  outer : ∀ α, ((f α).boundary H₁.k α).Equiv (H.side α)

theorem isFrameOn_side {H : PdHom X} (hv : H.v.dim = H.k) (hw : H.w.dim = H.k) :
    IsFrameOn H H H.side := by
  have hd : ∀ α, (H.side α).dim = H.k := fun α => by cases α <;> assumption
  exact ⟨rfl, fun α => by rw [hd]; omega, fun α => (hd α).ge,
    fun α => equiv_boundary_dim _ (hd α).le (!α), fun α => equiv_boundary_dim _ (hd α).le α⟩

theorem exists_isFrameOn_of_typed_trim {A : Set (RoundPastingDiagram X)} {H H' : PdHom X}
    {T : CtxExpr X} (hT : T.Typed A False H H') :
    ∀ {H₁ : PdHom X} {f : Bool → PastingDiagram X}, IsFrameOn H₁ H f →
      ∃ f' : Bool → PastingDiagram X, IsFrameOn H₁ H' f' ∧ ∀ y, InHom H₁ y →
        (T.app ((CtxExpr.frame (f false) (f true) H₁.k).app y)).Equiv
          ((CtxExpr.frame (f' false) (f' true) H₁.k).app y) := by
  induction hT with
  | @side H H' α v₀ u hu hdu V ι hι h hs e =>
    rintro ⟨k₁, v₁, w₁⟩ f hf
    have hk : H.k = k₁ := hf.k_eq
    subst hk
    set S := CtxExpr.side α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h
    have hdv₀ := CtxExpr.Typed.dim_side_of_isRewritable u hdu ι hι h
    have hsf : ((f α).boundary H.k α).Equiv v₀ := (hf.outer α).trans hs.symm
    have hne : (!α) ≠ α := by cases α <;> decide
    refine ⟨Function.update f α (S.app (f α)), ⟨e.k_eq.symm, fun β => ?_, fun β => ?_, fun β => ?_,
      fun β => ?_⟩, fun y hy => ?_⟩
    · rcases Bool.eq_or_eq_not β α with rfl | rfl
      · rw [Function.update_self]
        change (sidePaste _ _ _ _ _ _ _).dim ≤ _
        rw [sidePaste_of hsf, dim_pasteAtBoundary, hdu]
        exact max_le le_rfl (hf.dim_le β)
      · rw [Function.update_of_ne hne]
        exact hf.dim_le _
    · rcases Bool.eq_or_eq_not β α with rfl | rfl
      · rw [Function.update_self]
        change _ ≤ (sidePaste _ _ _ _ _ _ _).dim
        rw [sidePaste_of hsf, dim_pasteAtBoundary, hdu]
        exact le_max_of_le_right (hf.le_dim β)
      · rw [Function.update_of_ne hne]
        exact hf.le_dim _
    · rcases Bool.eq_or_eq_not β α with rfl | rfl
      · rw [Function.update_self]
        exact (equiv_boundary_not_sidePaste hsf).trans (hf.inner β)
      · rw [Function.update_of_ne hne]
        exact hf.inner _
    · have es := e.side β
      rcases Bool.eq_or_eq_not β α with rfl | rfl
      · rw [PdHom.side_setSide_self] at es
        rw [Function.update_self]
        exact (equiv_boundary_sidePaste_of_side u.isRound hdu hι hsf
          (equiv_boundary_dim v₀ hdv₀.le β) (hf.le_dim β) hdv₀.ge).trans es
      · rw [PdHom.side_setSide_not] at es
        rw [Function.update_of_ne hne]
        exact (hf.outer _).trans es
    have hL := (CtxExpr.typed_frameOf false (H := ⟨H.k, v₁, w₁⟩) (hf.dim_le false)
      (hf.inner false).symm).mapsInto y hy
    cases α
    · simp only [Function.update_self, Function.update_of_ne (show true ≠ false by decide)]
      exact (CtxExpr.side_app_frameOf_not hdu (hL.side false |>.trans hsf)
        ((hL.side true).trans (hf.inner true).symm) hL.lt_dim).trans
        (CtxExpr.app_equiv _ (CtxExpr.side_app_frameOf hdu (hf.dim_le false) (hf.le_dim false)
          hsf ((hy.side false).trans (hf.inner false).symm) hy.lt_dim))
    · simp only [Function.update_self, Function.update_of_ne (show false ≠ true by decide)]
      exact CtxExpr.side_app_frameOf hdu (hf.dim_le true) (hf.le_dim true) hsf
        ((hL.side true).trans (hf.inner true).symm) hL.lt_dim
  | id e =>
    intro H₁ f hf
    exact ⟨f, ⟨e.k_eq.symm.trans hf.k_eq, hf.dim_le, hf.le_dim, hf.inner,
      fun α => (hf.outer α).trans (e.side α)⟩, fun _ _ => .refl _⟩
  | comp _ _ ih₁ ih₂ =>
    intro H₁ f hf
    obtain ⟨f₁, hf₁, e₁⟩ := ih₁ hf
    obtain ⟨f₂, hf₂, e₂⟩ := ih₂ hf₁
    exact ⟨f₂, hf₂, fun y hy => (CtxExpr.app_equiv _ (e₁ y hy)).trans (e₂ y hy)⟩
  | promote hp => exact hp.elim

theorem natSim_paste_units {D D' : RoundHom X} {K : CtxExpr X} (hK : IsRoundCtxOn D D' K) :
    NatSim X D D' K.app (fun c => (CtxExpr.paste false D'.v.unit D'.k).app
      ((CtxExpr.paste true D'.w.unit D'.k).app (K.app c))) := by
  have u₀ := hasType_unit D'.dim_v
  have u₁ := hasType_unit D'.dim_w
  have hK' : IsRoundCtxOn D D' (.comp (CtxExpr.paste false D'.v.unit D'.k) K) :=
    (isRoundCtxOn_comp_paste false hK.typed (isRound_unit D'.isRound_v) u₀.dim_h
      u₀.other.symm).congr (.refl _) ⟨rfl, u₀.side, .refl _⟩
  refine ((NatSim.unit_left D D' (T := K) hK).trans_of_equiv
    (NatSim.unit_right D D' (T := .comp (CtxExpr.paste false D'.v.unit D'.k) K) hK').symm
    fun c hc => ?_).of_equiv (fun _ _ => .refl _) fun c hc => ?_
  · exact (CtxExpr.paste_app_pasteOr false
      (u₀.pastable_inHom (hK.typed.mapsInto c hc) (.refl _))).symm
  · have hKc := hK.typed.mapsInto c hc
    exact ((CtxExpr.paste_app_pasteOr true
      ((hK'.typed.mapsInto c hc).pastable_hasType u₁ (.refl _))).symm).trans
      (CtxExpr.pasteRight_app_pasteLeft (u₀.pastable_inHom hKc (.refl _))
        (hKc.pastable_hasType u₁ (.refl _)))

theorem natSim_trim_comp_rounded {A : Set (RoundPastingDiagram X)} {H H' : PdHom X}
    {F : CtxExpr X} (hF : IsRoundCtxOn H H' F) {v w : PastingDiagram X} (hv : IsRoundIn H v)
    (hw : IsRoundIn H w) {D : RoundHom X} {T : CtxExpr X}
    (hT : T.Typed A False ⟨H.k + 1, F.app v, F.app w⟩ D.toPdHom)
    (hE : IsRoundCtx (RoundHom.ofIsRoundIn hv hw).toPdHom (.comp T F)) :
    NatSim X (RoundHom.ofIsRoundIn hv hw) D (CtxExpr.comp T F).app
      (CtxExpr.comp T (F.rounded w H.k)).app := by
  obtain ⟨k', v', w'⟩ := H'
  obtain rfl : H.k = k' := hF.typed.k_eq.symm
  have hFv := hF.isRoundIn hv
  have hFw := hF.isRoundIn hw
  set H₁ : PdHom X := ⟨H.k + 1, F.app v, F.app w⟩
  have hk := hT.k_eq
  change D.k = H.k + 1 at hk
  obtain ⟨f, hf, hfr⟩ := exists_isFrameOn_of_typed_trim hT (H₁ := H₁)
    (isFrameOn_side hFv.dim_eq (hFw.dim_eq))
  have hH₁k : H₁.k = H.k + 1 := rfl
  have hid : ∀ y, (CtxExpr.frame (H₁.side false) (H₁.side true) H₁.k).app y = y := fun y => by
    change (CtxExpr.frameOf true _ _).app ((CtxExpr.frameOf false _ _).app y) = y
    have hdv : (F.app v).dim = H.k + 1 := hFv.dim_eq
    have hdw : (F.app w).dim = H.k + 1 := hFw.dim_eq
    rw [CtxExpr.frameOf_of_not true (by rw [hH₁k]; change ¬ (F.app w).dim = _; omega),
      CtxExpr.frameOf_of_not false (by rw [hH₁k]; change ¬ (F.app v).dim = _; omega)]
    rfl
  have ho : ∀ α, ((f α).boundary H₁.k α).Equiv (D.side α) := hf.outer
  have hdx : ∀ α, ((f α).boundary H₁.k α).dim = H₁.k := fun α =>
    dim_boundary _ (hf.le_dim α) α
  obtain ⟨ℓ', hℓ'r, tℓ', hℓ'⟩ := exists_pad_round false (hf.dim_le false) (hf.le_dim false)
    ((ho false).isRound_iff.2 (D.isRound_side false))
  obtain ⟨r', hr'r, tr', hr'⟩ := exists_pad_round true (hf.dim_le true) (hf.le_dim true)
    ((ho true).isRound_iff.2 (D.isRound_side true))
  have eD : D.toPdHom.Equiv
      ⟨H₁.k, (f false).boundary H₁.k false, (f true).boundary H₁.k true⟩ :=
    ⟨hk, (ho false).symm, (ho true).symm⟩
  set D' := D.ofEquiv eD
  have hFp := hF.typed.promote_of_inHom trivial hv.inHom hw.inHom
  have hRF := isRoundCtxOn_rounded hF hv hw
  have hTr : IsRoundCtxOn H₁ D T :=
    ⟨hT.mono (Set.subset_univ _) fun h => h.elim, isRoundCtx_of_trim hT⟩
  have hE' : IsRoundCtxOn (RoundHom.ofIsRoundIn hv hw) D' (.comp T F) :=
    ⟨(hFp.comp (hT.mono (Set.subset_univ _) fun h => h.elim)).congr_codomain eD, hE⟩
  have hTR : IsRoundCtxOn (RoundHom.ofIsRoundIn hv hw) D' (.comp T (F.rounded w H.k)) :=
    (hRF.comp hTr).congr (.refl _) eD
  have key : ∀ y, InHom H₁ y → ((CtxExpr.paste false D'.v.unit D'.k).app
      ((CtxExpr.paste true D'.w.unit D'.k).app (T.app y))).Equiv
        ((CtxExpr.paste false ℓ' H₁.k).app ((CtxExpr.paste true r' H₁.k).app y)) := by
    intro y hy
    have e := hfr y hy
    rw [hid] at e
    have hL := (CtxExpr.typed_frameOf false (H := H₁) (hf.dim_le false)
      (hf.inner false).symm).mapsInto y hy
    exact (CtxExpr.app_equiv _ ((CtxExpr.app_equiv _ e).trans
      (hr' _ ((hL.side true).trans (hf.inner true).symm) hL.lt_dim).symm)).trans
      ((CtxExpr.pasteRight_app_pasteLeft ((hasType_unit (hdx false)).pastable_inHom hL (.refl _))
        (hL.pastable_hasType tr' (hf.inner true).symm)).symm.trans
      ((CtxExpr.app_equiv _ (hℓ' y ((hy.side false).trans (hf.inner false).symm)
        hy.lt_dim).symm).trans
      (CtxExpr.pasteRight_app_pasteLeft (tℓ'.pastable_inHom hy (hf.inner false))
        (hy.pastable_hasType tr' (hf.inner true).symm))))
  have S₁ := (natSim_paste_units hE').of_equiv (fun _ _ => .refl _)
    fun c hc => key _ (hFp.mapsInto c hc)
  have S₂ := natSim_frames_rounded hF hv hw (D := D'.toPdHom) hH₁k hℓ'r
    (tℓ'.of_equiv_other (hf.inner false)) hr'r (tr'.of_equiv_side (hf.inner true))
  have S₃ := (natSim_paste_units hTR).of_equiv (fun _ _ => .refl _)
    fun c hc => key _ (hRF.typed.mapsInto c hc)
  exact (S₁.trans (S₂.trans (NatSim.symm S₃))).congr (.refl _) eD.symm

theorem IsWeakInvCtx.exists_trim_comp {H H' : RoundHom X} {F F' : CtxExpr X}
    (hF : IsWeakInvCtx H H' F F') {v w : PastingDiagram X} (hv : IsRoundIn H v)
    (hw : IsRoundIn H w) {D : RoundHom X} {T : CtxExpr X}
    (hT : T.Typed (equivalences X) False ⟨H.k + 1, F.app v, F.app w⟩ D.toPdHom)
    (hE : IsRoundCtx (RoundHom.ofIsRoundIn hv hw).toPdHom (.comp T F)) :
    ∃ E' : CtxExpr X, IsWeakInvCtx (.ofIsRoundIn hv hw) D (.comp T F) E' ∧ PresEqv D E' := by
  obtain ⟨⟨k', v', w'⟩, hv', hw', hdv', hp'⟩ := H'
  obtain rfl : H.k = k' := hF.round.typed.k_eq.symm
  obtain ⟨K, hK, hKe⟩ := hF.exists_rounded hv hw
  obtain ⟨T', hT', hT'e⟩ := exists_isWeakInvCtx_of_typed_trim
    (H := .ofIsRoundIn (hF.round.isRoundIn hv) (hF.round.isRoundIn hw)) (H' := D) hT
  have hFp := hF.round.typed.promote_of_inHom trivial hv.inHom hw.inHom
  exact ⟨_, (hK.comp hT').of_natSim (natSim_trim_comp_rounded hF.round hv hw hT hE)
    ⟨hFp.comp (hT.mono (Set.subset_univ _) fun h => h.elim), hE⟩, hT'e.comp hT'.round' hKe⟩

open Limits in
theorem CtxExpr.Typed.exists_trim_comp_round {A : Set (RoundPastingDiagram X)} {H : RoundHom X}
    {H' : PdHom X} {E : CtxExpr X} {k : ℕ} (hE : E.Typed A True H.toPdHom H')
    (hk : H.k = k + 1) (hr : IsRoundCtx H.toPdHom E) :
    ∃ (T G : CtxExpr X) (H₀ : PdHom X), G.Typed A True (H.boundary k) H₀ ∧
      T.Typed A False ⟨H.k, G.app H.v, G.app H.w⟩ H' ∧
      (∀ a, InHom H.toPdHom a → (E.app a).Equiv (T.app (G.app a))) ∧
      IsRoundCtx (H.boundary k) G ∧ IsRoundCtx H.toPdHom (.comp T G) := by
  have hvIn := H.isRoundIn_v hk
  have hwIn := H.isRoundIn_w hk
  obtain ⟨T, G, H₀, hG, hT, p, i⟩ := hE.exists_trim_comp hk hvIn.inHom hwIn.inHom
  have hP : G.Typed A True H.toPdHom ⟨H.k, G.app H.v, G.app H.w⟩ :=
    .promote trivial hk hvIn.inHom hwIn.inHom hG (.refl _)
  obtain ⟨e, he⟩ := exists_formalCell (H.mapTo (terminal.from X))
  have hTGe : ((T.mapTo (terminal.from X)).app ((G.mapTo (terminal.from X)).app e)).IsRound :=
    (i (terminal.from X) e he.inHom).isRound_iff.1 (hr e he.inHom he.dim_eq he.isRound)
  refine ⟨T, G, H₀, hG, hT, p, ?_, isRoundCtx_of_isRound_app (.comp hP (hT.mono
    (Set.Subset.refl A) fun h => h.elim)) he hTGe⟩
  set D : PdHom (⊤_ DiagSet.{u}) :=
    ⟨H.k, (G.app H.v).mapTo (terminal.from X), (G.app H.w).mapTo (terminal.from X)⟩
  have hdG : ∀ α, (D.side α).dim = D.k := fun α => by
    cases α
    · exact (hG.ctxLaws.dim_eq _ hvIn.inHom).trans H.dim_v
    · exact (hG.ctxLaws.dim_eq _ hwIn.inHom).trans H.dim_w
  obtain ⟨f, hf, hfr⟩ := exists_isFrameOn_of_typed_trim
    (hT.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial)
    (isFrameOn_side (H := D) (hdG false) (hdG true))
  have hid : ∀ y, (CtxExpr.frame (D.side false) (D.side true) D.k).app y = y := fun y => by
    change (CtxExpr.frameOf true _ _).app ((CtxExpr.frameOf false _ _).app y) = y
    rw [CtxExpr.frameOf_of_not true (by rw [hdG true]; omega),
      CtxExpr.frameOf_of_not false (by rw [hdG false]; omega)]
    rfl
  have hy := (hP.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial).mapsInto e he.inHom
  have e₁ := hfr _ hy
  rw [hid] at e₁
  have hFr := (CtxExpr.typed_frame (H := D) (hf.dim_le false) (hf.dim_le true)
    (hf.inner false).symm (hf.inner true).symm).mapsInto _ hy
  have hℓ₀ : ((f false).boundary D.k false).IsRound :=
    hFr.source.isRound_iff.1 (isRound_boundary_of_isRound (e₁.isRound_iff.1 hTGe) _ false)
  have hGv : ((G.app H.v).mapTo (terminal.from X)).IsRound :=
    (hf.inner false).isRound_iff.1
      ((f false).isRound_boundary_true_of_false_of_le (hf.dim_le false) hℓ₀)
  exact isRoundCtx_of_isRound_app hG ⟨hvIn.inHom.mapTo _, hvIn.dim_eq, hvIn.isRound⟩
    ((hG.app_mapTo (terminal.from X) H.v hvIn.inHom).isRound_iff.2 hGv)

theorem exists_isWeakInvCtx_of_typed {H H' : RoundHom X} {E : CtxExpr X}
    (hE : E.Typed (equivalences X) True H.toPdHom H'.toPdHom)
    (hr : IsRoundCtxOn H H'.toPdHom E) :
    ∃ E' : CtxExpr X, IsWeakInvCtx H H' E E' ∧ PresEqv H'.toPdHom E' := by
  suffices key : ∀ (n : ℕ) (H H' : RoundHom X) (E : CtxExpr X), H.k = n →
      E.Typed (equivalences X) True H.toPdHom H'.toPdHom → IsRoundCtxOn H H'.toPdHom E →
      ∃ E' : CtxExpr X, IsWeakInvCtx H H' E E' ∧ PresEqv H'.toPdHom E' from
    key _ H H' E rfl hE hr
  intro n
  induction n with
  | zero => exact fun H H' E hn hE _ => exists_isWeakInvCtx_of_typed_trim (hE.trim_of_k_eq_zero hn)
  | succ k ih =>
    rintro ⟨⟨k₀, v, w⟩, hv, hw, hdv, hpar⟩ H' E hn hE hr
    subst hn
    obtain ⟨T, G, H₀, hG, hT, p, hGr, hTGr⟩ := hE.exists_trim_comp_round rfl hr.round
    set H₁ : RoundHom X := ⟨⟨k + 1, v, w⟩, hv, hw, hdv, hpar⟩
    have hvIn := H₁.isRoundIn_v rfl
    have hwIn := H₁.isRoundIn_w rfl
    have hGo : IsRoundCtxOn (H₁.pred k rfl) H₀ G := ⟨hG.mono (Set.subset_univ _) fun h => h, hGr⟩
    have hGv := hGo.isRoundIn hvIn
    obtain ⟨G', hW, -⟩ := ih (H₁.pred k rfl) hGv.roundHom G rfl hG hGo
    obtain ⟨E', hW', hP'⟩ := hW.exists_trim_comp (v := v) (w := w) hvIn hwIn (D := H') hT hTGr
    exact ⟨E', hW'.of_natSim ((NatSim.refl H₁ hr).of_equiv (fun _ _ => .refl _) p) hr, hP'⟩

theorem exists_solution_of_typed {H H' : RoundHom X} {E : CtxExpr X}
    (hE : E.Typed (equivalences X) True H.toPdHom H'.toPdHom) (hr : IsRoundCtxOn H H'.toPdHom E)
    {b : PastingDiagram X} (hb : IsRoundIn H' b) :
    ∃ (a : PastingDiagram X) (ha : IsRoundIn H a),
      Equivalent ⟨E.app a, (hr.isRoundIn ha).isRound⟩ ⟨b, hb.isRound⟩ ∧
        ((⟨b, hb.isRound⟩ : RoundPastingDiagram X) ∈ equivalences X →
          (⟨a, ha.isRound⟩ : RoundPastingDiagram X) ∈ equivalences X) ∧
        ∀ (a' : PastingDiagram X) (ha' : IsRoundIn H a'),
          Equivalent ⟨E.app a', (hr.isRoundIn ha').isRound⟩ ⟨b, hb.isRound⟩ →
            Equivalent ⟨a, ha.isRound⟩ ⟨a', ha'.isRound⟩ := by
  obtain ⟨E', h, hP⟩ := exists_isWeakInvCtx_of_typed hE hr
  obtain ⟨a, ha, h₁, h₂⟩ := h.exists_solution hP hb
  exact ⟨a, ha, h₁, h₂, fun a' ha' h₃ =>
    h.equivalent_of_equivalent_app ha ha' (equivalent_trans h₁ (equivalent_symm h₃))⟩

end Atoms.Diagrammatic
