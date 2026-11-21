import Atoms.Diagrammatic.Context.Syntax

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem equiv_of_iso_top {a b : PastingDiagram (⊤_ DiagSet.{u})}
    (Θ : a.shape.ogp ≅ b.shape.ogp) : a.Equiv b :=
  ⟨Θ, terminal.hom_ext _ _⟩

theorem Parallel.mapTo {u v : RoundPastingDiagram X} (h : Parallel u v) (f : X ⟶ Y) :
    Parallel (u.mapTo f) (v.mapTo f) := by
  refine ⟨h.1, h.2.imp id fun hb α => ?_⟩
  change ((u.toPastingDiagram.mapTo f).boundary (u.dim - 1) α).Equiv
    ((v.toPastingDiagram.mapTo f).boundary (v.dim - 1) α)
  rw [PastingDiagram.boundary_mapTo, PastingDiagram.boundary_mapTo]
  exact (hb α).mapTo f

def IsRoundCtx (H : PdHom X) (t : CtxExpr X) : Prop :=
  ∀ a : PastingDiagram (⊤_ DiagSet.{u}), InHom (H.mapTo (terminal.from X)) a →
    a.dim = H.k + 1 → a.IsRound → ((t.mapTo (terminal.from X)).app a).IsRound

theorem isRound_app_of_trim {B : Set (RoundPastingDiagram Y)} {H H' : PdHom Y} {t : CtxExpr Y}
    (ht : t.Typed B False H H') :
    ∀ a, InHom H a → a.dim = H.k + 1 → a.IsRound → (t.app a).IsRound := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs₀ =>
    intro a ha hda har
    have hs : (a.boundary H.k α).Equiv v₀ := (ha.side α).trans hs₀.symm
    change (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h a).IsRound
    rw [sidePaste_of hs]
    exact isRound_pasteAtBoundary _ _ _ _ _ _ _ har (hdu.trans hda.symm) (by omega)
  | id => exact fun a _ _ har => har
  | comp ht₁ _ ih₁ ih₂ =>
    exact fun a ha hda har => ih₂ _ (ht₁.mapsInto a ha)
      ((ht₁.ctxLaws.dim_eq a ha).trans (hda.trans (by rw [ht₁.k_eq]))) (ih₁ a ha hda har)
  | promote hp => exact hp.elim

theorem isRoundCtx_of_trim {A : Set (RoundPastingDiagram X)} {H H' : PdHom X} {t : CtxExpr X}
    (ht : t.Typed A False H H') : IsRoundCtx H t :=
  isRound_app_of_trim (ht.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial)

theorem isRoundCtx_id (H : PdHom X) : IsRoundCtx H .id :=
  fun _ _ _ har => har

namespace IsRoundCtx

variable {A : Set (RoundPastingDiagram X)} {p : Prop}

theorem congr {H H₁ : PdHom X} {t : CtxExpr X} (hr : IsRoundCtx H t) (e : H.Equiv H₁) :
    IsRoundCtx H₁ t := fun a ha hda =>
  hr a (ha.congr (e.mapTo _).symm) (hda.trans (by rw [e.k_eq]))

theorem isRound_app {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H')
    (hr : IsRoundCtx H t) {a : PastingDiagram X} (ha : InHom H a) (hda : a.dim = H.k + 1)
    (har : a.IsRound) : (t.app a).IsRound :=
  (ht.app_mapTo (terminal.from X) a ha).isRound_iff.1 (hr _ (ha.mapTo _) hda har)

theorem comp {H H' : PdHom X} {s t : CtxExpr X} (ht : t.Typed A p H H') (hrt : IsRoundCtx H t)
    (hrs : IsRoundCtx H' s) : IsRoundCtx H (.comp s t) := by
  intro a ha hda har
  have ht' := ht.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial
  exact hrs _ (ht'.mapsInto a ha) ((ht'.ctxLaws.dim_eq a ha).trans (hda.trans (by rw [ht.k_eq])))
    (hrt a ha hda har)

end IsRoundCtx

structure IsRoundIn (H : PdHom X) (a : PastingDiagram X) : Prop where
  inHom : InHom H a
  dim_eq : a.dim = H.k + 1
  isRound : a.IsRound

structure IsRoundCtxOn (H H' : PdHom X) (t : CtxExpr X) : Prop where
  typed : t.Typed Set.univ True H H'
  round : IsRoundCtx H t

structure RoundHom (X : DiagSet.{u}) extends PdHom X where
  isRound_v : v.IsRound
  isRound_w : w.IsRound
  dim_v : v.dim = k
  parallel : Parallel ⟨v, isRound_v⟩ ⟨w, isRound_w⟩

instance : CoeOut (RoundHom X) (PdHom X) :=
  ⟨RoundHom.toPdHom⟩

theorem RoundHom.dim_w (H : RoundHom X) : H.w.dim = H.k :=
  H.parallel.1.symm.trans H.dim_v

theorem IsRoundCtxOn.congr {H H' H₁ H₁' : PdHom X} {t : CtxExpr X} (h : IsRoundCtxOn H H' t)
    (e : H.Equiv H₁) (e' : H'.Equiv H₁') : IsRoundCtxOn H₁ H₁' t :=
  ⟨(h.typed.congr_domain e).congr_codomain e', h.round.congr e⟩

theorem isRoundCtxOn_id {H : PdHom X} : IsRoundCtxOn H H .id :=
  ⟨.id (.refl _), isRoundCtx_id H⟩

theorem IsRoundCtxOn.comp {H H' H'' : PdHom X} {F G : CtxExpr X} (hF : IsRoundCtxOn H H' F)
    (hG : IsRoundCtxOn H' H'' G) : IsRoundCtxOn H H'' (.comp G F) :=
  ⟨.comp hF.typed hG.typed, hF.round.comp hF.typed hG.round⟩

theorem IsRoundIn.congr {H H₁ : PdHom X} {a : PastingDiagram X} (h : IsRoundIn H a)
    (e : H.Equiv H₁) : IsRoundIn H₁ a :=
  ⟨h.inHom.congr e, h.dim_eq.trans (by rw [e.k_eq]), h.isRound⟩

theorem IsRoundCtxOn.isRoundIn {H H' : PdHom X} {a : PastingDiagram X} {t : CtxExpr X}
    (ht : IsRoundCtxOn H H' t) (ha : IsRoundIn H a) : IsRoundIn H' (t.app a) :=
  ⟨ht.typed.mapsInto _ ha.inHom,
    (ht.typed.ctxLaws.dim_eq _ ha.inHom).trans (ha.dim_eq.trans (by rw [ht.typed.k_eq])),
    ht.round.isRound_app ht.typed ha.inHom ha.dim_eq ha.isRound⟩

theorem IsRoundIn.parallel {H : PdHom X} {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) : Parallel ⟨a, ha.isRound⟩ ⟨b, hb.isRound⟩ :=
  ⟨ha.dim_eq.trans hb.dim_eq.symm, Or.inr fun α => by
    change (a.boundary (a.dim - 1) α).Equiv (b.boundary (b.dim - 1) α)
    rw [ha.dim_eq, hb.dim_eq, Nat.add_sub_cancel]
    exact (ha.inHom.side α).trans ((hb.inHom.side α).symm)⟩

def IsRoundIn.roundHom {H : PdHom X} {a : PastingDiagram X} (ha : IsRoundIn H a) : RoundHom X :=
  have hk : H.k ≤ a.dim := by rw [ha.dim_eq]; omega
  have hv := ha.inHom.source.isRound_iff.1 (isRound_boundary_of_isRound ha.isRound H.k false)
  have hw := ha.inHom.target.isRound_iff.1 (isRound_boundary_of_isRound ha.isRound H.k true)
  have hdv : H.v.dim = H.k :=
    (PastingDiagram.dim_eq_of_equiv ha.inHom.source).symm.trans (dim_boundary a hk false)
  have hdw : H.w.dim = H.k :=
    (PastingDiagram.dim_eq_of_equiv ha.inHom.target).symm.trans (dim_boundary a hk true)
  ⟨H, hv, hw, hdv, ha.inHom.parallel hv hw hdv hdw⟩

@[simp]
theorem IsRoundIn.toPdHom_roundHom {H : PdHom X} {a : PastingDiagram X} (ha : IsRoundIn H a) :
    ha.roundHom.toPdHom = H :=
  rfl

def RoundHom.ofIsRoundIn {H : PdHom X} {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) : RoundHom X :=
  ⟨⟨H.k + 1, a, b⟩, ha.isRound, hb.isRound, ha.dim_eq, ha.parallel hb⟩

theorem RoundHom.isRoundIn_side (H : RoundHom X) {n : ℕ} (hn : H.k = n + 1) (α : Bool) :
    IsRoundIn (H.boundary n) (H.side α) := by
  have hd : (H.side α).dim = H.k :=
    Bool.cond_rec_prop (p := fun a : PastingDiagram X => a.dim = H.k) α H.dim_w H.dim_v
  refine ⟨InHom.of_side α ?_ ?_ ?_, hd.trans hn,
    Bool.cond_rec_prop α H.isRound_w H.isRound_v⟩
  · rw [PdHom.k_boundary, hd, hn]; omega
  · cases α <;> exact .refl _
  · have e := H.parallel.equiv_boundary_pred (H.dim_v.trans hn) (!α)
    cases α
    · exact e
    · exact e.symm

def RoundHom.mapTo (H : RoundHom X) (f : X ⟶ Y) : RoundHom Y :=
  ⟨H.toPdHom.mapTo f, H.isRound_v, H.isRound_w, H.dim_v, H.parallel.mapTo f⟩

theorem exists_formalCell (H : RoundHom (⊤_ DiagSet.{u})) :
    ∃ a : PastingDiagram (⊤_ DiagSet.{u}), IsRoundIn H a := by
  obtain ⟨⟨k, v, w⟩, hv, hw, hdv, hp⟩ := H
  dsimp only at hdv hp ⊢
  subst hdv
  have hd : v.shape.dimension = w.shape.dimension := hp.1
  obtain ⟨ψ, hψ⟩ : ∃ ψ : v.shape.ogp.restrict (v.shape.ogp.bdryFull ⊤) ≅
      w.shape.ogp.restrict (w.shape.ogp.bdryFull ⊤), ψ.IsSigned := by
    rcases Nat.eq_zero_or_pos v.dim with h0 | hpos
    · exact ⟨MoleculeShape.bdryIsoOfPoints v.shape w.shape h0 (hd ▸ h0),
        MoleculeShape.isSigned_bdryIsoOfPoints _ _ _ _⟩
    · obtain ⟨m, hm⟩ : ∃ m, v.dim = m + 1 := ⟨v.dim - 1, by omega⟩
      have hm' : w.dim = m + 1 := (show w.dim = v.dim from hd.symm).trans hm
      have h2 : ∀ α, (v.boundary (v.dim - 1) α).Equiv (w.boundary (w.dim - 1) α) :=
        hp.2.resolve_left (by change v.dim ≠ 0; omega)
      have hb : ∀ α, (v.boundary m α).Equiv (w.boundary m α) := fun α => by
        have e := h2 α
        rwa [show v.dim - 1 = m by omega, show w.dim - 1 = m by omega] at e
      exact ⟨MoleculeShape.bdryIsoOfParallel v.shape w.shape (fun α => (hb α).iso) hv hw hm hm',
        MoleculeShape.isSigned_bdryIsoOfParallel _ _ _ _ _ _ _⟩
  have hdS := MoleculeShape.dimension_rewriteAtom v.shape w.shape ψ hψ hv hw hd
  refine ⟨⟨MoleculeShape.rewriteAtom v.shape w.shape ψ hψ hv hw hd, terminal.from _⟩,
    ⟨?_, ?_, ?_⟩, hdS, MoleculeShape.isRound_rewriteAtom v.shape w.shape ψ hψ hv hw hd⟩
  · change v.dim < (MoleculeShape.rewriteAtom v.shape w.shape ψ hψ hv hw hd).dimension
    rw [hdS]
    exact Nat.lt_succ_self _
  · exact equiv_of_iso_top
      (MoleculeShape.boundaryIsoRewriteAtom v.shape w.shape ψ hψ hv hw hd false)
  · exact equiv_of_iso_top
      (MoleculeShape.boundaryIsoRewriteAtom v.shape w.shape ψ hψ hv hw hd true)

end Atoms.Diagrammatic
