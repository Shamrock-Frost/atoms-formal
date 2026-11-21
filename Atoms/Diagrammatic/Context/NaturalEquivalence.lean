import Atoms.Diagrammatic.Context.Equivalence
import Atoms.Diagrammatic.Equivalence.WeakInverse

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem exists_mem_equivalences_pasteOr {x y : PastingDiagram X} {n : ℕ} (hp : x.Pastable y n)
    {hr : (x.paste y n hp).IsRound}
    (hm : (⟨x.paste y n hp, hr⟩ : RoundPastingDiagram X) ∈ equivalences X) :
    ∃ hr' : (x.pasteOr y n).IsRound,
      (⟨x.pasteOr y n, hr'⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  rw [PastingDiagram.pasteOr_of hp]
  exact ⟨hr, hm⟩

theorem CtxExpr.Typed.promote_of_inHom {A : Set (RoundPastingDiagram X)} {p : Prop} (hp : p)
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') {a b : PastingDiagram X}
    (ha : InHom H a) (hb : InHom H b) : t.Typed A p ⟨H.k + 1, a, b⟩ ⟨H.k + 1, t.app a, t.app b⟩ :=
  .promote (k := H.k) hp rfl ⟨ha.lt_dim, .refl _, ha.target.trans hb.target.symm⟩
    ⟨hb.lt_dim, hb.source.trans ha.source.symm, .refl _⟩
    (ht.congr_domain ⟨rfl, ha.source.symm, hb.target.symm⟩) (.refl _)

theorem IsRoundCtx.comp_paste (α : Bool) {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') {u : PastingDiagram X}
    (hu : u.IsRound) (hdu : u.dim = H'.k + 1) (hb : (H'.side α).Equiv (u.boundary H'.k (!α))) :
    IsRoundCtx H (.comp (CtxExpr.paste α u H'.k) t) := by
  intro x hx hdx _
  have ht' := ht.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial
  have hy := ht'.mapsInto x hx
  have hdy : ((t.mapTo (terminal.from X)).app x).dim = H'.k + 1 :=
    (ht'.ctxLaws.dim_eq x hx).trans (hdx.trans (by rw [ht.k_eq]))
  have hs : (((t.mapTo (terminal.from X)).app x).boundary H'.k α).Equiv
      ((u.boundary H'.k (!α)).mapTo (terminal.from X)) :=
    (hy.side α).trans (by rw [PdHom.side_mapTo]; exact hb.mapTo (terminal.from X))
  have hp : (cond α ((t.mapTo (terminal.from X)).app x) (u.mapTo (terminal.from X))).Pastable
      (cond α (u.mapTo (terminal.from X)) ((t.mapTo (terminal.from X)).app x)) H'.k :=
    .of_side α (by rw [PastingDiagram.boundary_mapTo]; exact hs) (by omega)
      (by change H'.k < u.dim; omega)
  change (sidePaste α (u.mapTo (terminal.from X)) H'.k
    ((Within.refl (u.boundary H'.k (!α))).mapTo (terminal.from X))
        (Within.isSubmoleculeOf_image_refl _)
    ((PastingDiagram.Equiv.refl _).mapTo_boundary (terminal.from X))
    ((t.mapTo (terminal.from X)).app x)).IsRound
  exact (CtxExpr.sidePaste_equiv_paste α
    (ι := (Within.refl (u.boundary H'.k (!α))).mapTo (terminal.from X))
    (Within.image_refl _) _ hs hp).isRound_iff.2
    (isRound_paste_of_round α hp hu hdu hdy.le)

theorem isRoundCtxOn_comp_paste (α : Bool) {H H' : PdHom X} {u : PastingDiagram X}
    {t : CtxExpr X} (ht : t.Typed Set.univ True H H') (hu : u.IsRound)
    (hdu : u.dim = H'.k + 1) (hb : (H'.side α).Equiv (u.boundary H'.k (!α))) :
    IsRoundCtxOn H (H'.setSide α (u.boundary H'.k α)) (.comp (CtxExpr.paste α u H'.k) t) :=
  ⟨ht.comp (CtxExpr.typed_paste α (u := ⟨u, hu⟩) (Set.mem_univ _) hdu hb),
    IsRoundCtx.comp_paste α ht hu hdu hb⟩

theorem InHom.of_inHom_succ {H : PdHom X} {a b c : PastingDiagram X}
    (hc : InHom ⟨H.k + 1, a, b⟩ c) (ha : InHom H a) (hb : InHom H b) : InHom H c :=
  (hc.promote (Nat.lt_succ_self _)).congr ⟨rfl, ha.source, hb.target⟩

theorem InHom.pastable_hasBdry {H : PdHom X} {a b c θ : PastingDiagram X} (α : Bool)
    (hc : InHom H c) (hθ : HasBdry (!α) H.k θ a b) (e : (H.side α).Equiv a) :
    (cond α c θ).Pastable (cond α θ c) H.k :=
  Pastable.of_side α ((hc.side α).trans (e.trans hθ.side.symm))
    hc.lt_dim (by rw [hθ.dim_h]; omega)

@[elab_without_expected_type]
theorem InHom.pastable_hasType {H : PdHom X} {y' z c θ : PastingDiagram X} (hc : InHom H c)
    (hθ : HasBdry false H.k θ y' z) (e : H.w.Equiv y') : c.Pastable θ H.k :=
  InHom.pastable_hasBdry true hc hθ e

@[elab_without_expected_type]
theorem HasBdry.pastable_inHom {H : PdHom X} {x z c θ : PastingDiagram X} (hc : InHom H c)
    (hθ : HasBdry false H.k θ z x) (e : x.Equiv H.v) : θ.Pastable c H.k :=
  InHom.pastable_hasBdry false hc hθ.symm e.symm

structure CtxTriple (X : DiagSet.{u}) where
  dom : RoundHom X
  cod : PdHom X
  F : CtxExpr X
  G : CtxExpr X
  ϑ : PastingDiagram X → PastingDiagram X

namespace CtxTriple

structure Valid (τ : CtxTriple X) : Prop where
  ctxF : IsRoundCtxOn τ.dom τ.cod τ.F
  ctxG : IsRoundCtxOn τ.dom τ.cod τ.G
  comp : ∀ a, IsRoundIn τ.dom a → ∃ hr : (τ.ϑ a).IsRound,
    (⟨τ.ϑ a, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
      HasBdry false (τ.dom.k + 1) (τ.ϑ a) (τ.F.app a) (τ.G.app a)

def nextF (τ : CtxTriple X) (b : PastingDiagram X) : CtxExpr X :=
  .comp (CtxExpr.paste true (τ.ϑ b) (τ.dom.k + 1)) τ.F

def nextG (τ : CtxTriple X) (a : PastingDiagram X) : CtxExpr X :=
  .comp (CtxExpr.paste false (τ.ϑ a) (τ.dom.k + 1)) τ.G

theorem Valid.isRoundCtxOn_nextF {τ : CtxTriple X} (hτ : τ.Valid) {a b : PastingDiagram X}
    (ha : IsRoundIn τ.dom a) (hb : IsRoundIn τ.dom b) :
    IsRoundCtxOn ⟨τ.dom.k + 1, a, b⟩ ⟨τ.dom.k + 1, τ.F.app a, τ.G.app b⟩ (τ.nextF b) := by
  obtain ⟨hrb, -, htb⟩ := hτ.comp b hb
  have hpF := hτ.ctxF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  exact (isRoundCtxOn_comp_paste true hpF hrb htb.dim_h htb.side.symm).congr (.refl _)
    ⟨rfl, .refl _, htb.other⟩

theorem Valid.isRoundCtxOn_nextG {τ : CtxTriple X} (hτ : τ.Valid) {a b : PastingDiagram X}
    (ha : IsRoundIn τ.dom a) (hb : IsRoundIn τ.dom b) :
    IsRoundCtxOn ⟨τ.dom.k + 1, a, b⟩ ⟨τ.dom.k + 1, τ.F.app a, τ.G.app b⟩ (τ.nextG a) := by
  obtain ⟨hra, -, hta⟩ := hτ.comp a ha
  have hpG := hτ.ctxG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  exact (isRoundCtxOn_comp_paste false hpG hra hta.dim_h hta.other.symm).congr (.refl _)
    ⟨rfl, hta.side, .refl _⟩

structure Realizes (σ : CtxTriple X) (H H' : PdHom X)
    (F G : PastingDiagram X → PastingDiagram X) : Prop where
  equiv_dom : σ.dom.toPdHom.Equiv H
  equiv_cod : σ.cod.Equiv H'
  equiv_F : ∀ a, InHom H a → (σ.F.app a).Equiv (F a)
  equiv_G : ∀ a, InHom H a → (σ.G.app a).Equiv (G a)

theorem realizes_self (σ : CtxTriple X) : σ.Realizes σ.dom σ.cod σ.F.app σ.G.app :=
  ⟨.refl _, .refl _, fun _ _ => .refl _, fun _ _ => .refl _⟩

def natOp (A : Set (CtxTriple X)) : Set (CtxTriple X) :=
  {τ | τ.Valid ∧ ∀ a b, IsRoundIn τ.dom a → IsRoundIn τ.dom b →
    ∃ σ ∈ A, σ.Realizes ⟨τ.dom.k + 1, a, b⟩ ⟨τ.dom.k + 1, τ.F.app a, τ.G.app b⟩
      (τ.nextF b).app (τ.nextG a).app}

theorem natOp_mono {A B : Set (CtxTriple X)} (hAB : A ⊆ B) : natOp A ⊆ natOp B :=
  fun _ ⟨hv, h⟩ => ⟨hv, fun a b ha hb => (h a b ha hb).imp fun _ ⟨hσ, hr⟩ => ⟨hAB hσ, hr⟩⟩

def natOperator (X : DiagSet.{u}) : Set (CtxTriple X) →o Set (CtxTriple X) :=
  ⟨natOp, fun _ _ => natOp_mono⟩

inductive Closure (A : Set (CtxTriple X)) : CtxTriple X → Prop
  | base {τ : CtxTriple X} (hτ : τ ∈ A) : Closure A τ
  | comp {τ₁ τ₂ : CtxTriple X} (h₁ : Closure A τ₁) (h₂ : Closure A τ₂)
      (hm : τ₂.Realizes τ₁.dom τ₁.cod τ₁.G.app τ₂.G.app) :
      Closure A ⟨τ₁.dom, τ₁.cod, τ₁.F, τ₂.G, fun a => (τ₁.ϑ a).pasteOr (τ₂.ϑ a) (τ₁.dom.k + 1)⟩
  | left {τ : CtxTriple X} (h : Closure A τ) {H : CtxExpr X} {C : PdHom X}
      (hH : IsRoundCtxOn τ.cod C H) :
      Closure A ⟨τ.dom, C, .comp H τ.F, .comp H τ.G,
        fun a => (H.app (τ.ϑ a)).pasteOr (H.app (τ.G.app a)).unit (τ.dom.k + 1)⟩
  | right {τ : CtxTriple X} (h : Closure A τ) {H : CtxExpr X} {D : RoundHom X}
      (hH : IsRoundCtxOn D τ.dom H) :
      Closure A ⟨D, τ.cod, .comp τ.F H, .comp τ.G H, fun a => τ.ϑ (H.app a)⟩
  | inv {τ : CtxTriple X} (h : Closure A τ) {ϑ' : PastingDiagram X → PastingDiagram X}
      (hϑ' : ∀ a, IsRoundIn τ.dom a → IsWeakInverse (τ.ϑ a) (ϑ' a)) :
      Closure A ⟨τ.dom, τ.cod, τ.G, τ.F, ϑ'⟩

theorem Closure.mono {A B : Set (CtxTriple X)} (hAB : A ⊆ B) {τ : CtxTriple X}
    (h : Closure A τ) : Closure B τ := by
  induction h with
  | base hτ => exact .base (hAB hτ)
  | comp _ _ hm ih₁ ih₂ => exact .comp ih₁ ih₂ hm
  | left _ hH ih => exact .left ih hH
  | right _ hH ih => exact .right ih hH
  | inv _ hϑ' ih => exact .inv ih hϑ'

theorem Closure.valid {A : Set (CtxTriple X)} (hA : ∀ τ ∈ A, τ.Valid) {τ : CtxTriple X}
    (h : Closure A τ) : τ.Valid := by
  induction h with
  | base hτ => exact hA _ hτ
  | @comp τ₁ τ₂ _ _ hm ih₁ ih₂ =>
    refine ⟨ih₁.ctxF, ih₂.ctxG.congr hm.equiv_dom hm.equiv_cod, fun a ha => ?_⟩
    obtain ⟨hr₁, he₁, ht₁⟩ := ih₁.comp a ha
    obtain ⟨hr₂, he₂, ht₂⟩ := ih₂.comp a (ha.congr hm.equiv_dom.symm)
    rw [hm.equiv_dom.k_eq] at ht₂
    have e := (hm.equiv_F a ha.inHom).symm
    have hp := ht₁.pastable ht₂ e
    obtain ⟨hr, he⟩ := exists_mem_equivalences_pasteOr hp
      ((paste_mem_equivalences_iff_right (u := ⟨_, hr₁⟩) (v := ⟨_, hr₂⟩) he₁ ht₁.dim_h ht₂.dim_h
        hp).2 he₂)
    exact ⟨hr, he, ht₁.pasteOr ht₂ e⟩
  | @left τ _ H C hH ih =>
    refine ⟨ih.ctxF.comp hH, ih.ctxG.comp hH, fun a ha => ?_⟩
    obtain ⟨D, ⟨k', v', w'⟩, F, G, ϑ⟩ := τ
    obtain rfl : k' = D.k := ih.ctxF.typed.k_eq
    obtain ⟨hr, he, ht⟩ := ih.comp a ha
    have hFa := ih.ctxF.typed.mapsInto a ha.inHom
    have hin : InHom ⟨D.k, v', w'⟩ (ϑ a) := InHom.of_hasBdry ht hFa
    have hde : (ϑ a).dim = D.k + 1 + 1 := ht.dim_h
    obtain ⟨hp, hround, hmem⟩ := mem_equivalences_app_paste_unit hH.typed hH.round
      (e := ⟨ϑ a, hr⟩) he hin hde ht.other
    have L := hH.typed.ctxLaws
    have hGa := ih.ctxG.typed.mapsInto a ha.inHom
    have hdGa : (G.app a).dim = D.k + 1 := by
      rw [ih.ctxG.typed.ctxLaws.dim_eq a ha.inHom]; exact ha.dim_eq
    have hrG : (H.app (G.app a)).IsRound := hH.round.isRound_app hH.typed hGa hdGa
      (ih.ctxG.round.isRound_app ih.ctxG.typed ha.inHom ha.dim_eq ha.isRound)
    have hdHG : (H.app (G.app a)).dim = D.k + 1 := (L.dim_eq _ hGa).trans hdGa
    obtain ⟨hround', hmem'⟩ := exists_mem_equivalences_pasteOr hp hmem
    refine ⟨hround', hmem', ?_⟩
    dsimp only
    rw [PastingDiagram.pasteOr_of hp]
    refine ⟨by rw [dim_paste, L.dim_eq _ hin, hde, dim_unit, hdHG, max_self],
      (L.dim_eq _ hFa).trans ((ih.ctxF.typed.ctxLaws.dim_eq a ha.inHom).trans ha.dim_eq), hdHG,
      ?_, ?_⟩
    · exact (equiv_boundary_paste hp false).trans
        ((L.boundary _ hin (Nat.lt_succ_self D.k) (by omega) false).trans
          (CtxExpr.app_equiv H ht.side))
    · exact (equiv_boundary_paste hp true).trans
        (boundary_unit hdHG true)
  | @right τ _ H D hH ih =>
    refine ⟨hH.comp ih.ctxF, hH.comp ih.ctxG, fun a ha => ?_⟩
    obtain ⟨hr, he, ht⟩ := ih.comp (H.app a) (hH.isRoundIn ha)
    rw [hH.typed.k_eq] at ht
    exact ⟨hr, he, ht⟩
  | @inv τ _ ϑ' hϑ' ih =>
    refine ⟨ih.ctxG, ih.ctxF, fun a ha => ?_⟩
    obtain ⟨_, he, ht⟩ := ih.comp a ha
    obtain ⟨hr', he'⟩ := (hϑ' a ha).mem_equivalences fun _ => he
    exact ⟨hr', he', ((hϑ' a ha).hasBdry ht).2⟩

end CtxTriple

def natEqv (X : DiagSet.{u}) : Set (CtxTriple X) := (CtxTriple.natOperator X).gfp

theorem subset_natEqv {A : Set (CtxTriple X)} (h : A ⊆ CtxTriple.natOp A) : A ⊆ natEqv X :=
  (CtxTriple.natOperator X).le_gfp h

theorem natOp_natEqv : CtxTriple.natOp (natEqv X) = natEqv X :=
  (CtxTriple.natOperator X).map_gfp

theorem valid_of_mem_natEqv {τ : CtxTriple X} (h : τ ∈ natEqv X) : τ.Valid := by
  rw [← natOp_natEqv] at h
  exact h.1

end Atoms.Diagrammatic
