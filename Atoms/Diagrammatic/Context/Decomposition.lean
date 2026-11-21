import Atoms.Diagrammatic.Context.Interchange

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem equiv_boundary_sidePaste_of_gt {α : Bool} {u : PastingDiagram X} {n : ℕ}
    {v V : PastingDiagram X} {ι : Within V v} {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤}
    {h : (u.boundary n (!α)).Equiv V} {a : PastingDiagram X} (hs : (a.boundary n α).Equiv v)
    {j : ℕ} (hjn : j < n) (γ : Bool) :
    ((sidePaste α u n ι hι h a).boundary j γ).Equiv (a.boundary j γ) :=
  (equiv_boundary_boundary _ hjn (!α) γ).symm.trans
    (((equiv_boundary_not_sidePaste hs).boundary j γ).trans
      (equiv_boundary_boundary a hjn (!α) γ))

theorem InHom.of_inHom_sides {H₀ D : PdHom X} (hk : H₀.k < D.k) (hv : InHom H₀ D.v)
    (hw : InHom H₀ D.w) {x : PastingDiagram X} (hx : InHom D x) : InHom H₀ x :=
  ⟨hk.trans hx.lt_dim,
    (equiv_boundary_boundary x hk false false).symm.trans
      ((hx.source.boundary H₀.k false).trans hv.source),
    (equiv_boundary_boundary x hk true true).symm.trans
      ((hx.target.boundary H₀.k true).trans hw.target)⟩

theorem CtxExpr.Typed.mapsInto_of_lt {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H₀ H₀' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H₀ H₀') {D : PdHom X} (hk : H₀.k < D.k)
    (hv : InHom H₀ D.v) (hw : InHom H₀ D.w) {x : PastingDiagram X} (hx : InHom D x) :
    InHom ⟨D.k, t.app D.v, t.app D.w⟩ (t.app x) := by
  have L := ht.ctxLaws
  have hxH := InHom.of_inHom_sides hk hv hw hx
  exact ⟨by rw [L.dim_eq x hxH]; exact hx.lt_dim,
    (L.boundary x hxH hk hx.lt_dim false).trans
      (L.equiv _ _ (hv.of_equiv hx.source.symm) hx.source),
    (L.boundary x hxH hk hx.lt_dim true).trans
      (L.equiv _ _ (hw.of_equiv hx.target.symm) hx.target)⟩

theorem CtxExpr.Typed.inHom_side_of_trim {A : Set (RoundPastingDiagram X)} {D D' : PdHom X}
    {T : CtxExpr X} (hT : T.Typed A False D D') {H₀ : PdHom X} (hk : H₀.k < D.k)
    (hD : ∀ α, InHom H₀ (D.side α)) : ∀ α, InHom H₀ (D'.side α) := by
  induction hT with
  | @side D D' α v₀ u _ hdu V ι hι h hs e =>
    have hdv₀ := dim_side_of_isRewritable u hdu ι hι h
    have hsv : (v₀.boundary D.k α).Equiv v₀ := equiv_boundary_dim v₀ hdv₀.le α
    intro β
    rcases Bool.eq_or_eq_not β α with rfl | rfl
    · have es := e.side β
      rw [PdHom.side_setSide_self] at es
      have hd : D.k ≤ (sidePaste β u.toPastingDiagram D.k ι hι.isSubmoleculeOf h v₀).dim := by
        rw [sidePaste_of hsv, dim_pasteAtBoundary, hdu]
        exact le_max_of_le_left (Nat.le_succ _)
      have hγ : ∀ γ, (((sidePaste β u.toPastingDiagram D.k ι hι.isSubmoleculeOf h v₀).boundary
          D.k β).boundary H₀.k γ).Equiv (H₀.side γ) := fun γ =>
        (equiv_boundary_boundary _ hk β γ).trans ((equiv_boundary_sidePaste_of_gt hsv hk γ).trans
          ((hs.boundary H₀.k γ).trans ((hD β).side γ)))
      exact (InHom.of_side false (by rw [dim_boundary _ hd]; exact hk) (hγ false)
        (hγ true)).of_equiv es
    · have es := e.side (!α)
      rw [PdHom.side_setSide_not] at es
      exact (hD _).of_equiv es
  | id e => exact fun α => (hD α).of_equiv (e.side α)
  | comp ht₁ _ ih₁ ih₂ => exact ih₂ (by rw [ht₁.k_eq]; exact hk) (ih₁ hk hD)
  | promote hp => exact hp.elim

theorem CtxExpr.Typed.exists_interchange {A : Set (RoundPastingDiagram X)} {H₀ H₀' : PdHom X}
    {G : CtxExpr X} (hG : G.Typed A True H₀ H₀') :
    ∀ {D D' : PdHom X} {T : CtxExpr X}, T.Typed A False D D' → H₀.k < D.k →
      InHom H₀ D.v → InHom H₀ D.w →
      ∃ T'' : CtxExpr X, T''.Typed A False ⟨D.k, G.app D.v, G.app D.w⟩
          ⟨D'.k, G.app D'.v, G.app D'.w⟩ ∧
        (∀ x, InHom D x → (G.app (T.app x)).Equiv (T''.app (G.app x))) ∧
        ∀ {Y : DiagSet.{u}} (f : X ⟶ Y) (x : PastingDiagram Y), InHom (D.mapTo f) x →
          ((G.mapTo f).app ((T.mapTo f).app x)).Equiv
            ((T''.mapTo f).app ((G.mapTo f).app x)) := by
  induction hG with
  | @side H₀ H₀' β z₀ y _ hdy Z κ hκ hyZ hsG _ =>
    intro D D' T hT
    induction hT with
    | @side D D' α v₀ u hu hdu V ι hι h hs e =>
      intro hk hv hw
      have hD : ∀ γ, InHom H₀ (D.side γ) := fun γ => by cases γ <;> assumption
      have hdv₀ := dim_side_of_isRewritable u hdu ι hι h
      have hsv : (v₀.boundary D.k α).Equiv v₀ := equiv_boundary_dim v₀ hdv₀.le α
      have hs₀ : (v₀.boundary H₀.k β).Equiv z₀ :=
        ((hs.boundary H₀.k β).trans ((hD α).side β)).trans hsG.symm
      obtain ⟨w, wy, wv, ew, hc, hm⟩ :=
        exists_located_sidePaste (ι := κ) (hι := hκ.isSubmoleculeOf) (h := hyZ) hs₀
      have hdw : w.dim = D.k := by
        rw [← ew, dim_sidePaste hs₀ (by rw [hdy, hdv₀]; omega)]
        exact hdv₀
      have hιi := ι.isRewritableSubmolecule_image_iff.1 hι
      have hι' : w.shape.ogp.IsRewritableSubmolecule (ι.trans wv).image ⊤ :=
        (ι.trans wv).isRewritableSubmolecule_image_iff.2
          ⟨Within.isSubmoleculeOf_image_trans hιi.1 hc.isSubmoleculeOf_right, hιi.2.1,
            hιi.2.2.trans (hdv₀.trans hdw.symm)⟩
      have key := fun {a : PastingDiagram X} (hsa : (a.boundary D.k α).Equiv v₀) =>
        sidePaste_sidePaste_of_lt (hκ := hκ.isSubmoleculeOf) (hy := hyZ) (hι := hι.isSubmoleculeOf)
          (h := h) hdy hk wy wv hc hs₀ hm hι'.isSubmoleculeOf rfl hsa
      set Gs := CtxExpr.side β y.toPastingDiagram H₀.k κ hκ.isSubmoleculeOf hyZ
      refine ⟨.side α u.toPastingDiagram D.k (ι.trans wv) hι'.isSubmoleculeOf h, ?_,
        fun x hx => key ((hx.side α).trans hs.symm), fun f x hx => ?_⟩
      · refine .side (H := ⟨D.k, Gs.app D.v, Gs.app D.w⟩) (H' := ⟨D'.k, Gs.app D'.v, Gs.app D'.w⟩)
          α u hu hdu (ι.trans wv) hι' h ?_ ?_
        · rw [PdHom.side_mk_app, ← ew]
          exact sidePaste_equiv hs₀ hs
        · have es := e.side α
          have en := e.side (!α)
          rw [PdHom.side_setSide_self] at es
          rw [PdHom.side_setSide_not] at en
          refine .of_side α e.k_eq ?_ ?_
          · rw [PdHom.side_setSide_self, PdHom.side_mk_app]
            have hb := (key hsv).boundary D.k α
            rw [ew] at hb
            exact hb.symm.trans ((equiv_boundary_sidePaste_of_lt
              ((equiv_boundary_sidePaste_of_gt hsv hk β).trans hs₀) hdy hk α).trans
              (CtxExpr.app_equiv Gs es))
          · rw [PdHom.side_setSide_not, PdHom.side_mk_app, PdHom.side_mk_app]
            exact CtxExpr.app_equiv Gs en
      · have hsx : (x.boundary D.k α).Equiv (v₀.mapTo f) :=
          (hx.side α).trans (by rw [PdHom.side_mapTo]; exact (hs.mapTo f).symm)
        exact sidePaste_sidePaste_of_lt (y := y.toPastingDiagram.mapTo f) (κ := κ.mapTo f)
          (u := u.toPastingDiagram.mapTo f) (ι := ι.mapTo f) (hκ := hκ.isSubmoleculeOf)
          (hy := hyZ.mapTo_boundary f) (hι := hι.isSubmoleculeOf) (h := h.mapTo_boundary f)
          (ι' := (ι.trans wv).mapTo f) hdy hk (wy.mapTo f)
          (wv.mapTo f) hc (hs₀.mapTo_boundary f)
          ((image_trans_sideWithin_mapTo κ wv hs₀ f).trans hm) hι'.isSubmoleculeOf rfl hsx
    | id e =>
      intro _ _ _
      exact ⟨.id, .id ⟨e.k_eq, CtxExpr.app_equiv _ e.equiv_v, CtxExpr.app_equiv _ e.equiv_w⟩,
        fun _ _ => .refl _, fun _ _ _ => .refl _⟩
    | @comp D D₁ D' s t ht₁ _ ih₁ ih₂ =>
      intro hk hv hw
      obtain ⟨T₁, hT₁, p₁, i₁⟩ := ih₁ hk hv hw
      have hD₁ := ht₁.inHom_side_of_trim hk fun γ => by cases γ <;> assumption
      obtain ⟨T₂, hT₂, p₂, i₂⟩ := ih₂ (by rw [ht₁.k_eq]; exact hk) (hD₁ false) (hD₁ true)
      exact ⟨.comp T₂ T₁, .comp hT₁ hT₂,
        fun x hx => (p₂ _ (ht₁.mapsInto x hx)).trans (CtxExpr.app_equiv _ (p₁ x hx)),
        fun f x hx => (i₂ f _ ((ht₁.mapTo f (B := Set.univ) fun _ _ => trivial).mapsInto x
          hx)).trans (CtxExpr.app_equiv _ (i₁ f x hx))⟩
    | promote hp => exact hp.elim
  | id _ =>
    intro D D' T hT _ _ _
    exact ⟨T, hT, fun _ _ => .refl _, fun _ _ _ => .refl _⟩
  | @comp H₀ H₁ H₀' s t hG₁ _ ih₁ ih₂ =>
    intro D D' T hT hk hv hw
    obtain ⟨T₁, hT₁, p₁, i₁⟩ := ih₁ hT hk hv hw
    obtain ⟨T₂, hT₂, p₂, i₂⟩ := ih₂ hT₁ (by rw [hG₁.k_eq]; exact hk) (hG₁.mapsInto _ hv)
      (hG₁.mapsInto _ hw)
    refine ⟨T₂, hT₂, fun x hx => (CtxExpr.app_equiv s (p₁ x hx)).trans
      (p₂ _ (hG₁.mapsInto_of_lt hk hv hw hx)), fun f x hx => (CtxExpr.app_equiv _ (i₁ f x hx)).trans
        (i₂ f _ (((hG₁.mapTo f (B := Set.univ) fun _ _ => trivial).mapsInto_of_lt
          (D := D.mapTo f) hk (hv.mapTo f) (hw.mapTo f) hx).congr
            ⟨rfl, hG₁.app_mapTo f _ hv, hG₁.app_mapTo f _ hw⟩))⟩
  | promote _ hk' _ _ _ _ ih =>
    intro D D' T hT hk hv hw
    exact ih hT (by rw [PdHom.k_boundary]; omega) (hv.promote (by omega)) (hw.promote (by omega))

theorem CtxExpr.Typed.trim_of_k_eq_zero {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') (h0 : H.k = 0) :
    t.Typed A False H H' := by
  induction ht with
  | side α u hu hdu ι hι h hs e => exact .side α u hu hdu ι hι h hs e
  | id e => exact .id e
  | comp ht₁ _ ih₁ ih₂ => exact .comp (ih₁ h0) (ih₂ (ht₁.k_eq.trans h0))
  | promote _ hk => exact (Nat.succ_ne_zero _ (hk.symm.trans h0)).elim

theorem CtxExpr.Typed.exists_trim_comp {A : Set (RoundPastingDiagram X)} {H H' : PdHom X}
    {E : CtxExpr X} {k : ℕ} (hE : E.Typed A True H H') (hk : H.k = k + 1)
    (hv : InHom (H.boundary k) H.v) (hw : InHom (H.boundary k) H.w) :
    ∃ (T G : CtxExpr X) (H₀ : PdHom X), G.Typed A True (H.boundary k) H₀ ∧
      T.Typed A False ⟨H.k, G.app H.v, G.app H.w⟩ H' ∧
      (∀ a, InHom H a → (E.app a).Equiv (T.app (G.app a))) ∧
      ∀ {Y : DiagSet.{u}} (f : X ⟶ Y) (a : PastingDiagram Y), InHom (H.mapTo f) a →
        ((E.mapTo f).app a).Equiv ((T.mapTo f).app ((G.mapTo f).app a)) := by
  induction hE with
  | side α u hu hdu ι hι h hs e =>
    exact ⟨_, .id, _, .id (.refl _), .side α u hu hdu ι hι h hs e, fun _ _ => .refl _,
      fun _ _ _ => .refl _⟩
  | id e => exact ⟨.id, .id, _, .id (.refl _), .id e, fun _ _ => .refl _, fun _ _ _ => .refl _⟩
  | @promote k' H H₁ H' t _ hk' _ _ ht e _ =>
    obtain rfl : k = k' := by omega
    exact ⟨.id, t, H₁, ht, .id e, fun _ _ => .refl _, fun _ _ _ => .refl _⟩
  | @comp H H' H'' s t _ _ ih₁ ih₂ =>
    obtain ⟨T₁, G₁, ⟨k₀, v₀, w₀⟩, hG₁, hT₁, p₁, i₁⟩ := ih₁ hk hv hw
    obtain rfl : k = k₀ := hG₁.k_eq.symm
    have hP₁ : G₁.Typed A True H ⟨H.k, G₁.app H.v, G₁.app H.w⟩ :=
      .promote trivial hk hv hw hG₁ (.refl _)
    have hkH : k < H.k := by omega
    have hD : ∀ γ, InHom ⟨k, v₀, w₀⟩ ((⟨H.k, G₁.app H.v, G₁.app H.w⟩ : PdHom X).side γ) :=
      fun γ => by
        cases γ
        · exact hG₁.mapsInto _ hv
        · exact hG₁.mapsInto _ hw
    have hH' := hT₁.inHom_side_of_trim hkH hD
    have eH' : (H'.boundary k).Equiv ⟨k, v₀, w₀⟩ := ⟨rfl, (hH' false).source, (hH' true).target⟩
    have hk' : H'.k = k + 1 := hT₁.k_eq.trans hk
    obtain ⟨T₂, G₂, H₀', hG₂, hT₂, p₂, i₂⟩ :=
      ih₂ hk' ((hH' false).congr eH'.symm) ((hH' true).congr eH'.symm)
    obtain ⟨T₃, hT₃, p₃, i₃⟩ := hG₂.exists_interchange hT₁ hkH ((hD false).congr eH'.symm)
      ((hD true).congr eH'.symm)
    refine ⟨.comp T₂ T₃, .comp G₂ G₁, H₀', .comp hG₁ (hG₂.congr_domain eH'), .comp hT₃ hT₂,
      fun a ha => ?_, fun f a ha => ?_⟩
    · have hx := hP₁.mapsInto a ha
      exact (CtxExpr.app_equiv s (p₁ a ha)).trans ((p₂ _ (hT₁.mapsInto _ hx)).trans
        (CtxExpr.app_equiv T₂ (p₃ _ hx)))
    · have hx := (hP₁.mapTo f (B := Set.univ) fun _ _ => trivial).mapsInto a ha
      have hT₁f := hT₁.mapTo f (B := Set.univ) fun _ _ => trivial
      exact (CtxExpr.app_equiv (s.mapTo f) (i₁ f a ha)).trans ((i₂ f _ (hT₁f.mapsInto _ hx)).trans
        (CtxExpr.app_equiv (T₂.mapTo f) (i₃ f _ hx)))

end Atoms.Diagrammatic
