import Atoms.Diagrammatic.Context.RoundBicategory

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Bicategory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section Absorb

variable {k : ℕ}

theorem equivalent_rounding_paste {y z p q r : PastingDiagram X} (hy : HasBdry false (k + 1) y p q)
    (hz : HasBdry false (k + 1) z q r) (hq : q.IsRound) (hr : r.IsRound) :
    ∃ (hp : (y.rounding (k + 1)).Pastable (z.rounding (k + 1)) (k + 1))
      (hp' : y.Pastable z (k + 1))
      (hr₁ : ((y.rounding (k + 1)).paste (z.rounding (k + 1)) (k + 1) hp).IsRound)
      (hr₂ : ((y.paste z (k + 1) hp').rounding (k + 1)).IsRound),
      Equivalent ⟨_, hr₁⟩ ⟨_, hr₂⟩ := by
  have hY := hy.rounding
  have hZ := hz.rounding
  have hYr := isRound_rounding hy.dim_h (hy.other.isRound_iff.2 hq)
  have hZr := isRound_rounding hz.dim_h (hz.other.isRound_iff.2 hr)
  have hp := hY.pastable hZ (.refl _)
  have hp' := hy.pastable hz (.refl _)
  have hyz := hy.pasteOr hz (.refl _)
  rw [pasteOr_of hp'] at hyz
  have hk : ∀ {w : PastingDiagram X}, w.dim = k + 1 + 1 → k + 1 < w.dim := fun hw => by omega
  refine ⟨hp, hp', isRound_paste_of_dim ⟨_, hYr⟩ ⟨_, hZr⟩ hY.dim_h hZ.dim_h hp,
    isRound_rounding hyz.dim_h (hyz.other.isRound_iff.2 hr), ?_⟩
  have hy₁ := pastable_unit_boundary (hk hy.dim_h)
  have hZd : (z.rounding (k + 1)).dim = k + 1 + 1 := hZ.dim_h
  have hpY : (y.paste (y.boundary (k + 1) true).unit (k + 1) hy₁).Pastable (z.rounding (k + 1))
      (k + 1) := by
    rw [← rounding_eq (hk hy.dim_h)]; exact hp
  obtain ⟨h₃, h₄, e₁⟩ := equiv_paste_assoc hy₁ hpY
  have e₀ : ((y.rounding (k + 1)).paste (z.rounding (k + 1)) (k + 1) hp).Equiv
      ((y.paste (y.boundary (k + 1) true).unit (k + 1) hy₁).paste (z.rounding (k + 1)) (k + 1)
        hpY) := by
    rw [Subsingleton.elim hpY (by rw [← rounding_eq (hk hy.dim_h)]; exact hp)]
    exact Equiv.paste (by rw [rounding_eq (hk hy.dim_h)]) (.refl _) _ _
  have hUZ : (((y.boundary (k + 1) true).unit).paste (z.rounding (k + 1)) (k + 1) h₃).IsRound :=
    isRound_paste_of_dim (hy.other.isRound_iff.2 hq).unit ⟨_, hZr⟩
      (by rw [dim_unit, dim_boundary y (by rw [hy.dim_h]; omega)]) hZd h₃
  have E₁ : Equivalent ⟨_, hUZ⟩ ⟨_, hZr⟩ := equivalent_symm
    (equivalent_paste_unit_of_equiv false ⟨_, hZr⟩ hZd (hZ.side.trans hy.other.symm) _ _)
  have hpy : y.Pastable (z.rounding (k + 1)) (k + 1) := hy.pastable hZ (.refl _)
  have hyZ : (y.paste (z.rounding (k + 1)) (k + 1) hpy).IsRound :=
    isRound_paste_of_round true (u := z.rounding (k + 1)) (x := y) hpy hZr hZd hy.dim_h.le
  have E₂ := equivalent_paste_side true (c := y) (h := ⟨_, hUZ⟩) (h' := ⟨_, hZr⟩) E₁
    (by rw [dim_paste, hy.dim_h, hZd, dim_unit,
      dim_boundary y (by rw [hy.dim_h]; omega)]; omega) h₄ hpy ((e₀.trans e₁).isRound_iff.1
      (isRound_paste_of_dim ⟨_, hYr⟩ ⟨_, hZr⟩ hY.dim_h hZ.dim_h hp)) hyZ
  have hz₁ := pastable_unit_boundary (hk hz.dim_h)
  have hpz : y.Pastable (z.paste (z.boundary (k + 1) true).unit (k + 1) hz₁) (k + 1) := by
    rw [← rounding_eq (hk hz.dim_h)]; exact hpy
  have hzb : (z.boundary (k + 1) true).dim = k + 1 :=
    dim_boundary z (by rw [hz.dim_h]; omega) true
  have h₂ : (y.paste z (k + 1) hp').Pastable (z.boundary (k + 1) true).unit (k + 1) :=
    ⟨(equiv_boundary_paste hp' true).trans (boundary_unit hzb false).symm,
      lt_min (hk hyz.dim_h) (by rw [dim_unit, hzb]; omega)⟩
  obtain ⟨_, h₆, e₂⟩ := equiv_paste_assoc hp' h₂
  have e₃ : (y.paste (z.rounding (k + 1)) (k + 1) hpy).Equiv
      ((y.paste z (k + 1) hp').rounding (k + 1)) := by
    rw [rounding_eq (hk hyz.dim_h)]
    refine (Equiv.paste (.refl _) (by rw [rounding_eq (hk hz.dim_h)]) hpy h₆).trans
      (e₂.symm.trans (Equiv.paste (.refl _) ((equiv_boundary_paste hp' true).symm.unit) h₂ _))
  exact equivalent_trans (equivalent_of_equiv (e₀.trans e₁))
    (equivalent_trans E₂ (equivalent_of_equiv e₃))

theorem equivalent_rounding_paste_cond_paste (γ : Bool) {u y z p q r : PastingDiagram X}
    (hu : u.IsRound) (hdu : u.dim = k + 1) (hy : HasBdry false (k + 1) y p q)
    (hz : HasBdry false (k + 1) z q r) (hq : q.IsRound) (hr : r.IsRound)
    (hp : y.Pastable z (k + 1))
    (hpu : (cond γ (y.paste z (k + 1) hp) u).Pastable (cond γ u (y.paste z (k + 1) hp)) k) :
    ∃ (hpy : (cond γ y u).Pastable (cond γ u y) k) (hpz : (cond γ z u).Pastable (cond γ u z) k)
      (hp' : (((cond γ y u).paste (cond γ u y) k hpy).rounding (k + 1)).Pastable
        (((cond γ z u).paste (cond γ u z) k hpz).rounding (k + 1)) (k + 1))
      (hr₁ : (((cond γ (y.paste z (k + 1) hp) u).paste (cond γ u (y.paste z (k + 1) hp)) k
        hpu).rounding (k + 1)).IsRound)
      (hr₂ : ((((cond γ y u).paste (cond γ u y) k hpy).rounding (k + 1)).paste
        (((cond γ z u).paste (cond γ u z) k hpz).rounding (k + 1)) (k + 1) hp').IsRound),
      Equivalent ⟨_, hr₁⟩ ⟨_, hr₂⟩ := by
  obtain ⟨hpy, hpz, _, e⟩ := exists_paste_cond_paste γ hp hpu hdu (Nat.lt_succ_self k)
  obtain ⟨_, hpq, ty⟩ := hy.paste_cond γ hdu hpy
  obtain ⟨_, hpr, tz⟩ := hz.paste_cond γ hdu hpz
  have hround : ∀ {w : PastingDiagram X}, w.IsRound → w.dim = k + 1 →
      ∀ hw : (cond γ w u).Pastable (cond γ u w) k, ((cond γ w u).paste (cond γ u w) k hw).IsRound :=
    fun {w} hw hdw hpw => by
      cases γ
      · exact isRound_paste_of_dim ⟨u, hu⟩ ⟨w, hw⟩ hdu hdw hpw
      · exact isRound_paste_of_dim ⟨w, hw⟩ ⟨u, hu⟩ hdw hdu hpw
  obtain ⟨hp', _, hr₁, hr₂, E⟩ := equivalent_rounding_paste ty tz (hround hq hz.dim_a hpq)
    (hround hr hz.dim_b hpr)
  have hd : k + 1 < ((cond γ (y.paste z (k + 1) hp) u).paste (cond γ u (y.paste z (k + 1) hp)) k
      hpu).dim := by
    rw [dim_paste_cond, dim_paste, hy.dim_h, hz.dim_h, hdu]; omega
  exact ⟨hpy, hpz, hp', (e.rounding hd).isRound_iff.2 hr₂, hr₁,
    equivalent_trans (equivalent_of_equiv (v := ⟨_, hr₂⟩) (e.rounding hd)) (equivalent_symm E)⟩

theorem equivalent_paste_rounding {c w : PastingDiagram X} (hcw : c.Pastable w (k + 1))
    (hr : (c.paste w (k + 1) hcw).IsRound) (hdc : c.dim = k + 1 + 1) (hdw : w.dim = k + 1 + 1) :
    ∃ (hp : c.Pastable (w.rounding (k + 1)) (k + 1))
      (hr' : (c.paste (w.rounding (k + 1)) (k + 1) hp).IsRound),
      Equivalent ⟨_, hr'⟩ ⟨_, hr⟩ := by
  have hd : (c.paste w (k + 1) hcw).dim = k + 1 + 1 := by rw [dim_paste, hdc, hdw, max_self]
  have hb : ((c.paste w (k + 1) hcw).boundary (k + 1) true).Equiv (w.boundary (k + 1) true) :=
    equiv_boundary_paste hcw true
  have hv : (w.boundary (k + 1) true).IsRound :=
    hb.isRound_iff.1 (isRound_boundary_of_isRound hr _ _)
  have hdv : (w.boundary (k + 1) true).unit.dim = k + 1 + 1 := by
    rw [dim_unit, dim_boundary w (by omega) true]
  have h₂ : (c.paste w (k + 1) hcw).Pastable (w.boundary (k + 1) true).unit (k + 1) :=
    ⟨hb.trans (boundary_unit (dim_boundary w (by omega) true) false).symm,
      lt_min (by rw [hd]; omega) (by rw [hdv]; omega)⟩
  obtain ⟨_, h₄, e⟩ := equiv_paste_assoc hcw h₂
  have hp : c.Pastable (w.rounding (k + 1)) (k + 1) := by rw [rounding_eq (by omega)]; exact h₄
  have e' : (c.paste (w.rounding (k + 1)) (k + 1) hp).Equiv
      ((c.paste w (k + 1) hcw).paste (w.boundary (k + 1) true).unit (k + 1) h₂) :=
    (Equiv.paste (.refl _) (by rw [rounding_eq (by omega : k + 1 < w.dim)]) hp h₄).trans e.symm
  have hr₂ := isRound_paste_of_round true (u := (w.boundary (k + 1) true).unit)
    (x := c.paste w (k + 1) hcw) h₂ (isRound_unit hv) hdv hd.le
  exact ⟨hp, e'.isRound_iff.2 hr₂, equivalent_trans (equivalent_of_equiv (v := ⟨_, hr₂⟩) e')
    (equivalent_symm (equivalent_paste_unit_of_equiv true ⟨_, hr⟩ hd hb h₂ hr₂))⟩

theorem equivalent_rounding_paste_round {w : PastingDiagram X} {c : RoundPastingDiagram X}
    (hwc : w.Pastable c.toPastingDiagram (k + 1)) (hr : (w.paste c.toPastingDiagram (k + 1)
      hwc).IsRound) (hdc : c.dim = k + 1 + 1) (hdw : w.dim = k + 1 + 1) :
    ∃ (hp : (w.rounding (k + 1)).Pastable c.toPastingDiagram (k + 1))
      (hr' : ((w.rounding (k + 1)).paste c.toPastingDiagram (k + 1) hp).IsRound),
      Equivalent ⟨_, hr'⟩ ⟨_, hr⟩ := by
  have hw₁ := pastable_unit_boundary (by omega : k + 1 < w.dim)
  have hdv : (w.boundary (k + 1) true).unit.dim = k + 1 + 1 := by
    rw [dim_unit, dim_boundary w (by omega) true]
  have hp : (w.rounding (k + 1)).Pastable c.toPastingDiagram (k + 1) :=
    ⟨((by rw [rounding_eq (by omega : k + 1 < w.dim)] : (w.rounding (k + 1)).Equiv _).boundary
      (k + 1) true).trans ((equiv_boundary_paste hw₁ true).trans
        ((boundary_unit (dim_boundary w (by omega) true) true).trans hwc.1)),
      lt_min (by rw [rounding_eq (by omega), dim_paste, hdv]; omega) (by rw [hdc]; omega)⟩
  have hp₁ : (w.paste (w.boundary (k + 1) true).unit (k + 1) hw₁).Pastable c.toPastingDiagram
      (k + 1) := by rw [← rounding_eq (by omega : k + 1 < w.dim)]; exact hp
  obtain ⟨h₃, h₄, e⟩ := equiv_paste_assoc hw₁ hp₁
  have e₀ : ((w.rounding (k + 1)).paste c.toPastingDiagram (k + 1) hp).Equiv
      ((w.paste (w.boundary (k + 1) true).unit (k + 1) hw₁).paste c.toPastingDiagram (k + 1)
        hp₁) :=
    Equiv.paste (by rw [rounding_eq (by omega : k + 1 < w.dim)]) (.refl _) hp hp₁
  have hUc : ((w.boundary (k + 1) true).unit.paste c.toPastingDiagram (k + 1) h₃).IsRound :=
    isRound_paste_of_round true (u := c.toPastingDiagram) (x := (w.boundary (k + 1) true).unit)
      h₃ c.isRound hdc hdv.le
  have E₁ : Equivalent ⟨_, hUc⟩ c := equivalent_symm (equivalent_paste_unit_of_equiv false c hdc
    (hwc.1.symm) _ _)
  have hr' := (e₀.trans e).isRound_iff.2 (isRound_paste_of_round true
    (u := (w.boundary (k + 1) true).unit.paste c.toPastingDiagram (k + 1) h₃) (x := w) h₄ hUc
    (by rw [dim_paste, hdv, hdc, max_self]) hdw.le)
  exact ⟨hp, hr', equivalent_trans (equivalent_of_equiv (v := ⟨_, (e₀.trans e).isRound_iff.1 hr'⟩)
    (e₀.trans e)) (equivalent_paste_side true (c := w) E₁ (by rw [hdw, dim_paste, hdv, hdc,
      max_self]) h₄ hwc _ hr)⟩

end Absorb

namespace RoundBicat

variable {n : ℕ} {a b c : RoundBicat X n}

theorem whiskerLeft_comp (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    whiskerLeft f (η ≫ θ) = whiskerLeft f η ≫ whiskerLeft f θ := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨s, rfl⟩ := homMk_surjective θ
  rw [homMk_comp_homMk, whiskerLeft_homMk, whiskerLeft_homMk, whiskerLeft_homMk,
    homMk_comp_homMk, homMk_eq_homMk_iff]
  obtain ⟨_, _, _, _, _, E⟩ := equivalent_rounding_paste_cond_paste false f.rep.diag.isRound
    f.rep.hasBdry.dim_h (t.hasBdry g.mem_rep h.mem_rep) (s.hasBdry h.mem_rep i.mem_rep)
    h.mem_rep.isRound i.mem_rep.isRound (t.pastable s)
    (f.mem_rep.pastable_left (t.comp s).dim_diag (t.comp s).source)
  exact E

theorem comp_whiskerRight {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    whiskerRight (η ≫ θ) i = whiskerRight η i ≫ whiskerRight θ i := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨s, rfl⟩ := homMk_surjective θ
  rw [homMk_comp_homMk, homMk_whiskerRight, homMk_whiskerRight, homMk_whiskerRight,
    homMk_comp_homMk, homMk_eq_homMk_iff]
  obtain ⟨_, _, _, _, _, E⟩ := equivalent_rounding_paste_cond_paste true i.rep.diag.isRound
    i.rep.hasBdry.dim_h (t.hasBdry f.mem_rep g.mem_rep) (s.hasBdry g.mem_rep h.mem_rep)
    g.mem_rep.isRound h.mem_rep.isRound (t.pastable s)
    (i.mem_rep.pastable_right (t.comp s).dim_diag (t.comp s).target)
  exact E

theorem whiskerLeft_id (f : a ⟶ b) (g : b ⟶ c) : whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := by
  have : IsIso (whiskerLeft f (𝟙 g)) := by
    rw [id_eq_homMk, whiskerLeft_homMk, isIso_homMk_iff]
    exact mem_equivalences_rounding_paste_cond false f.rep.diag.isRound f.rep.hasBdry.dim_h
      (x := (Cell.unitOf g.mem_rep g.mem_rep).diag) (unit_mem_equivalences g.rep.diag)
      ((Cell.unitOf g.mem_rep g.mem_rep).hasBdry g.mem_rep g.mem_rep) _ _
  exact (cancel_epi (whiskerLeft f (𝟙 g))).1 (by
    rw [← whiskerLeft_comp, Category.id_comp, Category.comp_id])

theorem id_whiskerRight (f : a ⟶ b) (g : b ⟶ c) : whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := by
  have : IsIso (whiskerRight (𝟙 f) g) := by
    rw [id_eq_homMk, homMk_whiskerRight, isIso_homMk_iff]
    exact mem_equivalences_rounding_paste_cond true g.rep.diag.isRound g.rep.hasBdry.dim_h
      (x := (Cell.unitOf f.mem_rep f.mem_rep).diag) (unit_mem_equivalences f.rep.diag)
      ((Cell.unitOf f.mem_rep f.mem_rep).hasBdry f.mem_rep f.mem_rep) _ _
  exact (cancel_epi (whiskerRight (𝟙 f) g)).1 (by
    rw [← comp_whiskerRight, Category.id_comp, Category.comp_id])

private theorem equivalent_unitor_naturality (α : Bool) {x y : PastingDiagram X}
    (hx : IsRoundIn ⟨n, a.diag.toPastingDiagram, b.diag.toPastingDiagram⟩ x)
    (hy : IsRoundIn ⟨n, a.diag.toPastingDiagram, b.diag.toPastingDiagram⟩ y)
    {t : RoundPastingDiagram X} (ht : HasBdry false (n + 1) t.toPastingDiagram x y) :
    ∃ (hq₁ : ((cond α (unitCtx α a b) .id).app t.toPastingDiagram).Pastable
        ((unitorSpec α a b).fam y) (n + 1))
      (hq₂ : ((unitorSpec α a b).fam x).Pastable
        ((cond α .id (unitCtx α a b)).app t.toPastingDiagram) (n + 1))
      (hr₁ : (((cond α (unitCtx α a b) .id).app t.toPastingDiagram).paste
        ((unitorSpec α a b).fam y) (n + 1) hq₁).IsRound)
      (hr₂ : (((unitorSpec α a b).fam x).paste
        ((cond α .id (unitCtx α a b)).app t.toPastingDiagram) (n + 1) hq₂).IsRound),
      Equivalent ⟨_, hr₁⟩ ⟨_, hr₂⟩ := by
  have h := isCylTriple_unitorSpec α hx
  have h' := h.next hx hy
  have htin : IsRoundIn (RoundHom.ofIsRoundIn hx hy) t.toPastingDiagram :=
    ⟨⟨by change n + 1 < t.dim; rw [ht.dim_h]; omega, ht.side, ht.other⟩, ht.dim_h, t.isRound⟩
  obtain ⟨_, he, hb⟩ := h'.valid.comp t.toPastingDiagram htin
  have rF := (h'.valid.ctxF.isRoundIn htin).isRound
  have rG := (h'.valid.ctxG.isRoundIn htin).isRound
  have hE := equivalent_of_mem_equivalences_cond false (u := ⟨_, rF⟩) (v := ⟨_, rG⟩) he hb.dim_a
    hb.dim_b hb.dim_h hb.side hb.other
  have hin : InHom hx.roundHom.toPdHom t.toPastingDiagram :=
    htin.inHom.of_inHom_succ hx.inHom hy.inHom
  have LF := h.valid.ctxF.typed.ctxLaws
  have LG := h.valid.ctxG.typed.ctxLaws
  obtain ⟨-, -, hcy⟩ := h.valid.comp y hy
  obtain ⟨-, -, hcx⟩ := h.valid.comp x hx
  have hdy : ((unitorSpec α a b).fam y).dim = n + 1 + 1 := hcy.dim_h
  have hdx : ((unitorSpec α a b).fam x).dim = n + 1 + 1 := hcx.dim_h
  have hdt : n + 1 < t.dim := by rw [ht.dim_h]; omega
  have hq₁ : ((cond α (unitCtx α a b) .id).app t.toPastingDiagram).Pastable
      ((unitorSpec α a b).fam y) (n + 1) :=
    ⟨(LF.boundary _ hin (Nat.lt_succ_self n) hdt true).trans
      ((CtxExpr.app_equiv _ ht.other).trans hcy.side.symm),
      lt_min (by rw [LF.dim_eq _ hin, ht.dim_h]; omega) (by rw [hdy]; omega)⟩
  have hq₂ : ((unitorSpec α a b).fam x).Pastable
      ((cond α .id (unitCtx α a b)).app t.toPastingDiagram) (n + 1) :=
    ⟨hcx.other.trans ((LG.boundary _ hin (Nat.lt_succ_self n) hdt false).trans
      (CtxExpr.app_equiv _ ht.side)).symm,
      lt_min (by rw [hdx]; omega) (by rw [LG.dim_eq _ hin, ht.dim_h]; omega)⟩
  have e₁ := CtxExpr.paste_app true hq₁
  have e₂ := CtxExpr.paste_app false hq₂
  exact ⟨hq₁, hq₂, e₁.isRound_iff.1 rF, e₂.isRound_iff.1 rG,
    equivalent_trans (equivalent_of_equiv (v := ⟨_, rF⟩) e₁.symm)
      (equivalent_trans hE (equivalent_of_equiv (u := ⟨_, rG⟩) e₂))⟩

private theorem unitCtx_app_equiv (α : Bool) {f g : a ⟶ b} (t : Cell f g) :
    ((unitCtx α a b).app t.diag.toPastingDiagram).Equiv
      ((cond α t.diag.toPastingDiagram
          (𝟙 (cond α b a) : cond α b a ⟶ cond α b a).rep.diag.toPastingDiagram).paste
        (cond α (𝟙 (cond α b a) : cond α b a ⟶ cond α b a).rep.diag.toPastingDiagram
          t.diag.toPastingDiagram) n
        (by cases α; exacts [(Hom.mem_rep _).pastable_left t.dim_diag t.source,
          (Hom.mem_rep _).pastable_right t.dim_diag t.target])) := by
  have hz := dim_cond_diag α a b
  have hs : (t.diag.boundary n α).Equiv (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram) :=
    t.equiv_boundary α
  have hp := Pastable.of_side α (hs.trans (boundary_unit hz (!α)).symm)
    (by rw [t.dim_diag]; omega) (by rw [dim_unit, hz]; omega)
  refine (CtxExpr.sidePaste_equiv_paste α (Within.image_refl _) _ hs hp).trans ?_
  have e : (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit.Equiv
      (𝟙 (cond α b a) : cond α b a ⟶ cond α b a).rep.diag.toPastingDiagram := by
    cases α
    · exact (Hom.mem_id a).equiv (Hom.mem_rep _)
    · exact (Hom.mem_id b).equiv (Hom.mem_rep _)
  exact Equiv.paste ((PastingDiagram.Equiv.refl _).cond α e) (e.cond α (.refl _)) _ _

theorem homMk_comp_leftUnitor {f g : a ⟶ b} (t : Cell f g) :
    homMk t ≫ homMk (Cell.leftUnitor g) =
      homMk (Cell.leftUnitor f) ≫ whiskerLeft (𝟙 a) (homMk t) := by
  rw [whiskerLeft_homMk, homMk_comp_homMk, homMk_comp_homMk, homMk_eq_homMk_iff]
  obtain ⟨_, hq₂, _, hr₂, E⟩ := equivalent_unitor_naturality false f.mem_rep.isRoundIn
    g.mem_rep.isRoundIn (t.hasBdry f.mem_rep g.mem_rep)
  refine equivalent_trans E ?_
  have ew := unitCtx_app_equiv false t
  have hcw := hq₂.of_equiv (.refl _) ew
  have e := Equiv.paste (.refl _) ew hq₂ hcw
  obtain ⟨_, _, E'⟩ := equivalent_paste_rounding hcw (e.isRound_iff.1 hr₂)
    (Cell.leftUnitor f).dim_diag
    (by rw [dim_paste_cond, t.dim_diag, (Hom.rep _).hasBdry.dim_h]; omega)
  exact equivalent_trans (equivalent_of_equiv (v := ⟨_, e.isRound_iff.1 hr₂⟩) e)
    (equivalent_symm E')

theorem homMk_whiskerRight_comp_rightUnitor {f g : a ⟶ b} (t : Cell f g) :
    whiskerRight (homMk t) (𝟙 b) ≫ homMk (Cell.rightUnitor g) =
      homMk (Cell.rightUnitor f) ≫ homMk t := by
  rw [homMk_whiskerRight, homMk_comp_homMk, homMk_comp_homMk, homMk_eq_homMk_iff]
  obtain ⟨hq₁, _, hr₁, _, E⟩ := equivalent_unitor_naturality true f.mem_rep.isRoundIn
    g.mem_rep.isRoundIn (t.hasBdry f.mem_rep g.mem_rep)
  have ew := unitCtx_app_equiv true t
  have hwc := hq₁.of_equiv ew (.refl _)
  have e := Equiv.paste ew (.refl _) hq₁ hwc
  obtain ⟨_, _, E'⟩ := equivalent_rounding_paste_round (c := (Cell.rightUnitor g).diag) hwc
    (e.isRound_iff.1 hr₁) (Cell.rightUnitor g).dim_diag
    (by rw [dim_paste_cond, t.dim_diag, (Hom.rep _).hasBdry.dim_h]; omega)
  exact equivalent_trans E' (equivalent_trans (equivalent_of_equiv (u := ⟨_, e.isRound_iff.1 hr₁⟩)
    e.symm) E)

theorem id_whiskerLeft {f g : a ⟶ b} (η : f ⟶ g) :
    whiskerLeft (𝟙 a) η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [leftUnitor, leftUnitor, Iso.symm_hom, Iso.symm_inv, asIso_inv, asIso_hom,
    IsIso.eq_inv_comp]
  exact (homMk_comp_leftUnitor t).symm

theorem whiskerRight_id {f g : a ⟶ b} (η : f ⟶ g) :
    whiskerRight η (𝟙 b) = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  rw [rightUnitor, rightUnitor, asIso_inv, asIso_hom, ← Category.assoc, IsIso.eq_comp_inv]
  exact homMk_whiskerRight_comp_rightUnitor t

end RoundBicat

end Atoms.Diagrammatic
