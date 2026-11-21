import Atoms.Diagrammatic.Context.RoundBicategoryAxioms
import Atoms.Molecule.Cylinder.PasteUnit

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Bicategory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace RoundBicat

variable {n : ℕ} {a b c d e : RoundBicat X n}

theorem homMk_eq_eqToHom_comp_homMk_comp_eqToHom {f f' g g' : a ⟶ b} (hf : f = f')
    (hg : g = g') (t : Cell f g) (t' : Cell f' g') (h : Equivalent t.diag t'.diag) :
    homMk t = eqToHom hf ≫ homMk t' ≫ eqToHom hg.symm := by
  subst hf hg
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id, homMk_eq_homMk_iff]
  exact h

theorem homMk_unit_of_mem {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x) :
    homMk (Cell.unitOf hx hx) = 𝟙 f := by
  rw [id_eq_homMk, homMk_eq_homMk_iff]
  exact equivalent_of_equiv (Equiv.unit (hx.equiv f.mem_rep))

theorem eqToHom_eq_homMk_unit {f g : a ⟶ b} (hfg : f = g) {x : PastingDiagram X}
    (hx : f.Mem x) : eqToHom hfg = homMk (Cell.unitOf hx (hfg ▸ hx)) := by
  subst hfg
  exact (homMk_unit_of_mem hx).symm

theorem homMk_whiskerLeftOf_congr {f : a ⟶ b} {g h : b ⟶ c} {x x' w w' : PastingDiagram X}
    (hx : f.Mem x) (hx' : f.Mem x') (hww : w.Equiv w') (hw : w.dim = n + 1 + 1)
    (hs : g.Mem (w.boundary (n + 1) false)) (ht : h.Mem (w.boundary (n + 1) true))
    (hw' : w'.dim = n + 1 + 1) (hs' : g.Mem (w'.boundary (n + 1) false))
    (ht' : h.Mem (w'.boundary (n + 1) true)) :
    homMk (Cell.whiskerLeftOf hx w hw hs ht) = homMk (Cell.whiskerLeftOf hx' w' hw' hs' ht') := by
  rw [homMk_eq_homMk_iff]
  refine equivalent_of_equiv (Equiv.rounding (Equiv.paste (hx.equiv hx') hww _ _) ?_)
  rw [dim_paste, hw]; omega

theorem homMk_whiskerRightOf_congr {f g : a ⟶ b} {h : b ⟶ c} {z z' w w' : PastingDiagram X}
    (hz : h.Mem z) (hz' : h.Mem z') (hww : w.Equiv w') (hw : w.dim = n + 1 + 1)
    (hs : f.Mem (w.boundary (n + 1) false)) (ht : g.Mem (w.boundary (n + 1) true))
    (hw' : w'.dim = n + 1 + 1) (hs' : f.Mem (w'.boundary (n + 1) false))
    (ht' : g.Mem (w'.boundary (n + 1) true)) :
    homMk (Cell.whiskerRightOf w hw hs ht hz) = homMk (Cell.whiskerRightOf w' hw' hs' ht' hz') := by
  rw [homMk_eq_homMk_iff]
  refine equivalent_of_equiv (Equiv.rounding (Equiv.paste hww (hz.equiv hz') _ _) ?_)
  rw [dim_paste, hw]; omega

private theorem whiskerLeft_homMk_eq {f : a ⟶ b} {g h : b ⟶ c} {x : PastingDiagram X}
    (hx : f.Mem x) (t : Cell g h) :
    whiskerLeft f (homMk t) = homMk (Cell.whiskerLeftOf hx _ t.dim_diag t.source t.target) :=
  (whiskerLeft_homMk f t).trans (homMk_whiskerLeftOf_congr _ _ (.refl _) _ _ _ _ _ _)

private theorem homMk_whiskerRight_eq {f g : a ⟶ b} {h : b ⟶ c} {z : PastingDiagram X}
    (hz : h.Mem z) (t : Cell f g) :
    whiskerRight (homMk t) h = homMk (Cell.whiskerRightOf _ t.dim_diag t.source t.target hz) :=
  (homMk_whiskerRight t h).trans (homMk_whiskerRightOf_congr _ _ (.refl _) _ _ _ _ _ _)

theorem homMk_whiskerLeftOf_rounding {f : a ⟶ b} {g h : b ⟶ c} {x w : PastingDiagram X}
    (hx : f.Mem x) (hw : w.dim = n + 1 + 1) (hs : g.Mem (w.boundary (n + 1) false))
    (ht : h.Mem (w.boundary (n + 1) true)) (hw' : (w.rounding (n + 1)).dim = n + 1 + 1)
    (hs' : g.Mem ((w.rounding (n + 1)).boundary (n + 1) false))
    (ht' : h.Mem ((w.rounding (n + 1)).boundary (n + 1) true)) :
    homMk (Cell.whiskerLeftOf hx _ hw' hs' ht') = homMk (Cell.whiskerLeftOf hx w hw hs ht) := by
  have hk : n + 1 < w.dim := by omega
  have hp := pastable_unit_boundary hk
  have e : (w.rounding (n + 1)).Equiv (w.paste (w.boundary (n + 1) true).unit (n + 1) hp) := by
    rw [rounding_eq hk]
  have hd := dim_eq_of_equiv e
  obtain ⟨_, _, _, _, _, E⟩ := equivalent_rounding_paste_cond_paste false hx.isRound hx.dim_eq
    ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩ (hasType_unit ht.dim_eq) ht.isRound ht.isRound hp
    (hx.pastable_left (hd ▸ hw') (hs'.of_equiv (e.boundary _ false)))
  rw [homMk_whiskerLeftOf_congr hx hx e hw' hs' ht' (hd ▸ hw') (hs'.of_equiv (e.boundary _ false))
    (ht'.of_equiv (e.boundary _ true)), (homMk_eq_homMk_iff _
      ((Cell.whiskerLeftOf hx w hw hs ht).comp (Cell.whiskerLeftOf hx _
        (Cell.unitOf ht ht).dim_diag (Cell.unitOf ht ht).source (Cell.unitOf ht ht).target))).2 E,
    ← homMk_comp_homMk, ← whiskerLeft_homMk_eq, homMk_unit_of_mem, whiskerLeft_id,
    Category.comp_id]

theorem homMk_whiskerRightOf_rounding {f g : a ⟶ b} {h : b ⟶ c} {z w : PastingDiagram X}
    (hz : h.Mem z) (hw : w.dim = n + 1 + 1) (hs : f.Mem (w.boundary (n + 1) false))
    (ht : g.Mem (w.boundary (n + 1) true)) (hw' : (w.rounding (n + 1)).dim = n + 1 + 1)
    (hs' : f.Mem ((w.rounding (n + 1)).boundary (n + 1) false))
    (ht' : g.Mem ((w.rounding (n + 1)).boundary (n + 1) true)) :
    homMk (Cell.whiskerRightOf _ hw' hs' ht' hz) = homMk (Cell.whiskerRightOf w hw hs ht hz) := by
  have hk : n + 1 < w.dim := by omega
  have hp := pastable_unit_boundary hk
  have e : (w.rounding (n + 1)).Equiv (w.paste (w.boundary (n + 1) true).unit (n + 1) hp) := by
    rw [rounding_eq hk]
  have hd := dim_eq_of_equiv e
  obtain ⟨_, _, _, _, _, E⟩ := equivalent_rounding_paste_cond_paste true hz.isRound hz.dim_eq
    ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩ (hasType_unit ht.dim_eq) ht.isRound ht.isRound hp
    (hz.pastable_right (hd ▸ hw') (ht'.of_equiv (e.boundary _ true)))
  rw [homMk_whiskerRightOf_congr hz hz e hw' hs' ht' (hd ▸ hw') (hs'.of_equiv (e.boundary _ false))
    (ht'.of_equiv (e.boundary _ true)), (homMk_eq_homMk_iff _
      ((Cell.whiskerRightOf w hw hs ht hz).comp (Cell.whiskerRightOf _ (Cell.unitOf ht ht).dim_diag
        (Cell.unitOf ht ht).source (Cell.unitOf ht ht).target hz))).2 E,
    ← homMk_comp_homMk, ← homMk_whiskerRight_eq, homMk_unit_of_mem, id_whiskerRight,
    Category.comp_id]

private theorem exists_mem_paste_left {f : a ⟶ b} {g h : b ⟶ c} {x w : PastingDiagram X}
    (hx : f.Mem x) (hw : w.dim = n + 1 + 1) (hs : g.Mem (w.boundary (n + 1) false))
    (ht : h.Mem (w.boundary (n + 1) true)) :
    ∃ hp : x.Pastable w n, (x.paste w n hp).dim = n + 1 + 1 ∧
      (f ≫ g).Mem ((x.paste w n hp).boundary (n + 1) false) ∧
      (f ≫ h).Mem ((x.paste w n hp).boundary (n + 1) true) := by
  obtain ⟨hp₀, hp₁, hb⟩ := HasBdry.paste_cond false hx.dim_eq
    ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩ (hx.pastable_left hw hs)
  exact ⟨hx.pastable_left hw hs, hb.dim_h, (hx.comp hs hp₀).of_equiv hb.side.symm,
    (hx.comp ht hp₁).of_equiv hb.other.symm⟩

private theorem exists_mem_paste_right {f g : a ⟶ b} {h : b ⟶ c} {z w : PastingDiagram X}
    (hz : h.Mem z) (hw : w.dim = n + 1 + 1) (hs : f.Mem (w.boundary (n + 1) false))
    (ht : g.Mem (w.boundary (n + 1) true)) :
    ∃ hp : w.Pastable z n, (w.paste z n hp).dim = n + 1 + 1 ∧
      (f ≫ h).Mem ((w.paste z n hp).boundary (n + 1) false) ∧
      (g ≫ h).Mem ((w.paste z n hp).boundary (n + 1) true) := by
  obtain ⟨hp₀, hp₁, hb⟩ := HasBdry.paste_cond true hz.dim_eq
    ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩ (hz.pastable_right hw ht)
  exact ⟨hz.pastable_right hw ht, hb.dim_h, (hs.comp hz hp₀).of_equiv hb.side.symm,
    (ht.comp hz hp₁).of_equiv hb.other.symm⟩

private theorem pastable_rep (f : a ⟶ b) (g : b ⟶ c) :
    f.rep.diag.Pastable g.rep.diag.toPastingDiagram n :=
  f.rep.hasBdry.pastable g.rep.hasBdry (.refl _)

theorem comp_whiskerLeft (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    whiskerLeft (f ≫ g) η = eqToHom (assoc f g h) ≫ whiskerLeft f (whiskerLeft g η) ≫
      eqToHom (assoc f g h').symm := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨hp, hw, hs, ht⟩ := exists_mem_paste_left g.mem_rep t.dim_diag t.source t.target
  have key : whiskerLeft f (whiskerLeft g (homMk t)) =
      homMk (Cell.whiskerLeftOf f.mem_rep _ hw hs ht) := by
    rw [whiskerLeft_homMk, whiskerLeft_homMk]
    exact homMk_whiskerLeftOf_rounding _ _ _ _ _ _ _
  have hxy := f.mem_rep.comp g.mem_rep (pastable_rep f g)
  have hq := hxy.pastable_left t.dim_diag t.source
  obtain ⟨_, h₄, e⟩ := equiv_paste_assoc (pastable_rep f g) hq
  rw [key, whiskerLeft_homMk_eq hxy]
  refine homMk_eq_eqToHom_comp_homMk_comp_eqToHom (assoc f g h) (assoc f g h') _ _
    (equivalent_of_equiv ?_)
  exact Equiv.rounding (e.trans (Equiv.paste (.refl _) (.refl _) h₄
    (f.mem_rep.pastable_left hw hs)))
    (by rw [dim_paste, t.dim_diag]; omega)

theorem whiskerRight_comp {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    whiskerRight η (g ≫ h) = eqToHom (assoc f g h).symm ≫ whiskerRight (whiskerRight η g) h ≫
      eqToHom (assoc f' g h) := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨hp, hw, hs, ht⟩ := exists_mem_paste_right g.mem_rep t.dim_diag t.source t.target
  have key : whiskerRight (whiskerRight (homMk t) g) h =
      homMk (Cell.whiskerRightOf _ hw hs ht h.mem_rep) := by
    rw [homMk_whiskerRight, homMk_whiskerRight]
    exact homMk_whiskerRightOf_rounding _ _ _ _ _ _ _
  have hyz := g.mem_rep.comp h.mem_rep (pastable_rep g h)
  have hq := hyz.pastable_right t.dim_diag t.target
  obtain ⟨h₃, h₄, e⟩ := equiv_paste_assoc hp (h.mem_rep.pastable_right hw ht)
  rw [key, homMk_whiskerRight_eq hyz]
  refine homMk_eq_eqToHom_comp_homMk_comp_eqToHom (assoc f g h).symm (assoc f' g h).symm _ _
    (equivalent_of_equiv ?_)
  exact Equiv.rounding ((Equiv.paste (.refl _) (.refl _) hq h₄).trans e.symm)
    (by rw [dim_paste, t.dim_diag]; omega)

theorem whisker_assoc (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    whiskerRight (whiskerLeft f η) h =
      eqToHom (assoc f g h) ≫ whiskerLeft f (whiskerRight η h) ≫ eqToHom (assoc f g' h).symm := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨hp, hw, hs, ht⟩ := exists_mem_paste_left f.mem_rep t.dim_diag t.source t.target
  obtain ⟨hq, hw', hs', ht'⟩ := exists_mem_paste_right h.mem_rep t.dim_diag t.source t.target
  have key₁ : whiskerRight (whiskerLeft f (homMk t)) h =
      homMk (Cell.whiskerRightOf _ hw hs ht h.mem_rep) := by
    rw [whiskerLeft_homMk, homMk_whiskerRight]
    exact homMk_whiskerRightOf_rounding _ _ _ _ _ _ _
  have key₂ : whiskerLeft f (whiskerRight (homMk t) h) =
      homMk (Cell.whiskerLeftOf f.mem_rep _ hw' hs' ht') := by
    rw [homMk_whiskerRight, whiskerLeft_homMk]
    exact homMk_whiskerLeftOf_rounding _ _ _ _ _ _ _
  obtain ⟨_, h₄, e⟩ := equiv_paste_assoc hp (h.mem_rep.pastable_right hw ht)
  rw [key₁, key₂]
  refine homMk_eq_eqToHom_comp_homMk_comp_eqToHom (assoc f g h) (assoc f g' h) _ _
    (equivalent_of_equiv ?_)
  exact Equiv.rounding (e.trans (Equiv.paste (.refl _) (.refl _) h₄
    (f.mem_rep.pastable_left hw' hs'))) (by rw [dim_paste, dim_paste, t.dim_diag]; omega)

private theorem hasBdry_of_mem {f g : a ⟶ b} {w : PastingDiagram X} (hw : w.dim = n + 1 + 1)
    (hs : f.Mem (w.boundary (n + 1) false)) (ht : g.Mem (w.boundary (n + 1) true)) :
    HasBdry false (n + 1) w (w.boundary (n + 1) false) (w.boundary (n + 1) true) :=
  ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩

private theorem equivalent_comp_rounding {f g h : a ⟶ b} {y z : PastingDiagram X}
    (hy : y.dim = n + 1 + 1) (hys : f.Mem (y.boundary (n + 1) false))
    (hyt : g.Mem (y.boundary (n + 1) true)) (hz : z.dim = n + 1 + 1)
    (hzs : g.Mem (z.boundary (n + 1) false)) (hzt : h.Mem (z.boundary (n + 1) true))
    (t : Cell f g) (s : Cell g h) (et : t.diag.toPastingDiagram.Equiv (y.rounding (n + 1)))
    (es : s.diag.toPastingDiagram.Equiv (z.rounding (n + 1))) :
    ∃ (hp : y.Pastable z (n + 1)) (hr : ((y.paste z (n + 1) hp).rounding (n + 1)).IsRound),
      Equivalent (t.comp s).diag ⟨_, hr⟩ := by
  obtain ⟨hq, hp, hr₁, hr₂, E⟩ := equivalent_rounding_paste (hasBdry_of_mem hy hys hyt)
    ((hasBdry_of_mem hz hzs hzt).of_equiv_side (hzs.equiv hyt)) hyt.isRound hzt.isRound
  refine ⟨hp, hr₂, equivalent_trans (equivalent_of_equiv ?_) E⟩
  exact Equiv.paste et es (t.pastable s) hq

theorem whisker_exchange {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i) :
    whiskerLeft f θ ≫ whiskerRight η i = whiskerRight η h ≫ whiskerLeft g θ := by
  obtain ⟨t, rfl⟩ := homMk_surjective η
  obtain ⟨s, rfl⟩ := homMk_surjective θ
  rw [whiskerLeft_homMk_eq t.source, homMk_whiskerRight_eq s.target,
    homMk_whiskerRight_eq s.source, whiskerLeft_homMk_eq t.target, homMk_comp_homMk,
    homMk_comp_homMk, homMk_eq_homMk_iff]
  have hdt : n + 1 < t.diag.dim := by rw [t.dim_diag]; omega
  have hds : n + 1 < s.diag.dim := by rw [s.dim_diag]; omega
  have hp : t.diag.Pastable s.diag.toPastingDiagram n :=
    ⟨(t.equiv_boundary true).trans (s.equiv_boundary false).symm, lt_min (by omega) (by omega)⟩
  obtain ⟨_, hw₁, hs₁, ht₁⟩ := exists_mem_paste_left t.source s.dim_diag s.source s.target
  obtain ⟨_, hw₂, hs₂, ht₂⟩ := exists_mem_paste_right s.target t.dim_diag t.source t.target
  obtain ⟨_, hw₃, hs₃, ht₃⟩ := exists_mem_paste_right s.source t.dim_diag t.source t.target
  obtain ⟨_, hw₄, hs₄, ht₄⟩ := exists_mem_paste_left t.target s.dim_diag s.source s.target
  obtain ⟨_, _, E₁⟩ := equivalent_comp_rounding hw₁ hs₁ ht₁ hw₂ hs₂ ht₂
    (Cell.whiskerLeftOf t.source _ s.dim_diag s.source s.target)
    (Cell.whiskerRightOf _ t.dim_diag t.source t.target s.target) (.refl _) (.refl _)
  obtain ⟨_, _, E₂⟩ := equivalent_comp_rounding hw₃ hs₃ ht₃ hw₄ hs₄ ht₄
    (Cell.whiskerRightOf _ t.dim_diag t.source t.target s.source)
    (Cell.whiskerLeftOf t.target _ s.dim_diag s.source s.target) (.refl _) (.refl _)
  obtain ⟨_, _, _, e₁⟩ := equiv_paste_interchange false (c := s.diag.toPastingDiagram)
    (h := t.diag.toPastingDiagram) hp hds hdt
  obtain ⟨_, _, _, e₂⟩ := equiv_paste_interchange true (c := t.diag.toPastingDiagram)
    (h := s.diag.toPastingDiagram) hp hdt hds
  refine equivalent_trans E₁ (equivalent_trans (equivalent_of_equiv ?_) (equivalent_symm E₂))
  exact Equiv.rounding (e₁.trans e₂.symm)
    (by rw [dim_eq_of_equiv e₁, dim_paste]; exact lt_max_of_lt_left hdt)

private theorem whiskerLeft_eqToHom (f : a ⟶ b) {g h : b ⟶ c} (p : g = h) :
    whiskerLeft f (eqToHom p) = eqToHom (congrArg (f ≫ ·) p) := by
  subst p
  exact whiskerLeft_id f g

private theorem eqToHom_whiskerRight {f g : a ⟶ b} (p : f = g) (h : b ⟶ c) :
    whiskerRight (eqToHom p) h = eqToHom (congrArg (· ≫ h) p) := by
  subst p
  exact id_whiskerRight f h

theorem pentagon (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e) :
    whiskerRight (eqToHom (assoc f g h)) i ≫ eqToHom (assoc f (g ≫ h) i) ≫
        whiskerLeft f (eqToHom (assoc g h i)) =
      eqToHom (assoc (f ≫ g) h i) ≫ eqToHom (assoc f g (h ≫ i)) := by
  rw [whiskerLeft_eqToHom, eqToHom_whiskerRight, eqToHom_trans, eqToHom_trans, eqToHom_trans]

end RoundBicat

private theorem boundary_le_bdryFull {x : PastingDiagram X} {n : ℕ} (hdx : x.dim = n + 1)
    (β : Bool) : x.shape.ogp.boundary ⊤ n β ≤ x.shape.ogp.bdryFull ⊤ := by
  have hk : krullDim (⊤ : LowerSet x.shape.ogp) = (n : WithBot ℕ∞) + 1 := by
    rw [LowerSet.krullDim_top, x.shape.krullDim_eq_dimension, ← dim_def, hdx]; rfl
  rw [← bdry_eq_boundary hk β]
  cases β
  · exact le_sup_left
  · exact le_sup_right

open Classical in
theorem PastingDiagram.exists_equiv_unit_paste {x y : PastingDiagram X} {n : ℕ}
    (hp : x.Pastable y n) (hx : x.IsRound) (hy : y.IsRound) (hdx : x.dim = n + 1)
    (hdy : y.dim = n + 1) :
    ∃ (h₁ : x.Pastable (cylDiagram y (y.shape.ogp.boundary ⊤ n true)) n)
      (h₂ : (cylDiagram x (x.shape.ogp.boundary ⊤ n false)).Pastable y n)
      (h₃ : (x.paste (cylDiagram y (y.shape.ogp.boundary ⊤ n true)) n h₁).Pastable
        ((cylDiagram x (x.shape.ogp.boundary ⊤ n false)).paste y n h₂) (n + 1)),
      ((x.paste (cylDiagram y (y.shape.ogp.boundary ⊤ n true)) n h₁).paste
        ((cylDiagram x (x.shape.ogp.boundary ⊤ n false)).paste y n h₂) (n + 1) h₃).Equiv
        (x.paste y n hp).unit := by
  set m := x.paste y n hp
  let wx := Within.pasteInl x y n hp
  let wy := Within.pasteInr x y n hp
  have hpst : m.shape.ogp.IsPastingIn n wx.image wy.image ⊤ := Within.isPastingIn_paste x y n hp
  have hdm : m.dim = n + 1 := by rw [dim_paste, hdx, hdy, max_self]
  have hkx : (n : WithBot ℕ∞) < krullDim wx.image := by
    rw [Within.krullDim_image, hdx]; exact_mod_cast Nat.lt_succ_self n
  have hky : (n : WithBot ℕ∞) < krullDim wy.image := by
    rw [Within.krullDim_image, hdy]; exact_mod_cast Nat.lt_succ_self n
  have rx := wx.round_image_iff.2 hx
  have ry := wy.round_image_iff.2 hy
  have hK : m.shape.ogp.bdryFull ⊤ = m.shape.ogp.boundaryFull ⊤ n := by
    have hk : krullDim (⊤ : LowerSet m.shape.ogp) = (n : WithBot ℕ∞) + 1 := by
      rw [LowerSet.krullDim_top, m.shape.krullDim_eq_dimension, ← dim_def, hdm]; rfl
    rw [OGP.bdryFull, bdry_eq_boundary hk, bdry_eq_boundary hk]; rfl
  have hfy (z : y.shape.ogp) :
      wy.emb z ∈ m.shape.ogp.bdryFull ⊤ ↔ z ∈ y.shape.ogp.boundary ⊤ n true := by
    rw [hK, mem_boundaryFull_iff_of_isPastingIn_cond true rx ry wx.isMoleculeIn_image
      wy.isMoleculeIn_image hkx hky hpst (apply_mem_map_iff _ |>.2 trivial),
      Within.boundary_image, apply_mem_map_iff]
  have hfx (z : x.shape.ogp) :
      wx.emb z ∈ m.shape.ogp.bdryFull ⊤ ↔ z ∈ x.shape.ogp.boundary ⊤ n false := by
    rw [hK, mem_boundaryFull_iff_of_isPastingIn_cond false ry rx wy.isMoleculeIn_image
      wx.isMoleculeIn_image hky hkx hpst (apply_mem_map_iff _ |>.2 trivial),
      Within.boundary_image, apply_mem_map_iff]
  have hKF : m.shape.ogp.boundary wx.image n false ≤ m.shape.ogp.bdryFull ⊤ := by
    rw [← hpst.boundary_input, hK]; exact boundary_le_boundaryFull ⊤ n false
  have hKG : m.shape.ogp.boundary wy.image n true ≤ m.shape.ogp.bdryFull ⊤ := by
    rw [← hpst.boundary_output, hK]; exact boundary_le_boundaryFull ⊤ n true
  have hdF : krullDim wx.image ≤ (n + 1 : ℕ) := by rw [Within.krullDim_image, hdx]
  have hdG : krullDim wy.image ≤ (n + 1 : ℕ) := by rw [Within.krullDim_image, hdy]
  have mF := wx.isMoleculeIn_image
  have mG := wy.isMoleculeIn_image
  have c₁ : (partialCylinder m.shape.ogp (m.shape.ogp.bdryFull ⊤)).IsPastingIn n
      (PartialCylinder.copy _ false wx.image) (PartialCylinder.over _ wy.image)
      (PartialCylinder.copy _ false wx.image ⊔ PartialCylinder.over _ wy.image) :=
    PartialCylinder.isPastingIn_copy_over_cond true mG.isGlobular hpst hKG
  have c₂ : (partialCylinder m.shape.ogp (m.shape.ogp.bdryFull ⊤)).IsPastingIn n
      (PartialCylinder.over _ wx.image) (PartialCylinder.copy _ true wy.image)
      (PartialCylinder.over _ wx.image ⊔ PartialCylinder.copy _ true wy.image) := by
    rw [sup_comm]; exact PartialCylinder.isPastingIn_copy_over_cond false mF.isGlobular hpst hKF
  have c₃ := PartialCylinder.isPastingIn_copy_sup_over_over_sup_copy hpst mF mG hdF hdG hKF hKG
  let wf := wx.trans (Within.cylCopy m (m.shape.ogp.bdryFull ⊤) false)
  let wg := wy.trans (Within.cylCopy m (m.shape.ogp.bdryFull ⊤) true)
  let wl := Within.cyl m (m.shape.ogp.bdryFull ⊤) wy hfy
  let wr := Within.cyl m (m.shape.ogp.bdryFull ⊤) wx hfx
  have hdl : (cylDiagram y (y.shape.ogp.boundary ⊤ n true)).dim = n + 1 + 1 := by
    rw [dim_cylDiagram y _ (boundary_le_bdryFull hdy true), hdy]
  have hdr : (cylDiagram x (x.shape.ogp.boundary ⊤ n false)).dim = n + 1 + 1 := by
    rw [dim_cylDiagram x _ (boundary_le_bdryFull hdx false), hdx]
  have p₁ : (cylDiagram m (m.shape.ogp.bdryFull ⊤)).shape.ogp.IsPastingIn n wf.image wl.image
      (cylImage m (PartialCylinder.copy _ false wx.image ⊔ PartialCylinder.over _ wy.image)) := by
    rw [image_trans_cylCopy, image_cyl]; exact isPastingIn_cylImage c₁
  have p₂ : (cylDiagram m (m.shape.ogp.bdryFull ⊤)).shape.ogp.IsPastingIn n wr.image wg.image
      (cylImage m (PartialCylinder.over _ wx.image ⊔ PartialCylinder.copy _ true wy.image)) := by
    rw [image_trans_cylCopy, image_cyl]; exact isPastingIn_cylImage c₂
  have h₁ := pastable_of_isPastingIn wf wl p₁ (lt_min (by omega) (by omega))
  have h₂ := pastable_of_isPastingIn wr wg p₂ (lt_min (by omega) (by omega))
  have hR₁ := isMoleculeIn_cylImage (c₁.isMoleculeIn (PartialCylinder.isMoleculeIn_copy mF false)
    (PartialCylinder.isMoleculeIn_over mG))
  have hR₂ := isMoleculeIn_cylImage (c₂.isMoleculeIn (PartialCylinder.isMoleculeIn_over mF)
    (PartialCylinder.isMoleculeIn_copy mG true))
  let W₁ := (Within.ofEquiv (equiv_paste_of_within wf wl p₁ hR₁ h₁)).trans (Within.restrictTo _ hR₁)
  let W₂ := (Within.ofEquiv (equiv_paste_of_within wr wg p₂ hR₂ h₂)).trans (Within.restrictTo _ hR₂)
  have p₃ : (cylDiagram m (m.shape.ogp.bdryFull ⊤)).shape.ogp.IsPastingIn (n + 1) W₁.image
      W₂.image ⊤ := by
    rw [Within.image_ofEquiv_trans, Within.image_restrictTo, Within.image_ofEquiv_trans,
      Within.image_restrictTo, ← cylImage_top]
    exact isPastingIn_cylImage c₃
  have h₃ := pastable_of_isPastingIn W₁ W₂ p₃
    (lt_min (by rw [dim_paste, hdl]; omega) (by rw [dim_paste, hdr]; omega))
  exact ⟨h₁, h₂, h₃, (equiv_paste_of_within W₁ W₂ p₃ _ h₃).trans (equiv_restrictTo_univ _)⟩

namespace RoundBicat

variable {n : ℕ} {a b c : RoundBicat X n}

private theorem unitorSpec_V (α : Bool) {f : a ⟶ b} {y : PastingDiagram X} (hy : f.Mem y) :
    (unitorSpec α a b).V y = y.shape.ogp.boundary ⊤ n α := by
  have hs : (y.boundary n α).Equiv (unitorSpec α a b).z := by
    cases α
    · exact hy.hasBdry.side
    · exact hy.hasBdry.other
  have h : (unitorSpec α a b).V y = occSet n α (Within.refl _) y := rfl
  rw [h, occSet_of hs, Within.image_trans, Within.image_refl, ← Within.image, image_sideWithin,
    Within.image_refl]

theorem unitorSpec_K (α : Bool) {f : a ⟶ b} {y : PastingDiagram X} (hy : f.Mem y) :
    (unitorSpec α a b).K y = y.shape.ogp.boundary ⊤ n (!α) := by
  have hs : (y.boundary n α).Equiv (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram) := by
    cases α
    · exact hy.hasBdry.side
    · exact hy.hasBdry.other
  have hfit : (unitorSpec α a b).Fits y := ⟨hy.isRound, by rw [hy.dim_eq]; exact n.lt_succ_self, hs⟩
  refine SetLike.coe_injective ((CylSpec.Fits.coe_K hfit).trans ?_)
  rw [unitorSpec_V α hy]
  exact IsRound.coe_boundaryFull_diff_interior_boundary (y.shape.isRound_iff.1 hy.isRound)
    y.shape.isMolecule hfit.lt_krullDim_top α

private theorem whiskerLeft_comp_whiskerRight_unitor (f : a ⟶ b) (g : b ⟶ c) :
    whiskerLeft f (homMk (Cell.leftUnitor g)) ≫ eqToHom (assoc f (𝟙 b) g).symm ≫
      whiskerRight (homMk (Cell.rightUnitor f)) g = 𝟙 (f ≫ g) := by
  have hp := pastable_rep f g
  obtain ⟨h₁, h₂, h₃, e⟩ := PastingDiagram.exists_equiv_unit_paste hp f.rep.diag.isRound
    g.rep.diag.isRound f.rep.hasBdry.dim_h g.rep.hasBdry.dim_h
  have el : (Cell.leftUnitor g).diag.Equiv
      (cylDiagram g.rep.diag.toPastingDiagram
        (g.rep.diag.shape.ogp.boundary ⊤ n true)) := by
    rw [Cell.leftUnitor_diag, CylSpec.fam_def, cylDiagram_congr _ (unitorSpec_K false g.mem_rep),
      Bool.not_false]
  have er : (Cell.rightUnitor f).diag.Equiv
      (cylDiagram f.rep.diag.toPastingDiagram
        (f.rep.diag.shape.ogp.boundary ⊤ n false)) := by
    rw [Cell.rightUnitor_diag, CylSpec.fam_def, cylDiagram_congr _ (unitorSpec_K true f.mem_rep),
      Bool.not_true]
  rw [whiskerLeft_homMk, homMk_whiskerRight]
  let B := Cell.whiskerRightOf _ (Cell.rightUnitor f).dim_diag (Cell.rightUnitor f).source
    (Cell.rightUnitor f).target g.mem_rep
  let B' : Cell (f ≫ 𝟙 b ≫ g) (f ≫ g) := ⟨B.diag, B.dim_diag, assoc f (𝟙 b) g ▸ B.source, B.target⟩
  have hm := f.mem_rep.comp g.mem_rep hp
  rw [homMk_eq_eqToHom_comp_homMk_comp_eqToHom (assoc f (𝟙 b) g) rfl B B' (equivalent_refl _),
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_refl, Category.comp_id,
    homMk_comp_homMk, ← homMk_unit_of_mem hm, homMk_eq_homMk_iff]
  obtain ⟨hpl, hw₁, hs₁, ht₁⟩ := exists_mem_paste_left f.mem_rep (Cell.leftUnitor g).dim_diag
    (Cell.leftUnitor g).source (Cell.leftUnitor g).target
  obtain ⟨hpr, hw₂, hs₂, ht₂⟩ := exists_mem_paste_right g.mem_rep (Cell.rightUnitor f).dim_diag
    (Cell.rightUnitor f).source (Cell.rightUnitor f).target
  obtain ⟨hq, _, E⟩ := equivalent_comp_rounding hw₁ hs₁ ht₁ hw₂ (assoc f (𝟙 b) g ▸ hs₂) ht₂
    (Cell.whiskerLeftOf f.mem_rep _ (Cell.leftUnitor g).dim_diag (Cell.leftUnitor g).source
      (Cell.leftUnitor g).target) B' (.refl _) (.refl _)
  have eP := (Equiv.paste (Equiv.paste (.refl _) el hpl h₁) (Equiv.paste er (.refl _) hpr h₂) hq
    h₃).trans e
  have hdm : (f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).dim = n + 1 := by
    rw [dim_paste, f.rep.hasBdry.dim_h, g.rep.hasBdry.dim_h, max_self]
  have hdu : n + 1 < (f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).unit.dim := by
    rw [dim_unit, hdm]; omega
  have eR : ((f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).unit.rounding (n + 1)).Equiv
      ((f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).unit.paste
        ((f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).unit.boundary (n + 1) true).unit
        (n + 1) (pastable_unit_boundary hdu)) := by
    rw [rounding_eq hdu]
  have hdu' : (f.rep.diag.paste g.rep.diag.toPastingDiagram n hp).unit.dim = n + 1 + 1 := by
    rw [dim_unit, hdm]
  have hr := eR.isRound_iff.1 (isRound_rounding hdu'
    (isRound_boundary_of_isRound (Cell.unitOf hm hm).diag.isRound _ _))
  exact equivalent_trans E (equivalent_trans (equivalent_of_equiv (v := ⟨_, hr⟩) ((eP.rounding
    (by rw [dim_eq_of_equiv eP]; exact hdu)).trans eR)) (equivalent_symm
      (equivalent_paste_unit_of_equiv true (Cell.unitOf hm hm).diag hdu' (.refl _) _ hr)))

theorem triangle (f : a ⟶ b) (g : b ⟶ c) :
    eqToHom (assoc f (𝟙 b) g) ≫ whiskerLeft f (leftUnitor g).hom =
      whiskerRight (rightUnitor f).hom g := by
  have key := whiskerLeft_comp_whiskerRight_unitor f g
  have h : whiskerLeft f (inv (homMk (Cell.leftUnitor g))) =
      eqToHom (assoc f (𝟙 b) g).symm ≫ whiskerRight (homMk (Cell.rightUnitor f)) g := by
    calc whiskerLeft f (inv (homMk (Cell.leftUnitor g)))
        = whiskerLeft f (inv (homMk (Cell.leftUnitor g))) ≫ whiskerLeft f
            (homMk (Cell.leftUnitor g)) ≫ eqToHom (assoc f (𝟙 b) g).symm ≫
              whiskerRight (homMk (Cell.rightUnitor f)) g := by rw [key, Category.comp_id]
      _ = _ := by
        rw [← Category.assoc, ← whiskerLeft_comp, IsIso.inv_hom_id, whiskerLeft_id,
          Category.id_comp]
  rw [leftUnitor_hom, rightUnitor_hom, h, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

noncomputable instance instBicategory : Bicategory.{u, u} (RoundBicat X n) where
  homCategory := homCategory
  whiskerLeft := RoundBicat.whiskerLeft
  whiskerRight := RoundBicat.whiskerRight
  associator f g h := eqToIso (assoc f g h)
  leftUnitor := RoundBicat.leftUnitor
  rightUnitor := RoundBicat.rightUnitor
  whiskerLeft_id := RoundBicat.whiskerLeft_id
  whiskerLeft_comp := RoundBicat.whiskerLeft_comp
  id_whiskerLeft := RoundBicat.id_whiskerLeft
  comp_whiskerLeft := RoundBicat.comp_whiskerLeft
  id_whiskerRight := RoundBicat.id_whiskerRight
  comp_whiskerRight := RoundBicat.comp_whiskerRight
  whiskerRight_id := RoundBicat.whiskerRight_id
  whiskerRight_comp := RoundBicat.whiskerRight_comp
  whisker_assoc := RoundBicat.whisker_assoc
  whisker_exchange := RoundBicat.whisker_exchange
  pentagon := RoundBicat.pentagon
  triangle := RoundBicat.triangle

theorem associator_hom {d : RoundBicat X n} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom = eqToHom (assoc f g h) :=
  rfl

theorem whiskerLeft_homMk_of_mem {f : a ⟶ b} {g h : b ⟶ c} {x : PastingDiagram X}
    (hx : f.Mem x) (t : Cell g h) :
    f ◁ homMk t = homMk (Cell.whiskerLeftOf hx _ t.dim_diag t.source t.target) :=
  whiskerLeft_homMk_eq hx t

theorem homMk_whiskerRight_of_mem {f g : a ⟶ b} {h : b ⟶ c} {z : PastingDiagram X}
    (hz : h.Mem z) (t : Cell f g) :
    homMk t ▷ h = homMk (Cell.whiskerRightOf _ t.dim_diag t.source t.target hz) :=
  homMk_whiskerRight_eq hz t

theorem homMk_rounding_eq_homMk_unitFirst {f g : a ⟶ b} {y : PastingDiagram X}
    (hy : y.dim = n + 1 + 1) (hp : (y.boundary (n + 1) false).unit.Pastable y (n + 1))
    (t t' : Cell f g) (et : t.diag.toPastingDiagram.Equiv (y.rounding (n + 1)))
    (et' : t'.diag.toPastingDiagram.Equiv ((y.boundary (n + 1) false).unit.paste y (n + 1) hp)) :
    homMk t = homMk t' := by
  have hk : n + 1 < y.dim := by omega
  have hq := pastable_unit_boundary hk
  have e₀ : t.diag.toPastingDiagram.Equiv (y.paste (y.boundary (n + 1) true).unit (n + 1) hq) := by
    rw [← rounding_eq hk]; exact et
  have hdb : (y.boundary (n + 1) true).dim = n + 1 := dim_boundary y hk.le true
  have hdq : (y.paste (y.boundary (n + 1) true).unit (n + 1) hq).dim = n + 1 + 1 := by
    rw [dim_paste, dim_unit, hdb, hy, max_self]
  have hdp : ((y.boundary (n + 1) false).unit.paste y (n + 1) hp).dim = n + 1 + 1 := by
    rw [dim_paste, dim_unit, dim_boundary y hk.le false, hy, max_self]
  have rR := e₀.isRound_iff.1 t.diag.isRound
  have rL := et'.isRound_iff.1 t'.diag.isRound
  have h₂ : ((y.boundary (n + 1) false).unit.paste y (n + 1) hp).Pastable
      (y.boundary (n + 1) true).unit (n + 1) :=
    ⟨(equiv_boundary_paste hp true).trans (boundary_unit hdb false).symm,
      lt_min (by omega) (by rw [dim_unit, hdb]; omega)⟩
  obtain ⟨_, h₄, e⟩ := equiv_paste_assoc hp h₂
  have hb : (y.boundary (n + 1) true).IsRound :=
    ((equiv_boundary_paste hq true).trans (boundary_unit hdb true)).isRound_iff.1
      (isRound_boundary_of_isRound rR _ _)
  have rT := isRound_paste_of_round true (u := (y.boundary (n + 1) true).unit)
    (x := (y.boundary (n + 1) false).unit.paste y (n + 1) hp) h₂ (isRound_unit hb)
    (by rw [dim_unit, hdb]) hdp.le
  have E₁ : Equivalent ⟨_, rR⟩ ⟨_, e.isRound_iff.1 rT⟩ :=
    equivalent_paste_unit_of_equiv false ⟨_, rR⟩ hdq (equiv_boundary_paste hq false) h₄ _
  have E₂ : Equivalent ⟨_, rL⟩ ⟨_, rT⟩ :=
    equivalent_paste_unit_of_equiv true ⟨_, rL⟩ hdp (equiv_boundary_paste hp true) h₂ rT
  rw [homMk_eq_homMk_iff]
  exact equivalent_trans (equivalent_of_equiv e₀) (equivalent_trans E₁ (equivalent_trans
    (equivalent_of_equiv e.symm) (equivalent_trans (equivalent_symm E₂)
      (equivalent_of_equiv et'.symm))))

private theorem equiv_fam_unitorAt (α : Bool) {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x)
    (hd : 0 < x.dim) (hb : (x.boundary (x.dim - 1) α).IsRound) :
    ((unitorSpec α a b).fam f.rep.diag.toPastingDiagram).Equiv
      (unitorAt x hd hx.isRound α (Within.refl _) (isRewritableSubmolecule_image_refl hb)) := by
  have hs : (f.rep.diag.boundary n α).Equiv (unitorSpec α a b).z := by
    cases α
    · exact f.mem_rep.hasBdry.side
    · exact f.mem_rep.hasBdry.other
  have hfit : (unitorSpec α a b).Fits f.rep.diag.toPastingDiagram :=
    ⟨f.rep.diag.isRound, by rw [f.mem_rep.dim_eq]; exact n.lt_succ_self, hs⟩
  refine (CylSpec.fam_equiv hfit (f.mem_rep.equiv hx)).trans ?_
  have hdx : x.dim - 1 = n := by rw [hx.dim_eq]; rfl
  have hk : krullDim (⊤ : LowerSet x.shape.ogp) = ((x.dim - 1 : ℕ) : WithBot ℕ∞) + 1 :=
    x.shape.krullDim_top_eq (Nat.sub_add_cancel hd).symm
  have hK : unitorSubset x hd hx.isRound α (Within.refl _) (isRewritableSubmolecule_image_refl hb) =
      x.shape.ogp.boundary ⊤ n (!α) := by
    refine SetLike.coe_injective ?_
    have hV : unitorImage x α (Within.refl (x.boundary (x.dim - 1) α)) =
        x.shape.ogp.boundary ⊤ (x.dim - 1) α := by
      rw [unitorImage, bdryOccurrence, map_comp, ← Within.image, Within.image_refl,
        MoleculeShape.map_boundaryIncl_top]
    rw [IsSubmoleculeOf.coe_hornSet, hV, OGP.bdryFull, bdry_eq_boundary hk, bdry_eq_boundary hk,
      ← hdx]
    exact IsRound.coe_boundaryFull_diff_interior_boundary (x.shape.isRound_iff.1 hx.isRound)
      x.shape.isMolecule (by rw [hk]; exact_mod_cast Nat.lt_succ_self _) α
  rw [CylSpec.fam_def, cylDiagram_congr _ (unitorSpec_K α hx), unitorAt,
    cylDiagram_congr _ hK]

theorem leftUnitor_inv_eq_homMk_of_equiv {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x)
    (hd : 0 < x.dim) (hb : (x.boundary (x.dim - 1) false).IsRound) (t : Cell f (𝟙 a ≫ f))
    (ht : t.diag.toPastingDiagram.Equiv
      (unitorAt x hd hx.isRound false (Within.refl _) (isRewritableSubmolecule_image_refl hb))) :
    (λ_ f).inv = homMk t :=
  (homMk_eq_homMk_iff _ _).2 (equivalent_of_equiv ((equiv_fam_unitorAt false hx hd hb).trans
    ht.symm))

theorem rightUnitor_hom_eq_homMk_of_equiv {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x)
    (hd : 0 < x.dim) (hb : (x.boundary (x.dim - 1) true).IsRound) (t : Cell (f ≫ 𝟙 b) f)
    (ht : t.diag.toPastingDiagram.Equiv
      (unitorAt x hd hx.isRound true (Within.refl _) (isRewritableSubmolecule_image_refl hb))) :
    (ρ_ f).hom = homMk t :=
  (homMk_eq_homMk_iff _ _).2 (equivalent_of_equiv ((equiv_fam_unitorAt true hx hd hb).trans
    ht.symm))

end RoundBicat

end Atoms.Diagrammatic
