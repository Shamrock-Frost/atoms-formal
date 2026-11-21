import Atoms.Diagrammatic.Context.NaturalRounding

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem equiv_paste_interchange (α : Bool) {c h : PastingDiagram X} {k : ℕ}
    (hp : (cond α c h).Pastable (cond α h c) k) (hdc : k + 1 < c.dim) (hdh : k + 1 < h.dim) :
    ∃ (h₁ : (cond α c (h.boundary (k + 1) false)).Pastable
        (cond α (h.boundary (k + 1) false) c) k)
      (h₂ : (cond α (c.boundary (k + 1) true) h).Pastable (cond α h (c.boundary (k + 1) true)) k)
      (h₃ : ((cond α c (h.boundary (k + 1) false)).paste
          (cond α (h.boundary (k + 1) false) c) k h₁).Pastable
        ((cond α (c.boundary (k + 1) true) h).paste (cond α h (c.boundary (k + 1) true)) k h₂)
        (k + 1)),
      (((cond α c (h.boundary (k + 1) false)).paste (cond α (h.boundary (k + 1) false) c) k
        h₁).paste ((cond α (c.boundary (k + 1) true) h).paste
          (cond α h (c.boundary (k + 1) true)) k h₂) (k + 1) h₃).Equiv
        ((cond α c h).paste (cond α h c) k hp) := by
  classical
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn α hp
  let wh := Within.pasteIn α hp
  let m := (cond α c h).paste (cond α h c) k hp
  have gC := wc.isMoleculeIn_image.isGlobular
  have gH := wh.isMoleculeIn_image.isGlobular
  have c1 := hpst.isPastingIn_sup_boundary_false α gC gH
  have c2 := hpst.isPastingIn_boundary_true_sup α gC gH
  have c3 := hpst.whisker_interchange α gC gH
  let bh := (Within.boundary h (k + 1) false).trans wh
  let bc := (Within.boundary c (k + 1) true).trans wc
  have hbh : bh.image = m.shape.ogp.boundary wh.image (k + 1) false :=
    Within.image_boundary_trans _ _ _
  have hbc : bc.image = m.shape.ogp.boundary wc.image (k + 1) true :=
    Within.image_boundary_trans _ _ _
  rw [← hbh] at c1 c3
  rw [← hbc] at c2 c3
  have hR1 := c1.isMoleculeIn (Bool.cond_rec_prop α wc.isMoleculeIn_image bh.isMoleculeIn_image)
    (Bool.cond_rec_prop α bh.isMoleculeIn_image wc.isMoleculeIn_image)
  have hR2 := c2.isMoleculeIn (Bool.cond_rec_prop α bc.isMoleculeIn_image wh.isMoleculeIn_image)
    (Bool.cond_rec_prop α wh.isMoleculeIn_image bc.isMoleculeIn_image)
  have hdhb : (h.boundary (k + 1) false).dim = k + 1 := dim_boundary h (by omega) false
  have hdcb : (c.boundary (k + 1) true).dim = k + 1 := dim_boundary c (by omega) true
  have h₁ := pastable_cond_of_isPastingIn α wc bh c1 (by omega) (by omega)
  have h₂ := pastable_cond_of_isPastingIn α bc wh c2 (by omega) (by omega)
  let W1 := (Within.ofEquiv (equiv_paste_cond_of_within α wc bh c1 hR1 h₁)).trans
    (Within.restrictTo _ hR1)
  let W2 := (Within.ofEquiv (equiv_paste_cond_of_within α bc wh c2 hR2 h₂)).trans
    (Within.restrictTo _ hR2)
  have c3' : m.shape.ogp.IsPastingIn (k + 1) W1.image W2.image ⊤ := by
    rw [Within.image_ofEquiv_trans, Within.image_restrictTo, Within.image_ofEquiv_trans,
      Within.image_restrictTo]
    exact c3
  have hd1 : k + 1 < ((cond α c (h.boundary (k + 1) false)).paste
      (cond α (h.boundary (k + 1) false) c) k h₁).dim := by
    rw [dim_paste_cond]; exact lt_max_of_lt_left hdc
  have hd2 : k + 1 < ((cond α (c.boundary (k + 1) true) h).paste
      (cond α h (c.boundary (k + 1) true)) k h₂).dim := by
    rw [dim_paste_cond]; exact lt_max_of_lt_right hdh
  have h₃ := pastable_of_isPastingIn W1 W2 c3' (lt_min hd1 hd2)
  exact ⟨h₁, h₂, h₃, PastingDiagram.Equiv.trans
    (equiv_paste_of_within W1 W2 c3' m.shape.isMolecule h₃)
    (equiv_restrictTo_univ _)⟩

noncomputable def ctxPfw (α : Bool) (H : RoundHom X) (x x' h : PastingDiagram X) : CtxTriple X :=
  ⟨H, H.setSide α (x.boundary H.k α), CtxExpr.paste α x H.k, CtxExpr.paste α x' H.k,
    fun a => ((CtxExpr.paste (!α) a H.k).app h).pasteOr ((CtxExpr.paste (!α) a H.k).app x').unit
      (H.k + 1)⟩

theorem typed_paste_not {k : ℕ} {x : PastingDiagram X} (α : Bool) {a : PastingDiagram X}
    (har : a.IsRound) (hda : a.dim = k + 1)
    (hxa : (x.boundary k (!α)).Equiv (a.boundary k α)) {q : Prop} :
    (CtxExpr.paste (!α) a k).Typed Set.univ q ⟨k, x.boundary k false, x.boundary k true⟩
      (PdHom.setSide ⟨k, x.boundary k false, x.boundary k true⟩ (!α) (a.boundary k (!α))) :=
  CtxExpr.typed_paste (!α) (u := ⟨a, har⟩) (H := ⟨k, x.boundary k false, x.boundary k true⟩)
    (Set.mem_univ _) hda
    (by simp only [PdHom.side, PastingDiagram.cond_boundary, Bool.not_not]; exact hxa)

structure PfwSpec (k : ℕ) (x x' h : PastingDiagram X) : Prop where
  isRound_h : h.IsRound
  mem : (⟨h, isRound_h⟩ : RoundPastingDiagram X) ∈ equivalences X
  hasType : HasBdry false (k + 1) h x x'

namespace PfwSpec

section Level

variable {k : ℕ} {x x' h : PastingDiagram X} (hs : PfwSpec k x x' h)
include hs

theorem isRound_x : x.IsRound :=
  hs.hasType.side.isRound_iff.1 (isRound_boundary_of_isRound hs.isRound_h _ _)

theorem isRound_x' : x'.IsRound :=
  hs.hasType.other.isRound_iff.1 (isRound_boundary_of_isRound hs.isRound_h _ _)

theorem equiv_boundary_x (α : Bool) : (x.boundary k α).Equiv (x'.boundary k α) :=
  (hs.hasType.side.boundary k α).symm.trans
    ((equiv_boundary_boundary h (Nat.lt_succ_self k) false α).trans
      ((equiv_boundary_boundary h (Nat.lt_succ_self k) true α).symm.trans
        (hs.hasType.other.boundary k α)))

theorem inHom_h : InHom ⟨k, x.boundary k false, x.boundary k true⟩ h :=
  InHom.of_hasBdry hs.hasType
    ⟨by change k < x.dim; rw [hs.hasType.dim_a]; omega, .refl _, .refl _⟩

theorem equiv_boundary_h (α : Bool) : (h.boundary k (!α)).Equiv (x.boundary k (!α)) := by
  have e := hs.inHom_h.side (!α)
  simp only [PdHom.side] at e
  rwa [PastingDiagram.cond_boundary] at e

end Level

variable {H : RoundHom X} {x x' h : PastingDiagram X}

theorem component_paste_unit (hs : PfwSpec H.k x x' h) (α : Bool)
    (hx : (x.boundary H.k (!α)).Equiv (H.side α)) {a : PastingDiagram X} (ha : IsRoundIn H a) :
    ∃ (hp : ((CtxExpr.paste (!α) a H.k).app h).Pastable
        ((CtxExpr.paste (!α) a H.k).app x').unit (H.k + 1))
      (hround : (((CtxExpr.paste (!α) a H.k).app h).paste
        ((CtxExpr.paste (!α) a H.k).app x').unit (H.k + 1) hp).IsRound),
      (⟨_, hround⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  set k := H.k
  have hxa : (x.boundary k (!α)).Equiv (a.boundary k α) := hx.trans (ha.inHom.side α).symm
  exact mem_equivalences_app_paste_unit
    (typed_paste_not α ha.isRound ha.dim_eq hxa (q := True))
    (isRoundCtx_of_trim (typed_paste_not α ha.isRound ha.dim_eq hxa (q := False)))
    (e := ⟨h, hs.isRound_h⟩) hs.mem hs.inHom_h hs.hasType.dim_h hs.hasType.other

theorem valid (hs : PfwSpec H.k x x' h) (α : Bool)
    (hx : (x.boundary H.k (!α)).Equiv (H.side α)) : (ctxPfw α H x x' h).Valid := by
  set k := H.k
  have hF : IsRoundCtxOn H (H.setSide α (x.boundary k α)) (CtxExpr.paste α x k) := by
    have ht : ∀ {q : Prop}, (CtxExpr.paste α x k).Typed Set.univ q H
        (H.setSide α (x.boundary k α)) := fun {_} =>
      CtxExpr.typed_paste α (u := ⟨x, hs.isRound_x⟩) (Set.mem_univ _) hs.hasType.dim_a hx.symm
    exact ⟨ht, isRoundCtx_of_trim ht⟩
  have hG : IsRoundCtxOn H (H.setSide α (x.boundary k α)) (CtxExpr.paste α x' k) := by
    have ht : ∀ {q : Prop}, (CtxExpr.paste α x' k).Typed Set.univ q H
        (H.setSide α (x.boundary k α)) := fun {_} =>
      (CtxExpr.typed_paste α (u := ⟨x', hs.isRound_x'⟩) (Set.mem_univ _) hs.hasType.dim_b
        (hx.symm.trans (hs.equiv_boundary_x (!α)))).congr_codomain
          ((PdHom.Equiv.refl _).setSide α (hs.equiv_boundary_x α).symm)
    exact ⟨ht, isRoundCtx_of_trim ht⟩
  refine ⟨hF, hG, fun a ha => ?_⟩
  change IsRoundIn H a at ha
  have hxa : (x.boundary k (!α)).Equiv (a.boundary k α) := hx.trans (ha.inHom.side α).symm
  obtain ⟨hp, hround, hmem⟩ := hs.component_paste_unit α hx ha
  obtain ⟨hround', hmem'⟩ := exists_mem_equivalences_pasteOr hp hmem
  refine ⟨hround', hmem', ?_⟩
  change HasBdry false (k + 1) (((CtxExpr.paste (!α) a k).app h).pasteOr
    ((CtxExpr.paste (!α) a k).app x').unit (k + 1)) ((CtxExpr.paste α x k).app a)
    ((CtxExpr.paste α x' k).app a)
  rw [PastingDiagram.pasteOr_of hp]
  have L := (typed_paste_not α ha.isRound ha.dim_eq hxa (q := True)).ctxLaws
  have hpa : (cond α a x).Pastable (cond α x a) k :=
    .of_side α hxa.symm (by rw [ha.dim_eq]; exact Nat.lt_succ_self _)
        (by rw [hs.hasType.dim_a]; omega)
  have hpa' : (cond α a x').Pastable (cond α x' a) k :=
    .of_side α (hxa.symm.trans (hs.equiv_boundary_x (!α)))
        (by rw [ha.dim_eq]; exact Nat.lt_succ_self _)
      (by rw [hs.hasType.dim_b]; omega)
  have eF := (CtxExpr.paste_app_not α hpa).symm
  have eG := (CtxExpr.paste_app_not α hpa').symm
  have hGa := hG.isRoundIn ha
  have hdHh : ((CtxExpr.paste (!α) a k).app h).dim = k + 1 + 1 :=
    (L.dim_eq _ hs.inHom_h).trans hs.hasType.dim_h
  have hdHx' : ((CtxExpr.paste (!α) a k).app x').dim = k + 1 :=
    (dim_eq_of_equiv eG).trans hGa.dim_eq
  have hrHx' : ((CtxExpr.paste (!α) a k).app x').IsRound := eG.isRound_iff.2 hGa.isRound
  refine ⟨by rw [dim_paste, hdHh, dim_unit, hdHx', max_self],
    (hF.typed.ctxLaws.dim_eq a ha.inHom).trans ha.dim_eq,
    (hG.typed.ctxLaws.dim_eq a ha.inHom).trans ha.dim_eq, ?_, ?_⟩
  · exact (equiv_boundary_paste hp false).trans
      ((L.boundary _ hs.inHom_h (Nat.lt_succ_self k)
        (by rw [hs.hasType.dim_h]; omega) false).trans
        ((CtxExpr.app_equiv _ hs.hasType.side).trans eF))
  · exact (equiv_boundary_paste hp true).trans
      ((boundary_unit hdHx' true).trans eG)

theorem equiv_component (hs : PfwSpec H.k x x' h) (α : Bool)
    (hx : (x.boundary H.k (!α)).Equiv (H.side α)) {y : PastingDiagram X} (hy : IsRoundIn H y) :
    ∃ (q : ((CtxExpr.paste (!α) y H.k).app h).Pastable ((CtxExpr.paste α x' H.k).app y).unit
      (H.k + 1)), ((ctxPfw α H x x' h).ϑ y).Equiv
        (((CtxExpr.paste (!α) y H.k).app h).paste ((CtxExpr.paste α x' H.k).app y).unit
          (H.k + 1) q) := by
  set k := H.k
  have hxy : (x.boundary k (!α)).Equiv (y.boundary k α) := hx.trans (hy.inHom.side α).symm
  have hpy' : (cond α y x').Pastable (cond α x' y) k :=
    .of_side α (hxy.symm.trans (hs.equiv_boundary_x (!α)))
        (by rw [hy.dim_eq]; exact Nat.lt_succ_self _)
      (by rw [hs.hasType.dim_b]; omega)
  obtain ⟨hp, -, -⟩ := hs.component_paste_unit α hx hy
  have eG := (CtxExpr.paste_app_not α hpy').symm
  have q := Pastable.of_equiv hp (.refl _) (Equiv.unit eG)
  refine ⟨q, ?_⟩
  change (((CtxExpr.paste (!α) y k).app h).pasteOr ((CtxExpr.paste (!α) y k).app x').unit
    (k + 1)).Equiv _
  rw [PastingDiagram.pasteOr_of hp]
  exact Equiv.paste (.refl _) (Equiv.unit eG) hp q

theorem mem_natOp (hs : PfwSpec H.k x x' h) (α : Bool) {A : Set (CtxTriple X)}
    (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A)
    (hx : (x.boundary H.k (!α)).Equiv (H.side α)) :
    ctxPfw α H x x' h ∈ CtxTriple.natOp (CtxTriple.Closure A) := by
  have hval := hs.valid α hx
  set k := H.k
  refine ⟨hval, fun a b ha hb => ?_⟩
  change IsRoundIn H a at ha
  change IsRoundIn H b at hb
  have hG : IsRoundCtxOn H (H.setSide α (x.boundary k α)) (CtxExpr.paste α x' k) := hval.ctxG
  have hGa := hG.isRoundIn ha
  have hGb := hG.isRoundIn hb
  have hdGa₀ : ((CtxExpr.paste α x' k).app a).dim = k + 1 := hGa.dim_eq
  have hdGb₀ : ((CtxExpr.paste α x' k).app b).dim = k + 1 := hGb.dim_eq
  have hσ := CtxTriple.Sim.of_mem (A := A)
    (hU ⟨_, (isCylTriple_unit hGa.roundHom).next hGa hGb⟩)
  have hid : IsRoundCtxOn (H.setSide α (x.boundary k α)) (H.setSide α (x.boundary k α)) .id :=
    isRoundCtxOn_id
  have htU : ∀ {y : PastingDiagram X}, IsRoundIn (H.setSide α (x.boundary k α)) y →
      HasBdry false (k + 1) y.unit (CtxExpr.id.app y) (CtxExpr.id.app y) := fun {y} hy => by
    have hdy : y.dim = k + 1 := hy.dim_eq
    exact ⟨by rw [dim_unit, hdy], hdy, hdy, boundary_unit hdy false, boundary_unit hdy true⟩
  have S0 := CtxTriple.Sim.round_right hA hU hG hid hid ha hb (isRound_unit hGb.isRound)
    (isRound_unit hGa.isRound) (htU hGb) (htU hGa) hσ
  have hxa : (x.boundary k (!α)).Equiv (a.boundary k α) := hx.trans (ha.inHom.side α).symm
  let ℓ := (CtxExpr.paste (!α) a k).app h
  have L := (typed_paste_not α ha.isRound ha.dim_eq hxa (q := True)).ctxLaws
  have hdℓ : ℓ.dim = k + 1 + 1 := (L.dim_eq _ hs.inHom_h).trans hs.hasType.dim_h
  have hpa : (cond α a x).Pastable (cond α x a) k :=
    .of_side α hxa.symm (by rw [ha.dim_eq]; exact Nat.lt_succ_self _)
        (by rw [hs.hasType.dim_a]; omega)
  have hpa' : (cond α a x').Pastable (cond α x' a) k :=
    .of_side α (hxa.symm.trans (hs.equiv_boundary_x (!α)))
        (by rw [ha.dim_eq]; exact Nat.lt_succ_self _)
      (by rw [hs.hasType.dim_b]; omega)
  have hℓs : (ℓ.boundary (k + 1) false).Equiv ((CtxExpr.paste α x k).app a) :=
    (L.boundary _ hs.inHom_h (Nat.lt_succ_self k)
      (by rw [hs.hasType.dim_h]; omega) false).trans ((CtxExpr.app_equiv _ hs.hasType.side).trans
        (CtxExpr.paste_app_not α hpa).symm)
  have hℓt : (ℓ.boundary (k + 1) true).Equiv ((CtxExpr.paste α x' k).app a) :=
    (L.boundary _ hs.inHom_h (Nat.lt_succ_self k)
      (by rw [hs.hasType.dim_h]; omega) true).trans ((CtxExpr.app_equiv _ hs.hasType.other).trans
        (CtxExpr.paste_app_not α hpa').symm)
  set t := ℓ.frameCtx false hdℓ
  have happ := ℓ.frameCtx_app false hdℓ
  have htt := ℓ.typed_frameCtx false
    (H := ⟨k + 1, (CtxExpr.paste α x' k).app a, (CtxExpr.paste α x' k).app b⟩) hdℓ (hℓt.symm)
  have hT : IsRoundCtxOn ⟨k + 1, (CtxExpr.paste α x' k).app a, (CtxExpr.paste α x' k).app b⟩
      ⟨k + 1, ℓ.boundary (k + 1) false, (CtxExpr.paste α x' k).app b⟩ t :=
    ⟨htt.mono (Set.subset_univ _) (fun _ => trivial), isRoundCtx_of_trim htt⟩
  have S1 := (S0.left hT).congr
    (H₁' := ⟨k + 1, (CtxExpr.paste α x k).app a, (CtxExpr.paste α x' k).app b⟩) (.refl _)
    ⟨rfl, hℓs, .refl _⟩
  have hGp := hG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have uGa := boundary_unit hdGa₀
  have uGb := boundary_unit hdGb₀
  have hdGa : ((CtxExpr.paste α x' k).app a).unit.dim = k + 1 + 1 := by
    rw [dim_unit, hdGa₀]
  have hdGb : ((CtxExpr.paste α x' k).app b).unit.dim = k + 1 + 1 := by
    rw [dim_unit, hdGb₀]
  have hlt : ∀ {y z : PastingDiagram X} (hp : y.Pastable z (k + 1)), k + 1 < y.dim →
      k + 1 < (y.paste z (k + 1) hp).dim := fun hp hy => by
    rw [dim_paste]; exact lt_of_lt_of_le hy (le_max_left _ _)
  obtain ⟨qa, eϑa⟩ := hs.equiv_component α hx ha
  obtain ⟨qb, eϑb⟩ := hs.equiv_component α hx hb
  refine S1.of_equiv (fun c hc => ?_) (fun c hc => ?_)
  · have hGc := hGp.mapsInto c hc
    have hcin := hc.of_inHom_succ ha.inHom hb.inHom
    have r1 : ((CtxExpr.paste α x' k).app c).Pastable ((CtxExpr.paste α x' k).app b).unit
        (k + 1) :=
      ⟨hGc.target.trans ((uGb false).symm),
        lt_min hGc.lt_dim (by rw [hdGb]; omega)⟩
    have r2 : ℓ.Pastable ((CtxExpr.paste α x' k).app c) (k + 1) :=
      ⟨hℓt.trans (hGc.source.symm),
        lt_min (by rw [hdℓ]; omega) hGc.lt_dim⟩
    have r3 : (ℓ.paste ((CtxExpr.paste α x' k).app c) (k + 1) r2).Pastable
        ((CtxExpr.paste α x' k).app b).unit (k + 1) :=
      ⟨(equiv_boundary_paste r2 true).trans r1.1,
        lt_min (hlt r2 (by rw [hdℓ]; omega)) (by rw [hdGb]; omega)⟩
    obtain ⟨r₃, r₄, eA⟩ := equiv_paste_assoc r2 r3
    have rY := Pastable.of_equiv r₄ (.refl _)
      ((CtxExpr.paste_app true r₃).symm)
    have hxc : (x.boundary k (!α)).Equiv (c.boundary k α) := hx.trans (hcin.side α).symm
    have hhx := hs.equiv_boundary_h α
    have hdh : k < h.dim := by rw [hs.hasType.dim_h]; omega
    have hch : (cond α c h).Pastable (cond α h c) k :=
      .of_side α (hxc.symm.trans hhx.symm) hcin.lt_dim hdh
    have hhc : (cond (!α) h c).Pastable (cond (!α) c h) k :=
      .of_side (!α) (by rw [Bool.not_not]; exact hhx.trans hxc) hdh hcin.lt_dim
    obtain ⟨l₁, l₂, l₃, eL⟩ := equiv_paste_interchange α hch hc.lt_dim
      (by rw [hs.hasType.dim_h]; omega)
    obtain ⟨j₁, j₂, j₃, eJ⟩ := equiv_paste_interchange (!α) hhc (by rw [hs.hasType.dim_h]; omega)
      hc.lt_dim
    have hah : (cond (!α) h a).Pastable (cond (!α) a h) k :=
      .of_side (!α) (by rw [Bool.not_not]; exact hhx.trans hxa) hdh
          (by rw [ha.dim_eq]; exact Nat.lt_succ_self _)
    have hbh : (cond (!α) h b).Pastable (cond (!α) b h) k :=
      .of_side (!α) (by rw [Bool.not_not]; exact hhx.trans (hx.trans (hb.inHom.side α).symm))
        hdh (by rw [hb.dim_eq]; exact Nat.lt_succ_self _)
    have hcx : (cond α c x).Pastable (cond α x c) k :=
      .of_side α hxc.symm hcin.lt_dim (by rw [hs.hasType.dim_a]; omega)
    have hcx' : (cond α c x').Pastable (cond α x' c) k :=
      .of_side α (hxc.symm.trans (hs.equiv_boundary_x (!α))) hcin.lt_dim
        (by rw [hs.hasType.dim_b]; omega)
    have eℓ : ℓ.Equiv ((cond (!α) h (c.boundary (k + 1) false)).paste
        (cond (!α) (c.boundary (k + 1) false) h) k j₁) :=
      (CtxExpr.paste_app (!α) hah).trans (Equiv.paste
        (.cond (.refl _) (!α) hc.source.symm) (.cond hc.source.symm (!α) (.refl _)) hah j₁)
    have eGc : ((CtxExpr.paste α x' k).app c).Equiv ((cond (!α) (h.boundary (k + 1) true) c).paste
        (cond (!α) c (h.boundary (k + 1) true)) k j₂) :=
      (CtxExpr.paste_app α hcx').trans (Equiv.paste
        (by rw [Bool.cond_not]; exact .cond (.refl _) α hs.hasType.other.symm)
        (by rw [Bool.cond_not]; exact .cond hs.hasType.other.symm α (.refl _)) hcx' j₂)
    have eFc : ((cond α c (h.boundary (k + 1) false)).paste
        (cond α (h.boundary (k + 1) false) c) k l₁).Equiv ((CtxExpr.paste α x k).app c) :=
      (Equiv.paste (.cond (.refl _) α hs.hasType.side) (.cond hs.hasType.side α (.refl _))
        l₁ hcx).trans (CtxExpr.paste_app α hcx).symm
    have eℓb : ((cond α (c.boundary (k + 1) true) h).paste
        (cond α h (c.boundary (k + 1) true)) k l₂).Equiv ((CtxExpr.paste (!α) b k).app h) :=
      (Equiv.paste (by rw [Bool.cond_not]; exact .cond hc.target α (.refl _))
        (by rw [Bool.cond_not]; exact .cond (.refl _) α hc.target) l₂ hbh).trans
        (CtxExpr.paste_app (!α) hbh).symm
    have r4 := Pastable.of_equiv l₃ eFc eℓb
    have eX : (ℓ.paste ((CtxExpr.paste α x' k).app c) (k + 1) r2).Equiv
        (((CtxExpr.paste α x k).app c).paste ((CtxExpr.paste (!α) b k).app h) (k + 1) r4) :=
      (Equiv.paste eℓ eGc r2 j₃).trans (eJ.trans
        ((Equiv.paste (by rw [Bool.cond_not]) (by rw [Bool.cond_not]) hhc hch).trans
          (eL.symm.trans (Equiv.paste eFc eℓb l₃ r4))))
    have r5 := Pastable.of_equiv r3 eX (.refl _)
    obtain ⟨r₅, r₆, eB⟩ := equiv_paste_assoc r4 r5
    have r7 := Pastable.of_equiv r₆ (.refl _) (eϑb.symm)
    exact (happ _ rY).trans (PastingDiagram.Equiv.trans
      (Equiv.paste (.refl _) (CtxExpr.paste_app true r₃) rY r₄)
      (eA.symm.trans (PastingDiagram.Equiv.trans
        (Equiv.paste eX (.refl _) r3 r5) (eB.trans
          ((Equiv.paste (.refl _) (eϑb.symm) r₆ r7).trans ((CtxExpr.paste_app true r7).symm))))))
  · have hGc := hGp.mapsInto c hc
    have q1 : ((CtxExpr.paste α x' k).app a).unit.Pastable ((CtxExpr.paste α x' k).app c)
        (k + 1) :=
      ⟨(uGa true).trans (hGc.source.symm),
        lt_min (by rw [hdGa]; omega) hGc.lt_dim⟩
    have q2 : ℓ.Pastable ((CtxExpr.paste α x' k).app a).unit (k + 1) :=
      ⟨hℓt.trans ((uGa false).symm),
        lt_min (by rw [hdℓ]; omega) (by rw [hdGa]; omega)⟩
    have q3 : (ℓ.paste ((CtxExpr.paste α x' k).app a).unit (k + 1) q2).Pastable
        ((CtxExpr.paste α x' k).app c) (k + 1) :=
      ⟨(equiv_boundary_paste q2 true).trans q1.1,
        lt_min (hlt q2 (by rw [hdℓ]; omega)) hGc.lt_dim⟩
    obtain ⟨q₃, q₄, eA⟩ := equiv_paste_assoc q2 q3
    have qY := Pastable.of_equiv q₄ (.refl _)
      ((CtxExpr.paste_app false q₃).symm)
    have q5 := Pastable.of_equiv q3 (PastingDiagram.Equiv.trans
      (Equiv.paste (.refl _) (.refl _) q2 qa)
      (eϑa.symm)) (.refl _)
    exact (happ _ qY).trans (PastingDiagram.Equiv.trans
      (Equiv.paste (.refl _) (CtxExpr.paste_app false q₃) qY q₄)
      (eA.symm.trans (PastingDiagram.Equiv.trans
        (Equiv.paste (PastingDiagram.Equiv.trans
          (Equiv.paste (.refl _) (.refl _) q2 qa)
          (eϑa.symm)) (.refl _) q3 q5)
        ((CtxExpr.paste_app false q5).symm))))

end PfwSpec

end Atoms.Diagrammatic
