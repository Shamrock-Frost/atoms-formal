import Atoms.Diagrammatic.Context.NaturalClosure

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Bicategory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem equivalent_paste_side (α : Bool) {c : PastingDiagram X} {h h' : RoundPastingDiagram X}
    (hh : Equivalent h h') {k : ℕ} (hd : c.dim = h.dim)
    (hp : (cond α c h.toPastingDiagram).Pastable (cond α h.toPastingDiagram c) k)
    (hp' : (cond α c h'.toPastingDiagram).Pastable (cond α h'.toPastingDiagram c) k)
    (hr : ((cond α c h.toPastingDiagram).paste (cond α h.toPastingDiagram c) k hp).IsRound)
    (hr' : ((cond α c h'.toPastingDiagram).paste (cond α h'.toPastingDiagram c) k hp').IsRound) :
    Equivalent ⟨_, hr⟩ ⟨_, hr'⟩ := by
  let E := hh.data
  have hdp : ((cond α c h.toPastingDiagram).paste (cond α h.toPastingDiagram c) k hp).dim =
      h.dim := by
    rw [dim_paste_cond, hd, max_self]
  obtain ⟨wc, hpst⟩ := Within.exists_isPastingIn_pasteIn α hp
  have hsub : IsSubmoleculeOf _ (Within.pasteIn α hp).image ⊤ :=
    (hpst.isPastingFactorOf α (Within.pasteIn α hp).isMoleculeIn_image
      wc.isMoleculeIn_image).isSubmoleculeOf
  let D : SubstituteData ⟨_, hr⟩ h' :=
    { sub := h.toPastingDiagram
      occ := Within.pasteIn α hp
      rewritable := (Within.pasteIn α hp).isRewritableSubmolecule_image_iff.2
        ⟨hsub, h.isRound, hdp.symm⟩
      rewrite := E.equivalence
      dim_rewrite := by
        rw [E.dim_equivalence]
        exact congrArg (· + 1) hdp.symm
      source := by
        change (E.equivalence.boundary
          ((cond α c h.toPastingDiagram).paste (cond α h.toPastingDiagram c) k hp).dim
            false).Equiv _
        rw [PastingDiagram.boundary_congr E.equivalence.toPastingDiagram hdp]
        exact E.source
      target := by
        change (E.equivalence.boundary
          ((cond α c h.toPastingDiagram).paste (cond α h.toPastingDiagram c) k hp).dim
            true).Equiv _
        rw [PastingDiagram.boundary_congr E.equivalence.toPastingDiagram hdp]
        exact E.target }
  refine D.equivalent E.mem ?_
  have hq : D.pasteData.pasting.shape.ogp.IsPastingIn k
      (cond α (wc.trans D.withinU).image ((Within.pasteIn α hp).trans D.withinU).image)
      (cond α ((Within.pasteIn α hp).trans D.withinU).image (wc.trans D.withinU).image)
      D.withinU.image := by
    rw [Within.image_trans, Within.image_trans, ← Bool.apply_cond (OGP.map D.withinU.emb),
      ← Bool.apply_cond (OGP.map D.withinU.emb)]
    exact (isPastingIn_map_iff D.withinU.emb k _ _ _).2 hpst
  have hkh : k < h.dim := by
    rw [← hdp, dim_paste]
    exact lt_max_of_lt_left (lt_min_iff.1 hp.2).1
  have hk : (k : WithBot ℕ∞) < krullDim ((Within.pasteIn α hp).trans D.withinU).image := by
    rw [Within.krullDim_image]; exact_mod_cast hkh
  exact D.equiv_target_restrictTo.trans ((equiv_paste_cond_of_within α (wc.trans D.withinU)
    D.withinW (D.isSubstitutionIn.isPastingIn_self_cond α (wc.trans D.withinU).isMoleculeIn_image
      hk hq) D.isMoleculeIn_output hp').symm)

namespace PastingDiagram

noncomputable def rounding (y : PastingDiagram X) (k : ℕ) : PastingDiagram X :=
  y.pasteOr (y.boundary k true).unit k

theorem pastable_unit_boundary {y : PastingDiagram X} {k : ℕ} (hk : k < y.dim) :
    y.Pastable (y.boundary k true).unit k :=
  ⟨(boundary_unit (dim_boundary y hk.le true) false).symm,
    lt_min hk (by rw [dim_unit, dim_boundary y hk.le true]; omega)⟩

theorem rounding_eq {y : PastingDiagram X} {k : ℕ} (hk : k < y.dim) :
    y.rounding k = y.paste (y.boundary k true).unit k (pastable_unit_boundary hk) :=
  pasteOr_of _

theorem isRound_rounding {y : PastingDiagram X} {k : ℕ} (hd : y.dim = k + 1)
    (hb : (y.boundary k true).IsRound) : (y.rounding k).IsRound := by
  rw [rounding_eq (by omega : k < y.dim)]
  exact isRound_paste_of_round true (u := (y.boundary k true).unit) (x := y) _ (isRound_unit hb)
    (by rw [dim_unit, dim_boundary y (by omega) true]) hd.le

end PastingDiagram

theorem HasBdry.rounding {y a b : PastingDiagram X} {k : ℕ} (t : HasBdry false k y a b) :
    HasBdry false k (y.rounding k) a b :=
  (t.pasteOr (hasType_unit (dim_boundary y (by rw [t.dim_h]; omega) true))
    t.other.symm).of_equiv_other t.other

theorem PastingDiagram.Equiv.rounding {y y' : PastingDiagram X} (e : y.Equiv y') {k : ℕ}
    (hk : k < y.dim) :
    (y.rounding k).Equiv (y'.rounding k) := by
  have hk' : k < y'.dim := dim_eq_of_equiv e ▸ hk
  rw [rounding_eq hk, rounding_eq hk']
  exact Equiv.paste e (e.boundary k true).unit _ _

theorem PastingDiagram.equiv_rounding_mapTo {Y : DiagSet.{u}} (y : PastingDiagram X) {k : ℕ}
    (hk : k < y.dim) (φ : X ⟶ Y) :
    ((y.rounding k).mapTo φ).Equiv ((y.mapTo φ).rounding k) := by
  have hk' : k < (y.mapTo φ).dim := hk
  rw [rounding_eq hk, rounding_eq hk']
  refine (paste_mapTo _ _ _ _ φ ((pastable_unit_boundary hk).mapTo φ)).trans
    (Equiv.paste (.refl _) ?_ _ _)
  rw [boundary_mapTo, unit_mapTo]

theorem equivalent_paste_unit_of_equiv (α : Bool) (x : RoundPastingDiagram X) {k : ℕ}
    (hd : x.dim = k + 1) {v : PastingDiagram X} (hv : (x.boundary k α).Equiv v)
    (hp : (cond α x.toPastingDiagram v.unit).Pastable (cond α v.unit x.toPastingDiagram) k)
    (hr : ((cond α x.toPastingDiagram v.unit).paste (cond α v.unit x.toPastingDiagram) k
      hp).IsRound) :
    Equivalent x ⟨_, hr⟩ := by
  have ex : (cond α x.toPastingDiagram (x.boundary k α).unit).Equiv
      (cond α x.toPastingDiagram v.unit) := by
    cases α
    · exact hv.unit
    · exact .refl _
  have eu : (cond α (x.boundary k α).unit x.toPastingDiagram).Equiv
      (cond α v.unit x.toPastingDiagram) := by
    cases α
    · exact .refl _
    · exact hv.unit
  have hp₀ := hp.of_equiv ex.symm eu.symm
  have e := Equiv.paste ex eu hp₀ hp
  exact equivalent_trans (equivalent_paste_unit_cond α x hd hp₀ (e.isRound_iff.2 hr))
    (equivalent_of_equiv e)

section Whisker

variable {k : ℕ}

theorem HasBdry.paste_cond (γ : Bool) {u x y₀ y₁ : PastingDiagram X} (hdu : u.dim = k + 1)
    (hx : HasBdry false (k + 1) x y₀ y₁) (hp : (cond γ x u).Pastable (cond γ u x) k) :
    ∃ (hp₀ : (cond γ y₀ u).Pastable (cond γ u y₀) k)
      (hp₁ : (cond γ y₁ u).Pastable (cond γ u y₁) k),
      HasBdry false (k + 1) ((cond γ x u).paste (cond γ u x) k hp)
        ((cond γ y₀ u).paste (cond γ u y₀) k hp₀) ((cond γ y₁ u).paste (cond γ u y₁) k hp₁) := by
  have hxd : k + 1 ≤ x.dim := by rw [hx.dim_h]; omega
  obtain ⟨q₀, e₀⟩ := exists_equiv_boundary_paste_cond γ hp hdu (Nat.lt_succ_self k) hxd false
  obtain ⟨q₁, e₁⟩ := exists_equiv_boundary_paste_cond γ hp hdu (Nat.lt_succ_self k) hxd true
  have hp₀ := q₀.of_equiv (hx.side.cond γ (.refl u)) ((PastingDiagram.Equiv.refl u).cond γ hx.side)
  have hp₁ := q₁.of_equiv (hx.other.cond γ (.refl u))
    ((PastingDiagram.Equiv.refl u).cond γ hx.other)
  refine ⟨hp₀, hp₁, ⟨?_, ?_, ?_, e₀.trans (Equiv.paste (hx.side.cond γ (.refl u))
    ((PastingDiagram.Equiv.refl u).cond γ hx.side) q₀ hp₀),
    e₁.trans (Equiv.paste (hx.other.cond γ (.refl u))
      ((PastingDiagram.Equiv.refl u).cond γ hx.other) q₁ hp₁)⟩⟩
  · rw [dim_paste_cond, hx.dim_h, hdu]; omega
  · rw [dim_paste_cond, hx.dim_a, hdu, max_self]
  · rw [dim_paste_cond, hx.dim_b, hdu, max_self]

theorem HasBdry.rounding_paste_cond (γ : Bool) {u x y₀ y₁ : PastingDiagram X} (hu : u.IsRound)
    (hdu : u.dim = k + 1) (hx : HasBdry false (k + 1) x y₀ y₁) (hy₁ : y₁.IsRound)
    (hp : (cond γ x u).Pastable (cond γ u x) k) :
    ∃ (hp₀ : (cond γ y₀ u).Pastable (cond γ u y₀) k)
      (hp₁ : (cond γ y₁ u).Pastable (cond γ u y₁) k),
      HasBdry false (k + 1) (((cond γ x u).paste (cond γ u x) k hp).rounding (k + 1))
        ((cond γ y₀ u).paste (cond γ u y₀) k hp₀) ((cond γ y₁ u).paste (cond γ u y₁) k hp₁) ∧
      (((cond γ x u).paste (cond γ u x) k hp).rounding (k + 1)).IsRound := by
  obtain ⟨hp₀, hp₁, ht⟩ := hx.paste_cond γ hdu hp
  have hr₁ : ((cond γ y₁ u).paste (cond γ u y₁) k hp₁).IsRound := by
    cases γ
    · exact isRound_paste_of_dim ⟨u, hu⟩ ⟨y₁, hy₁⟩ hdu hx.dim_b hp₁
    · exact isRound_paste_of_dim ⟨y₁, hy₁⟩ ⟨u, hu⟩ hx.dim_b hdu hp₁
  exact ⟨hp₀, hp₁, ht.rounding, isRound_rounding ht.dim_h (ht.other.isRound_iff.2 hr₁)⟩

variable (γ : Bool) {u : PastingDiagram X} (hu : u.IsRound) (hdu : u.dim = k + 1)
  {y₀ y₁ : PastingDiagram X}

private abbrev lowerHom (y₀ : PastingDiagram X) (k : ℕ) : PdHom X :=
  ⟨k, y₀.boundary k false, y₀.boundary k true⟩

include hu hdu in
private theorem typed_paste_lowerHom (he : (y₀.boundary k γ).Equiv (u.boundary k (!γ)))
    {p : Prop} :
    (CtxExpr.paste γ u k).Typed Set.univ p (lowerHom y₀ k)
      ((lowerHom y₀ k).setSide γ (u.boundary k γ)) :=
  CtxExpr.typed_paste γ (u := ⟨u, hu⟩) (Set.mem_univ _) hdu (by
    change (cond γ (y₀.boundary k true) (y₀.boundary k false)).Equiv _
    rw [PastingDiagram.cond_boundary]
    exact he)

private theorem inHom_lowerHom {x : PastingDiagram X} (hx : HasBdry false (k + 1) x y₀ y₁) :
    InHom (lowerHom y₀ k) x :=
  ⟨by change k < x.dim; rw [hx.dim_h]; omega,
    (equiv_boundary_boundary x (Nat.lt_succ_self k) false false).symm.trans
      (hx.side.boundary k false),
    (equiv_boundary_boundary x (Nat.lt_succ_self k) false true).symm.trans
      (hx.side.boundary k true)⟩

private theorem equiv_boundary_of_pastable {x : PastingDiagram X}
    (hx : HasBdry false (k + 1) x y₀ y₁) (hp : (cond γ x u).Pastable (cond γ u x) k) :
    (y₀.boundary k γ).Equiv (u.boundary k (!γ)) :=
  ((hx.side.boundary k γ).symm.trans
    (equiv_boundary_boundary x (Nat.lt_succ_self k) false γ)).trans hp.side

private theorem inHom_lowerHom_target {x : PastingDiagram X}
    (hx : HasBdry false (k + 1) x y₀ y₁) : InHom (lowerHom y₀ k) y₁ :=
  ⟨by change k < y₁.dim; rw [hx.dim_b]; omega,
    (hx.equiv_boundary (Nat.lt_succ_self k) false).symm,
    (hx.equiv_boundary (Nat.lt_succ_self k) true).symm⟩

include hu hdu in
private theorem app_equiv_rounding {x : PastingDiagram X} (hx : HasBdry false (k + 1) x y₀ y₁)
    (hp : (cond γ x u).Pastable (cond γ u x) k) :
    ∃ hq : ((CtxExpr.paste γ u k).app x).Pastable ((CtxExpr.paste γ u k).app y₁).unit (k + 1),
      (((CtxExpr.paste γ u k).app x).paste ((CtxExpr.paste γ u k).app y₁).unit (k + 1)
        hq).Equiv (((cond γ x u).paste (cond γ u x) k hp).rounding (k + 1)) := by
  have he := equiv_boundary_of_pastable γ hx hp
  have L := (typed_paste_lowerHom (p := True) γ hu hdu (y₀ := y₀) he).ctxLaws
  have hin := inHom_lowerHom hx
  have hin₁ := inHom_lowerHom_target hx
  have ex := CtxExpr.paste_app γ hp
  have hdx : ((CtxExpr.paste γ u k).app x).dim = k + 1 + 1 := (L.dim_eq x hin).trans hx.dim_h
  have hb : (((CtxExpr.paste γ u k).app x).boundary (k + 1) true).Equiv
      ((CtxExpr.paste γ u k).app y₁) :=
    (L.boundary x hin (Nat.lt_succ_self k) (by rw [hx.dim_h]; omega) true).trans
      (CtxExpr.app_equiv _ hx.other)
  have hdq : ((CtxExpr.paste γ u k).app y₁).dim = k + 1 := (L.dim_eq y₁ hin₁).trans hx.dim_b
  have hq : ((CtxExpr.paste γ u k).app x).Pastable ((CtxExpr.paste γ u k).app y₁).unit
      (k + 1) :=
    ⟨hb.trans (boundary_unit hdq false).symm, lt_min (by rw [hdx]; omega)
      (by rw [dim_unit, hdq]; omega)⟩
  have hk : k + 1 < ((cond γ x u).paste (cond γ u x) k hp).dim := by
    rw [← dim_eq_of_equiv ex, hdx]; omega
  refine ⟨hq, ?_⟩
  rw [rounding_eq hk]
  exact Equiv.paste ex (hb.symm.trans (ex.boundary (k + 1) true)).unit hq _

include hu hdu in
theorem mem_equivalences_rounding_paste_cond {x : RoundPastingDiagram X}
    (hxe : x ∈ equivalences X) (hx : HasBdry false (k + 1) x.toPastingDiagram y₀ y₁)
    (hp : (cond γ x.toPastingDiagram u).Pastable (cond γ u x.toPastingDiagram) k)
    (hr : (((cond γ x.toPastingDiagram u).paste (cond γ u x.toPastingDiagram) k hp).rounding
      (k + 1)).IsRound) :
    (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  have he := equiv_boundary_of_pastable γ hx hp
  obtain ⟨_, _, hmem⟩ := mem_equivalences_app_paste_unit
    (typed_paste_lowerHom (p := True) γ hu hdu (y₀ := y₀) he)
    (isRoundCtx_of_trim (typed_paste_lowerHom (p := False) γ hu hdu (y₀ := y₀) he)) hxe
    (inHom_lowerHom hx) hx.dim_h hx.other
  obtain ⟨_, e⟩ := app_equiv_rounding γ hu hdu hx hp
  exact mem_equivalences_of_equiv e hmem

include hu hdu in
theorem equivalent_rounding_paste_cond {x x' : RoundPastingDiagram X} (hxx : Equivalent x x')
    (hx : HasBdry false (k + 1) x.toPastingDiagram y₀ y₁) (hy₁ : y₁.IsRound)
    (hp : (cond γ x.toPastingDiagram u).Pastable (cond γ u x.toPastingDiagram) k)
    (hp' : (cond γ x'.toPastingDiagram u).Pastable (cond γ u x'.toPastingDiagram) k)
    (hr : (((cond γ x.toPastingDiagram u).paste (cond γ u x.toPastingDiagram) k hp).rounding
      (k + 1)).IsRound)
    (hr' : (((cond γ x'.toPastingDiagram u).paste (cond γ u x'.toPastingDiagram) k hp').rounding
      (k + 1)).IsRound) :
    Equivalent ⟨_, hr⟩ ⟨_, hr'⟩ := by
  have E := hxx.data
  have hx' : HasBdry false (k + 1) x'.toPastingDiagram y₀ y₁ :=
    ⟨E.dim_eq.symm.trans hx.dim_h, hx.dim_a, hx.dim_b,
      (hxx.equiv_boundary (by rw [hx.dim_h]; omega) false).symm.trans hx.side,
      (hxx.equiv_boundary (by rw [hx.dim_h]; omega) true).symm.trans hx.other⟩
  have he := equiv_boundary_of_pastable γ hx hp
  have ht₀ := typed_paste_lowerHom (p := True) γ hu hdu (y₀ := y₀) he
  have hy₀ : InHom (lowerHom y₀ k) y₀ :=
    ⟨by change k < y₀.dim; rw [hx.dim_a]; omega, .refl _, .refl _⟩
  have hin₁ := inHom_lowerHom_target hx
  have ht₁ := ht₀.promote_of_inHom trivial hy₀ hin₁
  set Q := (CtxExpr.paste γ u k).app y₁
  have hQ : Q.IsRound := (isRoundCtx_of_trim (typed_paste_lowerHom (p := False) γ hu hdu
    (y₀ := y₀) he)).isRound_app ht₀ hin₁ hx.dim_b hy₁
  have hdQ : Q.dim = k + 1 := (ht₀.ctxLaws.dim_eq y₁ hin₁).trans hx.dim_b
  have hdU : Q.unit.dim = k + 1 + 1 := by rw [dim_unit, hdQ]
  have hT := IsRoundCtx.comp_paste true ht₁ (isRound_unit hQ) hdU (boundary_unit hdQ false).symm
  have htT := ht₁.comp (CtxExpr.typed_paste true (u := ⟨Q.unit, isRound_unit hQ⟩)
    (Set.mem_univ _) hdU (boundary_unit hdQ false).symm)
  have hEb : HasBdry false (k + 1 + 1) E.equivalence.toPastingDiagram x.toPastingDiagram
      x'.toPastingDiagram :=
    HasBdry.of_dim_eq hx.dim_h E.dim_equivalence hx.dim_h hx'.dim_h E.source E.target
  have hinx : InHom ⟨k + 1, y₀, y₁⟩ x.toPastingDiagram :=
    ⟨by change k + 1 < x.dim; rw [hx.dim_h]; omega, hx.side, hx.other⟩
  have hinE := InHom.of_hasBdry hEb hinx
  obtain ⟨hpz, hrz, hz⟩ := mem_equivalences_app_paste_unit htT hT E.mem hinE hEb.dim_h hEb.other
  have LT := htT.ctxLaws
  have hinx' : InHom ⟨k + 1, y₀, y₁⟩ x'.toPastingDiagram :=
    ⟨by change k + 1 < x'.dim; rw [hx'.dim_h]; omega, hx'.side, hx'.other⟩
  have hdTx : ∀ {w : PastingDiagram X}, InHom ⟨k + 1, y₀, y₁⟩ w → w.dim = k + 1 + 1 →
      (CtxExpr.app (.comp (CtxExpr.paste true Q.unit (k + 1)) (CtxExpr.paste γ u k)) w).dim =
        k + 1 + 1 := fun hw hdw => (LT.dim_eq _ hw).trans hdw
  have hrx := hT.isRound_app htT hinx hx.dim_h x.isRound
  have hrx' := hT.isRound_app htT hinx' hx'.dim_h x'.isRound
  have hxx' : Equivalent ⟨_, hrx⟩ ⟨_, hrx'⟩ :=
    equivalent_of_mem_equivalences_cond false hz (hdTx hinx hx.dim_h) (hdTx hinx' hx'.dim_h)
      (by rw [dim_paste, LT.dim_eq _ hinE, hEb.dim_h, dim_unit, hdTx hinx' hx'.dim_h]; omega)
      ((equiv_boundary_paste hpz false).trans ((LT.boundary _ hinE (Nat.lt_succ_self _)
        (by change k + 1 + 1 < _; rw [hEb.dim_h]; omega) false).trans
          (CtxExpr.app_equiv _ hEb.side)))
      ((equiv_boundary_paste hpz true).trans (boundary_unit (hdTx hinx' hx'.dim_h) true))
  have ev : ∀ {w : RoundPastingDiagram X} (hw : HasBdry false (k + 1) w.toPastingDiagram y₀ y₁)
      (hpw : (cond γ w.toPastingDiagram u).Pastable (cond γ u w.toPastingDiagram) k),
      (CtxExpr.app (.comp (CtxExpr.paste true Q.unit (k + 1)) (CtxExpr.paste γ u k))
        w.toPastingDiagram).Equiv
        (((cond γ w.toPastingDiagram u).paste (cond γ u w.toPastingDiagram) k hpw).rounding
          (k + 1)) := fun hw hpw => by
    obtain ⟨hq, e⟩ := app_equiv_rounding γ hu hdu hw hpw
    exact (CtxExpr.paste_app true hq).trans e
  exact equivalent_trans (equivalent_of_equiv (ev hx hp).symm)
    (equivalent_trans hxx' (equivalent_of_equiv (ev hx' hp')))

end Whisker

variable (X) (n : ℕ)

structure RoundBicat where
  diag : RoundPastingDiagram X
  dim_diag : diag.dim = n

variable {X} {n}

namespace RoundBicat

theorem ext_diag {a b : RoundBicat X n}
    (h : a.diag.toPastingDiagram = b.diag.toPastingDiagram) : a = b := by
  obtain ⟨da, ha⟩ := a
  obtain ⟨db, hb⟩ := b
  obtain rfl : da = db := RoundPastingDiagram.ext h
  rfl

structure Arrow (a b : RoundBicat X n) where
  diag : RoundPastingDiagram X
  hasBdry : HasBdry false n diag.toPastingDiagram a.diag.toPastingDiagram b.diag.toPastingDiagram

instance Arrow.setoid (a b : RoundBicat X n) : Setoid (Arrow a b) where
  r p q := p.diag.toPastingDiagram.Equiv q.diag.toPastingDiagram
  iseqv := ⟨fun _ => .refl _, fun h => h.symm, fun h h' => h.trans h'⟩

def Hom (a b : RoundBicat X n) : Type u :=
  Quotient (Arrow.setoid a b)

noncomputable def Arrow.comp {a b c : RoundBicat X n} (p : Arrow a b) (q : Arrow b c) :
    Arrow a c :=
  ⟨⟨p.diag.paste q.diag.toPastingDiagram n (p.hasBdry.pastable q.hasBdry (.refl _)),
    isRound_paste_of_dim p.diag q.diag p.hasBdry.dim_h q.hasBdry.dim_h _⟩, by
    have h := p.hasBdry.pasteOr q.hasBdry (.refl _)
    rwa [pasteOr_of (p.hasBdry.pastable q.hasBdry (.refl _))] at h⟩

noncomputable def Arrow.id (a : RoundBicat X n) : Arrow a a :=
  ⟨a.diag.isRound.unit, hasType_unit a.dim_diag⟩

noncomputable instance : CategoryStruct (RoundBicat X n) where
  Hom := Hom
  id a := ⟦Arrow.id a⟧
  comp f g := Quotient.map₂ Arrow.comp (fun p p' hp q q' hq => Equiv.paste hp hq
    (p.hasBdry.pastable q.hasBdry (.refl _)) (p'.hasBdry.pastable q'.hasBdry (.refl _))) f g

def Arrow.hom {a b : RoundBicat X n} (p : Arrow a b) : a ⟶ b :=
  Quotient.mk (Arrow.setoid a b) p

theorem Arrow.hom_surjective {a b : RoundBicat X n} (f : a ⟶ b) : ∃ p : Arrow a b, p.hom = f :=
  Quotient.exists_rep (s := Arrow.setoid a b) f

theorem Arrow.hom_eq_hom_iff {a b : RoundBicat X n} (p q : Arrow a b) :
    p.hom = q.hom ↔ p.diag.toPastingDiagram.Equiv q.diag.toPastingDiagram :=
  Quotient.eq (r := Arrow.setoid a b)

theorem Arrow.hom_heq {a a' b b' : RoundBicat X n} (ha : a = a') (hb : b = b') (p : Arrow a b)
    (q : Arrow a' b') (h : p.diag.toPastingDiagram.Equiv q.diag.toPastingDiagram) :
    p.hom ≍ q.hom := by
  subst ha hb
  exact heq_of_eq ((Arrow.hom_eq_hom_iff _ _).2 h)

theorem Arrow.hom_comp_hom {a b c : RoundBicat X n} (p : Arrow a b) (q : Arrow b c) :
    p.hom ≫ q.hom = (p.comp q).hom :=
  rfl

theorem id_eq (a : RoundBicat X n) : 𝟙 a = (Arrow.id a).hom :=
  rfl

theorem assoc {a b c d : RoundBicat X n} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h = f ≫ g ≫ h := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  obtain ⟨q, rfl⟩ := Arrow.hom_surjective g
  obtain ⟨r, rfl⟩ := Arrow.hom_surjective h
  obtain ⟨_, _, e⟩ := equiv_paste_assoc (p.hasBdry.pastable q.hasBdry (.refl _))
    ((p.comp q).hasBdry.pastable r.hasBdry (.refl _))
  exact (Arrow.hom_eq_hom_iff _ _).2 e

def Hom.Mem {a b : RoundBicat X n} (f : a ⟶ b) (x : PastingDiagram X) : Prop :=
  Quotient.liftOn (s := Arrow.setoid a b) f (fun p => p.diag.toPastingDiagram.Equiv x)
    fun _ _ h => propext ⟨fun hp => h.symm.trans hp, fun hq => h.trans hq⟩

theorem Arrow.mem_hom {a b : RoundBicat X n} (p : Arrow a b) (x : PastingDiagram X) :
    p.hom.Mem x ↔ p.diag.toPastingDiagram.Equiv x :=
  Iff.rfl

namespace Hom

variable {a b c : RoundBicat X n}

noncomputable def rep (f : a ⟶ b) : Arrow a b :=
  Quotient.out (s := Arrow.setoid a b) f

@[simp]
theorem rep_hom (f : a ⟶ b) : f.rep.hom = f :=
  Quotient.out_eq (s := Arrow.setoid a b) f

theorem mem_rep (f : a ⟶ b) : f.Mem f.rep.diag.toPastingDiagram := by
  conv => arg 1; rw [← rep_hom f]
  exact (Arrow.mem_hom _ _).2 (.refl _)

theorem Mem.equiv {f : a ⟶ b} {x y : PastingDiagram X} (hx : f.Mem x) (hy : f.Mem y) :
    x.Equiv y := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  exact ((Arrow.mem_hom p x).1 hx).symm.trans ((Arrow.mem_hom p y).1 hy)

theorem Mem.of_equiv {f : a ⟶ b} {x y : PastingDiagram X} (hx : f.Mem x) (e : x.Equiv y) :
    f.Mem y := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  exact (Arrow.mem_hom p y).2 (((Arrow.mem_hom p x).1 hx).trans e)

theorem Mem.hasBdry {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x) :
    HasBdry false n x a.diag.toPastingDiagram b.diag.toPastingDiagram := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  have e := (Arrow.mem_hom p x).1 hx
  exact ⟨(dim_eq_of_equiv e).symm.trans p.hasBdry.dim_h, p.hasBdry.dim_a, p.hasBdry.dim_b,
    (e.boundary n false).symm.trans p.hasBdry.side, (e.boundary n true).symm.trans p.hasBdry.other⟩

theorem Mem.dim_eq {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x) : x.dim = n + 1 :=
  hx.hasBdry.dim_h

theorem Mem.isRound {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x) : x.IsRound :=
  (f.mem_rep.equiv hx).isRound_iff.1 f.rep.diag.isRound

theorem Mem.comp {f : a ⟶ b} {g : b ⟶ c} {x y : PastingDiagram X} (hx : f.Mem x) (hy : g.Mem y)
    (hp : x.Pastable y n) : (f ≫ g).Mem (x.paste y n hp) := by
  obtain ⟨p, rfl⟩ := Arrow.hom_surjective f
  obtain ⟨q, rfl⟩ := Arrow.hom_surjective g
  rw [Arrow.hom_comp_hom]
  exact (Arrow.mem_hom _ _).2 (Equiv.paste ((Arrow.mem_hom p x).1 hx) ((Arrow.mem_hom q y).1 hy)
    (p.hasBdry.pastable q.hasBdry (.refl _)) hp)

theorem mem_id (a : RoundBicat X n) : (𝟙 a : a ⟶ a).Mem a.diag.unit :=
  (Arrow.mem_hom (Arrow.id a) _).2 (.refl _)

end Hom

structure Cell {a b : RoundBicat X n} (f g : a ⟶ b) where
  diag : RoundPastingDiagram X
  dim_diag : diag.dim = n + 1 + 1
  source : f.Mem (diag.boundary (n + 1) false)
  target : g.Mem (diag.boundary (n + 1) true)

namespace Cell

variable {a b : RoundBicat X n} {f g h : a ⟶ b}

instance setoid (f g : a ⟶ b) : Setoid (Cell f g) where
  r t s := Equivalent t.diag s.diag
  iseqv := ⟨fun _ => equivalent_refl _, equivalent_symm, equivalent_trans⟩

theorem hasBdry (t : Cell f g) {x y : PastingDiagram X} (hx : f.Mem x) (hy : g.Mem y) :
    HasBdry false (n + 1) t.diag.toPastingDiagram x y :=
  ⟨t.dim_diag, hx.dim_eq, hy.dim_eq, t.source.equiv hx, t.target.equiv hy⟩

theorem pastable (t : Cell f g) (s : Cell g h) :
    t.diag.Pastable s.diag.toPastingDiagram (n + 1) :=
  (t.hasBdry f.mem_rep g.mem_rep).pastable (s.hasBdry g.mem_rep h.mem_rep) (.refl _)

noncomputable def comp (t : Cell f g) (s : Cell g h) : Cell f h where
  diag := ⟨t.diag.paste s.diag.toPastingDiagram (n + 1) (t.pastable s),
    isRound_paste_of_dim t.diag s.diag t.dim_diag s.dim_diag _⟩
  dim_diag := by
    change (t.diag.paste s.diag.toPastingDiagram (n + 1) (t.pastable s)).dim = _
    rw [dim_paste, t.dim_diag, s.dim_diag, max_self]
  source := t.source.of_equiv (equiv_boundary_paste (t.pastable s) false).symm
  target := s.target.of_equiv (equiv_boundary_paste (t.pastable s) true).symm

noncomputable def unitOf {x : PastingDiagram X} (hx : f.Mem x) (hy : g.Mem x) : Cell f g where
  diag := ⟨x.unit, isRound_unit hx.isRound⟩
  dim_diag := by
    change x.unit.dim = _
    rw [dim_unit, hx.dim_eq]
  source := hx.of_equiv (boundary_unit hx.dim_eq false).symm
  target := hy.of_equiv (boundary_unit hx.dim_eq true).symm

theorem equivalent_comp {t t' : Cell f g} {s s' : Cell g h} (ht : Equivalent t.diag t'.diag)
    (hs : Equivalent s.diag s'.diag) : Equivalent (t.comp s).diag (t'.comp s').diag := by
  have hp₁ : t'.diag.Pastable s.diag.toPastingDiagram (n + 1) := t'.pastable s
  exact equivalent_trans
    (equivalent_paste_left ht (t.dim_diag.trans s.dim_diag.symm) _ hp₁ _
      (isRound_paste_of_dim t'.diag s.diag t'.dim_diag s.dim_diag _))
    (equivalent_paste_right hs rfl (t'.dim_diag.trans s.dim_diag.symm) _ _ _ _)

end Cell

noncomputable instance homCategory (a b : RoundBicat X n) : Category (a ⟶ b) where
  Hom f g := Quotient (Cell.setoid f g)
  id f := Quotient.mk _ (Cell.unitOf f.mem_rep f.mem_rep)
  comp η θ := Quotient.map₂ Cell.comp (fun _ _ ht _ _ hs => Cell.equivalent_comp ht hs) η θ
  id_comp η := by
    induction η using Quotient.inductionOn with | h t => ?_
    exact Quotient.sound (equivalent_symm (equivalent_paste_unit_of_equiv false t.diag t.dim_diag
      (t.source.equiv (Hom.mem_rep _)) _ _))
  comp_id η := by
    induction η using Quotient.inductionOn with | h t => ?_
    exact Quotient.sound (equivalent_symm (equivalent_paste_unit_of_equiv true t.diag t.dim_diag
      (t.target.equiv (Hom.mem_rep _)) _ _))
  assoc η θ ι := by
    induction η using Quotient.inductionOn with | h t => ?_
    induction θ using Quotient.inductionOn with | h s => ?_
    induction ι using Quotient.inductionOn with | h r => ?_
    obtain ⟨_, _, e⟩ := equiv_paste_assoc (t.pastable s) ((t.comp s).pastable r)
    exact Quotient.sound (equivalent_of_equiv e)

variable {a b : RoundBicat X n} {f g h : a ⟶ b}

def homMk (t : Cell f g) : f ⟶ g :=
  Quotient.mk (Cell.setoid f g) t

theorem homMk_surjective (η : f ⟶ g) : ∃ t : Cell f g, homMk t = η :=
  Quotient.exists_rep (s := Cell.setoid f g) η

theorem homMk_eq_homMk_iff (t t' : Cell f g) : homMk t = homMk t' ↔ Equivalent t.diag t'.diag :=
  Quotient.eq (r := Cell.setoid f g)

theorem homMk_congr {t t' : Cell f g}
    (h : t.diag.toPastingDiagram.Equiv t'.diag.toPastingDiagram) : homMk t = homMk t' :=
  (homMk_eq_homMk_iff _ _).2 (equivalent_of_equiv h)

theorem homMk_heq {a' b' : RoundBicat X n} {f' g' : a' ⟶ b'} (ha : a = a') (hb : b = b')
    (hf : f ≍ f') (hg : g ≍ g') (t : Cell f g) (t' : Cell f' g')
    (h : Equivalent t.diag t'.diag) : homMk t ≍ homMk t' := by
  subst ha hb
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  exact heq_of_eq ((homMk_eq_homMk_iff _ _).2 h)

theorem homMk_comp_homMk (t : Cell f g) (s : Cell g h) : homMk t ≫ homMk s = homMk (t.comp s) :=
  rfl

theorem id_eq_homMk (f : a ⟶ b) : 𝟙 f = homMk (Cell.unitOf f.mem_rep f.mem_rep) :=
  rfl

theorem isIso_homMk_iff (t : Cell f g) : IsIso (homMk t) ↔ t.diag ∈ equivalences X := by
  have ht := t.hasBdry f.mem_rep g.mem_rep
  constructor
  · intro hi
    obtain ⟨t', ht'⟩ := homMk_surjective (inv (homMk t))
    have h₁ := (homMk_eq_homMk_iff (t.comp t') (Cell.unitOf f.mem_rep f.mem_rep)).1
      (by rw [← homMk_comp_homMk, ht', IsIso.hom_inv_id, id_eq_homMk])
    have h₂ := (homMk_eq_homMk_iff (Cell.unitOf g.mem_rep g.mem_rep) (t'.comp t)).1
      (by rw [← homMk_comp_homMk, ht', IsIso.inv_hom_id, id_eq_homMk])
    exact mem_equivalences_of_equivalent_unit ht (t'.hasBdry g.mem_rep f.mem_rep)
      f.rep.diag.isRound g.rep.diag.isRound h₁ h₂
  · intro he
    obtain ⟨e', hw⟩ := exists_isWeakInverse he
    obtain ⟨-, te', ⟨z, hz, hzm, tz⟩, ⟨z', hz', hzm', tz'⟩⟩ := hw.spec ht
    let s : Cell g f :=
      ⟨e', te'.dim_h, g.mem_rep.of_equiv te'.side.symm, f.mem_rep.of_equiv te'.other.symm⟩
    have hp := ht.pastable te' (.refl _)
    have hq := te'.pastable ht (.refl _)
    rw [pasteOr_of hp] at tz
    rw [pasteOr_of hq] at tz'
    refine ⟨homMk s, ?_, ?_⟩
    · rw [homMk_comp_homMk, id_eq_homMk, homMk_eq_homMk_iff]
      exact equivalent_of_mem_equivalences_cond false (z := ⟨z, hz⟩) hzm tz.dim_a tz.dim_b
        tz.dim_h tz.side tz.other
    · rw [homMk_comp_homMk, id_eq_homMk, homMk_eq_homMk_iff]
      exact equivalent_of_mem_equivalences_cond true (z := ⟨z', hz'⟩) hzm' tz'.dim_b tz'.dim_a
        tz'.dim_h tz'.other tz'.side

namespace Cell

variable {c : RoundBicat X n}

theorem equiv_boundary (t : Cell f g) (β : Bool) :
    (t.diag.boundary n β).Equiv (cond β b.diag.toPastingDiagram a.diag.toPastingDiagram) := by
  refine (equiv_boundary_boundary t.diag.toPastingDiagram (Nat.lt_succ_self n) false β).symm.trans
    ((t.source.equiv f.mem_rep).boundary n β |>.trans ?_)
  cases β
  · exact f.rep.hasBdry.side
  · exact f.rep.hasBdry.other

theorem _root_.Atoms.Diagrammatic.RoundBicat.Hom.Mem.pastable_left {f : a ⟶ b} {g : b ⟶ c}
    {x w : PastingDiagram X} (hx : f.Mem x) (hw : w.dim = n + 1 + 1)
    (hs : g.Mem (w.boundary (n + 1) false)) : x.Pastable w n :=
  ⟨hx.hasBdry.other.trans (((equiv_boundary_boundary w (by omega) false false).symm.trans
      hs.hasBdry.side).symm), lt_min (by rw [hx.dim_eq]; omega) (by rw [hw]; omega)⟩

theorem _root_.Atoms.Diagrammatic.RoundBicat.Hom.Mem.pastable_right {g : a ⟶ b} {h : b ⟶ c}
    {w z : PastingDiagram X} (hz : h.Mem z) (hw : w.dim = n + 1 + 1)
    (ht : g.Mem (w.boundary (n + 1) true)) : w.Pastable z n :=
  ⟨((equiv_boundary_boundary w (by omega) true true).symm.trans ht.hasBdry.other).trans
      hz.hasBdry.side.symm, lt_min (by rw [hw]; omega) (by rw [hz.dim_eq]; omega)⟩

noncomputable def whiskerLeftOf {f : a ⟶ b} {g h : b ⟶ c} {x : PastingDiagram X} (hx : f.Mem x)
    (w : PastingDiagram X) (hw : w.dim = n + 1 + 1) (hs : g.Mem (w.boundary (n + 1) false))
    (ht : h.Mem (w.boundary (n + 1) true)) : Cell (f ≫ g) (f ≫ h) :=
  have hc := (show HasBdry false (n + 1) w _ _ from ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩)
    |>.rounding_paste_cond false hx.isRound hx.dim_eq ht.isRound (hx.pastable_left hw hs)
  { diag := ⟨_, hc.choose_spec.choose_spec.2⟩
    dim_diag := hc.choose_spec.choose_spec.1.dim_h
    source := (Hom.Mem.comp hx hs _).of_equiv hc.choose_spec.choose_spec.1.side.symm
    target := (Hom.Mem.comp hx ht _).of_equiv hc.choose_spec.choose_spec.1.other.symm }

noncomputable def whiskerRightOf {f g : a ⟶ b} {h : b ⟶ c} {z : PastingDiagram X}
    (w : PastingDiagram X) (hw : w.dim = n + 1 + 1) (hs : f.Mem (w.boundary (n + 1) false))
    (ht : g.Mem (w.boundary (n + 1) true)) (hz : h.Mem z) : Cell (f ≫ h) (g ≫ h) :=
  have hc := (show HasBdry false (n + 1) w _ _ from ⟨hw, hs.dim_eq, ht.dim_eq, .refl _, .refl _⟩)
    |>.rounding_paste_cond true hz.isRound hz.dim_eq ht.isRound
      (hz.pastable_right hw ht)
  { diag := ⟨_, hc.choose_spec.choose_spec.2⟩
    dim_diag := hc.choose_spec.choose_spec.1.dim_h
    source := (Hom.Mem.comp hs hz _).of_equiv hc.choose_spec.choose_spec.1.side.symm
    target := (Hom.Mem.comp ht hz _).of_equiv hc.choose_spec.choose_spec.1.other.symm }

end Cell

variable {c : RoundBicat X n}

noncomputable def whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) : f ≫ g ⟶ f ≫ h :=
  Quotient.map (fun t : Cell g h => Cell.whiskerLeftOf f.mem_rep _ t.dim_diag t.source t.target)
    (fun t _ htt => equivalent_rounding_paste_cond false f.rep.diag.isRound f.rep.hasBdry.dim_h htt
      (t.hasBdry g.mem_rep h.mem_rep) h.mem_rep.isRound _ _ _ _) η

noncomputable def whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) : f ≫ h ⟶ g ≫ h :=
  Quotient.map (fun t : Cell f g => Cell.whiskerRightOf _ t.dim_diag t.source t.target h.mem_rep)
    (fun t _ htt => equivalent_rounding_paste_cond true h.rep.diag.isRound h.rep.hasBdry.dim_h htt
      (t.hasBdry f.mem_rep g.mem_rep) g.mem_rep.isRound _ _ _ _) η

theorem whiskerLeft_homMk (f : a ⟶ b) {g h : b ⟶ c} (t : Cell g h) :
    whiskerLeft f (homMk t) =
      homMk (Cell.whiskerLeftOf f.mem_rep _ t.dim_diag t.source t.target) :=
  rfl

theorem homMk_whiskerRight (t : Cell f g) (h : b ⟶ c) :
    whiskerRight (homMk t) h =
      homMk (Cell.whiskerRightOf _ t.dim_diag t.source t.target h.mem_rep) :=
  rfl

theorem Hom.Mem.isRoundIn {f : a ⟶ b} {x : PastingDiagram X} (hx : f.Mem x) :
    IsRoundIn ⟨n, a.diag.toPastingDiagram, b.diag.toPastingDiagram⟩ x :=
  ⟨⟨by change n < x.dim; rw [hx.dim_eq]; omega, hx.hasBdry.side, hx.hasBdry.other⟩, hx.dim_eq,
    hx.isRound⟩

noncomputable def unitorSpec (α : Bool) (a b : RoundBicat X n) : CylSpec X :=
  ⟨n, α, cond α b.diag.toPastingDiagram a.diag.toPastingDiagram, some ⟨_, Within.refl _,
    isRewritableSubmolecule_image_refl (by cases α; exacts [a.diag.isRound, b.diag.isRound])⟩⟩

theorem isRound_cond_diag (α : Bool) (a b : RoundBicat X n) :
    (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).IsRound := by
  cases α; exacts [a.diag.isRound, b.diag.isRound]

theorem dim_cond_diag (α : Bool) (a b : RoundBicat X n) :
    (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).dim = n := by
  cases α; exacts [a.dim_diag, b.dim_diag]

noncomputable abbrev unitCtx (α : Bool) (a b : RoundBicat X n) : CtxExpr X :=
  .side α (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit n (Within.refl _)
    (isRewritableSubmolecule_image_refl (isRound_cond_diag α a b)).isSubmoleculeOf
    (boundary_unit (dim_cond_diag α a b) (!α))

theorem isCylTriple_unitorSpec (α : Bool) {x : PastingDiagram X}
    (hx : IsRoundIn ⟨n, a.diag.toPastingDiagram, b.diag.toPastingDiagram⟩ x) :
    IsCylTriple (unitorSpec α a b) ⟨hx.roundHom, hx.roundHom, cond α (unitCtx α a b) .id,
      cond α .id (unitCtx α a b), (unitorSpec α a b).fam⟩ :=
  isCylTriple_unitor α hx.roundHom (Within.refl _)
    (isRewritableSubmolecule_image_refl (isRound_cond_diag α a b))
    (boundary_unit (dim_cond_diag α a b) (!α))

theorem unitorSpec_fam_spec (α : Bool) {x : PastingDiagram X}
    (hx : IsRoundIn ⟨n, a.diag.toPastingDiagram, b.diag.toPastingDiagram⟩ x) :
    ∃ (hr : ((unitorSpec α a b).fam x).IsRound)
      (hp : (cond α x (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit).Pastable
        (cond α (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit x) n),
      (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
        HasBdry α (n + 1) ((unitorSpec α a b).fam x) x
          ((cond α x (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit).paste
            (cond α (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit x) n hp) := by
  obtain ⟨hr, he, ht⟩ := (isCylTriple_unitorSpec α hx).valid.comp x hx
  have hdz := dim_cond_diag α a b
  have hp := Pastable.of_side α (hx.inHom.side α |>.trans (boundary_unit hdz (!α)).symm)
    (by rw [hx.dim_eq]; omega)
    (by change n < (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram).unit.dim
        rw [dim_unit, hdz]; omega)
  have e := CtxExpr.sidePaste_equiv_paste α
    (ι := Within.refl (cond α b.diag.toPastingDiagram a.diag.toPastingDiagram))
    (hι := (isRewritableSubmolecule_image_refl (isRound_cond_diag α a b)).isSubmoleculeOf)
    (Within.image_refl _) (boundary_unit hdz (!α)) (hx.inHom.side α) hp
  refine ⟨hr, hp, he, ?_⟩
  cases α
  · exact ht.of_equiv_other e
  · exact (ht.of_equiv_side e).symm

namespace Cell

noncomputable def leftUnitor (f : a ⟶ b) : Cell f (𝟙 a ≫ f) :=
  have h := unitorSpec_fam_spec false f.mem_rep.isRoundIn
  { diag := ⟨_, h.choose⟩
    dim_diag := h.choose_spec.choose_spec.2.dim_h
    source := f.mem_rep.of_equiv h.choose_spec.choose_spec.2.side.symm
    target := (Hom.Mem.comp (Hom.mem_id a) f.mem_rep _).of_equiv
      h.choose_spec.choose_spec.2.other.symm }

noncomputable def rightUnitor (f : a ⟶ b) : Cell (f ≫ 𝟙 b) f :=
  have h := unitorSpec_fam_spec true f.mem_rep.isRoundIn
  { diag := ⟨_, h.choose⟩
    dim_diag := h.choose_spec.choose_spec.2.dim_h
    source := (Hom.Mem.comp f.mem_rep (Hom.mem_id b) _).of_equiv
      h.choose_spec.choose_spec.2.other.symm
    target := f.mem_rep.of_equiv h.choose_spec.choose_spec.2.side.symm }

theorem leftUnitor_diag (f : a ⟶ b) :
    (leftUnitor f).diag.toPastingDiagram = (unitorSpec false a b).fam f.rep.diag.toPastingDiagram :=
  rfl

theorem rightUnitor_diag (f : a ⟶ b) :
    (rightUnitor f).diag.toPastingDiagram = (unitorSpec true a b).fam f.rep.diag.toPastingDiagram :=
  rfl

theorem leftUnitor_mem (f : a ⟶ b) : (leftUnitor f).diag ∈ equivalences X :=
  (unitorSpec_fam_spec false f.mem_rep.isRoundIn).choose_spec.choose_spec.1

theorem rightUnitor_mem (f : a ⟶ b) : (rightUnitor f).diag ∈ equivalences X :=
  (unitorSpec_fam_spec true f.mem_rep.isRoundIn).choose_spec.choose_spec.1

end Cell

instance (f : a ⟶ b) : IsIso (homMk (Cell.leftUnitor f)) :=
  (isIso_homMk_iff _).2 (Cell.leftUnitor_mem f)

instance (f : a ⟶ b) : IsIso (homMk (Cell.rightUnitor f)) :=
  (isIso_homMk_iff _).2 (Cell.rightUnitor_mem f)

noncomputable def leftUnitor (f : a ⟶ b) : 𝟙 a ≫ f ≅ f :=
  (asIso (homMk (Cell.leftUnitor f))).symm

noncomputable def rightUnitor (f : a ⟶ b) : f ≫ 𝟙 b ≅ f :=
  asIso (homMk (Cell.rightUnitor f))

theorem leftUnitor_inv (f : a ⟶ b) : (leftUnitor f).inv = homMk (Cell.leftUnitor f) :=
  rfl

theorem leftUnitor_hom (f : a ⟶ b) : (leftUnitor f).hom = inv (homMk (Cell.leftUnitor f)) :=
  rfl

theorem rightUnitor_hom (f : a ⟶ b) : (rightUnitor f).hom = homMk (Cell.rightUnitor f) :=
  rfl

end RoundBicat

end Atoms.Diagrammatic
