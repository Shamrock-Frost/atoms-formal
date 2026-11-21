import Atoms.Diagrammatic.Context.WeaklyInvertible
import Atoms.Diagrammatic.Equivalence.PastingCriterion

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def CtxExpr.PastesOn (α : Bool) : CtxExpr X → Prop
  | .side β _ _ _ _ _ => β = α
  | .id => True
  | .comp s t => s.PastesOn α ∧ t.PastesOn α

private theorem HasSideInverse.of_paste {S : Set (RoundPastingDiagram X)} (α : Bool) {n : ℕ}
    {u u' : RoundPastingDiagram X} (hdu : u.dim = n + 1)
    (hb : HasBdry false n u'.toPastingDiagram (u.boundary n true) (u.boundary n false))
    (hp : (cond α u'.toPastingDiagram u.toPastingDiagram).Pastable
      (cond α u.toPastingDiagram u'.toPastingDiagram) n)
    (hr : ((cond α u'.toPastingDiagram u.toPastingDiagram).paste
      (cond α u.toPastingDiagram u'.toPastingDiagram) n hp).IsRound)
    (h : cond α (ArrowIn S (isRound_boundary_of_isRound u.isRound n true).unit ⟨_, hr⟩)
      (ArrowIn S ⟨_, hr⟩ (isRound_boundary_of_isRound u.isRound n false).unit)) :
    HasSideInverse S α u := by
  cases α
  · let d : PasteAtData false n u u' := PasteAtData.ofBoundary hdu hb.dim_h hp.1
    have e := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf
      (Within.image_refl _) d.equiv hp
    exact ⟨n, u', d, hb, Within.image_refl _, h.of_equiv_left (u' := d.round) e⟩
  · let d : PasteAtData false n u' u := PasteAtData.ofBoundary hb.dim_h hdu hp.1
    have e := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf
      (Within.image_refl _) d.equiv hp
    exact ⟨n, u', d, hb, Within.image_refl _, h.of_equiv_right (v' := d.round) e⟩

private theorem HasSideInverse.exists_paste {S : Set (RoundPastingDiagram X)} {α : Bool}
    {u : RoundPastingDiagram X} (h : HasSideInverse S α u) :
    ∃ (n : ℕ) (u' : RoundPastingDiagram X), u.dim = n + 1 ∧
      HasBdry false n u'.toPastingDiagram (u.boundary n true) (u.boundary n false) ∧
      ∃ (hp : (cond α u'.toPastingDiagram u.toPastingDiagram).Pastable
          (cond α u.toPastingDiagram u'.toPastingDiagram) n)
        (hr : ((cond α u'.toPastingDiagram u.toPastingDiagram).paste
          (cond α u.toPastingDiagram u'.toPastingDiagram) n hp).IsRound),
        cond α (ArrowIn S (isRound_boundary_of_isRound u.isRound n true).unit ⟨_, hr⟩)
          (ArrowIn S ⟨_, hr⟩ (isRound_boundary_of_isRound u.isRound n false).unit) := by
  obtain ⟨n, u', d, hb, hocc, ha⟩ := h
  have hpst : (cond α u' u).toPastingDiagram.Pastable (cond α u u').toPastingDiagram n :=
    ⟨d.equiv.trans (Within.equiv_of_image_eq d.occ (Within.refl _)
      (by rw [hocc, Within.image_refl])), by rw [d.dim_e, d.dim_u']; omega⟩
  have e := equiv_paste_pasteAtBoundary _ _ _ false d.occ d.rewritable.isSubmoleculeOf hocc
    d.equiv hpst
  have hr : ((cond α u' u).toPastingDiagram.paste (cond α u u').toPastingDiagram n hpst).IsRound :=
    e.isRound_iff.2 d.isRound_pasting
  cases α
  · exact ⟨n, u', d.dim_e, hb, hpst, hr, ha.of_equiv_left (u' := ⟨_, hr⟩) e.symm⟩
  · exact ⟨n, u', d.dim_u', hb, hpst, hr, ha.of_equiv_right (v' := ⟨_, hr⟩) e.symm⟩

theorem hasSideInverse_of_mem_equivalences (A : Set (RoundPastingDiagram X)) (β : Bool)
    {v : RoundPastingDiagram X} (hv : v ∈ equivalences X) :
    HasSideInverse (PastingClosure A) β v := by
  rw [← biInvOperator_equivalences, mem_biInvOperator_iff] at hv
  cases β
  exacts [hv.1.mono (equivalences_subset_pastingClosure A),
    hv.2.mono (equivalences_subset_pastingClosure A)]

theorem HasSideInverse.of_arrowIn {A : Set (RoundPastingDiagram X)} {β : Bool}
    {v y : RoundPastingDiagram X} (hv : HasSideInverse (PastingClosure A) β v)
    (h : cond β (ArrowIn (PastingClosure A) v y) (ArrowIn (PastingClosure A) y v)) :
    HasSideInverse (PastingClosure A) β y := by
  obtain ⟨n, v', hdv, hb, hp, hr, ha⟩ := hv.exists_paste
  have hd : y.dim = v.dim := by
    cases β
    · exact h.elim fun _ hh => hh.2.dim_a.trans hh.2.dim_b.symm
    · exact h.elim fun _ hh => hh.2.dim_b.trans hh.2.dim_a
  have hk : n < v.dim := by omega
  have hby : ∀ γ, (y.boundary n γ).Equiv (v.boundary n γ) := fun γ => by
    cases β
    · exact h.equiv_boundary (by omega) γ
    · exact (h.equiv_boundary hk γ).symm
  have hb' : HasBdry false n v'.toPastingDiagram (y.boundary n true) (y.boundary n false) :=
    ⟨hb.dim_h, by rw [dim_boundary _ (by omega)], by rw [dim_boundary _ (by omega)],
      hb.side.trans (hby true).symm, hb.other.trans (hby false).symm⟩
  have hdv' : v'.dim = y.dim := by rw [hb.dim_h, hd, hdv]
  cases β
  · have hp' : y.toPastingDiagram.Pastable v'.toPastingDiagram n :=
      ⟨(hby true).trans hp.1, by rw [hdv', hd, hdv]; omega⟩
    have hr' := isRound_paste_of_dim y v' (hd.trans hdv) hb.dim_h hp'
    refine HasSideInverse.of_paste false (hd.trans hdv) hb' hp' hr' ?_
    exact ((arrowIn_pastingClosure_paste_cond false h rfl hdv' hp' hp hr' hr).trans_pastingClosure
      ha).of_equiv_right (Equiv.unit (hby false).symm)
  · have hp' : v'.toPastingDiagram.Pastable y.toPastingDiagram n :=
      ⟨hp.1.trans (hby false).symm, by rw [hdv', hd, hdv]; omega⟩
    have hr' := isRound_paste_of_dim v' y hb.dim_h (hd.trans hdv) hp'
    refine HasSideInverse.of_paste true (hd.trans hdv) hb' hp' hr' ?_
    exact (ha.trans_pastingClosure (arrowIn_pastingClosure_paste_cond true h rfl
      (hb.dim_h.trans hdv.symm) hp hp'
      hr hr')).of_equiv_left (Equiv.unit (hby true).symm)

private theorem exists_inverse_of_hasSideInverse_paste_cond {A : Set (RoundPastingDiagram X)}
    (α : Bool) {k : ℕ} {y r : PastingDiagram X} (hdy : y.dim = k + 1) (hdr : r.dim = k + 1)
    (hp : (cond α y r).Pastable (cond α r y) k)
    (hround : ((cond α y r).paste (cond α r y) k hp).IsRound)
    (h : HasSideInverse (PastingClosure A) (!α) ⟨_, hround⟩) :
    ∃ w : RoundPastingDiagram X, HasBdry false k w.toPastingDiagram (y.boundary k true)
      (y.boundary k false) ∧
      ∃ (hpw : (cond (!α) w.toPastingDiagram y).Pastable (cond (!α) y w.toPastingDiagram) k)
        (hrw : ((cond (!α) w.toPastingDiagram y).paste (cond (!α) y w.toPastingDiagram) k
          hpw).IsRound),
        cond (!α) (ArrowIn (PastingClosure A) (isRound_boundary_of_isRound hrw k true).unit
          ⟨_, hrw⟩)
          (ArrowIn (PastingClosure A) ⟨_, hrw⟩ (isRound_boundary_of_isRound hrw k false).unit) := by
  obtain ⟨n, v, hdn, hb, hpv, _, ha⟩ := h.exists_paste
  have hdp : ((cond α y r).paste (cond α r y) k hp).dim = k + 1 := by
    rw [dim_paste_cond]; omega
  obtain rfl : n = k := by
    change ((cond α y r).paste _ k hp).dim = n + 1 at hdn
    omega
  have hb₁ := equiv_boundary_paste hp false
  have hb₂ := equiv_boundary_paste hp true
  cases α
  · have h₁ : v.toPastingDiagram.Pastable r n :=
      ⟨hpv.1.trans hb₁, by rw [hb.dim_h, hdr]; omega⟩
    have hdvr : (v.toPastingDiagram.paste r n h₁).dim = n + 1 := by
      rw [dim_paste, hb.dim_h, hdr, max_self]
    have h₂ : (v.toPastingDiagram.paste r n h₁).Pastable y n :=
      ⟨(equiv_boundary_paste h₁ true).trans hp.1, by rw [hdvr, hdy]; omega⟩
    obtain ⟨_, _, ea⟩ := equiv_paste_assoc h₁ h₂
    have hrvr := isRound_paste_of_round false (u := v.toPastingDiagram) h₁ v.isRound hb.dim_h hdr.le
    have hr' := isRound_paste_of_round false (u := v.toPastingDiagram.paste r n h₁) h₂ hrvr hdvr
      hdy.le
    refine ⟨⟨_, hrvr⟩, ⟨hdvr, dim_boundary _ (by omega) _, dim_boundary _ (by omega) _,
      (equiv_boundary_paste h₁ false).trans (hb.side.trans hb₂),
      (equiv_boundary_paste h₁ true).trans hp.1⟩, h₂, hr', ?_⟩
    exact (ha.of_equiv_right (v' := ⟨_, hr'⟩) ea.symm).of_equiv_left
      (Equiv.unit (hb₂.trans (equiv_boundary_paste h₂ true).symm))
  · obtain ⟨h₃, h₄, ea⟩ := equiv_paste_assoc hp hpv
    have hdrv : (r.paste v.toPastingDiagram n h₃).dim = n + 1 := by
      rw [dim_paste, hb.dim_h, hdr, max_self]
    have hrrv := isRound_paste_of_round true (u := v.toPastingDiagram) h₃ v.isRound hb.dim_h hdr.le
    have hr' := isRound_paste_of_round true (u := r.paste v.toPastingDiagram n h₃) h₄ hrrv hdrv
      hdy.le
    refine ⟨⟨_, hrrv⟩, ⟨hdrv, dim_boundary _ (by omega) _, dim_boundary _ (by omega) _,
      (equiv_boundary_paste h₃ false).trans hp.1.symm,
      (equiv_boundary_paste h₃ true).trans (hb.other.trans hb₁)⟩, h₄, hr', ?_⟩
    exact (ha.of_equiv_left (u' := ⟨_, hr'⟩) ea).of_equiv_right
      (Equiv.unit (hb₁.trans (equiv_boundary_paste h₄ false).symm))

theorem HasSideInverse.of_paste_cond {A : Set (RoundPastingDiagram X)} (α : Bool) {k : ℕ}
    {y r : RoundPastingDiagram X} (hdy : y.dim = k + 1) (hdr : r.dim = k + 1)
    (hp : (cond α y.toPastingDiagram r.toPastingDiagram).Pastable
      (cond α r.toPastingDiagram y.toPastingDiagram) k)
    (hround : ((cond α y.toPastingDiagram r.toPastingDiagram).paste
      (cond α r.toPastingDiagram y.toPastingDiagram) k hp).IsRound)
    (h : HasSideInverse (PastingClosure A) (!α) ⟨_, hround⟩) :
    HasSideInverse (PastingClosure A) (!α) y := by
  obtain ⟨w, hb, hpw, hrw, hw⟩ := exists_inverse_of_hasSideInverse_paste_cond α hdy hdr hp hround h
  cases α
  · exact HasSideInverse.of_paste true hdy hb hpw hrw
      (hw.of_equiv_left (Equiv.unit (equiv_boundary_paste hpw true)))
  · exact HasSideInverse.of_paste false hdy hb hpw hrw
      (hw.of_equiv_right (Equiv.unit (equiv_boundary_paste hpw false)))

private theorem CtxExpr.Typed.exists_frameOf_app_frameOf {A : Set (RoundPastingDiagram X)}
    {H H' : PdHom X} {T : CtxExpr X} (hT : T.Typed A False H H') {α : Bool} (hTα : T.PastesOn α)
    {H₁ : PdHom X} {r : PastingDiagram X} (hk : H.k = H₁.k) (hdr : r.dim ≤ H₁.k + 1)
    (hkr : H₁.k ≤ r.dim) (hin : (r.boundary H₁.k (!α)).Equiv (H₁.side α))
    (hout : (r.boundary H₁.k α).Equiv (H.side α)) :
    ∃ r' : PastingDiagram X, r'.dim ≤ H₁.k + 1 ∧ H₁.k ≤ r'.dim ∧
      (r'.boundary H₁.k (!α)).Equiv (H₁.side α) ∧ (r'.boundary H₁.k α).Equiv (H'.side α) ∧
      ∀ y, InHom H₁ y →
        (T.app ((CtxExpr.frameOf α r H₁.k).app y)).Equiv ((CtxExpr.frameOf α r' H₁.k).app y) := by
  induction hT generalizing r with
  | @side H H' β v₀ u hu hdu V ι hι h hs e =>
    obtain rfl : β = α := hTα
    obtain ⟨k₁, v₁, w₁⟩ := H₁
    change H.k = k₁ at hk
    subst hk
    have hdv₀ := CtxExpr.Typed.dim_side_of_isRewritable u hdu ι hι h
    have hsf : (r.boundary H.k β).Equiv v₀ := hout.trans hs.symm
    have es := e.side β
    rw [PdHom.side_setSide_self] at es
    refine ⟨(CtxExpr.side β u.toPastingDiagram H.k ι hι.isSubmoleculeOf h).app r, ?_, ?_,
      (equiv_boundary_not_sidePaste hsf).trans hin, ?_, fun y hy => ?_⟩
    · change (sidePaste _ _ _ _ _ _ _).dim ≤ _
      rw [sidePaste_of hsf, dim_pasteAtBoundary, hdu]
      exact max_le le_rfl hdr
    · change _ ≤ (sidePaste _ _ _ _ _ _ _).dim
      rw [sidePaste_of hsf, dim_pasteAtBoundary, hdu]
      exact le_max_of_le_right hkr
    · exact (equiv_boundary_sidePaste_of_side u.isRound hdu hι hsf
        (equiv_boundary_dim v₀ hdv₀.le β) hkr hdv₀.ge).trans es
    · exact CtxExpr.side_app_frameOf hdu hdr hkr hsf ((hy.side β).trans hin.symm) hy.lt_dim
  | id e =>
    exact ⟨r, hdr, hkr, hin, hout.trans (e.side α), fun _ _ => .refl _⟩
  | comp ht₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, h₁, h₂, h₃, h₄, e₁⟩ := ih₁ hTα.2 hk hdr hkr hin hout
    obtain ⟨r₂, h₅, h₆, h₇, h₈, e₂⟩ := ih₂ hTα.1 (ht₁.k_eq.trans hk) h₁ h₂ h₃ h₄
    exact ⟨r₂, h₅, h₆, h₇, h₈, fun y hy => (CtxExpr.app_equiv _ (e₁ y hy)).trans (e₂ y hy)⟩
  | promote hp => exact hp.elim

theorem CtxExpr.Typed.exists_frameOf_of_pastesOn {A : Set (RoundPastingDiagram X)}
    {H H' : PdHom X} {T : CtxExpr X} (hT : T.Typed A False H H') {α : Bool}
    (hTα : T.PastesOn α) (hd : (H.side α).dim = H.k) :
    ∃ r : PastingDiagram X, r.dim ≤ H.k + 1 ∧ H.k ≤ r.dim ∧
      (r.boundary H.k (!α)).Equiv (H.side α) ∧ (r.boundary H.k α).Equiv (H'.side α) ∧
      ∀ y, InHom H y → (T.app y).Equiv ((CtxExpr.frameOf α r H.k).app y) := by
  obtain ⟨r, h₁, h₂, h₃, h₄, e⟩ := hT.exists_frameOf_app_frameOf hTα rfl (by omega) hd.ge
    (equiv_boundary_dim _ hd.le (!α)) (equiv_boundary_dim _ hd.le α)
  refine ⟨r, h₁, h₂, h₃, h₄, fun y hy => ?_⟩
  have ey := e y hy
  rw [CtxExpr.frameOf_of_not α (by omega)] at ey
  exact ey

theorem NatSim.exists_square {H H' : PdHom X} {F G : PastingDiagram X → PastingDiagram X}
    (h : NatSim X H H' F G) {a b : PastingDiagram X} (ha : IsRoundIn H a) (hb : IsRoundIn H b) :
    ∃ ϑ : PastingDiagram X → PastingDiagram X,
      (∀ c, IsRoundIn H c → ∃ hr : (ϑ c).IsRound,
        (⟨ϑ c, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
          HasBdry false (H.k + 1) (ϑ c) (F c) (G c)) ∧
      NatSim X ⟨H.k + 1, a, b⟩ ⟨H.k + 1, F a, G b⟩
        (fun x => (CtxExpr.paste true (ϑ b) (H.k + 1)).app (F x))
        (fun x => (CtxExpr.paste false (ϑ a) (H.k + 1)).app (G x)) := by
  obtain ⟨σ, hσ, r⟩ := h
  have hσ' : σ ∈ natEqv X := by rw [← closure_natEqv]; exact hσ
  have hk : σ.dom.k = H.k := r.equiv_dom.k_eq
  rw [← natOp_natEqv] at hσ'
  obtain ⟨hv, N⟩ := hσ'
  refine ⟨σ.ϑ, fun c hc => ?_, ?_⟩
  · obtain ⟨hr, he, ht⟩ := hv.comp c (hc.congr r.equiv_dom.symm)
    rw [hk] at ht
    exact ⟨hr, he, (ht.of_equiv_side (r.equiv_F c hc.inHom)).of_equiv_other
      (r.equiv_G c hc.inHom)⟩
  · obtain ⟨σ', hσ'', r'⟩ := N a b (ha.congr r.equiv_dom.symm) (hb.congr r.equiv_dom.symm)
    have e₁ : PdHom.Equiv ⟨σ.dom.k + 1, a, b⟩ ⟨H.k + 1, a, b⟩ :=
      ⟨congrArg (· + 1) hk, .refl _, .refl _⟩
    have hF : ∀ c, InHom ⟨σ.dom.k + 1, a, b⟩ c → ((σ.nextF b).app c).Equiv
        ((CtxExpr.paste true (σ.ϑ b) (H.k + 1)).app (F c)) := fun c hc => by
      rw [← hk]
      exact CtxExpr.app_equiv (CtxExpr.paste true (σ.ϑ b) (σ.dom.k + 1))
        (r.equiv_F c (InHom.of_inHom_succ (hc.congr e₁) ha.inHom hb.inHom))
    have hG : ∀ c, InHom ⟨σ.dom.k + 1, a, b⟩ c → ((σ.nextG a).app c).Equiv
        ((CtxExpr.paste false (σ.ϑ a) (H.k + 1)).app (G c)) := fun c hc => by
      rw [← hk]
      exact CtxExpr.app_equiv (CtxExpr.paste false (σ.ϑ a) (σ.dom.k + 1))
        (r.equiv_G c (InHom.of_inHom_succ (hc.congr e₁) ha.inHom hb.inHom))
    exact ⟨σ', .base hσ'', (CtxTriple.Realizes.of_equiv r' hF hG).congr e₁
      ⟨congrArg (· + 1) hk, r.equiv_F a ha.inHom, r.equiv_G b hb.inHom⟩⟩

section ArgOcc

variable {k n : ℕ} {x y V B : PastingDiagram X} {ω : Within x y} {Fr : LowerSet y.shape.ogp}

private noncomputable def argOcc (hω : ArgLoc k ω Fr) (hkn : k < n) (β : Bool)
    (eV : V.Equiv (x.boundary n β)) (eB : (y.boundary n β).Equiv B) : Within V B :=
  (Within.ofEquiv eV).trans ((Within.ofImageLE ((Within.boundary x n β).trans ω)
    (Within.boundary y n β) (by
      rw [Within.image_boundary_trans, Within.image_boundary]
      exact (hω.isSubmoleculeOf hkn β).le)).trans (Within.ofEquiv eB))

private theorem argOcc_trans_ofEquiv (hω : ArgLoc k ω Fr) (hkn : k < n) (β : Bool)
    (eV : V.Equiv (x.boundary n β)) (eB : (y.boundary n β).Equiv B) {B' : PastingDiagram X}
    (f : B.Equiv B') :
    (argOcc hω hkn β eV eB).trans (Within.ofEquiv f) = argOcc hω hkn β eV (eB.trans f) := by
  rw [argOcc, argOcc, Within.trans_assoc, Within.trans_assoc]
  congr 2
  exact Within.ext_of_image_eq _ _ (by
    rw [Within.image_ofEquiv_trans, Within.image_ofEquiv, Within.image_ofEquiv])

private theorem isRewritableSubmolecule_image_argOcc (hω : ArgLoc k ω Fr) (hkn : k < n)
    (β : Bool) (eV : V.Equiv (x.boundary n β)) (eB : (y.boundary n β).Equiv B) (hr : V.IsRound)
    (hd : V.dim = B.dim) :
    B.shape.ogp.IsRewritableSubmolecule (argOcc hω hkn β eV eB).image ⊤ := by
  refine (Within.isRewritableSubmolecule_image_iff _).2 ⟨?_, hr, hd⟩
  rw [argOcc, Within.image_ofEquiv_trans, Within.isSubmoleculeOf_image_trans_ofEquiv_iff]
  refine (isSubmoleculeOf_map_iff (Within.boundary y n β).emb).1 ?_
  rw [← Within.image_trans, Within.image_ofImageLE_trans, Within.image_boundary_trans]
  change y.shape.ogp.IsSubmoleculeOf _ (Within.boundary y n β).image
  rw [Within.image_boundary]
  exact hω.isSubmoleculeOf hkn β

private theorem image_argOcc_trans (hω : ArgLoc k ω Fr) (hkn : k < n) (β : Bool)
    (eV : V.Equiv (x.boundary n β)) (eB : (y.boundary n β).Equiv B) {m : PastingDiagram X}
    (wy : Within y m) (wB : Within B m) (hB : wB.image = m.shape.ogp.boundary wy.image n β) :
    ((argOcc hω hkn β eV eB).trans wB).image = m.shape.ogp.boundary (ω.trans wy).image n β := by
  have e : (Within.ofEquiv eB).trans wB = (Within.boundary y n β).trans wy :=
    Within.ext_of_image_eq _ _ (by rw [Within.image_ofEquiv_trans, hB, Within.image_boundary_trans])
  rw [argOcc, Within.trans_assoc, Within.trans_assoc, e, ← Within.trans_assoc _ _ wy,
    Within.ofImageLE_trans, Within.image_ofEquiv_trans, Within.trans_assoc,
    Within.image_boundary_trans]

end ArgOcc

private theorem image_trans_eq_of_image_eq {a a' b m : PastingDiagram X} {o : Within a b}
    {o' : Within a' b} (h : o.image = o'.image) (w : Within b m) :
    (o.trans w).image = (o'.trans w).image := by
  rw [Within.image_trans, Within.image_trans, h]

private theorem ArgLoc.isPastingAtIn_trans_cond {k : ℕ} {u e H m : PastingDiagram X}
    {Fr : LowerSet H.shape.ogp} {ω : Within e H} (hω : ArgLoc k ω Fr) (wU : Within u m)
    (wH : Within H m) (α : Bool)
    (hpm : m.shape.ogp.IsPastingIn (k + 1) (cond α wU.image wH.image) (cond α wH.image wU.image)
      ⊤) :
    m.shape.ogp.IsPastingAtIn (k + 1) α (ω.trans wH).image wU.image ⊤ := by
  obtain ⟨hsup, hmeetH, hmeetU⟩ := (isPastingIn_cond_iff α).1 hpm
  have hk1 : k < k + 1 := Nat.lt_succ_self k
  let wE := ω.trans wH
  have hE : wE.image = OGP.map wH.emb ω.image := Within.image_trans ω wH
  have hBH : m.shape.ogp.boundary wH.image (k + 1) (!α) =
      OGP.map wH.emb (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) (!α)) := by
    rw [← hω.boundary_eq hk1 (!α), map_boundary]
    rfl
  have hBE : m.shape.ogp.boundary wE.image (k + 1) (!α) =
      OGP.map wH.emb (H.shape.ogp.boundary ω.image (k + 1) (!α)) := by
    rw [hE, map_boundary]
  have hFr : OGP.map wH.emb Fr ≤ wU.image := by
    refine le_trans ?_ (hmeetH.ge.trans inf_le_left)
    rw [hBH, map_sup]
    exact le_sup_left
  have hinter : wE.image ⊓ wU.image = m.shape.ogp.boundary wE.image (k + 1) (!α) := by
    have hEH : wE.image ≤ wH.image := by rw [hE]; exact map_mono _ le_top
    refine le_antisymm ?_ (le_inf (boundary_le _ _ _) ?_)
    · calc wE.image ⊓ wU.image ≤ wE.image ⊓ (wU.image ⊓ wH.image) :=
            le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hEH))
        _ = OGP.map wH.emb (ω.image ⊓ (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) (!α))) := by
            rw [hmeetH, hBH, hE, OGP.map_inf]
        _ ≤ m.shape.ogp.boundary wE.image (k + 1) (!α) := by
            rw [hBE]
            refine map_mono _ ?_
            rw [inf_sup_left, inf_comm]
            exact sup_le (hω.inf_le hk1 (!α)) inf_le_right
    · calc m.shape.ogp.boundary wE.image (k + 1) (!α)
          ≤ OGP.map wH.emb (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) (!α)) := by
            rw [hBE]; exact map_mono _ le_sup_right
        _ = wU.image ⊓ wH.image := by rw [← hBH, hmeetH]
        _ ≤ wU.image := inf_le_left
  refine ⟨wE.isMoleculeIn_image, wU.isMoleculeIn_image, ?_, hinter, ?_⟩
  · have hH : wH.image = OGP.map wH.emb Fr ⊔ wE.image := by
      rw [hE, ← map_sup, ← hω.eq_sup]
      rfl
    rw [← hsup, hH, ← sup_assoc, sup_eq_left.2 hFr, sup_comm]
  · rw [hinter, ← hmeetU, hmeetH, hBE, hBH, ← hω.boundary_eq hk1 (!α)]
    exact (isSubmoleculeOf_map_iff wH.emb).2 (hω.isSubmoleculeOf hk1 (!α))

private theorem arrowIn_pasteAt_unit (A : Set (RoundPastingDiagram X)) {α : Bool} {n : ℕ}
    {e x : RoundPastingDiagram X} (d : PasteAtData α n e x) (he : e.Equiv d.sub.unit) :
    ArrowIn (PastingClosure A) d.round x ∧ ArrowIn (PastingClosure A) x d.round := by
  have hdx : x.dim = n + 1 := d.dim_u'
  obtain rfl : n = x.dim - 1 := by omega
  have hd : 0 < x.dim := by omega
  let d₀ := unitData x hd α d.occ d.rewritable
  let ε : RoundPastingDiagram X := (d.occ.round_image_iff.1 d.rewritable.isRound).unit
  have h₁ : ArrowIn (PastingClosure A) d.round d₀.round :=
    arrowIn_pastingClosure_pasteAt d d₀ rfl
      ((equivalent_of_equiv (v := ε) he).arrowIn_pastingClosure A)
  have h₂ : ArrowIn (PastingClosure A) d₀.round d.round :=
    arrowIn_pastingClosure_pasteAt d₀ d rfl
      ((equivalent_of_equiv (u := ε) (v := e) he.symm).arrowIn_pastingClosure A)
  have hl := hasBdry_unitorRound x hd α d.occ d.rewritable
  have hm := mem_equivalences_of_isDegenerate _ (isDegenerate_unitorRound x hd α d.occ d.rewritable)
  have hq : Equivalent x d₀.round := by
    cases α
    · rw [← hdx] at hl
      exact arrowIn_equivalences_iff.1 ⟨_, hm, hl.dim_h, hl.dim_b, hl.dim_a, hl.other, hl.side⟩
    · refine equivalent_symm (arrowIn_equivalences_iff.1 ⟨_, hm, ?_⟩)
      rw [show d₀.round.dim = x.dim - 1 + 1 from d₀.dim_pasting]
      exact hl
  exact ⟨h₁.trans_pastingClosure ((equivalent_symm hq).arrowIn_pastingClosure A),
    (hq.arrowIn_pastingClosure A).trans_pastingClosure h₂⟩

private theorem equiv_paste_pasteAt (α : Bool) {n : ℕ} {u ϑ w : RoundPastingDiagram X}
    (e : PasteAtData α n w ϑ)
    (hp : (cond α u.toPastingDiagram e.round.toPastingDiagram).Pastable
      (cond α e.round.toPastingDiagram u.toPastingDiagram) n)
    (hpb : (cond α u.toPastingDiagram ϑ.toPastingDiagram).Pastable
      (cond α ϑ.toPastingDiagram u.toPastingDiagram) n)
    (hrb : ((cond α u.toPastingDiagram ϑ.toPastingDiagram).paste
      (cond α ϑ.toPastingDiagram u.toPastingDiagram) n hpb).IsRound)
    (d : PasteAtData α n w ⟨_, hrb⟩)
    (f : (ϑ.boundary n α).Equiv (((cond α u.toPastingDiagram ϑ.toPastingDiagram).paste
      (cond α ϑ.toPastingDiagram u.toPastingDiagram) n hpb).boundary n α))
    (hocc : d.occ.image = (e.occ.trans (Within.ofEquiv f)).image) :
    ((cond α u.toPastingDiagram e.round.toPastingDiagram).paste
      (cond α e.round.toPastingDiagram u.toPastingDiagram) n hp).Equiv d.pasting := by
  classical
  let wE : Within e.pasting _ := Within.pasteIn α hp
  obtain ⟨wu, hN⟩ := Within.exists_isPastingIn_pasteIn α hp
  let ww := e.pasteAtInl.trans wE
  let wϑ := e.pasteAtInr.trans wE
  have he : IsPastingAtIn _ n α ww.image wϑ.image wE.image := e.isPastingAtIn_trans wE
  have he' : IsPastingAtIn _ n α ww.image wϑ.image (ww.image ⊔ wϑ.image) :=
    ⟨he.isMoleculeIn_left, he.isMoleculeIn_right, rfl, he.inf_eq, he.isSubmoleculeOf_inf⟩
  obtain ⟨hs, hi₁, hi₂⟩ : wu.image ⊔ wE.image = ⊤ ∧ wu.image ⊓ wE.image = _ ∧
      wu.image ⊓ wE.image = _ := (isPastingIn_cond_iff α).1 hN
  have hNf : IsPastingAtIn _ n α wE.image wu.image ⊤ :=
    ⟨wE.isMoleculeIn_image, wu.isMoleculeIn_image, hs.symm.trans (sup_comm _ _),
      (inf_comm _ _).trans hi₁, by
        rw [inf_comm, hi₂]
        exact IsSubmoleculeOf.refl (wu.isMoleculeIn_image.boundary n α)⟩
  rw [he.eq_sup] at hNf
  obtain ⟨c1, c2⟩ := he'.assoc_right hNf
  have hb1 : wϑ.image ⊓ wu.image = _ :=
    c1.inf_eq.trans (he.boundary_not.symm.trans (hi₁.symm.trans hi₂))
  have hQ := c1.isPastingIn_of_inf_eq hb1
  let wQ : Within ((cond α u.toPastingDiagram ϑ.toPastingDiagram).paste
      (cond α ϑ.toPastingDiagram u.toPastingDiagram) n hpb) _ :=
    (Within.ofEquiv (equiv_paste_cond_of_within α wu wϑ hQ c1.isMoleculeIn hpb)).trans
      (Within.restrictTo _ c1.isMoleculeIn)
  have hwQ : wQ.image = wϑ.image ⊔ wu.image :=
    (Within.image_ofEquiv_trans _ _).trans (Within.image_restrictTo _ _)
  rw [← hwQ] at c2
  have hf : (Within.ofEquiv f).trans ((Within.boundary ((cond α u.toPastingDiagram
      ϑ.toPastingDiagram).paste (cond α ϑ.toPastingDiagram u.toPastingDiagram) n hpb) n α).trans
        wQ) = (Within.boundary ϑ.toPastingDiagram n α).trans wϑ :=
    Within.ext_of_image_eq _ _ (by
      rw [Within.image_ofEquiv_trans, Within.image_boundary_trans, Within.image_boundary_trans,
        hwQ]
      exact c1.boundary_eq_left_of_inf_eq hb1)
  have hmeet : (d.occ.trans ((Within.boundary ((cond α u.toPastingDiagram
      ϑ.toPastingDiagram).paste (cond α ϑ.toPastingDiagram u.toPastingDiagram) n hpb) n α).trans
        wQ)).image = ww.image ⊓ wQ.image := by
    rw [image_trans_eq_of_image_eq hocc, Within.trans_assoc, hf, c2.inf_eq, ← Within.trans_assoc]
    refine (Within.image_trans_assoc _ e.pasteAtInr wE).trans ?_
    rw [Within.trans_assoc, e.image_occ_pasteAtInr]
    exact ((OGP.map_inf _ _ _).trans (congrArg₂ (· ⊓ ·) (Within.image_trans _ _).symm
      (Within.image_trans _ _).symm)).trans he.inf_eq
  obtain ⟨wd, hwd⟩ := d.exists_within ww wQ c2 hmeet
  exact (Within.equiv_of_image_eq wd (Within.refl _) (hwd.trans (Within.image_refl _).symm)).symm

private theorem equiv_pasteAt_paste_argLoc (α : Bool) {k : ℕ} {w ϑ : RoundPastingDiagram X}
    {y z : PastingDiagram X} {ω : Within y z} {Fr : LowerSet z.shape.ogp} (hω : ArgLoc k ω Fr)
    (hpa : (cond α ϑ.toPastingDiagram z).Pastable (cond α z ϑ.toPastingDiagram) (k + 1))
    (hra : ((cond α ϑ.toPastingDiagram z).paste (cond α z ϑ.toPastingDiagram) _ hpa).IsRound)
    (d : PasteAtData α (k + 1) w ⟨_, hra⟩) (eV : d.sub.Equiv (y.boundary (k + 1) α))
    (eB : (z.boundary (k + 1) α).Equiv
      (((cond α ϑ.toPastingDiagram z).paste (cond α z ϑ.toPastingDiagram) (k + 1) hpa).boundary
        (k + 1) α))
    (hocc : d.occ.image = (argOcc hω (Nat.lt_succ_self k) α eV eB).image)
    (hpy : (cond α y w.toPastingDiagram).Pastable (cond α w.toPastingDiagram y) (k + 1))
    (hry : ((cond α y w.toPastingDiagram).paste (cond α w.toPastingDiagram y) _ hpy).IsRound)
    (d' : PasteAtData α (k + 1) ⟨_, hry⟩ ϑ) (eV' : d'.sub.Equiv (y.boundary (k + 1) (!α)))
    (eB' : (z.boundary (k + 1) (!α)).Equiv (ϑ.boundary (k + 1) α))
    (hocc' : d'.occ.image = (argOcc hω (Nat.lt_succ_self k) (!α) eV' eB').image) :
    d.pasting.Equiv d'.pasting := by
  classical
  let wP : Within ((cond α ϑ.toPastingDiagram z).paste (cond α z ϑ.toPastingDiagram) (k + 1) hpa)
    d.pasting := d.pasteAtInr
  let ww : Within w.toPastingDiagram d.pasting := d.pasteAtInl
  obtain ⟨wϑ, hϑz⟩ := Within.exists_isPastingIn_pasteIn α hpa
  let wA := wϑ.trans wP
  let wZ := (Within.pasteIn α hpa).trans wP
  let wy := ω.trans wZ
  have hM : IsPastingAtIn _ (k + 1) α ww.image wP.image ⊤ := d.isPastingAtIn_pasteAtInl
  have hP : IsPastingIn _ (k + 1) (cond α wA.image wZ.image) (cond α wZ.image wA.image)
      wP.image := by
    have h := (isPastingIn_map_iff wP.emb (k + 1) _ _ _).2 hϑz
    rwa [Bool.apply_cond (OGP.map wP.emb), Bool.apply_cond (OGP.map wP.emb), ← Within.image_trans,
      ← Within.image_trans] at h
  have hyA : IsPastingAtIn _ (k + 1) α wy.image wA.image wP.image := by
    have e1 : wy.image = OGP.map wP.emb (ω.trans (Within.pasteIn α hpa)).image :=
      Within.image_trans_assoc _ _ _
    have e2 : wA.image = OGP.map wP.emb wϑ.image := Within.image_trans _ _
    rw [e1, e2]
    exact (ArgLoc.isPastingAtIn_trans_cond hω wϑ _ α hϑz).map wP.emb
  obtain ⟨-, hPm, hPb⟩ := (isPastingIn_cond_iff α).1 hP
  have hdo : ww.image ⊓ wP.image = d.pasting.shape.ogp.boundary wy.image (k + 1) α := by
    refine d.image_occ_pasteAtInr.symm.trans ((image_trans_eq_of_image_eq hocc _).trans ?_)
    refine image_argOcc_trans hω _ α eV eB wZ _ ?_
    rw [Within.image_boundary_trans]
    exact hP.boundary_cond α
  have hww : ww.image ⊓ wP.image = d.pasting.shape.ogp.boundary ww.image (k + 1) (!α) :=
    hM.inf_eq
  have hinf : wy.image ⊓ ww.image = d.pasting.shape.ogp.boundary wy.image (k + 1) α :=
    le_antisymm ((le_inf inf_le_right (inf_le_left.trans hyA.left_le)).trans hdo.le)
      (le_inf (boundary_le _ _ _) (hdo.ge.trans inf_le_left))
  have h₁ : IsPastingAtIn _ (k + 1) (!α) wy.image ww.image (wy.image ⊔ ww.image) :=
    ⟨wy.isMoleculeIn_image, ww.isMoleculeIn_image, rfl, by rw [Bool.not_not]; exact hinf, by
      rw [hinf, ← hdo, hww]
      exact IsSubmoleculeOf.refl (ww.isMoleculeIn_image.boundary _ _)⟩
  have hYe : wy.image ⊓ ww.image = _ := hinf.trans (hdo.symm.trans hww)
  have hYin : IsPastingIn _ (k + 1) (cond α wy.image ww.image) (cond α ww.image wy.image)
      (wy.image ⊔ ww.image) := by
    simpa only [Bool.cond_not] using h₁.isPastingIn_of_inf_eq hYe
  have hmid : (wy.image ⊔ ww.image) ⊓ wA.image = wy.image ⊓ wA.image := by
    refine le_antisymm ?_ (inf_le_inf_right _ le_sup_left)
    rw [inf_sup_right]
    refine sup_le le_rfl (le_inf ?_ inf_le_right)
    calc ww.image ⊓ wA.image ≤ ww.image ⊓ wP.image := inf_le_inf_left _ hyA.right_le
      _ ≤ wy.image := hdo.le.trans (boundary_le _ _ _)
  have hc : IsPastingAtIn _ (k + 1) α (wy.image ⊔ ww.image) wA.image ⊤ :=
    ⟨h₁.isMoleculeIn, hyA.isMoleculeIn_right, by
      rw [hM.eq_sup, hyA.eq_sup, sup_comm wy.image ww.image, sup_assoc],
      hmid.trans (hyA.inf_eq.trans (h₁.boundary_eq_left_of_inf_eq hYe).symm),
      hmid ▸ hyA.isSubmoleculeOf_inf⟩
  let wY : Within ((cond α y w.toPastingDiagram).paste (cond α w.toPastingDiagram y) (k + 1) hpy)
      d.pasting :=
    (Within.ofEquiv (equiv_paste_cond_of_within α wy ww hYin h₁.isMoleculeIn hpy)).trans
      (Within.restrictTo _ h₁.isMoleculeIn)
  have hwY : wY.image = wy.image ⊔ ww.image :=
    (Within.image_ofEquiv_trans _ _).trans (Within.image_restrictTo _ _)
  rw [← hwY] at hc
  have hmeet : (d'.occ.trans ((Within.boundary ϑ.toPastingDiagram (k + 1) α).trans wA)).image =
      wY.image ⊓ wA.image := by
    rw [image_trans_eq_of_image_eq hocc', image_argOcc_trans hω _ (!α) eV' eB' wZ _ (by
        rw [Within.image_boundary_trans, ← hPb, hPm]),
      hc.inf_eq, hwY, h₁.boundary_eq_left_of_inf_eq hYe]
  obtain ⟨wd, hwd⟩ := d'.exists_within wY wA hc hmeet
  exact (Within.equiv_of_image_eq wd (Within.refl _) (hwd.trans (Within.image_refl _).symm)).symm

private theorem exists_arrowIn_paste_pasteAt_true {A : Set (RoundPastingDiagram X)} {k : ℕ}
    {u w ϑa ϑb : RoundPastingDiagram X} {y z : PastingDiagram X} {ω : Within y z}
    {Fr : LowerSet z.shape.ogp} (hω : ArgLoc k ω Fr) (hdu : u.dim = k + 1 + 1)
    (hdy : y.dim = k + 1 + 1) (hdz : z.dim = k + 1 + 1)
    (hϑa : HasBdry false (k + 1) ϑa.toPastingDiagram (u.boundary (k + 1) false)
      (z.boundary (k + 1) false))
    (hϑb : HasBdry false (k + 1) ϑb.toPastingDiagram (u.boundary (k + 1) true)
      (z.boundary (k + 1) true))
    (hpa : ϑa.toPastingDiagram.Pastable z (k + 1))
    (hra : (ϑa.toPastingDiagram.paste z _ hpa).IsRound)
    (hpb : u.toPastingDiagram.Pastable ϑb.toPastingDiagram (k + 1))
    (hrb : (u.toPastingDiagram.paste ϑb.toPastingDiagram _ hpb).IsRound)
    (hsq : Equivalent ⟨_, hrb⟩ ⟨_, hra⟩)
    (hw : HasBdry false (k + 1) w.toPastingDiagram (y.boundary (k + 1) true)
      (y.boundary (k + 1) false))
    (hpy : y.Pastable w.toPastingDiagram (k + 1))
    (hry : (y.paste w.toPastingDiagram _ hpy).IsRound)
    (hyw : ArrowIn (PastingClosure A) ⟨_, hry⟩
      (isRound_boundary_of_isRound hry (k + 1) false).unit) :
    ∃ (E : RoundPastingDiagram X) (hp : u.toPastingDiagram.Pastable E.toPastingDiagram (k + 1)),
      E.dim = k + 1 + 1 ∧ ∃ hr : (u.toPastingDiagram.paste E.toPastingDiagram _ hp).IsRound,
        ArrowIn (PastingClosure A) ⟨_, hr⟩ ϑa := by
  have hk : k < k + 1 := Nat.lt_succ_self k
  have hdw := hw.dim_h
  have hdb := hϑb.dim_h
  have hda := hϑa.dim_h
  have hιb := isRewritableSubmolecule_image_argOcc hω hk true hw.side hϑb.other.symm
    (isRound_boundary_of_isRound w.isRound _ _)
    (by rw [dim_boundary _ (by omega), dim_boundary _ (by omega)])
  let e : PasteAtData true (k + 1) w ϑb := ⟨hdw, hdb, _, _, hιb, .refl _⟩
  have hdE : e.pasting.dim = k + 1 + 1 := e.dim_pasting
  have hp : u.toPastingDiagram.Pastable e.round.toPastingDiagram (k + 1) :=
    ⟨hϑb.side.symm.trans e.equiv_boundary_not.symm, lt_min (by omega) (by
      change k + 1 < e.pasting.dim
      omega)⟩
  have hr := isRound_paste_of_dim u e.round hdu e.dim_pasting hp
  refine ⟨e.round, hp, e.dim_pasting, hr, ?_⟩
  let Q : RoundPastingDiagram X := ⟨_, hrb⟩
  let P : RoundPastingDiagram X := ⟨_, hra⟩
  have hdQ : Q.dim = k + 1 + 1 := by
    change (u.toPastingDiagram.paste _ _ hpb).dim = _
    rw [dim_paste, hdu, hdb, max_self]
  have hdP : P.dim = k + 1 + 1 := by
    change (ϑa.toPastingDiagram.paste _ _ hpa).dim = _
    rw [dim_paste, hda, hdz, max_self]
  have hQP : ArrowIn (PastingClosure A) Q P := hsq.arrowIn_pastingClosure A
  have f₁ : (ϑb.boundary (k + 1) true).Equiv (Q.boundary (k + 1) true) :=
    (equiv_boundary_paste hpb true).symm
  have f : (Q.boundary (k + 1) true).Equiv (P.boundary (k + 1) true) :=
    hQP.equiv_boundary (by omega) true
  let d₁ : PasteAtData true (k + 1) w Q := ⟨hdw, hdQ, _, e.occ.trans (Within.ofEquiv f₁),
    (Within.isRewritableSubmolecule_image_trans_ofEquiv_iff _ _).2 hιb, .refl _⟩
  have h₁ := equiv_paste_pasteAt true e hp hpb hrb d₁ f₁ rfl
  let d₂ : PasteAtData true (k + 1) w P := ⟨hdw, hdP, _, d₁.occ.trans (Within.ofEquiv f),
    (Within.isRewritableSubmolecule_image_trans_ofEquiv_iff _ _).2 d₁.rewritable, .refl _⟩
  have h₂ : ArrowIn (PastingClosure A) d₁.round d₂.round :=
    arrowIn_pastingClosure_pasteAt_host d₁ d₂ f rfl hQP
  have hocc₂ : d₂.occ = argOcc hω hk true hw.side ((hϑb.other.symm.trans f₁).trans f) :=
    (congrArg (·.trans (Within.ofEquiv f)) (argOcc_trans_ofEquiv hω hk true hw.side _ f₁)).trans
      (argOcc_trans_ofEquiv hω hk true hw.side _ f)
  let Y : RoundPastingDiagram X := ⟨_, hry⟩
  have hdY : Y.dim = k + 1 + 1 := by
    change (y.paste _ _ hpy).dim = _
    rw [dim_paste, hdy, hdw, max_self]
  have eY : (Y.boundary (k + 1) false).Equiv (y.boundary (k + 1) false) :=
    equiv_boundary_paste hpy false
  have hιa := isRewritableSubmolecule_image_argOcc hω hk false eY hϑa.other.symm
    (isRound_boundary_of_isRound hry _ _)
    (by rw [dim_boundary _ (by omega), dim_boundary _ (by omega)])
  let d₃ : PasteAtData true (k + 1) Y ϑa := ⟨hdY, hda, _, _, hιa, .refl _⟩
  have h₃ := equiv_pasteAt_paste_argLoc true hω hpa hra d₂ hw.side
    ((hϑb.other.symm.trans f₁).trans f) (congrArg Within.image hocc₂) hpy hry d₃ eY
    hϑa.other.symm rfl
  have hdYb : (Y.boundary (k + 1) false).dim = k + 1 := dim_boundary _ (by omega) _
  let d₄ : PasteAtData true (k + 1) (isRound_boundary_of_isRound hry (k + 1) false).unit ϑa :=
    ⟨by change (Y.boundary (k + 1) false).unit.dim = _; rw [dim_unit, hdYb], hda, _, d₃.occ, hιa,
      boundary_unit hdYb false⟩
  have h₄ : ArrowIn (PastingClosure A) d₃.round d₄.round :=
    arrowIn_pastingClosure_pasteAt d₃ d₄ rfl hyw
  have h₅ := (arrowIn_pasteAt_unit A d₄ (.refl _)).1
  exact ((h₂.of_equiv_left (u' := ⟨_, hr⟩) h₁.symm).trans_pastingClosure
    (h₄.of_equiv_left (u' := d₂.round) h₃.symm)).trans_pastingClosure h₅

private theorem exists_arrowIn_pasteAt_paste_false {A : Set (RoundPastingDiagram X)} {k : ℕ}
    {u w ψa ψb : RoundPastingDiagram X} {y z : PastingDiagram X} {ω : Within y z}
    {Fr : LowerSet z.shape.ogp} (hω : ArgLoc k ω Fr) (hdu : u.dim = k + 1 + 1)
    (hdy : y.dim = k + 1 + 1) (hdz : z.dim = k + 1 + 1)
    (hψa : HasBdry false (k + 1) ψa.toPastingDiagram (z.boundary (k + 1) false)
      (u.boundary (k + 1) false))
    (hψb : HasBdry false (k + 1) ψb.toPastingDiagram (z.boundary (k + 1) true)
      (u.boundary (k + 1) true))
    (hpb : z.Pastable ψb.toPastingDiagram (k + 1))
    (hrb : (z.paste ψb.toPastingDiagram _ hpb).IsRound)
    (hpa : ψa.toPastingDiagram.Pastable u.toPastingDiagram (k + 1))
    (hra : (ψa.toPastingDiagram.paste u.toPastingDiagram _ hpa).IsRound)
    (hsq : Equivalent ⟨_, hrb⟩ ⟨_, hra⟩)
    (hw : HasBdry false (k + 1) w.toPastingDiagram (y.boundary (k + 1) true)
      (y.boundary (k + 1) false))
    (hpy : w.toPastingDiagram.Pastable y (k + 1))
    (hry : (w.toPastingDiagram.paste y _ hpy).IsRound)
    (hyw : ArrowIn (PastingClosure A) (isRound_boundary_of_isRound hry (k + 1) true).unit
      ⟨_, hry⟩) :
    ∃ (E : RoundPastingDiagram X) (hp : E.toPastingDiagram.Pastable u.toPastingDiagram (k + 1)),
      E.dim = k + 1 + 1 ∧ ∃ hr : (E.toPastingDiagram.paste u.toPastingDiagram _ hp).IsRound,
        ArrowIn (PastingClosure A) ψb ⟨_, hr⟩ := by
  have hk : k < k + 1 := Nat.lt_succ_self k
  have hdw := hw.dim_h
  have hdb := hψb.dim_h
  have hda := hψa.dim_h
  have hιa := isRewritableSubmolecule_image_argOcc hω hk false hw.other hψa.side.symm
    (isRound_boundary_of_isRound w.isRound _ _)
    (by rw [dim_boundary _ (by omega), dim_boundary _ (by omega)])
  let e : PasteAtData false (k + 1) w ψa := ⟨hdw, hda, _, _, hιa, .refl _⟩
  have hdE : e.pasting.dim = k + 1 + 1 := e.dim_pasting
  have hp : e.round.toPastingDiagram.Pastable u.toPastingDiagram (k + 1) :=
    ⟨e.equiv_boundary_not.trans hψa.other, lt_min (by
      change k + 1 < e.pasting.dim
      omega) (by omega)⟩
  have hr := isRound_paste_of_dim e.round u e.dim_pasting hdu hp
  refine ⟨e.round, hp, e.dim_pasting, hr, ?_⟩
  let Q : RoundPastingDiagram X := ⟨_, hra⟩
  let P : RoundPastingDiagram X := ⟨_, hrb⟩
  have hdQ : Q.dim = k + 1 + 1 := by
    change (ψa.toPastingDiagram.paste _ _ hpa).dim = _
    rw [dim_paste, hdu, hda, max_self]
  have hdP : P.dim = k + 1 + 1 := by
    change (z.paste _ _ hpb).dim = _
    rw [dim_paste, hdb, hdz, max_self]
  have hPQ : ArrowIn (PastingClosure A) P Q := hsq.arrowIn_pastingClosure A
  have f₁ : (ψa.boundary (k + 1) false).Equiv (Q.boundary (k + 1) false) :=
    (equiv_boundary_paste hpa false).symm
  have f : (P.boundary (k + 1) false).Equiv (Q.boundary (k + 1) false) :=
    hPQ.equiv_boundary (by omega) false
  let d₁ : PasteAtData false (k + 1) w Q := ⟨hdw, hdQ, _, e.occ.trans (Within.ofEquiv f₁),
    (Within.isRewritableSubmolecule_image_trans_ofEquiv_iff _ _).2 hιa, .refl _⟩
  have h₁ := equiv_paste_pasteAt false e hp hpa hra d₁ f₁ rfl
  have eB : (z.boundary (k + 1) false).Equiv (P.boundary (k + 1) false) :=
    hψa.side.symm.trans (f₁.trans f.symm)
  have hιa' := isRewritableSubmolecule_image_argOcc hω hk false hw.other eB
    (isRound_boundary_of_isRound w.isRound _ _)
    (by rw [dim_boundary _ (by omega), dim_boundary _ (by omega)])
  let d₂ : PasteAtData false (k + 1) w P := ⟨hdw, hdP, _, _, hιa', .refl _⟩
  have hocc : d₁.occ = d₂.occ.trans (Within.ofEquiv f) :=
    (argOcc_trans_ofEquiv hω hk false hw.other _ f₁).trans
      (argOcc_trans_ofEquiv hω hk false hw.other eB f).symm
  have h₂ : ArrowIn (PastingClosure A) d₂.round d₁.round :=
    arrowIn_pastingClosure_pasteAt_host d₂ d₁ f (congrArg Within.image hocc) hPQ
  let Y : RoundPastingDiagram X := ⟨_, hry⟩
  have hdY : Y.dim = k + 1 + 1 := by
    change (w.toPastingDiagram.paste y _ hpy).dim = _
    rw [dim_paste, hdy, hdw, max_self]
  have eY : (Y.boundary (k + 1) true).Equiv (y.boundary (k + 1) true) :=
    equiv_boundary_paste hpy true
  have hιb := isRewritableSubmolecule_image_argOcc hω hk true eY hψb.side.symm
    (isRound_boundary_of_isRound hry _ _)
    (by rw [dim_boundary _ (by omega), dim_boundary _ (by omega)])
  let d₃ : PasteAtData false (k + 1) Y ψb := ⟨hdY, hdb, _, _, hιb, .refl _⟩
  have h₃ := equiv_pasteAt_paste_argLoc false hω hpb hrb d₂ hw.other eB rfl hpy hry d₃ eY
    hψb.side.symm rfl
  have hdYb : (Y.boundary (k + 1) true).dim = k + 1 := dim_boundary _ (by omega) _
  let d₄ : PasteAtData false (k + 1) (isRound_boundary_of_isRound hry (k + 1) true).unit ψb :=
    ⟨by change (Y.boundary (k + 1) true).unit.dim = _; rw [dim_unit, hdYb], hdb, _, d₃.occ, hιb,
      boundary_unit hdYb true⟩
  have h₄ : ArrowIn (PastingClosure A) d₄.round d₃.round :=
    arrowIn_pastingClosure_pasteAt d₄ d₃ rfl hyw
  have h₅ := (arrowIn_pasteAt_unit A d₄ (.refl _)).2
  exact (((h₅.trans_pastingClosure h₄).of_equiv_right (v' := d₂.round) h₃.symm).trans_pastingClosure
    h₂).of_equiv_right (v' := ⟨_, hr⟩) h₁.symm

private theorem equivalent_square {x x' y y' : PastingDiagram X} (ex : x'.Equiv x)
    (ey : y'.Equiv y) (hx : x.IsRound) (hy : y.IsRound)
    (h : ∀ (hx' : x'.IsRound) (hy' : y'.IsRound), Equivalent ⟨x', hx'⟩ ⟨y', hy'⟩) :
    Equivalent ⟨x, hx⟩ ⟨y, hy⟩ :=
  equivalent_trans (equivalent_of_equiv (u := ⟨x, hx⟩) (v := ⟨x', ex.isRound_iff.2 hx⟩) ex.symm)
    (equivalent_trans (h _ (ey.isRound_iff.2 hy)) (equivalent_of_equiv (v := ⟨y, hy⟩) ey))

theorem HasSideInverse.of_isWeakInvCtx {A : Set (RoundPastingDiagram X)} (β : Bool)
    {H H' : RoundHom X} {G G' : CtxExpr X} (hGG : IsWeakInvCtx H H' G G')
    {a b : PastingDiagram X} (ha : IsRoundIn H.toPdHom a) (hb : IsRoundIn H.toPdHom b)
    {u : RoundPastingDiagram X} (hu : IsRoundIn ⟨H.k + 1, a, b⟩ u.toPastingDiagram)
    {w : RoundPastingDiagram X}
    (hw : HasBdry false (H.k + 1) w.toPastingDiagram
      ((G.app u.toPastingDiagram).boundary (H.k + 1) true)
      ((G.app u.toPastingDiagram).boundary (H.k + 1) false))
    (hp : (cond β w.toPastingDiagram (G.app u.toPastingDiagram)).Pastable
      (cond β (G.app u.toPastingDiagram) w.toPastingDiagram) (H.k + 1))
    (hr : ((cond β w.toPastingDiagram (G.app u.toPastingDiagram)).paste
      (cond β (G.app u.toPastingDiagram) w.toPastingDiagram) (H.k + 1) hp).IsRound)
    (h : cond β
      (ArrowIn (PastingClosure A) (isRound_boundary_of_isRound hr (H.k + 1) true).unit ⟨_, hr⟩)
      (ArrowIn (PastingClosure A) ⟨_, hr⟩ (isRound_boundary_of_isRound hr (H.k + 1) false).unit)) :
    HasSideInverse (PastingClosure A) β u := by
  have hk' : H'.k = H.k := hGG.round.typed.k_eq
  have hdu : u.dim = H.k + 1 + 1 := hu.dim_eq
  have tG := hGG.round.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have tGG := (hGG.round.comp hGG.round').typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGu := tG.mapsInto _ hu.inHom
  have hz := tGG.mapsInto _ hu.inHom
  have hdy : (G.app u.toPastingDiagram).dim = H.k + 1 + 1 :=
    (tG.ctxLaws.dim_eq _ hu.inHom).trans hdu
  have hdz : (G'.app (G.app u.toPastingDiagram)).dim = H.k + 1 + 1 :=
    (tGG.ctxLaws.dim_eq _ hu.inHom).trans hdu
  have hGuH' : InHom H'.toPdHom (G.app u.toPastingDiagram) :=
    InHom.of_inHom_succ (hGu.congr ⟨congrArg (· + 1) hk'.symm, .refl _, .refl _⟩)
      (hGG.round.isRoundIn ha).inHom (hGG.round.isRoundIn hb).inHom
  obtain ⟨ω, Fr, hω⟩ := hGG.round'.typed.exists_argLoc _ hGuH'
  rw [hk'] at hω
  cases β
  · obtain ⟨ϑ, hϑ, hN⟩ := (NatSim.symm hGG.left).exists_square ha hb
    obtain ⟨hra', hea, hta⟩ := hϑ a ha
    obtain ⟨hrb', -, htb⟩ := hϑ b hb
    have hpa : (ϑ a).Pastable (G'.app (G.app u.toPastingDiagram)) (H.k + 1) :=
      ⟨hta.other.trans hz.source.symm, by rw [hta.dim_h, hdz]; omega⟩
    have hra := isRound_paste_of_round false (u := ϑ a) hpa hra' hta.dim_h hdz.le
    have hpb : u.toPastingDiagram.Pastable (ϑ b) (H.k + 1) :=
      ⟨hu.inHom.target.trans htb.side.symm, by rw [htb.dim_h, hdu]; omega⟩
    have hrb := isRound_paste_of_dim u ⟨ϑ b, hrb'⟩ hdu htb.dim_h hpb
    have hsq : Equivalent ⟨_, hrb⟩ ⟨_, hra⟩ :=
      equivalent_square (CtxExpr.paste_app true hpb) (CtxExpr.paste_app false hpa) hrb hra
        (fun hF hG => hN.equivalent_app hu hF hG)
    obtain ⟨E, hpE, hdE, hrE, hE⟩ := exists_arrowIn_paste_pasteAt_true (A := A) (u := u)
      (y := G.app u.toPastingDiagram) (w := w) (ϑa := ⟨ϑ a, hra'⟩) (ϑb := ⟨ϑ b, hrb'⟩) hω hdu
      hdy hdz ((hta.of_equiv_side hu.inHom.source.symm).of_equiv_other hz.source.symm)
      ((htb.of_equiv_side hu.inHom.target.symm).of_equiv_other hz.target.symm)
      hpa hra hpb hrb hsq hw hp hr h
    exact HasSideInverse.of_paste_cond true hdu hdE hpE hrE
      (HasSideInverse.of_arrowIn (β := false) (hasSideInverse_of_mem_equivalences A false hea) hE)
  · obtain ⟨ψ, hψ, hN⟩ := hGG.left.exists_square ha hb
    obtain ⟨hra', -, hta⟩ := hψ a ha
    obtain ⟨hrb', heb, htb⟩ := hψ b hb
    have hpb : (G'.app (G.app u.toPastingDiagram)).Pastable (ψ b) (H.k + 1) :=
      ⟨hz.target.trans htb.side.symm, by rw [htb.dim_h, hdz]; omega⟩
    have hrb := isRound_paste_of_round true (u := ψ b) hpb hrb' htb.dim_h hdz.le
    have hpa : (ψ a).Pastable u.toPastingDiagram (H.k + 1) :=
      ⟨hta.other.trans hu.inHom.source.symm, by rw [hta.dim_h, hdu]; omega⟩
    have hra := isRound_paste_of_dim ⟨ψ a, hra'⟩ u hta.dim_h hdu hpa
    have hsq : Equivalent ⟨_, hrb⟩ ⟨_, hra⟩ :=
      equivalent_square (CtxExpr.paste_app true hpb) (CtxExpr.paste_app false hpa) hrb hra
        (fun hF hG => hN.equivalent_app hu hF hG)
    obtain ⟨E, hpE, hdE, hrE, hE⟩ := exists_arrowIn_pasteAt_paste_false (A := A) (u := u)
      (y := G.app u.toPastingDiagram) (w := w) (ψa := ⟨ψ a, hra'⟩) (ψb := ⟨ψ b, hrb'⟩) hω hdu
      hdy hdz ((hta.of_equiv_side hz.source.symm).of_equiv_other hu.inHom.source.symm)
      ((htb.of_equiv_side hz.target.symm).of_equiv_other hu.inHom.target.symm)
      hpb hrb hpa hra hsq hw hp hr h
    exact HasSideInverse.of_paste_cond false hdu hdE hpE hrE
      (HasSideInverse.of_arrowIn (β := true) (hasSideInverse_of_mem_equivalences A true heb) hE)

private theorem exists_inverse_of_hasSideInverse_frameOf {A : Set (RoundPastingDiagram X)}
    (α : Bool) {k : ℕ} {y r : PastingDiagram X} {x : RoundPastingDiagram X} (hdy : y.dim = k + 1)
    (hdr : r.dim ≤ k + 1) (hyr : (y.boundary k α).Equiv (r.boundary k (!α)))
    (hx : x.Equiv ((CtxExpr.frameOf α r k).app y))
    (h : HasSideInverse (PastingClosure A) (!α) x) :
    ∃ w : RoundPastingDiagram X, HasBdry false k w.toPastingDiagram (y.boundary k true)
      (y.boundary k false) ∧
      ∃ (hpw : (cond (!α) w.toPastingDiagram y).Pastable (cond (!α) y w.toPastingDiagram) k)
        (hrw : ((cond (!α) w.toPastingDiagram y).paste (cond (!α) y w.toPastingDiagram) k
          hpw).IsRound),
        cond (!α) (ArrowIn (PastingClosure A) (isRound_boundary_of_isRound hrw k true).unit
          ⟨_, hrw⟩)
          (ArrowIn (PastingClosure A) ⟨_, hrw⟩ (isRound_boundary_of_isRound hrw k false).unit) := by
  by_cases hd : r.dim = k + 1
  · have hp : (cond α y r).Pastable (cond α r y) k := .of_side α hyr (by omega) (by omega)
    have e := hx.trans ((CtxExpr.frameOf_app_equiv α hd hp).trans (CtxExpr.paste_app α hp))
    have hround := e.isRound_iff.1 x.isRound
    refine exists_inverse_of_hasSideInverse_paste_cond α hdy hd hp hround
      (h.of_arrowIn ?_)
    cases α
    · exact (equivalent_of_equiv (v := ⟨_, hround⟩) e).arrowIn_pastingClosure A
    · exact (equivalent_of_equiv (u := ⟨_, hround⟩) (v := x) e.symm).arrowIn_pastingClosure A
  · rw [CtxExpr.frameOf_of_not α hd] at hx
    have hry : y.IsRound := hx.isRound_iff.1 x.isRound
    have h' : HasSideInverse (PastingClosure A) (!α) ⟨y, hry⟩ := by
      refine h.of_arrowIn ?_
      cases α
      · exact (equivalent_of_equiv (v := ⟨y, hry⟩) hx).arrowIn_pastingClosure A
      · exact (equivalent_of_equiv (u := ⟨y, hry⟩) (v := x) hx.symm).arrowIn_pastingClosure A
    obtain ⟨n, w, hdn, hb, hpw, hrw, hw⟩ := h'.exists_paste
    obtain rfl : n = k := by
      change y.dim = n + 1 at hdn
      omega
    refine ⟨w, hb, hpw, hrw, ?_⟩
    cases α
    · exact hw.of_equiv_left (Equiv.unit (equiv_boundary_paste hpw true).symm)
    · exact hw.of_equiv_right (Equiv.unit (equiv_boundary_paste hpw false).symm)

theorem hasSideInverse_of_arrowIn_trim_comp {A : Set (RoundPastingDiagram X)} (α : Bool)
    {H H' : RoundHom X} {G : CtxExpr X}
    (hG : G.Typed (equivalences X) True H.toPdHom H'.toPdHom)
    (hGr : IsRoundCtxOn H.toPdHom H'.toPdHom G)
    {a b : PastingDiagram X} (ha : IsRoundIn H.toPdHom a) (hb : IsRoundIn H.toPdHom b)
    {D : PdHom X} {T : CtxExpr X}
    (hT : T.Typed Set.univ False ⟨H.k + 1, G.app a, G.app b⟩ D) (hTα : T.PastesOn α)
    {u v : RoundPastingDiagram X} (hu : IsRoundIn ⟨H.k + 1, a, b⟩ u.toPastingDiagram)
    (hr : (T.app (G.app u.toPastingDiagram)).IsRound)
    (hv : HasSideInverse (PastingClosure A) (!α) v)
    (huv : cond α (ArrowIn (PastingClosure A) ⟨_, hr⟩ v)
      (ArrowIn (PastingClosure A) v ⟨_, hr⟩)) :
    HasSideInverse (PastingClosure A) (!α) u := by
  obtain ⟨G', hGG, -⟩ := exists_isWeakInvCtx_of_typed hG hGr
  have h₁ : HasSideInverse (PastingClosure A) (!α) ⟨_, hr⟩ :=
    hv.of_arrowIn (by cases α <;> exact huv)
  have hk' : H'.k = H.k := hGG.round.typed.k_eq
  have hd : ((⟨H.k + 1, G.app a, G.app b⟩ : PdHom X).side α).dim = H.k + 1 := by
    cases α
    · exact (hGG.round.isRoundIn ha).dim_eq.trans (by rw [hk'])
    · exact (hGG.round.isRoundIn hb).dim_eq.trans (by rw [hk'])
  obtain ⟨r, hdr, -, hin, -, hTr⟩ := hT.exists_frameOf_of_pastesOn hTα hd
  have tG := hGG.round.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGu := tG.mapsInto _ hu.inHom
  have hdy : (G.app u.toPastingDiagram).dim = H.k + 1 + 1 :=
    (tG.ctxLaws.dim_eq _ hu.inHom).trans hu.dim_eq
  obtain ⟨w, hbw, hpw, hrw, hw⟩ := exists_inverse_of_hasSideInverse_frameOf α hdy hdr
    ((hGu.side α).trans hin.symm) (x := ⟨_, hr⟩) (hTr _ hGu) h₁
  exact HasSideInverse.of_isWeakInvCtx (!α) hGG ha hb hu hbw hpw hrw hw

end Atoms.Diagrammatic
