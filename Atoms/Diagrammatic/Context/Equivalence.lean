import Atoms.Diagrammatic.Context.Round
import Atoms.Diagrammatic.Equivalence.Congruence

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure ArgLoc (k : ℕ) {x y : PastingDiagram X} (ω : Within x y)
    (Fr : LowerSet y.shape.ogp) : Prop where
  eq_sup : (⊤ : LowerSet y.shape.ogp) = Fr ⊔ ω.image
  boundary_eq : ∀ {n : ℕ}, k < n → ∀ β : Bool,
    y.shape.ogp.boundary ⊤ n β = Fr ⊔ y.shape.ogp.boundary ω.image n β
  inf_le : ∀ {n : ℕ}, k < n → ∀ β : Bool, Fr ⊓ ω.image ≤ y.shape.ogp.boundary ω.image n β
  isSubmoleculeOf : ∀ {n : ℕ}, k < n → ∀ β : Bool,
    IsSubmoleculeOf y.shape.ogp (y.shape.ogp.boundary ω.image n β)
      (y.shape.ogp.boundary ⊤ n β)

namespace ArgLoc

theorem refl (k : ℕ) (x : PastingDiagram X) : ArgLoc k (Within.refl x) ⊥ where
  eq_sup := by rw [bot_sup_eq, Within.image_refl]
  boundary_eq := fun _ _ => by rw [bot_sup_eq, Within.image_refl]
  inf_le := fun _ _ => by rw [bot_inf_eq]; exact bot_le
  isSubmoleculeOf := fun {n} _ β => by
    rw [Within.image_refl]
    exact IsSubmoleculeOf.refl (x.shape.isMolecule.boundary n β)

theorem mono {k k' : ℕ} (hk : k ≤ k') {x y : PastingDiagram X} {ω : Within x y}
    {Fr : LowerSet y.shape.ogp} (h : ArgLoc k ω Fr) : ArgLoc k' ω Fr where
  eq_sup := h.eq_sup
  boundary_eq := fun hn β => h.boundary_eq (by omega) β
  inf_le := fun hn β => h.inf_le (by omega) β
  isSubmoleculeOf := fun hn β => h.isSubmoleculeOf (by omega) β

theorem of_isPastingAtIn {k : ℕ} {α : Bool} {x y : PastingDiagram X} (ω : Within x y)
    {S : LowerSet y.shape.ogp} (hc : y.shape.ogp.IsPastingAtIn k α S ω.image ⊤)
    (hdS : krullDim S = (k + 1 : ℕ)) : ArgLoc k ω S where
  eq_sup := hc.eq_sup
  boundary_eq := fun hkn β =>
    hc.boundary_eq_sup_of_lt hkn (by rw [hdS]; exact_mod_cast Nat.succ_le_of_lt hkn) β
  inf_le := fun hkn β => hc.inf_le_boundary_of_lt hkn β
  isSubmoleculeOf := fun hkn β => by
    have h' := (hc.isPastingAtIn_boundary_of_lt hkn β).isSubmoleculeOf_right
    rwa [← hc.boundary_eq_sup_of_lt hkn (by rw [hdS]; exact_mod_cast Nat.succ_le_of_lt hkn) β]
      at h'

theorem trans {k : ℕ} {x y z : PastingDiagram X} {ω₁ : Within x y} {ω₂ : Within y z}
    {Fr₁ : LowerSet y.shape.ogp} {Fr₂ : LowerSet z.shape.ogp}
    (h₁ : ArgLoc k ω₁ Fr₁) (h₂ : ArgLoc k ω₂ Fr₂) :
    ArgLoc k (ω₁.trans ω₂) (Fr₂ ⊔ OGP.map ω₂.emb Fr₁) := by
  have hB : ∀ (n : ℕ) (β : Bool), z.shape.ogp.boundary ω₂.image n β =
      OGP.map ω₂.emb (y.shape.ogp.boundary ⊤ n β) := fun n β => (map_boundary _ _ _ _).symm
  have hB₁ : ∀ (n : ℕ) (β : Bool), z.shape.ogp.boundary (ω₁.trans ω₂).image n β =
      OGP.map ω₂.emb (y.shape.ogp.boundary ω₁.image n β) := fun n β => by
    rw [Within.image_trans, map_boundary]
  refine ⟨?_, fun {n} hkn β => ?_, fun {n} hkn β => ?_, fun {n} hkn β => ?_⟩
  · rw [Within.image_trans, sup_assoc, ← map_sup, ← h₁.eq_sup]
    exact h₂.eq_sup
  · rw [h₂.boundary_eq hkn β, hB, h₁.boundary_eq hkn β, map_sup, hB₁, sup_assoc]
  · rw [hB₁, Within.image_trans, inf_sup_right]
    refine sup_le ?_ (by rw [← OGP.map_inf]; exact map_mono _ (h₁.inf_le hkn β))
    have hle : OGP.map ω₂.emb ω₁.image ≤ ω₂.image := map_mono _ le_top
    calc Fr₂ ⊓ OGP.map ω₂.emb ω₁.image
        ≤ z.shape.ogp.boundary ω₂.image n β ⊓ OGP.map ω₂.emb ω₁.image :=
          le_inf ((inf_le_inf_left _ hle).trans (h₂.inf_le hkn β)) inf_le_right
      _ = OGP.map ω₂.emb ((Fr₁ ⊔ y.shape.ogp.boundary ω₁.image n β) ⊓ ω₁.image) := by
          rw [hB, h₁.boundary_eq hkn β, OGP.map_inf]
      _ ≤ OGP.map ω₂.emb (y.shape.ogp.boundary ω₁.image n β) := map_mono _ (by
          rw [inf_sup_right]; exact sup_le (h₁.inf_le hkn β) inf_le_left)
  · rw [hB₁]
    refine ((isSubmoleculeOf_map_iff ω₂.emb).2 (h₁.isSubmoleculeOf hkn β)).trans ?_
    rw [← hB]
    exact h₂.isSubmoleculeOf hkn β

end ArgLoc

theorem ArgLoc.isPastingAtIn_trans {k : ℕ} {u e H m : PastingDiagram X}
    {Fr : LowerSet H.shape.ogp} {ω : Within e H} (hω : ArgLoc k ω Fr) (wU : Within u m)
    (wH : Within H m) (hpm : m.shape.ogp.IsPastingIn (k + 1) wU.image wH.image ⊤) :
    m.shape.ogp.IsPastingAtIn (k + 1) true (ω.trans wH).image wU.image ⊤ := by
  have hk1 : k < k + 1 := Nat.lt_succ_self k
  let wE := ω.trans wH
  have hE : wE.image = OGP.map wH.emb ω.image := Within.image_trans ω wH
  have hBH : m.shape.ogp.boundary wH.image (k + 1) false =
      OGP.map wH.emb (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) false) := by
    rw [← hω.boundary_eq hk1 false, map_boundary]
    rfl
  have hBE : m.shape.ogp.boundary wE.image (k + 1) false =
      OGP.map wH.emb (H.shape.ogp.boundary ω.image (k + 1) false) := by
    rw [hE, map_boundary]
  have hmeet : wU.image ⊓ wH.image = m.shape.ogp.boundary wH.image (k + 1) false :=
    hpm.inf_eq_input
  have hFr : OGP.map wH.emb Fr ≤ wU.image := by
    refine le_trans ?_ (hmeet.ge.trans inf_le_left)
    rw [hBH, map_sup]
    exact le_sup_left
  have hinter : wE.image ⊓ wU.image = m.shape.ogp.boundary wE.image (k + 1) false := by
    have hEH : wE.image ≤ wH.image := by rw [hE]; exact map_mono _ le_top
    refine le_antisymm ?_ (le_inf (boundary_le _ _ _) ?_)
    · calc wE.image ⊓ wU.image ≤ wE.image ⊓ (wU.image ⊓ wH.image) :=
            le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hEH))
        _ = OGP.map wH.emb (ω.image ⊓ (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) false)) := by
            rw [hmeet, hBH, hE, OGP.map_inf]
        _ ≤ m.shape.ogp.boundary wE.image (k + 1) false := by
            rw [hBE]
            refine map_mono _ ?_
            rw [inf_sup_left, inf_comm]
            exact sup_le (hω.inf_le hk1 false) inf_le_right
    · calc m.shape.ogp.boundary wE.image (k + 1) false
          ≤ OGP.map wH.emb (Fr ⊔ H.shape.ogp.boundary ω.image (k + 1) false) := by
            rw [hBE]; exact map_mono _ le_sup_right
        _ = wU.image ⊓ wH.image := by rw [← hBH, hmeet]
        _ ≤ wU.image := inf_le_left
  change m.shape.ogp.IsPastingAtIn (k + 1) true wE.image wU.image ⊤
  refine ⟨wE.isMoleculeIn_image, wU.isMoleculeIn_image, ?_, hinter, ?_⟩
  · have hH : wH.image = OGP.map wH.emb Fr ⊔ wE.image := by
      rw [hE, ← map_sup, ← hω.eq_sup]
      rfl
    rw [← hpm.sup_eq, hH, ← sup_assoc, sup_eq_left.2 hFr, sup_comm]
  · rw [hinter, ← hpm.inf_eq_output, hmeet, hBE, hBH, ← hω.boundary_eq hk1 false]
    exact (isSubmoleculeOf_map_iff wH.emb).2 (hω.isSubmoleculeOf hk1 false)

theorem CtxExpr.Typed.exists_argLoc {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') :
    ∀ a, InHom H a →
      ∃ (ω : Within a (t.app a)) (Fr : LowerSet (t.app a).shape.ogp), ArgLoc H.k ω Fr := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs₀ =>
    intro a ha
    have hs : (a.boundary H.k α).Equiv v₀ := (ha.side α).trans hs₀.symm
    change ∃ (ω : Within a (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h a))
      (Fr : LowerSet (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h a).shape.ogp),
        ArgLoc H.k ω Fr
    rw [sidePaste_of hs]
    exact ⟨_, _, ArgLoc.of_isPastingAtIn _ (Within.isPastingAtIn_pasteAt _ _ _ _ _ _ _)
      (by rw [Within.krullDim_image]; exact_mod_cast hdu)⟩
  | id => exact fun a _ => ⟨Within.refl a, ⊥, ArgLoc.refl _ a⟩
  | comp ht₁ _ ih₁ ih₂ =>
    intro a ha
    obtain ⟨ω₁, Fr₁, h₁⟩ := ih₁ a ha
    obtain ⟨ω₂, Fr₂, h₂⟩ := ih₂ _ (ht₁.mapsInto a ha)
    exact ⟨_, _, h₁.trans (h₂.mono ht₁.k_eq.le)⟩
  | promote _ hk _ _ _ _ ih =>
    intro a ha
    obtain ⟨ω, Fr, h⟩ := ih a (ha.promote (by omega))
    exact ⟨ω, Fr, h.mono (by rw [PdHom.k_boundary]; omega)⟩

theorem InHom.of_hasBdry {β : Bool} {H : PdHom X} {e a b : PastingDiagram X}
    (ht : HasBdry β (H.k + 1) e a b) (hx : InHom H a) : InHom H e :=
  ⟨by rw [ht.dim_h]; omega,
    (PastingDiagram.Equiv.symm
      (equiv_boundary_boundary e (Nat.lt_succ_self H.k) β false)).trans
      ((ht.side.boundary H.k false).trans hx.source),
    (PastingDiagram.Equiv.symm
      (equiv_boundary_boundary e (Nat.lt_succ_self H.k) β true)).trans
      ((ht.side.boundary H.k true).trans hx.target)⟩

theorem paste_mem_equivalences_iff_right {u v : RoundPastingDiagram X} {n : ℕ}
    (hu : u ∈ equivalences X) (hdu : u.dim = n + 1) (hdv : v.dim = n + 1)
    (hp : u.1.Pastable v.1 n) :
    (⟨u.1.paste v.1 n hp, isRound_paste_of_dim u v hdu hdv hp⟩ : RoundPastingDiagram X) ∈
      equivalences X ↔ v ∈ equivalences X := by
  have e := equiv_paste_pasteAtBoundary _ _ _ false (pasteData u v hdu hdv hp).occ
    (pasteData u v hdu hdv hp).rewritable.isSubmoleculeOf (Within.image_refl _)
    (pasteData u v hdu hdv hp).equiv hp
  rw [← pasteAt_mem_equivalences_iff (pasteData u v hdu hdv hp) hu]
  exact ⟨fun h => mem_equivalences_of_equiv e h,
    fun h => mem_equivalences_of_equiv (e.symm) h⟩

theorem mem_equivalences_app_paste_unit {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') (hr : IsRoundCtx H t)
    {e : RoundPastingDiagram X} (he : e ∈ equivalences X) (hin : InHom H e.toPastingDiagram)
    (hde : e.dim = H.k + 1 + 1) {q : PastingDiagram X} (hq : (e.boundary (H.k + 1) true).Equiv q) :
    ∃ (hp : (t.app e.toPastingDiagram).Pastable (t.app q).unit (H.k + 1))
      (hround : ((t.app e.toPastingDiagram).paste (t.app q).unit (H.k + 1) hp).IsRound),
      (⟨_, hround⟩ : RoundPastingDiagram X) ∈ equivalences X := by
  set k := H.k
  have L := ht.ctxLaws
  have hk1 : k < k + 1 := Nat.lt_succ_self k
  have hk2 : k + 1 < e.dim := by omega
  have hp₀ := hin.boundary hk1 hk2 false
  have hq₀ := hin.boundary hk1 hk2 true
  have hdp₀ : (e.boundary (k + 1) false).dim = k + 1 := dim_boundary _ (by omega) false
  have hdq₀ : (e.boundary (k + 1) true).dim = k + 1 := dim_boundary _ (by omega) true
  have hdq : q.dim = k + 1 := (dim_eq_of_equiv hq).symm.trans hdq₀
  have hHp : (t.app (e.boundary (k + 1) false)).IsRound :=
    hr.isRound_app ht hp₀ hdp₀ (isRound_boundary_of_isRound e.isRound _ _)
  have hHq : (t.app q).IsRound := hr.isRound_app ht (hq₀.of_equiv hq) hdq
    (hq.isRound_iff.1 (isRound_boundary_of_isRound e.isRound _ _))
  have hdHp : (t.app (e.boundary (k + 1) false)).dim = k + 1 := (L.dim_eq _ hp₀).trans hdp₀
  have hdHq : (t.app q).dim = k + 1 := (L.dim_eq _ (hq₀.of_equiv hq)).trans hdq
  have hdHe : (t.app e.toPastingDiagram).dim = k + 1 + 1 := (L.dim_eq _ hin).trans hde
  have hbe₀ := L.boundary _ hin hk1 hk2 false
  have hbe₁ : ((t.app e.toPastingDiagram).boundary (k + 1) true).Equiv (t.app q) :=
    (L.boundary _ hin hk1 hk2 true).trans (CtxExpr.app_equiv t hq)
  have hdu₀ : (t.app (e.boundary (k + 1) false)).unit.dim = k + 1 + 1 := by rw [dim_unit, hdHp]
  have hdu₁ : (t.app q).unit.dim = k + 1 + 1 := by rw [dim_unit, hdHq]
  have hp₁ : (t.app (e.boundary (k + 1) false)).unit.Pastable (t.app e.toPastingDiagram)
      (k + 1) :=
    ⟨(boundary_unit hdHp true).trans
      (hbe₀.symm), by rw [hdu₀, hdHe]; omega⟩
  have hp : (t.app e.toPastingDiagram).Pastable (t.app q).unit (k + 1) :=
    ⟨hbe₁.trans
      ((boundary_unit hdHq false).symm), by
      rw [hdHe, hdu₁]; omega⟩
  set m := (t.app (e.boundary (k + 1) false)).unit.paste (t.app e.toPastingDiagram) (k + 1) hp₁
  let wU := Within.pasteInl _ _ (k + 1) hp₁
  let wH := Within.pasteInr _ _ (k + 1) hp₁
  have hpm : m.shape.ogp.IsPastingIn (k + 1) wU.image wH.image ⊤ :=
    Within.isPastingIn_paste _ _ (k + 1) hp₁
  obtain ⟨ω, Fr, hω⟩ := ht.exists_argLoc e.toPastingDiagram hin
  let wE := ω.trans wH
  have hc : m.shape.ogp.IsPastingAtIn (k + 1) true wE.image wU.image ⊤ :=
    hω.isPastingAtIn_trans wU wH hpm
  have hV := hc.isSubmoleculeOf_inf
  have hh' : (e.toPastingDiagram.boundary (k + 1) (!true)).Equiv
      (occurrenceDiagram wU (k + 1) true hV) :=
    equiv_boundary_occurrence wU (k + 1) true hV wE hc.inf_eq.symm
  have hpaste := equiv_pasteAtBoundary_of_within wE wU hc (occurrence wU (k + 1) true hV)
    (isSubmoleculeOf_image_occurrence _ _ _ _) (image_occurrence wU (k + 1) true hV) hh'
  have hdsub : (occurrenceDiagram wU (k + 1) true hV).dim =
      ((t.app (e.boundary (k + 1) false)).unit.boundary (k + 1) true).dim := by
    rw [← dim_eq_of_equiv hh', dim_boundary _ (by omega), dim_boundary _ (by omega)]
  let d : PasteAtData true (k + 1) e hHp.unit :=
    ⟨hde, hdu₀, _, occurrence wU (k + 1) true hV,
      (occurrence wU (k + 1) true hV).isRewritableSubmolecule_image_iff.2
        ⟨isSubmoleculeOf_image_occurrence _ _ _ _,
          hh'.isRound_iff.1 (isRound_boundary_of_isRound e.isRound _ _), hdsub⟩, hh'⟩
  have hdm : d.round ∈ equivalences X :=
    (pasteAt_mem_equivalences_iff d he).2 (unit_mem_equivalences ⟨_, hHp⟩)
  have hmE : d.pasting.Equiv m :=
    hpaste.trans (equiv_restrictTo_univ m)
  have hmR : m.IsRound := hmE.isRound_iff.1 d.isRound_pasting
  have hmem : (⟨m, hmR⟩ : RoundPastingDiagram X) ∈ equivalences X :=
    mem_equivalences_of_equiv hmE hdm
  have hR := isRound_paste_of_round true hp (isRound_unit hHq) hdu₁ (by rw [hdHe])
  refine ⟨hp, hR, ?_⟩
  have hdm' : m.dim = k + 1 + 1 := by rw [dim_paste, hdu₀, hdHe, max_self]
  have h₂ : m.Pastable (t.app q).unit (k + 1) :=
    ⟨(equiv_boundary_paste hp₁ true).trans hp.1, by
      rw [hdm', hdu₁]; omega⟩
  obtain ⟨h₃, h₄, ea⟩ := equiv_paste_assoc hp₁ h₂
  have hdR : ((t.app e.toPastingDiagram).paste (t.app q).unit (k + 1) hp).dim = k + 1 + 1 := by
    rw [dim_paste, hdHe, hdu₁, max_self]
  have hmz := (paste_mem_equivalences_iff_right (v := hHq.unit) hmem hdm' hdu₁
    h₂).2 (unit_mem_equivalences ⟨_, hHq⟩)
  have hxR := mem_equivalences_of_equiv (e' := ⟨_, isRound_paste_of_dim
    hHp.unit ⟨_, hR⟩ hdu₀ hdR h₄⟩) ea hmz
  exact (paste_mem_equivalences_iff_right (u := hHp.unit) (v := ⟨_, hR⟩)
    (unit_mem_equivalences ⟨_, hHp⟩) hdu₀ hdR h₄).1 hxR

end Atoms.Diagrammatic
