import Atoms.Diagrammatic.Pasting.Boundary

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem PastingDiagram.cond_boundary (a : PastingDiagram X) (k : ℕ) (β : Bool) :
    cond β (a.boundary k true) (a.boundary k false) = a.boundary k β := by
  cases β <;> rfl

structure PdHom (X : DiagSet.{u}) where
  k : ℕ
  v : PastingDiagram X
  w : PastingDiagram X

namespace PdHom

variable (H : PdHom X)

def side (α : Bool) : PastingDiagram X :=
  cond α H.w H.v

@[simp]
theorem side_false : H.side false = H.v :=
  rfl

@[simp]
theorem side_true : H.side true = H.w :=
  rfl

theorem side_mk_app (k : ℕ) (F : PastingDiagram X → PastingDiagram X) (D : PdHom X)
    (α : Bool) : (⟨k, F D.v, F D.w⟩ : PdHom X).side α = F (D.side α) := by
  cases α <;> rfl

def setSide (α : Bool) (x : PastingDiagram X) : PdHom X :=
  ⟨H.k, cond α H.v x, cond α x H.w⟩

@[simp]
theorem k_setSide (α : Bool) (x : PastingDiagram X) : (H.setSide α x).k = H.k :=
  rfl

@[simp]
theorem side_setSide_self (α : Bool) (x : PastingDiagram X) : (H.setSide α x).side α = x := by
  cases α <;> rfl

@[simp]
theorem side_setSide_not (α : Bool) (x : PastingDiagram X) :
    (H.setSide α x).side (!α) = H.side (!α) := by
  cases α <;> rfl

@[simp]
theorem setSide_setSide (α : Bool) (x y : PastingDiagram X) :
    (H.setSide α x).setSide α y = H.setSide α y := by
  cases α <;> rfl

def boundary (n : ℕ) : PdHom X :=
  ⟨n, H.v.boundary n false, H.w.boundary n true⟩

@[simp]
theorem k_boundary (n : ℕ) : (H.boundary n).k = n :=
  rfl

structure Equiv (H H' : PdHom X) : Prop where
  k_eq : H.k = H'.k
  equiv_v : H.v.Equiv H'.v
  equiv_w : H.w.Equiv H'.w

namespace Equiv

variable {H} {H' H'' : PdHom X}

@[refl]
protected theorem refl (H : PdHom X) : H.Equiv H :=
  ⟨rfl, .refl _, .refl _⟩

@[symm]
protected theorem symm (e : H.Equiv H') : H'.Equiv H :=
  ⟨e.k_eq.symm, e.equiv_v.symm, e.equiv_w.symm⟩

@[trans]
protected theorem trans (e : H.Equiv H') (e' : H'.Equiv H'') : H.Equiv H'' :=
  ⟨e.k_eq.trans e'.k_eq, e.equiv_v.trans e'.equiv_v, e.equiv_w.trans e'.equiv_w⟩

theorem side (e : H.Equiv H') (α : Bool) : (H.side α).Equiv (H'.side α) := by
  cases α
  · exact e.equiv_v
  · exact e.equiv_w

theorem of_side (α : Bool) (hk : H.k = H'.k) (hs : (H.side α).Equiv (H'.side α))
    (hn : (H.side (!α)).Equiv (H'.side (!α))) : H.Equiv H' := by
  cases α
  · exact ⟨hk, hs, hn⟩
  · exact ⟨hk, hn, hs⟩

theorem setSide (e : H.Equiv H') (α : Bool) {x x' : PastingDiagram X} (ex : x.Equiv x') :
    (H.setSide α x).Equiv (H'.setSide α x') :=
  ⟨e.k_eq, e.equiv_v.cond α ex, ex.cond α e.equiv_w⟩

end Equiv

theorem equiv_setSide {α : Bool} {x : PastingDiagram X} (e : (H.side α).Equiv x) :
    H.Equiv (H.setSide α x) := by
  cases α
  · exact ⟨rfl, e, .refl _⟩
  · exact ⟨rfl, .refl _, e⟩

end PdHom

structure InHom (H : PdHom X) (a : PastingDiagram X) : Prop where
  lt_dim : H.k < a.dim
  source : (a.boundary H.k false).Equiv H.v
  target : (a.boundary H.k true).Equiv H.w

namespace InHom

variable {H : PdHom X} {a : PastingDiagram X}

theorem side (h : InHom H a) (α : Bool) : (a.boundary H.k α).Equiv (H.side α) := by
  cases α
  · exact h.source
  · exact h.target

theorem of_side (α : Bool) (hk : H.k < a.dim) (hs : (a.boundary H.k α).Equiv (H.side α))
    (hn : (a.boundary H.k (!α)).Equiv (H.side (!α))) : InHom H a := by
  cases α
  · exact ⟨hk, hs, hn⟩
  · exact ⟨hk, hn, hs⟩

theorem of_equiv (h : InHom H a) {a' : PastingDiagram X} (e : a.Equiv a') : InHom H a' :=
  ⟨by rw [← dim_eq_of_equiv e]; exact h.lt_dim,
    (e.boundary H.k false).symm.trans h.source,
    (e.boundary H.k true).symm.trans h.target⟩

theorem congr (h : InHom H a) {H' : PdHom X} (e : H.Equiv H') : InHom H' a := by
  obtain ⟨k, v, w⟩ := H
  obtain ⟨k', v', w'⟩ := H'
  obtain ⟨rfl, ev, ew⟩ := e
  exact ⟨h.lt_dim, h.source.trans ev, h.target.trans ew⟩

theorem boundary (h : InHom H a) {n : ℕ} (hkn : H.k < n) (hn : n < a.dim) (β : Bool) :
    InHom H (a.boundary n β) :=
  ⟨by rw [dim_boundary a (by omega) β]; exact hkn,
    (equiv_boundary_boundary a hkn β false).trans h.source,
    (equiv_boundary_boundary a hkn β true).trans h.target⟩

theorem parallel (ha : InHom H a) (hv : H.v.IsRound) (hw : H.w.IsRound) (hdv : H.v.dim = H.k)
    (hdw : H.w.dim = H.k) : Parallel ⟨H.v, hv⟩ ⟨H.w, hw⟩ := by
  refine ⟨hdv.trans hdw.symm, ?_⟩
  rcases Nat.eq_zero_or_pos H.k with h0 | hpos
  · exact Or.inl (hdv.trans h0)
  · refine Or.inr fun α => ?_
    change (H.v.boundary (H.v.dim - 1) α).Equiv (H.w.boundary (H.w.dim - 1) α)
    rw [hdv, hdw]
    exact (ha.source.boundary _ α).symm.trans
      ((equiv_boundary_boundary a (by omega) false α).trans
        ((PastingDiagram.Equiv.symm
          (equiv_boundary_boundary a (by omega) true α)).trans (ha.target.boundary _ α)))

end InHom

def PastingDiagram.homAt (a : PastingDiagram X) (n : ℕ) : PdHom X :=
  ⟨n, a.boundary n false, a.boundary n true⟩

namespace PastingDiagram

@[simp]
theorem k_homAt (a : PastingDiagram X) (n : ℕ) : (a.homAt n).k = n :=
  rfl

@[simp]
theorem side_homAt (a : PastingDiagram X) (n : ℕ) (β : Bool) :
    (a.homAt n).side β = a.boundary n β := by
  cases β <;> rfl

theorem inHom_homAt_boundary (a : PastingDiagram X) {n N : ℕ} (hn : n < N) (hN : N ≤ a.dim)
    (β : Bool) : InHom (a.homAt n) (a.boundary N β) :=
  ⟨by rw [k_homAt, dim_boundary a hN]; exact hn, equiv_boundary_boundary a hn β false,
    equiv_boundary_boundary a hn β true⟩

theorem homAt_boundary_equiv (a : PastingDiagram X) {n N : ℕ} (hn : n < N) :
    ((a.homAt N).boundary n).Equiv (a.homAt n) :=
  ⟨rfl, equiv_boundary_boundary a hn false false, equiv_boundary_boundary a hn true true⟩

end PastingDiagram

section SideOcc

variable (α : Bool) (k : ℕ) {v a V : PastingDiagram X} (ι : Within V v)

noncomputable def sideOcc (hs : (a.boundary k α).Equiv v) : Within V (a.boundary k α) :=
  ι.trans (Within.ofEquiv hs.symm)

theorem isSubmoleculeOf_image_sideOcc (hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hs : (a.boundary k α).Equiv v) :
    (a.boundary k α).shape.ogp.IsSubmoleculeOf (sideOcc α k ι hs).image ⊤ :=
  (ι.isSubmoleculeOf_image_trans_ofEquiv_iff hs.symm).2 hι

end SideOcc

section SideWithin

variable {m Q v : PastingDiagram X} (wQ : Within Q m) (k : ℕ) (α : Bool)

noncomputable def sideWithin (hs : (Q.boundary k α).Equiv v) : Within v m :=
  (Within.ofEquiv (hs.symm)).trans ((Within.boundary Q k α).trans wQ)

theorem image_sideWithin (hs : (Q.boundary k α).Equiv v) :
    (sideWithin wQ k α hs).image = m.shape.ogp.boundary wQ.image k α := by
  change ((Within.ofEquiv (hs.symm)).trans
    ((Within.boundary Q k α).trans wQ)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary_trans _ _ _

theorem sideWithin_congr {Q' : PastingDiagram X} (wQ' : Within Q' m)
    (hs : (Q.boundary k α).Equiv v) (hs' : (Q'.boundary k α).Equiv v)
    (hb : m.shape.ogp.boundary wQ.image k α = m.shape.ogp.boundary wQ'.image k α) :
    sideWithin wQ k α hs = sideWithin wQ' k α hs' :=
  Within.ext_of_image_eq _ _ ((image_sideWithin wQ k α hs).trans
    (hb.trans (image_sideWithin wQ' k α hs').symm))

theorem image_sideOcc_trans_boundary (hs : (Q.boundary k α).Equiv v) {V : PastingDiagram X}
    (ι : Within V v) :
    ((sideOcc α k ι hs).trans ((Within.boundary Q k α).trans wQ)).image =
      (ι.trans (sideWithin wQ k α hs)).image :=
  rfl

end SideWithin

theorem equiv_pasteAtBoundary_relocate (P : PastingDiagram X) {Q Q' : PastingDiagram X}
    (e : Q.Equiv Q') {k : ℕ} {α : Bool} {V V' : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (ι' : Within V' (Q'.boundary k α))
    (hι' : (Q'.boundary k α).shape.ogp.IsSubmoleculeOf ι'.image ⊤)
    (h : (P.boundary k (!α)).Equiv V) (h' : (P.boundary k (!α)).Equiv V')
    (himg : (ι'.trans ((Within.boundary Q' k α).trans
        ((Within.ofEquiv (e.symm)).trans
          (Within.pasteAtInr P Q k α ι hι h)))).image =
      (ι.trans ((Within.boundary Q k α).trans
        (Within.pasteAtInr P Q k α ι hι h))).image) :
    (pasteAtBoundary P Q k α ι hι h).Equiv (pasteAtBoundary P Q' k α ι' hι' h') := by
  have hc := Within.isPastingAtIn_pasteAt P Q k α ι hι h
  have hR' : ((Within.ofEquiv (e.symm)).trans
      (Within.pasteAtInr P Q k α ι hι h)).image = (Within.pasteAtInr P Q k α ι hι h).image := by
    rw [Within.image_trans, Within.image_ofEquiv]
    rfl
  have hocc : (ι'.trans ((Within.boundary Q' k α).trans
      ((Within.ofEquiv (e.symm)).trans
        (Within.pasteAtInr P Q k α ι hι h)))).image =
      (Within.pasteAtInl P Q k α ι hι h).image ⊓
        ((Within.ofEquiv (e.symm)).trans
          (Within.pasteAtInr P Q k α ι hι h)).image := by
    rw [himg, image_occurrence_pasteAt, hR']
  rw [← hR'] at hc
  exact PastingDiagram.Equiv.trans
    ((equiv_restrictTo_univ (pasteAtBoundary P Q k α ι hι h)).symm)
    ((equiv_pasteAtBoundary_of_within (Within.pasteAtInl P Q k α ι hι h)
      ((Within.ofEquiv (e.symm)).trans (Within.pasteAtInr P Q k α ι hι h)) hc ι' hι'
      hocc h').symm)

section SidePaste

variable (α : Bool) (u : PastingDiagram X) (k : ℕ) {v V : PastingDiagram X} (ι : Within V v)
  (hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤) (h : (u.boundary k (!α)).Equiv V)

open Classical in
noncomputable def sidePaste (a : PastingDiagram X) : PastingDiagram X :=
  if hs : (a.boundary k α).Equiv v then
    pasteAtBoundary u a k α (sideOcc α k ι hs) (isSubmoleculeOf_image_sideOcc α k ι hι hs) h
  else a

variable {α u k ι hι h}

theorem sidePaste_of {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v) :
    sidePaste α u k ι hι h a =
      pasteAtBoundary u a k α (sideOcc α k ι hs) (isSubmoleculeOf_image_sideOcc α k ι hι hs) h :=
  dif_pos hs

theorem sidePaste_of_not {a : PastingDiagram X} (hs : ¬ (a.boundary k α).Equiv v) :
    sidePaste α u k ι hι h a = a :=
  dif_neg hs

theorem dim_sidePaste {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v)
    (hu : u.dim ≤ a.dim) : (sidePaste α u k ι hι h a).dim = a.dim := by
  rw [sidePaste_of hs]
  exact (dim_pasteAtBoundary u a k α (sideOcc α k ι hs)
      (isSubmoleculeOf_image_sideOcc α k ι hι hs) h).trans
    (max_eq_right hu)

theorem equiv_boundary_not_sidePaste {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v) :
    ((sidePaste α u k ι hι h a).boundary k (!α)).Equiv (a.boundary k (!α)) := by
  rw [sidePaste_of hs]
  exact equiv_boundary_not_pasteAtBoundary u a k α (sideOcc α k ι hs)
    (isSubmoleculeOf_image_sideOcc α k ι hι hs) h

theorem sidePaste_equiv {a a' : PastingDiagram X} (hs : (a.boundary k α).Equiv v)
    (e : a.Equiv a') : (sidePaste α u k ι hι h a).Equiv (sidePaste α u k ι hι h a') := by
  have hs' : (a'.boundary k α).Equiv v :=
    (e.boundary k α).symm.trans hs
  rw [sidePaste_of hs, sidePaste_of hs']
  refine equiv_pasteAtBoundary_relocate u e (sideOcc α k ι hs)
    (isSubmoleculeOf_image_sideOcc α k ι hι hs) (sideOcc α k ι hs')
    (isSubmoleculeOf_image_sideOcc α k ι hι hs') h h ?_
  have hW : sideWithin ((Within.ofEquiv (e.symm)).trans
      (Within.pasteAtInr u a k α (sideOcc α k ι hs)
          (isSubmoleculeOf_image_sideOcc α k ι hι hs) h)) k α hs' =
      sideWithin (Within.pasteAtInr u a k α (sideOcc α k ι hs)
          (isSubmoleculeOf_image_sideOcc α k ι hι hs) h)
        k α hs :=
    Within.ext_of_image_eq _ _ (by
      rw [image_sideWithin, image_sideWithin, Within.image_ofEquiv_trans])
  exact (image_sideOcc_trans_boundary _ k α hs' ι).trans
    ((congrArg (fun w => (ι.trans w).image) hW).trans
      (image_sideOcc_trans_boundary _ k α hs ι).symm)

theorem image_occ_sidePaste {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v) :
    (ι.trans (sideWithin (Within.pasteAtInr u a k α (sideOcc α k ι hs)
      (isSubmoleculeOf_image_sideOcc α k ι hι hs) h) k α hs)).image =
      (Within.pasteAtInl u a k α (sideOcc α k ι hs)
          (isSubmoleculeOf_image_sideOcc α k ι hι hs) h).image ⊓
        (Within.pasteAtInr u a k α (sideOcc α k ι hs)
            (isSubmoleculeOf_image_sideOcc α k ι hι hs) h).image :=
  (image_sideOcc_trans_boundary _ k α hs ι).symm.trans
    (image_occurrence_pasteAt u a k α (sideOcc α k ι hs)
        (isSubmoleculeOf_image_sideOcc α k ι hι hs) h)

section Located

variable {m Q : PastingDiagram X} (wU : Within u m) (wQ : Within Q m)
  (hs : (Q.boundary k α).Equiv v) {R : LowerSet m.shape.ogp}
  (hc : m.shape.ogp.IsPastingAtIn k α wU.image wQ.image R)
  (hocc : (ι.trans (sideWithin wQ k α hs)).image = wU.image ⊓ wQ.image)

include hc hocc in
theorem sidePaste_equiv_restrictTo [DecidablePred (· ∈ R)] (hR : IsMoleculeIn m.shape.ogp R) :
    (sidePaste α u k ι hι h Q).Equiv (m.restrictTo hR) := by
  rw [sidePaste_of hs]
  exact equiv_pasteAtBoundary_of_within wU wQ hc (sideOcc α k ι hs)
    (isSubmoleculeOf_image_sideOcc α k ι hι hs) (by
      rw [image_sideOcc_trans_boundary]; exact hocc) h

include hc hocc in
theorem sidePaste_boundary_equiv_restrictTo {n : ℕ} (hkn : k < n) (β : Bool) :
    ∃ hR' : IsMoleculeIn m.shape.ogp (wU.image ⊔ m.shape.ogp.boundary wQ.image n β),
      (sidePaste α u k ι hι h (Q.boundary n β)).Equiv (m.restrictTo hR') := by
  have hsn : ((Q.boundary n β).boundary k α).Equiv v :=
    (equiv_boundary_boundary Q hkn β α).trans hs
  have hcB := hc.isPastingAtIn_boundary_of_lt hkn β
  have hR' := hcB.isMoleculeIn
  rw [← Within.image_boundary_trans] at hcB
  have hside : sideWithin ((Within.boundary Q n β).trans wQ) k α hsn = sideWithin wQ k α hs :=
    sideWithin_congr ((Within.boundary Q n β).trans wQ) k α wQ hsn hs (by
      rw [Within.image_boundary_trans, wQ.isMoleculeIn_image.isGlobular k n hkn α β])
  have hR'' : IsMoleculeIn m.shape.ogp (wU.image ⊔ ((Within.boundary Q n β).trans wQ).image) := by
    rw [Within.image_boundary_trans]; exact hR'
  refine ⟨hR', PastingDiagram.Equiv.trans
    (sidePaste_equiv_restrictTo wU ((Within.boundary Q n β).trans wQ) hsn hcB (by
      rw [hside, hocc, Within.image_boundary_trans, hc.inf_boundary_of_lt hkn β]) hR'')
    (m.equiv_restrictTo_of_eq hR'' hR' (by rw [Within.image_boundary_trans]))⟩

include hc hocc in
theorem substitute_equiv_restrictTo_boundary [DecidablePred (· ∈ R)] (hu : u.IsRound)
    (hdu : u.dim = k + 1)
    (hkQ : k ≤ Q.dim) (hr : v.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
    (hw : Parallel ⟨V, ι.round_image_iff.1 hr.isRound⟩
      ⟨u.boundary k α, isRound_boundary_of_isRound hu k α⟩) :
    ∃ hR' : IsMoleculeIn m.shape.ogp (m.shape.ogp.boundary R k α),
      (v.substitute ι hr ⟨u.boundary k α, isRound_boundary_of_isRound hu k α⟩ hw).Equiv
        (m.restrictTo hR') := by
  have hR' := hc.isMoleculeIn.boundary k α
  have hsub := hc.isSubstitutionIn_boundary (wU.round_image_iff.2 hu)
    (by rw [Within.krullDim_image, hdu]; norm_cast)
    (by rw [Within.krullDim_image]; exact_mod_cast hkQ)
  rw [← image_sideWithin wQ k α hs, ← hocc, ← Within.image_boundary_trans] at hsub
  exact ⟨hR', equiv_substitute_of_within ι hr _ hw (sideWithin wQ k α hs)
    ((Within.boundary u k α).trans wU) hsub hR'⟩

end Located

section Interchange

variable {m y z : PastingDiagram X} {n : ℕ} (hp : y.Pastable z n) (wU : Within u m)
  (wT : Within (y.paste z n hp) m) (hs : ((y.paste z n hp).boundary k α).Equiv v)
  {R : LowerSet m.shape.ogp} (hc : m.shape.ogp.IsPastingAtIn k α wU.image wT.image R)
  (hocc : (ι.trans (sideWithin wT k α hs)).image = wU.image ⊓ wT.image)

theorem equiv_boundary_paste_of_lt (γ : Bool) (hkn : k < n) (β : Bool) :
    ((_root_.cond γ z y).boundary k β).Equiv ((y.paste z n hp).boundary k β) :=
  Within.equiv_of_image_eq
    ((Within.boundary _ k β).trans
      (Within.cond γ (Within.pasteInr y z n hp) (Within.pasteInl y z n hp)))
    (Within.boundary (y.paste z n hp) k β) (by
      rw [Within.image_boundary_trans, Within.image_boundary, Within.image_cond]
      have hP := Within.isPastingIn_paste y z n hp
      have hg := (Within.pasteInl y z n hp).isMoleculeIn_image.isGlobular
      have hg' := (Within.pasteInr y z n hp).isMoleculeIn_image.isGlobular
      exact Bool.cond_rec_prop (p := fun S => (y.paste z n hp).shape.ogp.boundary S k β = _) γ
        (hP.boundary_eq_of_lt_cond true hg hg' hkn β).symm
        (hP.boundary_eq_of_lt_cond false hg' hg hkn β).symm)

include hc hocc in
theorem sidePaste_paste_located (hkn : k < n) (hdu : u.dim = k + 1) :
    ∃ (hY : IsMoleculeIn m.shape.ogp (wU.image ⊔ ((Within.pasteInl y z n hp).trans wT).image))
      (hZ : IsMoleculeIn m.shape.ogp (wU.image ⊔ ((Within.pasteInr y z n hp).trans wT).image)),
      m.shape.ogp.IsPastingIn n (wU.image ⊔ ((Within.pasteInl y z n hp).trans wT).image)
        (wU.image ⊔ ((Within.pasteInr y z n hp).trans wT).image) R ∧
      (sidePaste α u k ι hι h y).Equiv (m.restrictTo hY) ∧
        (sidePaste α u k ι hι h z).Equiv (m.restrictTo hZ) := by
  have hpT : m.shape.ogp.IsPastingIn n ((Within.pasteInl y z n hp).trans wT).image
      ((Within.pasteInr y z n hp).trans wT).image wT.image := by
    rw [Within.image_trans, Within.image_trans]
    exact (isPastingIn_map_iff wT.emb n _ _ _).2 (Within.isPastingIn_paste y z n hp)
  have hgY := ((Within.pasteInl y z n hp).trans wT).isMoleculeIn_image.isGlobular
  have hgZ := ((Within.pasteInr y z n hp).trans wT).isMoleculeIn_image.isGlobular
  obtain ⟨hpU, hcY, hcZ⟩ := hc.isPastingIn_sup hpT
    ((Within.pasteInl y z n hp).trans wT).isMoleculeIn_image
    ((Within.pasteInr y z n hp).trans wT).isMoleculeIn_image hkn
    (by rw [Within.krullDim_image, hdu]; exact_mod_cast hkn)
  have hsY : (y.boundary k α).Equiv v :=
    (equiv_boundary_paste_of_lt hp false hkn α).trans hs
  have hsZ : (z.boundary k α).Equiv v :=
    (equiv_boundary_paste_of_lt hp true hkn α).trans hs
  have hbY : m.shape.ogp.boundary ((Within.pasteInl y z n hp).trans wT).image k α =
      m.shape.ogp.boundary wT.image k α :=
    (hpT.boundary_eq_of_lt_cond false hgZ hgY hkn α).symm
  have hbZ : m.shape.ogp.boundary ((Within.pasteInr y z n hp).trans wT).image k α =
      m.shape.ogp.boundary wT.image k α :=
    (hpT.boundary_eq_of_lt_cond true hgY hgZ hkn α).symm
  have hY := hcY.isMoleculeIn
  have hZ := hcZ.isMoleculeIn
  refine ⟨hY, hZ, hpU,
    sidePaste_equiv_restrictTo _ _ hsY hcY ?_ hY, sidePaste_equiv_restrictTo _ _ hsZ hcZ ?_ hZ⟩
  · rw [sideWithin_congr _ k α wT hsY hs hbY, hocc, hc.inf_eq, hcY.inf_eq]
  · rw [sideWithin_congr _ k α wT hsZ hs hbZ, hocc, hc.inf_eq, hcZ.inf_eq]

end Interchange

theorem exists_sidePaste_paste {y z : PastingDiagram X} {n : ℕ} (hp : y.Pastable z n)
    (hs : ((y.paste z n hp).boundary k α).Equiv v) (hdu : u.dim = k + 1) (hkn : k < n) :
    ∃ hp' : (sidePaste α u k ι hι h y).Pastable (sidePaste α u k ι hι h z) n,
      (sidePaste α u k ι hι h (y.paste z n hp)).Equiv
        ((sidePaste α u k ι hι h y).paste (sidePaste α u k ι hι h z) n hp') := by
  have hc := Within.isPastingAtIn_pasteAt u (y.paste z n hp) k α (sideOcc α k ι hs)
    (isSubmoleculeOf_image_sideOcc α k ι hι hs) h
  have hocc := image_occ_sidePaste (ι := ι) (hι := hι) (h := h) hs
  have h0 := sidePaste_equiv_restrictTo (hι := hι) (h := h) _ _ hs hc hocc
    (pasteAtBoundary u (y.paste z n hp) k α (sideOcc α k ι hs)
      (isSubmoleculeOf_image_sideOcc α k ι hι hs) h).shape.isMolecule
  obtain ⟨hY, hZ, hpU, eY, eZ⟩ := sidePaste_paste_located (hι := hι)
      (h := h) hp _ _ hs hc hocc hkn hdu
  have hdy : n < y.dim := (lt_min_iff.1 hp.2).1
  have hdz : n < z.dim := (lt_min_iff.1 hp.2).2
  let m := pasteAtBoundary u (y.paste z n hp) k α (sideOcc α k ι hs)
      (isSubmoleculeOf_image_sideOcc α k ι hι hs) h
  have hpU' : ∀ {R}, m.shape.ogp.IsPastingIn n _ _ R → m.shape.ogp.IsPastingIn n
      (Within.restrictTo m hY).image (Within.restrictTo m hZ).image R := fun hq => by
    rw [Within.image_restrictTo, Within.image_restrictTo]
    exact hq
  have hdY : n < (m.restrictTo hY).dim := by
    have h1 := dim_restrictTo m hY
    rw [LowerSet.krullDim_sup, Within.krullDim_image, Within.krullDim_image] at h1
    have h2 : ((n : ℕ) : WithBot ℕ∞) < ((m.restrictTo hY).dim : WithBot ℕ∞) := by
      rw [h1]
      exact lt_sup_of_lt_right (by exact_mod_cast hdy)
    exact_mod_cast h2
  have hdZ : n < (m.restrictTo hZ).dim := by
    have h1 := dim_restrictTo m hZ
    rw [LowerSet.krullDim_sup, Within.krullDim_image, Within.krullDim_image] at h1
    have h2 : ((n : ℕ) : WithBot ℕ∞) < ((m.restrictTo hZ).dim : WithBot ℕ∞) := by
      rw [h1]
      exact lt_sup_of_lt_right (by exact_mod_cast hdz)
    exact_mod_cast h2
  have hp'' := pastable_of_isPastingIn (Within.restrictTo m hY) (Within.restrictTo m hZ)
    (hpU' hpU) (lt_min hdY hdZ)
  have hp' : (sidePaste α u k ι hι h y).Pastable (sidePaste α u k ι hι h z) n :=
    ⟨(eY.boundary n true).trans (hp''.1.trans
      ((eZ.boundary n false).symm)),
      by rw [dim_eq_of_equiv eY, dim_eq_of_equiv eZ]; exact hp''.2⟩
  exact ⟨hp', h0.trans (PastingDiagram.Equiv.trans
    ((equiv_paste_of_within (Within.restrictTo m hY) (Within.restrictTo m hZ) (hpU' hpU) _
      hp'').symm)
    ((Equiv.paste eY eZ hp' hp'').symm))⟩

theorem equiv_boundary_sidePaste_of_lt {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v)
    (hdu : u.dim = k + 1) {n : ℕ} (hkn : k < n) (β : Bool) :
    ((sidePaste α u k ι hι h a).boundary n β).Equiv (sidePaste α u k ι hι h (a.boundary n β)) := by
  have hc := Within.isPastingAtIn_pasteAt u a k α (sideOcc α k ι hs)
      (isSubmoleculeOf_image_sideOcc α k ι hι hs) h
  have hocc := image_occ_sidePaste (ι := ι) (hι := hι) (h := h) hs
  have h0 := sidePaste_equiv_restrictTo (hι := hι) (h := h) _ _ hs hc hocc
    (pasteAtBoundary u a k α (sideOcc α k ι hs)
        (isSubmoleculeOf_image_sideOcc α k ι hι hs) h).shape.isMolecule
  obtain ⟨hR', h1⟩ := sidePaste_boundary_equiv_restrictTo (hι := hι)
      (h := h) _ _ hs hc hocc hkn β
  have hb := hc.boundary_eq_sup_of_lt hkn (by rw [Within.krullDim_image, hdu]; exact_mod_cast hkn) β
  refine (h0.boundary n β).trans (PastingDiagram.Equiv.trans
    (equiv_boundary_restrictTo _ _ n β) (PastingDiagram.Equiv.trans ?_ (h1.symm)))
  exact equiv_restrictTo_of_eq _ _ _ hb

theorem equiv_boundary_sidePaste_substitute (hu : u.IsRound) (hdu : u.dim = k + 1)
    (hr : v.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
    (hw : Parallel ⟨V, ι.round_image_iff.1 hr.isRound⟩
      ⟨u.boundary k α, isRound_boundary_of_isRound hu k α⟩)
    {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v) (hka : k ≤ a.dim) :
    ((sidePaste α u k ι hι h a).boundary k α).Equiv
      (v.substitute ι hr ⟨u.boundary k α, isRound_boundary_of_isRound hu k α⟩ hw) := by
  obtain ⟨hR', e⟩ := substitute_equiv_restrictTo_boundary
    (Within.pasteAtInl u a k α (sideOcc α k ι hs) (isSubmoleculeOf_image_sideOcc α k ι hι hs) h)
    (Within.pasteAtInr u a k α (sideOcc α k ι hs) (isSubmoleculeOf_image_sideOcc α k ι hι hs) h) hs
    (Within.isPastingAtIn_pasteAt u a k α (sideOcc α k ι hs)
        (isSubmoleculeOf_image_sideOcc α k ι hι hs) h)
    (image_occ_sidePaste (ι := ι) (hι := hι) (h := h) hs) hu hdu hka hr hw
  rw [sidePaste_of hs]
  exact PastingDiagram.Equiv.trans
    (Within.equiv_restrictTo_of_eq (Within.boundary _ k α) (Within.image_boundary _ k α) hR')
    (e.symm)

theorem equiv_boundary_sidePaste_of_side (hu : u.IsRound) (hdu : u.dim = k + 1)
    (hr : v.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤) {a b : PastingDiagram X}
    (ha : (a.boundary k α).Equiv v)
    (hb : (b.boundary k α).Equiv v) (hka : k ≤ a.dim) (hkb : k ≤ b.dim) :
    ((sidePaste α u k ι hι h a).boundary k α).Equiv ((sidePaste α u k ι hι h b).boundary k α) := by
  have hw : Parallel ⟨V, ι.round_image_iff.1 hr.isRound⟩
      ⟨u.boundary k α, isRound_boundary_of_isRound hu k α⟩ :=
    (parallel_boundary hu hdu (!α) α).of_equiv_left (h.symm)
  exact (equiv_boundary_sidePaste_substitute hu hdu hr hw ha hka).trans
    ((equiv_boundary_sidePaste_substitute hu hdu hr hw hb hkb).symm)

end SidePaste

theorem paste_cond_equiv_sidePaste (γ : Bool) {u v a : PastingDiagram X} {k : ℕ}
    (hsub : v.shape.ogp.IsSubmoleculeOf (Within.refl v).image ⊤)
    (h : (u.boundary k (!γ)).Equiv v) (hs : (a.boundary k γ).Equiv v)
    (hpa : (cond γ a u).Pastable (cond γ u a) k) :
    ((cond γ a u).paste (cond γ u a) k hpa).Equiv (sidePaste γ u k (Within.refl v) hsub h a) := by
  rw [sidePaste_of hs]
  refine equiv_paste_pasteAtBoundary u _ k γ _ _ ?_ h hpa
  rw [sideOcc, Within.image_trans, Within.image_refl]
  exact Within.image_ofEquiv _

theorem exists_equiv_boundary_paste_cond (γ : Bool) {u x : PastingDiagram X} {k n : ℕ}
    (hp : (cond γ x u).Pastable (cond γ u x) k) (hdu : u.dim = k + 1) (hkn : k < n)
    (hn : n ≤ x.dim) (β : Bool) :
    ∃ hp' : (cond γ (x.boundary n β) u).Pastable (cond γ u (x.boundary n β)) k,
      (((cond γ x u).paste (cond γ u x) k hp).boundary n β).Equiv
        ((cond γ (x.boundary n β) u).paste (cond γ u (x.boundary n β)) k hp') := by
  have hsub := Within.isSubmoleculeOf_image_refl (x.boundary k γ)
  have h : (u.boundary k (!γ)).Equiv (x.boundary k γ) := hp.side.symm
  have hs' : ((x.boundary n β).boundary k γ).Equiv (x.boundary k γ) :=
    equiv_boundary_boundary x hkn β γ
  have hp' : (cond γ (x.boundary n β) u).Pastable (cond γ u (x.boundary n β)) k :=
    Pastable.of_side γ (hs'.trans hp.side) (by rw [dim_boundary x hn]; exact hkn)
      (by rw [hdu]; exact Nat.lt_succ_self k)
  refine ⟨hp', ((paste_cond_equiv_sidePaste γ hsub h (.refl _) hp).boundary n β).trans
    ((equiv_boundary_sidePaste_of_lt (.refl _) hdu hkn β).trans ?_)⟩
  exact (sidePaste_equiv hs' (.refl _)).trans (paste_cond_equiv_sidePaste γ hsub h hs' hp').symm

theorem exists_paste_cond_paste (γ : Bool) {u y z : PastingDiagram X} {k n : ℕ}
    (hp : y.Pastable z n)
    (hpu : (cond γ (y.paste z n hp) u).Pastable (cond γ u (y.paste z n hp)) k)
    (hdu : u.dim = k + 1) (hkn : k < n) :
    ∃ (hy : (cond γ y u).Pastable (cond γ u y) k) (hz : (cond γ z u).Pastable (cond γ u z) k)
      (hyz : ((cond γ y u).paste (cond γ u y) k hy).Pastable
        ((cond γ z u).paste (cond γ u z) k hz) n),
      ((cond γ (y.paste z n hp) u).paste (cond γ u (y.paste z n hp)) k hpu).Equiv
        (((cond γ y u).paste (cond γ u y) k hy).paste ((cond γ z u).paste (cond γ u z) k hz) n
          hyz) := by
  have hsub := Within.isSubmoleculeOf_image_refl ((y.paste z n hp).boundary k γ)
  have h : (u.boundary k (!γ)).Equiv ((y.paste z n hp).boundary k γ) := hpu.side.symm
  have hsy : (y.boundary k γ).Equiv ((y.paste z n hp).boundary k γ) :=
    equiv_boundary_paste_of_lt hp false hkn γ
  have hsz : (z.boundary k γ).Equiv ((y.paste z n hp).boundary k γ) :=
    equiv_boundary_paste_of_lt hp true hkn γ
  have hku : k < u.dim := by rw [hdu]; exact Nat.lt_succ_self k
  have hy : (cond γ y u).Pastable (cond γ u y) k :=
    Pastable.of_side γ (hsy.trans hpu.side) (hkn.trans (lt_min_iff.1 hp.2).1) hku
  have hz : (cond γ z u).Pastable (cond γ u z) k :=
    Pastable.of_side γ (hsz.trans hpu.side) (hkn.trans (lt_min_iff.1 hp.2).2) hku
  have ey := paste_cond_equiv_sidePaste γ hsub h hsy hy
  have ez := paste_cond_equiv_sidePaste γ hsub h hsz hz
  obtain ⟨hp', e⟩ := exists_sidePaste_paste (ι := Within.refl _) (hι := hsub) (h := h) hp
    (.refl _) hdu hkn
  have hyz := hp'.of_equiv ey.symm ez.symm
  exact ⟨hy, hz, hyz, (paste_cond_equiv_sidePaste γ hsub h (.refl _) hpu).trans
    (e.trans (Equiv.paste ey.symm ez.symm hp' hyz))⟩

namespace InHom

variable {H : PdHom X} {a : PastingDiagram X}

theorem promote (h : InHom H a) {n : ℕ} (hn : n < H.k) : InHom (H.boundary n) a :=
  ⟨by have := h.lt_dim; change n < a.dim; omega,
    (PastingDiagram.Equiv.symm (equiv_boundary_boundary a hn false false)).trans
      (h.source.boundary n false),
    (PastingDiagram.Equiv.symm (equiv_boundary_boundary a hn true true)).trans
      (h.target.boundary n true)⟩

theorem factor {y z : PastingDiagram X} {n : ℕ} {hp : y.Pastable z n}
    (h : InHom H (y.paste z n hp)) (hkn : H.k < n) (γ : Bool) : InHom H (cond γ z y) :=
  ⟨by obtain ⟨hy, hz⟩ := lt_min_iff.1 hp.2; cases γ <;> simp only [cond] <;> omega,
    (equiv_boundary_paste_of_lt hp γ hkn false).trans h.source,
    (equiv_boundary_paste_of_lt hp γ hkn true).trans h.target⟩

end InHom

structure CtxLaws (H : PdHom X) (F : PastingDiagram X → PastingDiagram X) : Prop where
  equiv : ∀ a a', InHom H a → a.Equiv a' → (F a).Equiv (F a')
  dim_eq : ∀ a, InHom H a → (F a).dim = a.dim
  boundary : ∀ a, InHom H a → ∀ {n : ℕ}, H.k < n → n < a.dim → ∀ β : Bool,
    ((F a).boundary n β).Equiv (F (a.boundary n β))
  paste : ∀ (y z : PastingDiagram X) {n : ℕ} (hp : y.Pastable z n),
    InHom H (y.paste z n hp) → H.k < n →
      ∃ hp' : (F y).Pastable (F z) n, (F (y.paste z n hp)).Equiv ((F y).paste (F z) n hp')

end Atoms.Diagrammatic
