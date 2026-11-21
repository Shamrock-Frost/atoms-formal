import Atoms.Diagrammatic.Context.Trim

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section SidePaste

variable {α : Bool} {u : PastingDiagram X} {k : ℕ} {v V : PastingDiagram X} {ι : Within V v}
  {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤} {h : (u.boundary k (!α)).Equiv V}

theorem sidePaste_paste_not (hdu : u.dim = k + 1) {y c : PastingDiagram X}
    (hs : (y.boundary k α).Equiv v) (hp : (cond (!α) y c).Pastable (cond (!α) c y) k) :
    ∃ hp' : (cond (!α) (sidePaste α u k ι hι h y) c).Pastable
        (cond (!α) c (sidePaste α u k ι hι h y)) k,
      (sidePaste α u k ι hι h ((cond (!α) y c).paste (cond (!α) c y) k hp)).Equiv
        ((cond (!α) (sidePaste α u k ι hι h y) c).paste
          (cond (!α) c (sidePaste α u k ι hι h y)) k hp') := by
  set T := (cond (!α) y c).paste (cond (!α) c y) k hp
  have hdy : k < y.dim := by
    have := hp.2
    cases α <;>
      simp only [Bool.not_true, Bool.not_false, cond_true, cond_false, lt_min_iff] at this <;>
      omega
  have hdc : k < c.dim := by
    have := hp.2
    cases α <;>
      simp only [Bool.not_true, Bool.not_false, cond_true, cond_false, lt_min_iff] at this <;>
      omega
  have hsT : (T.boundary k α).Equiv v :=
    (equiv_boundary_paste hp α).trans (by cases α <;> exact hs)
  have hιT := isSubmoleculeOf_image_sideOcc α k ι hι hsT
  set m := pasteAtBoundary u T k α (sideOcc α k ι hsT) hιT h
  set wL := Within.pasteAtInl u T k α (sideOcc α k ι hsT) hιT h
  set wR := Within.pasteAtInr u T k α (sideOcc α k ι hsT) hιT h
  have hc := Within.isPastingAtIn_pasteAt u T k α (sideOcc α k ι hsT) hιT h
  obtain ⟨wy, hpT⟩ := Within.exists_isPastingIn_pasteIn (!α) hp
  set wc := Within.pasteIn (!α) hp
  have hpm : m.shape.ogp.IsPastingIn k (cond (!α) (wy.trans wR).image (wc.trans wR).image)
      (cond (!α) (wc.trans wR).image (wy.trans wR).image) wR.image := by
    have e := (isPastingIn_map_iff wR.emb k _ _ _).2 hpT
    rw [Bool.apply_cond (OGP.map wR.emb), Bool.apply_cond (OGP.map wR.emb)] at e
    rw [Within.image_trans, Within.image_trans]
    exact e
  obtain ⟨hSY, hcY, hpR⟩ := isPastingAtIn_of_isPastingIn_not hc (wy.trans wR).isMoleculeIn_image hpm
  have hY := hcY.isMoleculeIn
  have hbT : m.shape.ogp.boundary (wy.trans wR).image k α = m.shape.ogp.boundary wR.image k α := by
    have e := ((isPastingIn_cond_comm (!α)).1 hpm).boundary_cond (!!α)
    rw [Bool.not_not] at e
    exact e.symm
  have eY : (sidePaste α u k ι hι h y).Equiv (m.restrictTo hY) :=
    sidePaste_equiv_restrictTo wL (wy.trans wR) hs hcY (by
      rw [sideWithin_congr (wy.trans wR) k α wR hs hsT hbT, hSY]
      exact image_occ_sidePaste (hι := hι) hsT) hY
  have hdY : k < (m.restrictTo hY).dim := by
    rw [← dim_eq_of_equiv eY, dim_sidePaste hs (by omega)]
    exact hdy
  have hpR' : m.shape.ogp.IsPastingIn k
      (cond (!α) (Within.restrictTo m hY).image (wc.trans wR).image)
      (cond (!α) (wc.trans wR).image (Within.restrictTo m hY).image) ⊤ := by
    rw [Within.image_restrictTo]
    exact hpR
  have hp'' := pastable_cond_of_isPastingIn (!α) (Within.restrictTo m hY) (wc.trans wR) hpR' hdY
    hdc
  have e₁ : (cond (!α) (m.restrictTo hY) c).Equiv (cond (!α) (sidePaste α u k ι hι h y) c) := by
    cases α <;> first | exact eY.symm | exact .refl _
  have e₂ : (cond (!α) c (m.restrictTo hY)).Equiv (cond (!α) c (sidePaste α u k ι hι h y)) := by
    cases α <;> first | exact eY.symm | exact .refl _
  have hp' := hp''.of_equiv e₁ e₂
  refine ⟨hp', ?_⟩
  rw [sidePaste_of hsT]
  exact (equiv_restrictTo_univ m).symm.trans
    ((equiv_paste_cond_of_within (!α) (Within.restrictTo m hY) (wc.trans wR) hpR'
      m.shape.isMolecule hp'').symm.trans (Equiv.paste e₁ e₂ hp'' hp'))

theorem sidePaste_equiv_paste_sidePaste (hdu : u.dim = k + 1) (hdv : v.dim = k)
    {y : PastingDiagram X} (hs : (y.boundary k α).Equiv v) (hky : k < y.dim) :
    ∃ hp : (cond α y (sidePaste α u k ι hι h v)).Pastable
        (cond α (sidePaste α u k ι hι h v) y) k,
      (sidePaste α u k ι hι h y).Equiv
        ((cond α y (sidePaste α u k ι hι h v)).paste
          (cond α (sidePaste α u k ι hι h v) y) k hp) := by
  have hιy := isSubmoleculeOf_image_sideOcc α k ι hι hs
  set m := pasteAtBoundary u y k α (sideOcc α k ι hs) hιy h
  set wL := Within.pasteAtInl u y k α (sideOcc α k ι hs) hιy h
  set wR := Within.pasteAtInr u y k α (sideOcc α k ι hs) hιy h
  have hc := Within.isPastingAtIn_pasteAt u y k α (sideOcc α k ι hs) hιy h
  obtain ⟨hcB, hpm⟩ := hc.isPastingAtIn_boundary_and_isPastingIn_sup_boundary
  have hB := hcB.isMoleculeIn
  set wv := sideWithin wR k α hs
  have hwv : wv.image = m.shape.ogp.boundary wR.image k α := image_sideWithin wR k α hs
  have hsv : (v.boundary k α).Equiv v := equiv_boundary_dim v hdv.le α
  have hself : sideWithin wv k α hsv = wv := Within.ext_of_image_eq _ _ (by
    rw [image_sideWithin, hwv, boundary_boundary_of_le le_rfl])
  have eP : (sidePaste α u k ι hι h v).Equiv (m.restrictTo hB) :=
    sidePaste_equiv_restrictTo wL wv hsv (by rw [hwv]; exact hcB) (by
      rw [hself, hwv, hc.inf_boundary_right]
      exact image_occ_sidePaste (hι := hι) hs) hB
  have hdP : k < (m.restrictTo hB).dim := by
    rw [← dim_eq_of_equiv eP, sidePaste_of hsv, dim_pasteAtBoundary, hdu]
    omega
  have hpR : m.shape.ogp.IsPastingIn k (cond α wR.image (Within.restrictTo m hB).image)
      (cond α (Within.restrictTo m hB).image wR.image) ⊤ := by
    rw [Within.image_restrictTo]
    exact hpm
  have hp'' := pastable_cond_of_isPastingIn α wR (Within.restrictTo m hB) hpR hky hdP
  have e₁ : (cond α y (m.restrictTo hB)).Equiv (cond α y (sidePaste α u k ι hι h v)) := by
    cases α <;> first | exact eP.symm | exact .refl _
  have e₂ : (cond α (m.restrictTo hB) y).Equiv (cond α (sidePaste α u k ι hι h v) y) := by
    cases α <;> first | exact eP.symm | exact .refl _
  have hp' := hp''.of_equiv e₁ e₂
  refine ⟨hp', ?_⟩
  rw [sidePaste_of hs]
  exact (equiv_restrictTo_univ m).symm.trans
    ((equiv_paste_cond_of_within α wR (Within.restrictTo m hB) hpR m.shape.isMolecule
      hp'').symm.trans (Equiv.paste e₁ e₂ hp'' hp'))

end SidePaste

theorem exists_located_sidePaste {α : Bool} {u : PastingDiagram X} {k : ℕ}
    {v V : PastingDiagram X} {ι : Within V v} {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤}
    {h : (u.boundary k (!α)).Equiv V} {a : PastingDiagram X} (hs : (a.boundary k α).Equiv v) :
    ∃ (m : PastingDiagram X) (wU : Within u m) (wA : Within a m), sidePaste α u k ι hι h a = m ∧
      m.shape.ogp.IsPastingAtIn k α wU.image wA.image ⊤ ∧
      (ι.trans (sideWithin wA k α hs)).image = wU.image ⊓ wA.image :=
  ⟨_, _, _, sidePaste_of hs, Within.isPastingAtIn_pasteAt _ _ _ _ _ _ _,
    image_occ_sidePaste (ι := ι) (hι := hι) (h := h) hs⟩

section Swap

variable {β : Bool} {y : PastingDiagram X} {j : ℕ} {z₀ Z : PastingDiagram X} {κ : Within Z z₀}
  {hκ : z₀.shape.ogp.IsSubmoleculeOf κ.image ⊤} {hy : (y.boundary j (!β)).Equiv Z}
  {α : Bool} {u : PastingDiagram X} {n : ℕ} {v₀ V : PastingDiagram X} {ι : Within V v₀}
  {hι : v₀.shape.ogp.IsSubmoleculeOf ι.image ⊤} {h : (u.boundary n (!α)).Equiv V}

theorem sidePaste_sidePaste_of_lt (hdy : y.dim = j + 1) (hjn : j < n) {w : PastingDiagram X}
    (wy : Within y w) (wv : Within v₀ w) (hc : w.shape.ogp.IsPastingAtIn j β wy.image wv.image ⊤)
    (hs₀ : (v₀.boundary j β).Equiv z₀)
    (hm : (κ.trans (sideWithin wv j β hs₀)).image = wy.image ⊓ wv.image) {ι' : Within V w}
    (hι' : w.shape.ogp.IsSubmoleculeOf ι'.image ⊤) (hι'i : ι'.image = (ι.trans wv).image)
    {a : PastingDiagram X} (hsa : (a.boundary n α).Equiv v₀) :
    (sidePaste β y j κ hκ hy (sidePaste α u n ι hι h a)).Equiv
      (sidePaste α u n ι' hι' h (sidePaste β y j κ hκ hy a)) := by
  have hsb : (a.boundary j β).Equiv z₀ :=
    (equiv_boundary_boundary a hjn α β).symm.trans ((hsa.boundary j β).trans hs₀)
  have hlow : ((sidePaste α u n ι hι h a).boundary j β).Equiv z₀ :=
    (equiv_boundary_boundary _ hjn (!α) β).symm.trans
      (((equiv_boundary_not_sidePaste hsa).boundary j β).trans
        ((equiv_boundary_boundary a hjn (!α) β).trans hsb))
  obtain ⟨m₁, wU₁, wA₁, e₁, hc₁, hocc₁⟩ :=
    exists_located_sidePaste (ι := ι) (hι := hι) (h := h) hsa
  rw [e₁] at hlow ⊢
  obtain ⟨m, wY, wR, e₂, hc₂, hocc₂⟩ :=
    exists_located_sidePaste (ι := κ) (hι := hκ) (h := hy) hlow
  rw [e₂]
  set wU := wU₁.trans wR
  set wA := wA₁.trans wR
  have hc₁' : m.shape.ogp.IsPastingAtIn n α wU.image wA.image wR.image := by
    rw [Within.image_trans, Within.image_trans]
    exact hc₁.map wR.emb
  have hdY : Order.krullDim wY.image ≤ n := by
    rw [Within.krullDim_image, hdy]
    exact_mod_cast Nat.succ_le_of_lt hjn
  obtain ⟨hbd, hYm, hYA, hUYA⟩ := hc₁'.swap_of_lt hc₂ hjn hdY
  have hoccA : (κ.trans (sideWithin wA j β hsb)).image = wY.image ⊓ wA.image := by
    rw [sideWithin_congr wA j β wR hsb hlow hbd, hocc₂, hYm]
  set Q := sidePaste β y j κ hκ hy a
  have eQ : Q.Equiv (m.restrictTo hYA.isMoleculeIn) :=
    sidePaste_equiv_restrictTo wY wA hsb hYA hoccA hYA.isMoleculeIn
  set wQ : Within Q m := (Within.ofEquiv eQ).trans (Within.restrictTo m hYA.isMoleculeIn)
  have hwQ : wQ.image = wY.image ⊔ wA.image := by
    rw [Within.image_trans, Within.image_ofEquiv]
    exact Within.image_restrictTo m _
  have hsQ : (Q.boundary n α).Equiv w :=
    (equiv_boundary_sidePaste_of_lt hsb hdy hjn α).trans
      ((sidePaste_equiv ((equiv_boundary_boundary a hjn α β).trans hsb) hsa).trans
        ((sidePaste_equiv_restrictTo wy wv hs₀ hc hm w.shape.isMolecule).trans
          (equiv_restrictTo_univ w)))
  have hsA : sideWithin wA n α hsa = (sideWithin wA₁ n α hsa).trans wR :=
    Within.ext_of_image_eq _ _ (by
      rw [image_sideWithin, Within.image_trans wA₁ wR, Within.image_trans, image_sideWithin,
        map_boundary])
  have hoccU : (ι.trans (sideWithin wA n α hsa)).image = wU.image ⊓ wA.image := by
    rw [hsA, Within.image_trans_assoc, hocc₁, map_inf, ← Within.image_trans,
      ← Within.image_trans]
  set P₀ := pasteAtBoundary y v₀ j β (sideOcc β j κ hs₀)
    (isSubmoleculeOf_image_sideOcc β j κ hκ hs₀) hy
  obtain ⟨ω₁, hω₁i, hω₁⟩ : ∃ ω₁ : Within P₀ w, ω₁.image = ⊤ ∧
      (Within.pasteAtInr y v₀ j β (sideOcc β j κ hs₀)
        (isSubmoleculeOf_image_sideOcc β j κ hκ hs₀) hy).trans ω₁ = wv :=
    ⟨_, Within.image_pasteAtOfWithin wy wv hc _ _ ((image_sideOcc_trans_boundary wv j β hs₀ κ).trans
      hm) hy, (Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin wy wv hc _ _
        ((image_sideOcc_trans_boundary wv j β hs₀ κ).trans hm) hy).2⟩
  set sV := sideWithin wA n α hsa
  have hcV : m.shape.ogp.IsPastingAtIn j β wY.image sV.image
      (wY.image ⊔ m.shape.ogp.boundary wA.image n α) := by
    rw [image_sideWithin]
    exact hYA.isPastingAtIn_boundary_of_lt hjn α
  have hmV : ((sideOcc β j κ hs₀).trans ((Within.boundary v₀ j β).trans sV)).image =
      wY.image ⊓ sV.image := by
    rw [image_sideOcc_trans_boundary, sideWithin_congr sV j β wA hs₀ hsb (by
      rw [image_sideWithin, wA.isMoleculeIn_image.isGlobular j n hjn β α]), hoccA,
      image_sideWithin, hYA.inf_boundary_of_lt hjn α]
  obtain ⟨ω₂, hω₂i, hω₂⟩ : ∃ ω₂ : Within P₀ m,
      ω₂.image = wY.image ⊔ m.shape.ogp.boundary wA.image n α ∧
      (Within.pasteAtInr y v₀ j β (sideOcc β j κ hs₀)
        (isSubmoleculeOf_image_sideOcc β j κ hκ hs₀) hy).trans ω₂ = sV :=
    ⟨_, Within.image_pasteAtOfWithin wY sV hcV _ _ hmV hy,
      (Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin wY sV hcV _ _ hmV hy).2⟩
  set sQ := sideWithin wQ n α hsQ
  have hω : ω₁.trans sQ = ω₂ := Within.ext_of_image_eq _ _ (by
    rw [Within.image_trans, hω₁i, hω₂i]
    change sQ.image = _
    rw [image_sideWithin, hwQ, hYA.boundary_eq_sup_of_lt hjn hdY α])
  have hv : wv.trans sQ = sV := by
    rw [← hω₁, Within.trans_assoc, hω, hω₂]
  have hι'e : ι' = ι.trans wv := Within.ext_of_image_eq _ _ hι'i
  have hoccQ : (ι'.trans sQ).image = wU.image ⊓ wQ.image := by
    rw [hι'e, Within.trans_assoc, hv, hoccU, hwQ, hUYA.inf_eq, hc₁'.inf_eq]
  have hcQ : m.shape.ogp.IsPastingAtIn n α wU.image wQ.image ⊤ := by
    rw [hwQ]
    exact hUYA
  exact ((sidePaste_equiv_restrictTo wU wQ hsQ hcQ hoccQ m.shape.isMolecule).trans
    (equiv_restrictTo_univ m)).symm

end Swap

namespace CtxExpr

theorem side_app_paste_not {α : Bool} {u : PastingDiagram X} {k : ℕ} {v V : PastingDiagram X}
    {ι : Within V v} {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤}
    {h : (u.boundary k (!α)).Equiv V} (hdu : u.dim = k + 1) {y c : PastingDiagram X}
    (hs : (y.boundary k α).Equiv v) (hp : (cond (!α) y c).Pastable (cond (!α) c y) k) :
    ((side α u k ι hι h).app ((paste (!α) c k).app y)).Equiv
      ((paste (!α) c k).app ((side α u k ι hι h).app y)) := by
  obtain ⟨hp', e⟩ := sidePaste_paste_not (ι := ι) (hι := hι) (h := h) hdu hs hp
  have hsT : (((cond (!α) y c).paste (cond (!α) c y) k hp).boundary k α).Equiv v :=
    (equiv_boundary_paste hp α).trans (by cases α <;> exact hs)
  have hsa : (((paste (!α) c k).app y).boundary k α).Equiv v :=
    ((paste_app (!α) hp).boundary k α).trans hsT
  exact (sidePaste_equiv hsa (paste_app (!α) hp)).trans (e.trans (paste_app (!α) hp').symm)

theorem side_app_equiv_paste {α : Bool} {u : PastingDiagram X} {k : ℕ} {v V : PastingDiagram X}
    {ι : Within V v} {hι : v.shape.ogp.IsSubmoleculeOf ι.image ⊤}
    {h : (u.boundary k (!α)).Equiv V} (hdu : u.dim = k + 1) (hdv : v.dim = k)
    {y : PastingDiagram X} (hs : (y.boundary k α).Equiv v) (hky : k < y.dim) :
    ((side α u k ι hι h).app y).Equiv ((paste α ((side α u k ι hι h).app v) k).app y) := by
  obtain ⟨hp, e⟩ := sidePaste_equiv_paste_sidePaste (ι := ι) (hι := hι) (h := h) hdu hdv hs hky
  exact e.trans (paste_app α hp).symm

end CtxExpr

end Atoms.Diagrammatic
