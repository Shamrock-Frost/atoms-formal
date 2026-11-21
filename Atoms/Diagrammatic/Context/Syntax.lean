import Atoms.Diagrammatic.Context.Pasting

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

def PastingDiagram.Within.mapTo {a m : PastingDiagram X} (w : Within a m) (f : X ⟶ Y) :
    Within (a.mapTo f) (m.mapTo f) :=
  ⟨w.emb, by
    change realize.map (RDCpx.ofInclusion (P := a.shape.rdc) (Q := m.shape.rdc) w.emb) ≫
        (m.map ≫ f) =
      a.map ≫ f
    rw [← Category.assoc, w.comm]⟩

theorem PastingDiagram.Within.image_mapTo {a m : PastingDiagram X} (w : Within a m) (f : X ⟶ Y) :
    (w.mapTo f).image = w.image :=
  rfl

def RoundPastingDiagram.mapTo (u : RoundPastingDiagram X) (f : X ⟶ Y) :
    RoundPastingDiagram Y :=
  ⟨u.toPastingDiagram.mapTo f, u.isRound⟩

theorem image_trans_sideWithin_mapTo {Y : DiagSet.{u}} {z₀ Z v₀ w : PastingDiagram X}
    (κ : Within Z z₀) (wv : Within v₀ w) {j : ℕ} {β : Bool} (hs₀ : (v₀.boundary j β).Equiv z₀)
    (f : X ⟶ Y) :
    ((κ.mapTo f).trans (sideWithin (wv.mapTo f) j β (hs₀.mapTo_boundary f))).image =
      (κ.trans (sideWithin wv j β hs₀)).image := by
  have e : sideWithin (wv.mapTo f) j β (hs₀.mapTo_boundary f) = (sideWithin wv j β hs₀).mapTo f :=
    Within.ext_of_image_eq _ _ (by
      rw [image_sideWithin, Within.image_mapTo, Within.image_mapTo, image_sideWithin]
      rfl)
  rw [e]
  rfl

theorem sidePaste_mapTo (α : Bool) (u : PastingDiagram X) (k : ℕ) {v V : PastingDiagram X}
    (ι : Within V v) (hι : IsSubmoleculeOf v.shape.ogp ι.image ⊤)
    (h : (u.boundary k (!α)).Equiv V) (f : X ⟶ Y) {a : PastingDiagram X}
    (hs : (a.boundary k α).Equiv v) :
    (sidePaste α (u.mapTo f) k (ι.mapTo f) hι (h.mapTo_boundary f) (a.mapTo f)).Equiv
      ((sidePaste α u k ι hι h a).mapTo f) := by
  have hs' : ((a.mapTo f).boundary k α).Equiv (v.mapTo f) := hs.mapTo_boundary f
  rw [sidePaste_of hs]
  have hιs := isSubmoleculeOf_image_sideOcc α k ι hι hs
  have hc := Within.isPastingAtIn_pasteAt u a k α (sideOcc α k ι hs) hιs h
  have hocc0 := image_occ_sidePaste (ι := ι) (hι := hι) (h := h) hs
  let wR := Within.pasteAtInr u a k α (sideOcc α k ι hs) hιs h
  let wL := Within.pasteAtInl u a k α (sideOcc α k ι hs) hιs h
  have hW : ∀ x, (sideWithin (wR.mapTo f) k α hs').emb x = (sideWithin wR k α hs).emb x :=
    fun x => IsMoleculeIn.eqOn_of_map_eq (f := (sideWithin (wR.mapTo f) k α hs').emb)
      (g := (sideWithin wR k α hs).emb) v.shape.isMolecule
      ((image_sideWithin _ k α hs').trans (image_sideWithin _ k α hs).symm)
      (LowerSet.mem_top (a := x))
  have hocc : ((ι.mapTo f).trans (sideWithin (wR.mapTo f) k α hs')).image =
      (wL.mapTo f).image ⊓ (wR.mapTo f).image := by
    refine Eq.trans ?_ hocc0
    rw [Within.image_trans, Within.image_trans]
    exact SetLike.coe_injective (by rw [coe_map, coe_map]; exact Set.image_congr fun x _ => hW x)
  exact PastingDiagram.Equiv.trans
    (sidePaste_equiv_restrictTo (ι := ι.mapTo f) (hι := hι) (h := h.mapTo_boundary f) _ _ hs'
      hc hocc (pasteAtBoundary u a k α (sideOcc α k ι hs) hιs h).shape.isMolecule)
    (equiv_restrictTo_univ _)

def PdHom.mapTo (H : PdHom X) (f : X ⟶ Y) : PdHom Y :=
  ⟨H.k, H.v.mapTo f, H.w.mapTo f⟩

@[simp]
theorem PdHom.k_mapTo (H : PdHom X) (f : X ⟶ Y) : (H.mapTo f).k = H.k :=
  rfl

@[simp]
theorem PdHom.side_mapTo (H : PdHom X) (f : X ⟶ Y) (α : Bool) :
    (H.mapTo f).side α = (H.side α).mapTo f := by
  cases α <;> rfl

theorem PdHom.boundary_mapTo (H : PdHom X) (f : X ⟶ Y) (n : ℕ) :
    (H.mapTo f).boundary n = (H.boundary n).mapTo f := by
  simp only [PdHom.boundary, PdHom.mapTo, PastingDiagram.boundary_mapTo]

theorem PdHom.Equiv.mapTo {H H' : PdHom X} (e : H.Equiv H') (f : X ⟶ Y) :
    (H.mapTo f).Equiv (H'.mapTo f) :=
  ⟨e.k_eq, e.equiv_v.mapTo f, e.equiv_w.mapTo f⟩

theorem InHom.mapTo {H : PdHom X} {a : PastingDiagram X} (h : InHom H a) (f : X ⟶ Y) :
    InHom (H.mapTo f) (a.mapTo f) :=
  ⟨h.lt_dim, by rw [PastingDiagram.boundary_mapTo]; exact h.source.mapTo f,
    by rw [PastingDiagram.boundary_mapTo]; exact h.target.mapTo f⟩

inductive CtxExpr (X : DiagSet.{u}) : Type u
  | side (α : Bool) (u : PastingDiagram X) (k : ℕ) {v V : PastingDiagram X} (ι : Within V v)
      (hι : IsSubmoleculeOf v.shape.ogp ι.image ⊤) (h : (u.boundary k (!α)).Equiv V)
  | id
  | comp (s t : CtxExpr X)

namespace CtxExpr

noncomputable def app : CtxExpr X → PastingDiagram X → PastingDiagram X
  | side α u k ι hι h => sidePaste α u k ι hι h
  | id => fun a => a
  | comp s t => fun a => s.app (t.app a)

def mapTo (f : X ⟶ Y) : CtxExpr X → CtxExpr Y
  | side α u k ι hι h => side α (u.mapTo f) k (ι.mapTo f) hι (h.mapTo_boundary f)
  | id => id
  | comp s t => comp (s.mapTo f) (t.mapTo f)

theorem mapTo_mapTo {Z : DiagSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ t : CtxExpr X, (t.mapTo f).mapTo g = t.mapTo (f ≫ g)
  | .side _ _ _ _ _ _ => rfl
  | .id => rfl
  | .comp s t => by
    change CtxExpr.comp ((s.mapTo f).mapTo g) ((t.mapTo f).mapTo g) = .comp _ _
    rw [mapTo_mapTo f g s, mapTo_mapTo f g t]

theorem app_equiv : ∀ (t : CtxExpr X) {a a' : PastingDiagram X}, a.Equiv a' →
    (t.app a).Equiv (t.app a')
  | @side _ α u k v _ ι hι h, a, a', e => by
    by_cases hs : (a.boundary k α).Equiv v
    · exact sidePaste_equiv hs e
    · have hs' : ¬ (a'.boundary k α).Equiv v := fun hs' =>
        hs ((e.boundary k α).trans hs')
      change (sidePaste α u k ι hι h a).Equiv (sidePaste α u k ι hι h a')
      rw [sidePaste_of_not hs, sidePaste_of_not hs']
      exact e
  | id, _, _, e => e
  | comp s t, _, _, e => s.app_equiv (t.app_equiv e)

inductive Typed (A : Set (RoundPastingDiagram X)) (p : Prop) :
    PdHom X → CtxExpr X → PdHom X → Prop
  | side {H H' : PdHom X} (α : Bool) {v₀ : PastingDiagram X} (u : RoundPastingDiagram X)
      (hu : u ∈ A) (hdu : u.dim = H.k + 1) {V : PastingDiagram X} (ι : Within V v₀)
      (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
      (h : (u.boundary H.k (!α)).Equiv V) (hs : v₀.Equiv (H.side α))
      (e : (H.setSide α ((sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h v₀).boundary
        H.k α)).Equiv H') :
      Typed A p H (side α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h) H'
  | id {H H' : PdHom X} (e : H.Equiv H') : Typed A p H id H'
  | comp {H H' H'' : PdHom X} {s t : CtxExpr X} :
      Typed A p H t H' → Typed A p H' s H'' → Typed A p H (comp s t) H''
  | promote {k : ℕ} {H H₁ H' : PdHom X} {t : CtxExpr X} (hp : p) (hk : H.k = k + 1)
      (hv : InHom (H.boundary k) H.v) (hw : InHom (H.boundary k) H.w)
      (ht : Typed A p (H.boundary k) t H₁)
      (e : (⟨H.k, t.app H.v, t.app H.w⟩ : PdHom X).Equiv H') : Typed A p H t H'

namespace Typed

variable {A : Set (RoundPastingDiagram X)} {p : Prop}

theorem dim_side_of_isRewritable {k : ℕ} {α : Bool} {v₀ : PastingDiagram X}
    (u : RoundPastingDiagram X) (hdu : u.dim = k + 1) {V : PastingDiagram X} (ι : Within V v₀)
    (hι : v₀.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (h : (u.boundary k (!α)).Equiv V) : v₀.dim = k := by
  rw [← (ι.isRewritableSubmolecule_image_iff.1 hι).2.2, ← dim_eq_of_equiv h]
  exact dim_boundary _ (by omega) _

theorem k_eq {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') : H'.k = H.k := by
  induction ht with
  | side _ _ _ _ _ _ _ _ e => exact e.k_eq.symm
  | id e => exact e.k_eq.symm
  | comp _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | promote _ _ _ _ _ e _ => exact e.k_eq.symm

private theorem ctxLaws_and_mapsInto {H H' : PdHom X} {t : CtxExpr X}
    (ht : Typed A p H t H') : CtxLaws H t.app ∧ ∀ a, InHom H a → InHom H' (t.app a) := by
  induction ht with
  | @side H H' α v₀ u _ hdu V ι hι h hs₀ e =>
    have hd0 := dim_side_of_isRewritable u hdu ι hι h
    have hsa : ∀ {a : PastingDiagram X}, InHom H a → (a.boundary H.k α).Equiv v₀ :=
      fun ha => (ha.side α).trans hs₀.symm
    refine ⟨⟨fun a a' ha e => sidePaste_equiv (hsa ha) e,
      fun a ha => dim_sidePaste (hsa ha) (by have := ha.lt_dim; omega),
      fun a ha n hkn _ β => equiv_boundary_sidePaste_of_lt (hsa ha) hdu hkn β,
      fun y z n hp hyz hkn => exists_sidePaste_paste hp (hsa hyz) hdu hkn⟩, fun a ha => ?_⟩
    have hs : (a.boundary H.k α).Equiv v₀ := hsa ha
    have hs0 : (v₀.boundary H.k α).Equiv v₀ := equiv_boundary_dim v₀ hd0.le α
    refine (InHom.of_side α ?_ ?_ ?_).congr e
    · change H.k < (sidePaste α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h a).dim
      rw [dim_sidePaste hs (by rw [hdu]; exact ha.lt_dim)]
      exact ha.lt_dim
    · rw [PdHom.side_setSide_self]
      exact equiv_boundary_sidePaste_of_side u.isRound hdu hι hs hs0 ha.lt_dim.le hd0.ge
    · rw [PdHom.side_setSide_not]
      exact (equiv_boundary_not_sidePaste hs).trans (ha.side (!α))
  | id e =>
    exact ⟨⟨fun _ _ _ e => e, fun _ _ => rfl, fun _ _ _ _ _ _ => .refl _,
      fun _ _ _ hp _ _ => ⟨hp, .refl _⟩⟩, fun a ha => ha.congr e⟩
  | comp ht₁ _ ih₁ ih₂ =>
    obtain ⟨ihF, hM⟩ := ih₁
    obtain ⟨ihG, hM'⟩ := ih₂
    have hk := ht₁.k_eq
    refine ⟨⟨fun a a' ha e => ihG.equiv _ _ (hM a ha) (ihF.equiv a a' ha e),
      fun a ha => (ihG.dim_eq _ (hM a ha)).trans (ihF.dim_eq a ha),
      fun a ha n hkn hna β => ?_, fun y z n hp hyz hkn => ?_⟩, fun a ha => hM' _ (hM a ha)⟩
    · have hFa := hM a ha
      have hd := ihF.dim_eq a ha
      exact (ihG.boundary _ hFa (by omega) (by omega) β).trans
        (ihG.equiv _ _ (hFa.boundary (by omega) (by omega) β) (ihF.boundary a ha hkn hna β))
    · obtain ⟨hp', e⟩ := ihF.paste y z hp hyz hkn
      have hF := (hM _ hyz).of_equiv e
      obtain ⟨hp'', e'⟩ := ihG.paste _ _ hp' hF (by omega)
      exact ⟨hp'', (ihG.equiv _ _ (hM _ hyz) e).trans e'⟩
  | @promote k H H₁ H' t _ hk _ _ _ e ih =>
    have L := ih.1
    have hkH : k < H.k := by omega
    have pr : ∀ {a}, InHom H a → InHom (H.boundary k) a := fun ha => ha.promote hkH
    refine ⟨⟨fun a a' ha e => L.equiv a a' (pr ha) e, fun a ha => L.dim_eq a (pr ha),
      fun a ha n hkn hna β => L.boundary a (pr ha) (hkH.trans hkn) hna β,
      fun y z n hp hyz hkn => L.paste y z hp (pr hyz) (hkH.trans hkn)⟩, fun a ha => ?_⟩
    have hp' := pr ha
    refine InHom.congr ⟨by rw [L.dim_eq a hp']; exact ha.lt_dim, ?_, ?_⟩ e
    · exact (L.boundary a hp' hkH ha.lt_dim false).trans
        (L.equiv _ _ (hp'.boundary hkH ha.lt_dim false) ha.source)
    · exact (L.boundary a hp' hkH ha.lt_dim true).trans
        (L.equiv _ _ (hp'.boundary hkH ha.lt_dim true) ha.target)

theorem ctxLaws {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') : CtxLaws H t.app :=
  ht.ctxLaws_and_mapsInto.1

theorem mapsInto {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') :
    ∀ a, InHom H a → InHom H' (t.app a) :=
  ht.ctxLaws_and_mapsInto.2

theorem mono {B : Set (RoundPastingDiagram X)} (hAB : A ⊆ B) {q : Prop} (hpq : p → q)
    {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') : Typed B q H t H' := by
  induction ht with
  | side α u hu hdu ι hι h hs e => exact .side α u (hAB hu) hdu ι hι h hs e
  | id e => exact .id e
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | promote hp hk hv hw _ e ih => exact .promote (hpq hp) hk hv hw ih e

theorem congr_codomain {H H' H'' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H')
    (e : H'.Equiv H'') : Typed A p H t H'' := by
  induction ht generalizing H'' with
  | side α u hu hdu ι hι h hs e' => exact .side α u hu hdu ι hι h hs (e'.trans e)
  | id e' => exact .id (e'.trans e)
  | comp ht₁ _ _ ih₂ => exact .comp ht₁ (ih₂ e)
  | promote hp hk hv hw ht e' _ => exact .promote hp hk hv hw ht (e'.trans e)

theorem congr_domain {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') :
    ∀ {H₁ : PdHom X}, H.Equiv H₁ → Typed A p H₁ t H' := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs e' =>
    rintro ⟨k₁, v₁, w₁⟩ e
    obtain rfl : H.k = k₁ := e.k_eq
    exact .side (H := ⟨H.k, v₁, w₁⟩) α u hu hdu ι hι h (hs.trans (e.side α))
      ((e.symm.setSide α (.refl _)).trans e')
  | id e' => exact fun e => .id (e.symm.trans e')
  | comp _ ht₂ ih₁ _ => exact fun e => .comp (ih₁ e) ht₂
  | @promote k H H₁ H' t hp hk hv hw ht e' ih =>
    intro H₂ e
    have eb : (H.boundary k).Equiv (H₂.boundary k) :=
      ⟨rfl, e.equiv_v.boundary k false, e.equiv_w.boundary k true⟩
    exact .promote hp (e.k_eq ▸ hk) ((hv.of_equiv e.equiv_v).congr eb)
      ((hw.of_equiv e.equiv_w).congr eb) (ih eb)
      ((⟨e.k_eq.symm, app_equiv t e.equiv_v.symm, app_equiv t e.equiv_w.symm⟩ :
        PdHom.Equiv ⟨H₂.k, t.app H₂.v, t.app H₂.w⟩ ⟨H.k, t.app H.v, t.app H.w⟩).trans e')

theorem app_mapTo (f : X ⟶ Y) {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') :
    ∀ a, InHom H a → ((t.mapTo f).app (a.mapTo f)).Equiv ((t.app a).mapTo f) := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs =>
    exact fun a ha => sidePaste_mapTo α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h f
      ((ha.side α).trans hs.symm)
  | id => exact fun a _ => .refl _
  | @comp H H' H'' s t ht₁ _ ih₁ ih₂ =>
    exact fun a ha => (CtxExpr.app_equiv (s.mapTo f) (ih₁ a ha)).trans
      (ih₂ _ (ht₁.mapsInto a ha))
  | promote _ hk _ _ _ _ ih => exact fun a ha => ih a (ha.promote (by omega))

theorem mapTo (f : X ⟶ Y) {B : Set (RoundPastingDiagram Y)} (hA : ∀ u ∈ A, u.mapTo f ∈ B)
    {H H' : PdHom X} {t : CtxExpr X} (ht : Typed A p H t H') :
    Typed B p (H.mapTo f) (t.mapTo f) (H'.mapTo f) := by
  induction ht with
  | @side H H' α v₀ u hu hdu V ι hι h hs e =>
    have hs0 : (v₀.boundary H.k α).Equiv v₀ :=
      equiv_boundary_dim v₀ (dim_side_of_isRewritable u hdu ι hι h).le α
    have eb := (sidePaste_mapTo α u.toPastingDiagram H.k ι hι.isSubmoleculeOf h f hs0).boundary
      H.k α
    rw [PastingDiagram.boundary_mapTo] at eb
    have es := e.side α
    have en := e.side (!α)
    rw [PdHom.side_setSide_self] at es
    rw [PdHom.side_setSide_not] at en
    refine .side (H := H.mapTo f) (H' := H'.mapTo f) α (u.mapTo f) (hA u hu) hdu (ι.mapTo f)
      hι (h.mapTo_boundary f) (by rw [PdHom.side_mapTo]; exact hs.mapTo f)
      (.of_side α e.k_eq ?_ ?_)
    · rw [PdHom.side_setSide_self, PdHom.side_mapTo]
      exact eb.trans (es.mapTo f)
    · rw [PdHom.side_setSide_not, PdHom.side_mapTo, PdHom.side_mapTo]
      exact en.mapTo f
  | id e => exact .id (e.mapTo f)
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | @promote k H H₁ H' t hp hk hv hw ht e ih =>
    rw [← PdHom.boundary_mapTo] at ih
    exact .promote hp hk (by rw [PdHom.boundary_mapTo]; exact hv.mapTo f)
      (by rw [PdHom.boundary_mapTo]; exact hw.mapTo f) ih
      ((⟨rfl, ht.app_mapTo f H.v hv, ht.app_mapTo f H.w hw⟩ :
        PdHom.Equiv ⟨H.k, (t.mapTo f).app (H.v.mapTo f), (t.mapTo f).app (H.w.mapTo f)⟩
          ⟨H.k, (t.app H.v).mapTo f, (t.app H.w).mapTo f⟩).trans (e.mapTo f))

end Typed

end CtxExpr

end Atoms.Diagrammatic
