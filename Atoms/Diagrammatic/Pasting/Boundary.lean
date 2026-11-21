import Atoms.Molecule.Layering.Ordering
import Atoms.Diagrammatic.Pasting.Within

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X : DiagSet.{u}}

theorem isRound_boundary_iff (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    (u.boundary k α).IsRound ↔ u.shape.ogp.IsRound (u.shape.ogp.boundary ⊤ k α) := by
  rw [boundary_eq_restrictTo]
  exact isRound_restrictTo_iff u _

theorem isRound_boundary_of_isRound {u : PastingDiagram X} (hu : u.IsRound) (k : ℕ) (α : Bool) :
    (u.boundary k α).IsRound :=
  u.shape.isRound_boundary hu k α

theorem isRound_boundary_true_of_false (d : PastingDiagram X) {k : ℕ}
    (hd : d.dim = k + 1) (h : (d.boundary k false).IsRound) : (d.boundary k true).IsRound := by
  rw [isRound_boundary_iff] at h ⊢
  exact isRound_boundary_true_of_isRound_boundary_false d.shape.isMolecule
    (by rw [LowerSet.krullDim_top, d.shape.krullDim_eq_dimension]; exact_mod_cast hd) h

theorem Within.isRewritableSubmolecule_of_equiv_boundary {a u : PastingDiagram X} {n : ℕ}
    {γ : Bool} {ι : Within a u} (hι : u.shape.ogp.IsSubmoleculeOf ι.image ⊤)
    {e : RoundPastingDiagram X} (h : a.Equiv (e.boundary n γ)) (he : e.dim = n + 1)
    (hu : u.dim = n) : u.shape.ogp.IsRewritableSubmolecule ι.image ⊤ :=
  ι.isRewritableSubmolecule_image_iff.2
    ⟨hι, (Equiv.isRound_iff h).2 (isRound_boundary_of_isRound e.isRound n γ), by
      rw [dim_eq_of_equiv h, dim_boundary e.toPastingDiagram (by omega) γ, hu]⟩

section PasteAt

variable (P Q : PastingDiagram X) (k : ℕ) (α : Bool) {V : PastingDiagram X}
  (ι : Within V (Q.boundary k α))
  (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
  (h : (P.boundary k (!α)).Equiv V)

theorem dim_pasteAtBoundary : (pasteAtBoundary P Q k α ι hι h).dim = max P.dim Q.dim := by
  have e := congrArg (fun S : LowerSet (pasteAtShape P Q k α ι hι h).ogp => krullDim S)
    (map_pasteAtInl_sup_map_pasteAtInr P Q k α ι hι h)
  simp only [LowerSet.krullDim_sup, krullDim_map, LowerSet.krullDim_top,
    MoleculeShape.krullDim_eq_dimension] at e
  have e' : (pasteAtShape P Q k α ι hι h).dimension = max P.shape.dimension Q.shape.dimension := by
    rcases le_total P.shape.dimension Q.shape.dimension with hle | hle
    · rw [max_eq_right (by exact_mod_cast hle)] at e
      rw [max_eq_right hle]
      exact_mod_cast e.symm
    · rw [max_eq_left (by exact_mod_cast hle)] at e
      rw [max_eq_left hle]
      exact_mod_cast e.symm
  exact e'

theorem image_occurrence_pasteAt :
    (ι.trans ((Within.boundary Q k α).trans
      (Within.pasteAtInr P Q k α ι hι h))).image =
      (Within.pasteAtInl P Q k α ι hι h).image ⊓ (Within.pasteAtInr P Q k α ι hι h).image := by
  change OGP.map (ι.emb ≫ Q.shape.boundaryIncl k α ≫ glue.inr (pasteAtIso P Q k α ι h) ≫
      (pasteAtShapeIso P Q k α ι hι h).hom) ⊤ =
    OGP.map (glue.inl (pasteAtIso P Q k α ι h) ≫ (pasteAtShapeIso P Q k α ι hι h).hom) ⊤ ⊓
      OGP.map (glue.inr (pasteAtIso P Q k α ι h) ≫ (pasteAtShapeIso P Q k α ι hι h).hom) ⊤
  simp only [map_comp]
  rw [← map_inf, ← map_inl_boundary_pastingAt, map_inl_boundary_eq_map_inr_pastingAt,
    ← map_comp ι.emb]
  rfl

theorem equiv_boundary_not_pasteAtBoundary :
    ((pasteAtBoundary P Q k α ι hι h).boundary k (!α)).Equiv (Q.boundary k (!α)) :=
  Within.equiv_of_image_eq (Within.boundary _ k (!α))
    ((Within.boundary Q k (!α)).trans (Within.pasteAtInr P Q k α ι hι h)) (by
      rw [Within.image_boundary, Within.image_boundary_trans]
      exact (Within.isPastingAtIn_pasteAt P Q k α ι hι h).boundary_not)

end PasteAt

theorem isRound_pasteAtBoundary (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (h : (P.boundary k (!α)).Equiv V) (hQ : Q.IsRound) (hd : P.dim = Q.dim) (hk : Q.dim - 1 = k) :
    (pasteAtBoundary P Q k α ι hι h).IsRound := by
  subst hk
  change (pasteAtShape P Q (Q.dim - 1) α ι hι h).ogp.IsRound ⊤
  rcases Nat.eq_zero_or_pos Q.dim with h0 | hpos
  · have hdim : (pasteAtShape P Q (Q.dim - 1) α ι hι h).dimension =
        max P.shape.dimension Q.shape.dimension := dim_pasteAtBoundary P Q (Q.dim - 1) α ι hι h
    have hdim' : (pasteAtShape P Q (Q.dim - 1) α ι hι h).dimension = 0 := by
      rw [hdim]
      rw [dim_def, dim_def] at hd
      rw [dim_def] at h0
      omega
    refine isRound_of_krullDim_le_zero ?_
    rw [LowerSet.krullDim_top, MoleculeShape.krullDim_eq_dimension, hdim']
    rfl
  · have hQr : Q.shape.ogp.IsRound ⊤ := hQ
    have hn : krullDim Q.shape.ogp = ((Q.dim - 1 : ℕ) : WithBot ℕ∞) + 1 := by
      rw [Q.shape.krullDim_eq_dimension, ← dim_def]
      exact_mod_cast (Nat.sub_add_cancel hpos).symm
    have hPQ : krullDim P.shape.ogp = krullDim Q.shape.ogp := by
      rw [P.shape.krullDim_eq_dimension, Q.shape.krullDim_eq_dimension]
      exact_mod_cast hd
    exact (isRound_top_iff_of_iso (pasteAtShapeIso P Q (Q.dim - 1) α ι hι h)).2
      (isRound_pastingAt (isSubmoleculeOf_bdryOccurrence Q (Q.dim - 1) α ι hι)
        (pasteAtIso P Q (Q.dim - 1) α ι h) P.shape.isMolecule Q.shape.isMolecule hQr hn hPQ)

section SubstituteUniv

variable {u v : PastingDiagram X} (ι : Within v u)
  (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
  (w : RoundPastingDiagram X) (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)

theorem image_substitute_of_image_eq_univ (h : ι.image = ⊤) :
    (Within.substitute ι hι w hw).image = ⊤ := by
  refine top_unique fun z _ => ?_
  have hz : z ∈ OGP.map (substInlEmb u ι hι w hw) ⊤ ⊔ OGP.map (substInrEmb u ι hι w hw) ⊤ := by
    rw [map_substInlEmb_sup_map_substInrEmb u ι hι w hw]
    exact LowerSet.mem_top
  rcases LowerSet.mem_sup_iff.1 hz with ⟨a, -, rfl⟩ | hz
  · have hU : (OGP.map ι.emb ⊤ : LowerSet u.shape.ogp) = ⊤ := h
    have hint (x : u.shape.ogp) (hx : x ∉ u.shape.ogp.interior (OGP.map ι.emb ⊤)) :
        x ∈ u.shape.ogp.bdryFull (OGP.map ι.emb ⊤) := by
      rw [hU] at hx ⊢
      have hb := mem_properBoundary_of_notMem_interior LowerSet.mem_top hx
      rwa [u.shape.isMolecule.properBoundary_eq_bdryFull] at hb
    have ha : a.1 ∈ u.shape.ogp.bdryFull (OGP.map ι.emb ⊤) := hint a.1 a.2.2
    let φ := bdryIsoAlong ι.emb (substBdryIso u ι hι w hw)
    refine ⟨(φ.hom ⟨a.1, ha⟩).1, LowerSet.mem_top, ?_⟩
    exact congrArg (substShapeIso u ι hι w hw).hom
      (Subtype.ext (glue.inl_eq_inr_iff.2 ⟨ha, rfl⟩).symm)
  · exact hz

theorem equiv_substitute_of_image_eq_univ (h : ι.image = ⊤) :
    (u.substitute ι hι w hw).Equiv w.toPastingDiagram :=
  (Within.equiv_of_image_eq (Within.substitute ι hι w hw) (Within.refl _)
    (by rw [image_substitute_of_image_eq_univ ι hι w hw h, Within.image_refl])).symm

end SubstituteUniv

theorem equiv_mk_iff {S : MoleculeShape} {m m' : realize.obj S.rdc ⟶ X} :
    (⟨S, m⟩ : PastingDiagram X).Equiv ⟨S, m'⟩ ↔ m = m' := by
  refine ⟨fun ⟨ψ, hψ⟩ => ?_, fun h => h ▸ .refl _⟩
  have : Subsingleton (S.ogp ≅ S.ogp) := S.isMolecule.subsingleton_iso
  obtain rfl : ψ = Iso.refl _ := Subsingleton.elim _ _
  have he : realize.map (RDCpx.isoOfIso (P := S.rdc) (Q := S.rdc) (Iso.refl S.ogp)).hom = 𝟙 _ :=
    (congrArg realize.map (by ext; rfl :
      (RDCpx.isoOfIso (P := S.rdc) (Q := S.rdc) (Iso.refl S.ogp)).hom = 𝟙 _)).trans
      (realize.map_id _)
  exact ((Category.id_comp _).symm.trans ((congrArg (· ≫ m') he.symm).trans hψ)).symm

theorem ofCell_equiv_ofCell_iff {U : Atom} {x y : diagram X U} :
    (ofCell x).Equiv (ofCell y) ↔ x = y :=
  equiv_mk_iff.trans ⟨ofCell_map_injective, fun h => h ▸ rfl⟩

private theorem eq_of_equiv_pasteAlong {S T : MoleculeShape} {k : ℕ}
    {m m' : realize.obj S.rdc ⟶ X} {n n' : realize.obj T.rdc ⟶ X}
    (ψ ψ' : (S.boundary k true).ogp ≅ (T.boundary k false).ogp)
    (hab : realize.map (RDCpx.isoOfIso (P := (S.boundary k true).rdc)
      (Q := (T.boundary k false).rdc) ψ).hom ≫ ((⟨T, n⟩ : PastingDiagram X).boundary k false).map =
        ((⟨S, m⟩ : PastingDiagram X).boundary k true).map)
    (hab' : realize.map (RDCpx.isoOfIso (P := (S.boundary k true).rdc)
      (Q := (T.boundary k false).rdc) ψ').hom ≫
        ((⟨T, n'⟩ : PastingDiagram X).boundary k false).map =
          ((⟨S, m'⟩ : PastingDiagram X).boundary k true).map)
    (e : (pasteAlong ⟨S, m⟩ ⟨T, n⟩ k ψ hab).Equiv (pasteAlong ⟨S, m'⟩ ⟨T, n'⟩ k ψ' hab')) :
    m = m' ∧ n = n' := by
  have : Subsingleton ((S.boundary k true).ogp ≅ (T.boundary k false).ogp) :=
    (S.boundary k true).isMolecule.subsingleton_iso
  have hψ : ψ = ψ' := Subsingleton.elim _ _
  subst hψ
  have hm := equiv_mk_iff.1 e
  exact ⟨(ofInclusion_pasteInl_map ⟨S, m⟩ ⟨T, n⟩ k ψ hab).symm.trans
      ((congrArg (realize.map (RDCpx.ofInclusion (P := S.rdc) (Q := (S.paste T k ψ).rdc)
        (pasteInl ⟨S, m⟩ ⟨T, n⟩ k ψ)) ≫ ·) hm).trans
        (ofInclusion_pasteInl_map ⟨S, m'⟩ ⟨T, n'⟩ k ψ hab')),
    (ofInclusion_pasteInr_map ⟨S, m⟩ ⟨T, n⟩ k ψ hab).symm.trans
      ((congrArg (realize.map (RDCpx.ofInclusion (P := T.rdc) (Q := (S.paste T k ψ).rdc)
        (pasteInr ⟨S, m⟩ ⟨T, n⟩ k ψ)) ≫ ·) hm).trans
        (ofInclusion_pasteInr_map ⟨S, m'⟩ ⟨T, n'⟩ k ψ hab'))⟩

theorem eq_of_equiv_paste {S T : MoleculeShape} {k : ℕ}
    {m m' : realize.obj S.rdc ⟶ X} {n n' : realize.obj T.rdc ⟶ X}
    (h : (⟨S, m⟩ : PastingDiagram X).Pastable ⟨T, n⟩ k)
    (h' : (⟨S, m'⟩ : PastingDiagram X).Pastable ⟨T, n'⟩ k)
    (e : ((⟨S, m⟩ : PastingDiagram X).paste ⟨T, n⟩ k h).Equiv
      ((⟨S, m'⟩ : PastingDiagram X).paste ⟨T, n'⟩ k h')) :
    m = m' ∧ n = n' :=
  eq_of_equiv_pasteAlong _ _ h.1.map_comm h'.1.map_comm e

end Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

open PastingDiagram

variable {X : DiagSet.{u}}

theorem parallel_boundary {P : PastingDiagram X} (hP : P.IsRound) {k : ℕ} (hdP : P.dim = k + 1)
    (α β : Bool) :
    Parallel ⟨P.boundary k α, isRound_boundary_of_isRound hP k α⟩
      ⟨P.boundary k β, isRound_boundary_of_isRound hP k β⟩ := by
  have hd : ∀ γ, (P.boundary k γ).dim = k := fun γ => dim_boundary P (by omega) γ
  change (P.boundary k α).dim = (P.boundary k β).dim ∧ ((P.boundary k α).dim = 0 ∨ ∀ γ : Bool,
    ((P.boundary k α).boundary ((P.boundary k α).dim - 1) γ).Equiv
      ((P.boundary k β).boundary ((P.boundary k β).dim - 1) γ))
  refine ⟨(hd α).trans (hd β).symm, ?_⟩
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exact Or.inl ((hd α).trans hk0)
  · refine Or.inr fun γ => ?_
    rw [hd α, hd β]
    exact (equiv_boundary_boundary P (by omega) α γ).trans
      ((equiv_boundary_boundary P (by omega) β γ).symm)

theorem Parallel.symm {u v : RoundPastingDiagram X} (h : Parallel u v) : Parallel v u := by
  obtain ⟨hd, h2⟩ := h
  refine ⟨hd.symm, ?_⟩
  rcases h2 with h0 | hb
  · exact Or.inl (hd ▸ h0)
  · exact Or.inr fun β => (hb β).symm

theorem Parallel.trans {u v w : RoundPastingDiagram X} (h₁ : Parallel u v)
    (h₂ : Parallel v w) : Parallel u w := by
  obtain ⟨hd₁, h₁⟩ := h₁
  obtain ⟨hd₂, h₂⟩ := h₂
  refine ⟨hd₁.trans hd₂, ?_⟩
  rcases h₁ with h0 | hb₁
  · exact Or.inl h0
  · rcases h₂ with h0 | hb₂
    · exact Or.inl (hd₁.trans h0)
    · exact Or.inr fun β => (hb₁ β).trans (hb₂ β)

theorem Parallel.of_equiv_left {u u' v : RoundPastingDiagram X} (h : Parallel u v)
    (e : u'.Equiv u.toPastingDiagram) : Parallel u' v := by
  obtain ⟨hd, h2⟩ := h
  have hd' : u'.dim = u.dim := dim_eq_of_equiv e
  refine ⟨hd'.trans hd, ?_⟩
  rcases h2 with h0 | hb
  · exact Or.inl (hd'.trans h0)
  · refine Or.inr fun β => ?_
    rw [hd']
    exact (e.boundary (u.dim - 1) β).trans (hb β)

theorem Parallel.of_equiv_right {u v v' : RoundPastingDiagram X} (h : Parallel u v)
    (e : v'.Equiv v.toPastingDiagram) : Parallel u v' :=
  (h.symm.of_equiv_left e).symm

theorem inter_eq_boundary_pasteAt_of_image_univ (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hsub : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hι : ι.image = ⊤) (h : (P.boundary k (!α)).Equiv V) :
    (Within.pasteAtInl P Q k α ι hsub h).image ⊓ (Within.pasteAtInr P Q k α ι hsub h).image =
      (pasteAtBoundary P Q k α ι hsub h).shape.ogp.boundary
        (Within.pasteAtInr P Q k α ι hsub h).image k α := by
  rw [← image_occurrence_pasteAt, Within.image_trans, hι]
  exact Within.image_boundary_trans _ _ _

theorem equiv_paste_pasteAtBoundary (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hsub : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hι : ι.image = ⊤) (h : (P.boundary k (!α)).Equiv V)
    (hp : (cond α Q P).Pastable (cond α P Q) k) :
    ((cond α Q P).paste (cond α P Q) k hp).Equiv (pasteAtBoundary P Q k α ι hsub h) := by
  have hc := Within.isPastingAtIn_pasteAt P Q k α ι hsub h
  have he := inter_eq_boundary_pasteAt_of_image_univ P Q k α ι hsub hι h
  exact (equiv_paste_cond_of_within α (Within.pasteAtInr P Q k α ι hsub h)
    (Within.pasteAtInl P Q k α ι hsub h) (hc.isPastingIn_of_inf_eq he)
    (pasteAtBoundary P Q k α ι hsub h).shape.isMolecule hp).trans (equiv_restrictTo_univ _)

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem Within.image_ofEquiv_trans {a b m : PastingDiagram X} (e : b.Equiv a) (w : Within a m) :
    ((Within.ofEquiv e).trans w).image = w.image := by
  rw [Within.image_trans, Within.image_ofEquiv]
  rfl

theorem PastingDiagram.Within.image_eq_univ_of_equiv {a m : PastingDiagram X} (w : Within a m)
    (h : a.Equiv m) : w.image = ⊤ := by
  have hb := (Fintype.bijective_iff_injective_and_card w.emb).2
    ⟨IsInclusion.injective, Fintype.card_congr (orderIsoOfIso h.iso).toEquiv⟩
  refine top_unique fun y _ => ?_
  obtain ⟨x, rfl⟩ := hb.2 y
  exact ⟨x, LowerSet.mem_top, rfl⟩

theorem equiv_paste_assoc {x y z : PastingDiagram X} {n : ℕ} (h₁ : x.Pastable y n)
    (h₂ : (x.paste y n h₁).Pastable z n) :
    ∃ (h₃ : y.Pastable z n) (h₄ : x.Pastable (y.paste z n h₃) n),
      ((x.paste y n h₁).paste z n h₂).Equiv (x.paste (y.paste z n h₃) n h₄) := by
  classical
  let wA := Within.pasteInl (x.paste y n h₁) z n h₂
  let wZ := Within.pasteInr (x.paste y n h₁) z n h₂
  let wX := (Within.pasteInl x y n h₁).trans wA
  let wY := (Within.pasteInr x y n h₁).trans wA
  have hA : ((x.paste y n h₁).paste z n h₂).shape.ogp.IsPastingIn n wX.image wY.image
      wA.image := by
    rw [Within.image_trans, Within.image_trans]
    exact (isPastingIn_map_iff wA.emb n _ _ _).2 (Within.isPastingIn_paste x y n h₁)
  have hB := Within.isPastingIn_paste _ z n h₂
  have hp₁ := hA.isPastingIn_right_sup hB
  have hp₂ := hA.assoc hB
  have hYZ := hp₁.isMoleculeIn wY.isMoleculeIn_image wZ.isMoleculeIn_image
  have hdx : n < x.dim := (lt_min_iff.1 h₁.2).1
  have hdy : n < y.dim := (lt_min_iff.1 h₁.2).2
  have hdz : n < z.dim := (lt_min_iff.1 h₂.2).2
  have h₃ : y.Pastable z n := pastable_of_isPastingIn wY wZ hp₁ (lt_min hdy hdz)
  let wYZ := (Within.ofEquiv (equiv_paste_of_within wY wZ hp₁ hYZ h₃)).trans
    (Within.restrictTo _ hYZ)
  have hwYZ : wYZ.image = wY.image ⊔ wZ.image := by
    rw [Within.image_ofEquiv_trans, Within.image_restrictTo]
  have hp₂' : ((x.paste y n h₁).paste z n h₂).shape.ogp.IsPastingIn n wX.image wYZ.image ⊤ := by
    rw [hwYZ]; exact hp₂
  have h₄ : x.Pastable (y.paste z n h₃) n := pastable_of_isPastingIn wX wYZ hp₂' (lt_min hdx (by
    rw [dim_paste]; exact lt_max_of_lt_left hdy))
  exact ⟨h₃, h₄, PastingDiagram.Equiv.trans
    ((equiv_restrictTo_univ _).symm)
    ((equiv_paste_of_within wX wYZ hp₂' _ h₄).symm)⟩

theorem isRound_paste_of_round (γ : Bool) {u x : PastingDiagram X} {n : ℕ}
    (h : (cond γ x u).Pastable (cond γ u x) n) (hu : u.IsRound) (hdu : u.dim = n + 1)
    (hdx : x.dim ≤ n + 1) : ((cond γ x u).paste (cond γ u x) n h).IsRound := by
  have hd : ((cond γ x u).paste (cond γ u x) n h).dim = n + 1 := by
    rw [dim_paste_cond]; omega
  have hd' : krullDim (⊤ : LowerSet ((cond γ x u).paste (cond γ u x) n h).shape.ogp) =
      ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [LowerSet.krullDim_top, MoleculeShape.krullDim_eq_dimension]
    exact_mod_cast hd
  obtain ⟨wx, hpst⟩ := Within.exists_isPastingIn_pasteIn γ h
  exact hpst.isRound_cond γ wx.isMoleculeIn_image.isGlobular
    (Within.pasteIn γ h).isMoleculeIn_image.isGlobular ((Within.pasteIn γ h).round_image_iff.2 hu)
    (by rw [Within.krullDim_image, hdu]; push_cast; rfl) hd'

theorem isRound_paste_of_dim (u v : RoundPastingDiagram X) {k : ℕ} (hu : u.dim = k + 1)
    (hv : v.dim = k + 1) (hp : u.Pastable v.toPastingDiagram k) :
    (u.paste v.toPastingDiagram k hp).IsRound :=
  isRound_paste_of_round false (u := u.toPastingDiagram) (x := v.toPastingDiagram) hp u.isRound
    hu hv.le

theorem isRound_paste (u v : RoundPastingDiagram X) (hd : u.dim = v.dim)
    (hp : u.Pastable v.toPastingDiagram (u.dim - 1)) :
    (u.paste v.toPastingDiagram (u.dim - 1) hp).IsRound := by
  have hpos : 0 < u.dim := by have := hp.2; omega
  exact isRound_paste_of_dim u v (by omega) (by omega) hp

theorem Parallel.equiv_boundary_pred {u v : RoundPastingDiagram X} (h : Parallel u v) {k : ℕ}
    (hd : u.dim = k + 1) (α : Bool) :
    (u.toPastingDiagram.boundary k α).Equiv (v.toPastingDiagram.boundary k α) := by
  obtain ⟨hdv, h2⟩ := h
  rcases h2 with h0 | hb
  · exact absurd (hd.symm.trans h0) (Nat.succ_ne_zero k)
  · have e := hb α
    have hu : u.dim - 1 = k := by omega
    have hv' : v.dim - 1 = k := by omega
    rw [hu, hv'] at e
    exact e

noncomputable def PastingDiagram.pasteOr (x y : PastingDiagram X) (n : ℕ) : PastingDiagram X :=
  open Classical in if h : x.Pastable y n then x.paste y n h else x

theorem PastingDiagram.pasteOr_of {x y : PastingDiagram X} {n : ℕ} (h : x.Pastable y n) :
    x.pasteOr y n = x.paste y n h :=
  dif_pos h

theorem PastingDiagram.Pastable.paste_side {x y z : PastingDiagram X} {n : ℕ} {α : Bool}
    (h₁ : (cond α x y).Pastable (cond α y x) n)
    (h₂ : (cond α y z).Pastable (cond α z y) n) :
    (cond α ((cond α x y).paste (cond α y x) n h₁) z).Pastable
      (cond α z ((cond α x y).paste (cond α y x) n h₁)) n := by
  have hb : (((cond α x y).paste (cond α y x) n h₁).boundary n α).Equiv
      (y.boundary n α) := by cases α <;> exact equiv_boundary_paste h₁ _
  have hd : n < min y.dim z.dim := by
    cases α <;> simpa only [cond_false, cond_true, min_comm] using h₂.2
  refine Pastable.of_side α (hb.trans h₂.side) ?_ (lt_min_iff.1 hd).2
  rw [dim_paste_cond]
  exact lt_of_lt_of_le (lt_min_iff.1 hd).1 (le_max_right _ _)

theorem PastingDiagram.Pastable.paste_left {x y z : PastingDiagram X} {n : ℕ} (h₁ : x.Pastable y n)
    (h₂ : y.Pastable z n) : (x.paste y n h₁).Pastable z n :=
  Pastable.paste_side (α := true) h₁ h₂

theorem PastingDiagram.Pastable.paste_right {x y z : PastingDiagram X} {n : ℕ} (h₁ : x.Pastable y n)
    (h₂ : y.Pastable z n) : x.Pastable (y.paste z n h₂) n :=
  Pastable.paste_side (α := false) h₂ h₁

theorem PastingDiagram.paste_eq_pasteOr {u v u' v' : PastingDiagram X} {i j : ℕ}
    (p : u.Pastable v i) (hi : i = j) (hu : u = u') (hv : v = v') :
    u.paste v i p = u'.pasteOr v' j := by
  subst hi hu hv
  exact (PastingDiagram.pasteOr_of p).symm

end Atoms.Diagrammatic
