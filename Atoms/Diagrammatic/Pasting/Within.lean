import Atoms.Diagrammatic.Pasting.Substitution
import Atoms.Molecule.Pasting.AtSubmoleculeSubstitution

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic.PastingDiagram

variable {X : DiagSet.{u}}

section Occurrence

variable {m Q : PastingDiagram X}

theorem isSubmoleculeOf_comap_occurrence (wQ : Within Q m) (k : ℕ) (α : Bool)
    {V : LowerSet m.shape.ogp}
    (hV : m.shape.ogp.IsSubmoleculeOf V (m.shape.ogp.boundary wQ.image k α)) :
    (Q.boundary k α).shape.ogp.IsSubmoleculeOf
      (comap ((Within.boundary Q k α).trans wQ).emb V) ⊤ := by
  refine (isSubmoleculeOf_map_iff ((Within.boundary Q k α).trans wQ).emb).1 ?_
  rw [map_comap_of_le _ (hV.le.trans (wQ.image_boundary_trans k α).ge)]
  rwa [← Within.image, wQ.image_boundary_trans k α]

variable (wQ : Within Q m) (k : ℕ) (α : Bool) {V : LowerSet m.shape.ogp} [DecidablePred (· ∈ V)]
  (hV : m.shape.ogp.IsSubmoleculeOf V (m.shape.ogp.boundary wQ.image k α))

def occurrenceDiagram : PastingDiagram X :=
  (Q.boundary k α).restrictTo (isSubmoleculeOf_comap_occurrence wQ k α hV).isMoleculeIn

def occurrence : Within (occurrenceDiagram wQ k α hV) (Q.boundary k α) :=
  Within.restrictTo (Q.boundary k α) (isSubmoleculeOf_comap_occurrence wQ k α hV).isMoleculeIn

theorem isSubmoleculeOf_image_occurrence :
    (Q.boundary k α).shape.ogp.IsSubmoleculeOf (occurrence wQ k α hV).image ⊤ :=
  Within.isSubmoleculeOf_image_restrictTo _ (isSubmoleculeOf_comap_occurrence wQ k α hV)

theorem image_occurrence_eq_comap :
    (occurrence wQ k α hV).image = comap ((Within.boundary Q k α).trans wQ).emb V :=
  Within.image_restrictTo _ _

theorem image_occurrence :
    ((occurrence wQ k α hV).trans ((Within.boundary Q k α).trans wQ)).image = V := by
  rw [Within.image_trans, image_occurrence_eq_comap]
  exact map_comap_of_le _ (hV.le.trans (wQ.image_boundary_trans k α).ge)

theorem equiv_occurrence_of_image_eq {P : PastingDiagram X} (wP : Within P m)
    (hPV : wP.image = V) : P.Equiv (occurrenceDiagram wQ k α hV) :=
  Within.equiv_of_image_eq wP
    ((occurrence wQ k α hV).trans ((Within.boundary Q k α).trans wQ))
    (hPV.trans (image_occurrence wQ k α hV).symm)

theorem equiv_boundary_occurrence {P : PastingDiagram X} (wP : Within P m)
    (hPV : m.shape.ogp.boundary wP.image k (!α) = V) :
    (P.boundary k (!α)).Equiv (occurrenceDiagram wQ k α hV) :=
  Within.equiv_of_image_eq ((Within.boundary P k (!α)).trans wP)
    ((occurrence wQ k α hV).trans ((Within.boundary Q k α).trans wQ))
    ((wP.image_boundary_trans k (!α)).trans (hPV.trans (image_occurrence wQ k α hV).symm))

end Occurrence

section Paste

variable {m P Q : PastingDiagram X} (wP : Within P m) (wQ : Within Q m) {k : ℕ}
  {R : LowerSet m.shape.ogp}

theorem equiv_boundary_of_isPastingIn (hp : m.shape.ogp.IsPastingIn k wP.image wQ.image R) :
    (P.boundary k true).Equiv (Q.boundary k false) :=
  Within.equiv_of_image_eq ((Within.boundary P k true).trans wP)
    ((Within.boundary Q k false).trans wQ)
    ((wP.image_boundary_trans k true).trans (hp.inf_eq_output.symm.trans
      (hp.inf_eq_input.trans (wQ.image_boundary_trans k false).symm)))

theorem pastable_of_isPastingIn (hp : m.shape.ogp.IsPastingIn k wP.image wQ.image R)
    (hk : k < min P.dim Q.dim) : P.Pastable Q k :=
  ⟨equiv_boundary_of_isPastingIn wP wQ hp, hk⟩

theorem equiv_paste_of_within (hp : m.shape.ogp.IsPastingIn k wP.image wQ.image R)
    [DecidablePred (· ∈ R)] (hR : IsMoleculeIn m.shape.ogp R) (h : P.Pastable Q k) :
    (P.paste Q k h).Equiv (m.restrictTo hR) :=
  equiv_paste_of_emb P Q (m.restrictTo hR) k h m.map (m.shape.subIncl hR) wP.emb wQ.emb rfl
    wP.comm wQ.comm (by rw [m.shape.map_subIncl_top hR]; exact hp)

noncomputable def Within.pasteInl (P Q : PastingDiagram X) (k : ℕ) (h : P.Pastable Q k) :
    Within P (P.paste Q k h) :=
  ⟨PastingDiagram.pasteInl P Q k h.1.iso, ofInclusion_pasteInl_map P Q k h.1.iso h.1.map_comm⟩

noncomputable def Within.pasteInr (P Q : PastingDiagram X) (k : ℕ) (h : P.Pastable Q k) :
    Within Q (P.paste Q k h) :=
  ⟨PastingDiagram.pasteInr P Q k h.1.iso, ofInclusion_pasteInr_map P Q k h.1.iso h.1.map_comm⟩

theorem Within.isPastingIn_paste (P Q : PastingDiagram X) (k : ℕ) (h : P.Pastable Q k) :
    (P.paste Q k h).shape.ogp.IsPastingIn k (Within.pasteInl P Q k h).image
      (Within.pasteInr P Q k h).image ⊤ :=
  PastingDiagram.isPastingIn_paste P Q k h.1.iso

noncomputable def Within.pasteIn (α : Bool) {c h : PastingDiagram X}
    (hp : (_root_.cond α c h).Pastable (_root_.cond α h c) k) :
    Within h ((_root_.cond α c h).paste (_root_.cond α h c) k hp) :=
  match α, hp with
  | true, hp => Within.pasteInr c h k hp
  | false, hp => Within.pasteInl h c k hp

theorem Within.exists_isPastingIn_pasteIn (α : Bool) {c h : PastingDiagram X}
    (hp : (_root_.cond α c h).Pastable (_root_.cond α h c) k) :
    ∃ wc : Within c ((_root_.cond α c h).paste (_root_.cond α h c) k hp),
      ((_root_.cond α c h).paste (_root_.cond α h c) k hp).shape.ogp.IsPastingIn k
        (_root_.cond α wc.image (Within.pasteIn α hp).image)
        (_root_.cond α (Within.pasteIn α hp).image wc.image) ⊤ := by
  cases α <;> exact ⟨_, Within.isPastingIn_paste _ _ k hp⟩

theorem pastable_cond_of_isPastingIn (α : Bool) {c h : PastingDiagram X} (wc : Within c m)
    (wh : Within h m)
    (hp : m.shape.ogp.IsPastingIn k (cond α wc.image wh.image) (cond α wh.image wc.image) R)
    (hc : k < c.dim) (hh : k < h.dim) : (cond α c h).Pastable (cond α h c) k := by
  obtain ⟨-, h₁, h₂⟩ := (isPastingIn_cond_iff α).1 hp
  refine Pastable.of_side α (Within.equiv_of_image_eq ((Within.boundary c k α).trans wc)
    ((Within.boundary h k (!α)).trans wh) ?_) hc hh
  rw [Within.image_boundary_trans, Within.image_boundary_trans, ← h₂, h₁]

theorem equiv_paste_cond_of_within (α : Bool) {c h : PastingDiagram X} (wc : Within c m)
    (wh : Within h m)
    (hp : m.shape.ogp.IsPastingIn k (cond α wc.image wh.image) (cond α wh.image wc.image) R)
    [DecidablePred (· ∈ R)] (hR : IsMoleculeIn m.shape.ogp R)
    (hpst : (cond α c h).Pastable (cond α h c) k) :
    ((cond α c h).paste (cond α h c) k hpst).Equiv (m.restrictTo hR) :=
  equiv_paste_of_within (Within.cond α wc wh) (Within.cond α wh wc)
    (by rwa [Within.image_cond, Within.image_cond]) hR hpst

end Paste

section PasteAt

variable {m P Q : PastingDiagram X} (wP : Within P m) (wQ : Within Q m) {k : ℕ} {α : Bool}
  {R : LowerSet m.shape.ogp}

theorem mem_boundary_of_apply_mem_of_isPastingAtIn
    (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R) {x : P.shape.ogp}
    (hx : wP.emb x ∈ wQ.image) : x ∈ P.shape.ogp.boundary ⊤ k (!α) := by
  have hmem := hc.mem_boundary_of_mem (wP.mem_image_apply x) hx
  rwa [wP.boundary_image, apply_mem_map_iff] at hmem

variable [DecidablePred (· ∈ R)]

theorem exists_iso_pasteAtBoundary_of_within
    (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R) {V : PastingDiagram X}
    (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (h : (P.boundary k (!α)).Equiv V) :
    ∃ Θ : (m.restrictTo hc.isMoleculeIn).shape.ogp ≅ (pasteAtShape P Q k α ι hι h).ogp,
      realize.map (RDCpx.isoOfIso (P := (m.restrictTo hc.isMoleculeIn).shape.rdc)
        (Q := (pasteAtShape P Q k α ι hι h).rdc) Θ).hom ≫
          (pasteAtBoundary P Q k α ι hι h).map = (m.restrictTo hc.isMoleculeIn).map ∧
      (∀ x, m.shape.subIncl hc.isMoleculeIn (Θ.inv (pasteAtInl P Q k α ι hι h x)) = wP.emb x) ∧
      (∀ y, m.shape.subIncl hc.isMoleculeIn (Θ.inv (pasteAtInr P Q k α ι hι h y)) = wQ.emb y) := by
  let e := P.shape.subIso (P.shape.isMolecule.boundary k (!α))
  have hiso (x : P.shape.ogp) (hx : x ∈ P.shape.ogp.boundary ⊤ k (!α)) :
      wQ.emb ((pasteAtIso P Q k α ι h).hom ⟨x, hx⟩).1 = wP.emb x := by
    have e2 := (P.boundary k (!α)).shape.isMolecule.eqOn_of_map_eq
      (P.shape.boundaryIncl k (!α) ≫ wP.emb)
      (h.iso.hom ≫ ι.emb ≫ Q.shape.boundaryIncl k α ≫ wQ.emb :
        (P.boundary k (!α)).shape.ogp ⟶ m.shape.ogp)
      (by
        rw [map_comp, P.shape.map_boundaryIncl_top, ← wP.boundary_image, ← hc.inf_eq,
          ← hmeet, map_comp, map_top_of_isIso]
        rfl)
      (LowerSet.mem_top (a := e.hom ⟨x, hx⟩))
    let z : P.shape.ogp.restrict (P.shape.ogp.boundary ⊤ k (!α)) := ⟨x, hx⟩
    have e3 : P.shape.boundaryIncl k (!α) (e.hom z) = x :=
      congrArg Subtype.val (e.hom_inv_id_apply z)
    exact e2.symm.trans (congrArg wP.emb e3)
  have hglue (x : P.shape.ogp) (y : Q.shape.ogp) :
      pasteAtInl P Q k α ι hι h x = pasteAtInr P Q k α ι hι h y ↔
        ∃ hx : x ∈ P.shape.ogp.boundary ⊤ k (!α),
          ((pasteAtIso P Q k α ι h).hom ⟨x, hx⟩).1 = y :=
    (IsInclusion.injective (f := (pasteAtShapeIso P Q k α ι hι h).hom)).eq_iff.trans
      glue.inl_eq_inr_iff
  have hcond (x : P.shape.ogp) (y : Q.shape.ogp) : wP.emb x = wQ.emb y ↔
      pasteAtInl P Q k α ι hι h x = pasteAtInr P Q k α ι hι h y := by
    refine Iff.trans ?_ (hglue x y).symm
    constructor
    · intro hxy
      have hx : x ∈ P.shape.ogp.boundary ⊤ k (!α) :=
        mem_boundary_of_apply_mem_of_isPastingAtIn wP wQ hc (by
          rw [hxy]; exact wQ.mem_image_apply y)
      exact ⟨hx, IsInclusion.injective (f := wQ.emb) ((hiso x hx).trans hxy)⟩
    · rintro ⟨hx, rfl⟩
      exact (hiso x hx).symm
  exact exists_iso_of_covers (a := m.restrictTo hc.isMoleculeIn)
    (b := pasteAtBoundary P Q k α ι hι h) (C := m.shape.rdc) (P := P.shape.rdc)
    (Q := Q.shape.rdc) m.map (m.shape.subIncl hc.isMoleculeIn) rfl wP.emb wQ.emb
    (hc.eq_sup.symm.trans (m.shape.map_subIncl_top hc.isMoleculeIn).symm)
    (pasteAtInl P Q k α ι hι h) (pasteAtInr P Q k α ι hι h)
    (map_pasteAtInl_sup_map_pasteAtInr P Q k α ι hι h)
    hcond (wP.comm.trans (ofInclusion_pasteAtInl_map P Q k α ι hι h).symm)
    (wQ.comm.trans (ofInclusion_pasteAtInr_map P Q k α ι hι h).symm)

theorem equiv_pasteAtBoundary_of_within (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (h : (P.boundary k (!α)).Equiv V) :
    (pasteAtBoundary P Q k α ι hι h).Equiv (m.restrictTo hc.isMoleculeIn) :=
  (exists_iso_pasteAtBoundary_of_within wP wQ hc ι hι hmeet h).elim fun Θ hΘ =>
    PastingDiagram.Equiv.symm ⟨Θ, hΘ.1⟩

theorem apply_iso_pasteAtInl_and_pasteAtInr_of_within
    (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (hR : IsMoleculeIn m.shape.ogp R) (h : (P.boundary k (!α)).Equiv V)
    (e : (pasteAtBoundary P Q k α ι hι h).Equiv (m.restrictTo hR)) :
    (∀ x, m.shape.subIncl hR (e.iso.hom (pasteAtInl P Q k α ι hι h x)) = wP.emb x) ∧
      ∀ y, m.shape.subIncl hR (e.iso.hom (pasteAtInr P Q k α ι hι h y)) = wQ.emb y := by
  obtain ⟨Θ, -, hl, hr⟩ := exists_iso_pasteAtBoundary_of_within wP wQ hc ι hι hmeet h
  have : e.iso = Θ.symm := (pasteAtShape P Q k α ι hι h).isMolecule.subsingleton_iso.elim _ _
  rw [this]
  exact ⟨hl, hr⟩

omit [DecidablePred (· ∈ R)] in
noncomputable def Within.pasteAtInl (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (h : (P.boundary k (!α)).Equiv V) :
    Within P (pasteAtBoundary P Q k α ι hι h) :=
  ⟨PastingDiagram.pasteAtInl P Q k α ι hι h, ofInclusion_pasteAtInl_map P Q k α ι hι h⟩

omit [DecidablePred (· ∈ R)] in
noncomputable def Within.pasteAtInr (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (h : (P.boundary k (!α)).Equiv V) :
    Within Q (pasteAtBoundary P Q k α ι hι h) :=
  ⟨PastingDiagram.pasteAtInr P Q k α ι hι h, ofInclusion_pasteAtInr_map P Q k α ι hι h⟩

omit [DecidablePred (· ∈ R)] in
private theorem isPastingAtIn_sup (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R) :
    m.shape.ogp.IsPastingAtIn k α wP.image wQ.image (wP.image ⊔ wQ.image) :=
  { hc with eq_sup := rfl }

omit [DecidablePred (· ∈ R)] in
noncomputable def Within.pasteAtOfWithin (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (h : (P.boundary k (!α)).Equiv V) :
    Within (pasteAtBoundary P Q k α ι hι h) m :=
  (Within.ofEquiv (equiv_pasteAtBoundary_of_within wP wQ (isPastingAtIn_sup wP wQ hc) ι hι hmeet
    h)).trans
    (Within.restrictTo m (isPastingAtIn_sup wP wQ hc).isMoleculeIn)

omit [DecidablePred (· ∈ R)] in
theorem Within.image_pasteAtOfWithin (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (h : (P.boundary k (!α)).Equiv V) :
    (Within.pasteAtOfWithin wP wQ hc ι hι hmeet h).image = R := by
  rw [Within.pasteAtOfWithin, Within.image_trans, Within.image_ofEquiv]
  exact (Within.image_restrictTo m _).trans hc.eq_sup.symm

omit [DecidablePred (· ∈ R)] in
theorem Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin
    (hc : m.shape.ogp.IsPastingAtIn k α wP.image wQ.image R)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (hmeet : (ι.trans ((Within.boundary Q k α).trans wQ)).image = wP.image ⊓ wQ.image)
    (h : (P.boundary k (!α)).Equiv V) :
    (Within.pasteAtInl P Q k α ι hι h).trans (Within.pasteAtOfWithin wP wQ hc ι hι hmeet h) =
      wP ∧
    (Within.pasteAtInr P Q k α ι hι h).trans (Within.pasteAtOfWithin wP wQ hc ι hι hmeet h) =
      wQ := by
  have he := apply_iso_pasteAtInl_and_pasteAtInr_of_within wP wQ (isPastingAtIn_sup wP wQ hc) ι
    hι hmeet (isPastingAtIn_sup wP wQ hc).isMoleculeIn h
    (equiv_pasteAtBoundary_of_within wP wQ (isPastingAtIn_sup wP wQ hc) ι hι hmeet h)
  exact ⟨Within.ext_of_image_eq _ _ (congrArg (fun f => OGP.map f ⊤) (by ext x; exact he.1 x)),
    Within.ext_of_image_eq _ _ (congrArg (fun f => OGP.map f ⊤) (by ext y; exact he.2 y))⟩

omit [DecidablePred (· ∈ R)] in
theorem Within.isPastingAtIn_pasteAt (P Q : PastingDiagram X) (k : ℕ) (α : Bool)
    {V : PastingDiagram X} (ι : Within V (Q.boundary k α))
    (hι : (Q.boundary k α).shape.ogp.IsSubmoleculeOf ι.image ⊤)
    (h : (P.boundary k (!α)).Equiv V) :
    (pasteAtBoundary P Q k α ι hι h).shape.ogp.IsPastingAtIn k α
      (Within.pasteAtInl P Q k α ι hι h).image (Within.pasteAtInr P Q k α ι hι h).image ⊤ := by
  have hc := (isPastingAtIn_pastingAt (pasteAtIso P Q k α ι h)
    (isSubmoleculeOf_bdryOccurrence Q k α ι hι) P.shape.isMolecule Q.shape.isMolecule).map
      (pasteAtShapeIso P Q k α ι hι h).hom
  have e1 : (Within.pasteAtInl P Q k α ι hι h).image = OGP.map
      (pasteAtShapeIso P Q k α ι hι h).hom (OGP.map (glue.inl (pasteAtIso P Q k α ι h)) ⊤) :=
    map_comp (glue.inl (pasteAtIso P Q k α ι h)) (pasteAtShapeIso P Q k α ι hι h).hom ⊤
  have e2 : (Within.pasteAtInr P Q k α ι hι h).image = OGP.map
      (pasteAtShapeIso P Q k α ι hι h).hom (OGP.map (glue.inr (pasteAtIso P Q k α ι h)) ⊤) :=
    map_comp (glue.inr (pasteAtIso P Q k α ι h)) (pasteAtShapeIso P Q k α ι hι h).hom ⊤
  have e3 : (⊤ : LowerSet (pasteAtBoundary P Q k α ι hι h).shape.ogp) =
      OGP.map (pasteAtShapeIso P Q k α ι hι h).hom ⊤ := (map_top_of_isIso _).symm
  rw [e1, e2, e3]
  exact hc

end PasteAt

section Substitute

variable {m u v : PastingDiagram X} (ι : Within v u)
  (hι : u.shape.ogp.IsRewritableSubmolecule (OGP.map ι.emb ⊤) ⊤)
  (w : RoundPastingDiagram X) (hw : Parallel ⟨v, ι.round_image_iff.1 hι.isRound⟩ w)
  (wU : Within u m)
  (wW : Within w.toPastingDiagram m) {R : LowerSet m.shape.ogp} [DecidablePred (· ∈ R)]

theorem exists_iso_substitute_of_within
    (hs : m.shape.ogp.IsSubstitutionIn wU.image (ι.trans wU).image wW.image R)
    (hR : IsMoleculeIn m.shape.ogp R) :
    ∃ Θ : (m.restrictTo hR).shape.ogp ≅ (substShape u ι hι w hw).ogp,
      realize.map (RDCpx.isoOfIso (P := (m.restrictTo hR).shape.rdc)
        (Q := (substShape u ι hι w hw).rdc) Θ).hom ≫ (u.substitute ι hι w hw).map =
          (m.restrictTo hR).map ∧
      (∀ x, m.shape.subIncl hR (Θ.inv (substInlEmb u ι hι w hw x)) = wU.emb x.1) ∧
      (∀ y, m.shape.subIncl hR (Θ.inv (substInrEmb u ι hι w hw y)) = wW.emb y) := by
  rw [Within.image_trans] at hs
  simp only [Within.image] at hs
  let φ := bdryIsoAlong ι.emb (substBdryIso u ι hι w hw)
  let i : (substInlRDC u ι hι).obj.toOGP ⟶ m.shape.ogp := incl hι.complement ≫ wU.emb
  have hi_img : OGP.map i ⊤ = hs.rewritable.complement := by
    rw [map_comp, map_incl_top]
    exact IsSubmoleculeOf.map_complement wU.emb hι.isSubmoleculeOf hι.krullDim_eq
      hs.rewritable.isSubmoleculeOf hs.rewritable.krullDim_eq
  have hrig (x : v.shape.ogp.restrict (v.shape.ogp.bdryFull ⊤)) :
      wW.emb ((substBdryIso u ι hι w hw).hom x).1 = wU.emb (ι.emb x.1) :=
    apply_eq_of_isSigned_of_map_bdry_eq v.shape.isMolecule (ι.emb ≫ wU.emb) wW.emb
      (fun β => by rw [map_bdry, map_bdry, map_comp]; exact (hs.bdry_eq β).symm)
      (isSigned_substBdryIso u ι hι w hw) x
  have hrig' (z : u.shape.ogp) (hz : z ∈ u.shape.ogp.bdryFull (OGP.map ι.emb ⊤)) :
      wW.emb (φ.hom ⟨z, hz⟩).1 = wU.emb z := by
    have hz' : z ∈ OGP.map ι.emb (v.shape.ogp.bdryFull ⊤) := by rwa [map_bdryFull]
    obtain ⟨x₀, hx₀, rfl⟩ := hz'
    rw [bdryIsoAlong_apply ι.emb (substBdryIso u ι hι w hw) ⟨x₀, hx₀⟩ hz]
    exact hrig ⟨x₀, hx₀⟩
  have hglue (x : u.shape.ogp.restrict hι.complement) (y : w.shape.ogp) :
      substInlEmb u ι hι w hw x = substInrEmb u ι hι w hw y ↔
        ∃ hx : x.1 ∈ u.shape.ogp.bdryFull (OGP.map ι.emb ⊤), (φ.hom ⟨x.1, hx⟩).1 = y :=
    (IsInclusion.injective (f := (substShapeIso u ι hι w hw).hom)).eq_iff.trans
      (Subtype.ext_iff.trans glue.inl_eq_inr_iff)
  have hamb (x : u.shape.ogp.restrict hι.complement) (y : w.shape.ogp) :
      i x = wW.emb y ↔
        ∃ hx : x.1 ∈ u.shape.ogp.bdryFull (OGP.map ι.emb ⊤), (φ.hom ⟨x.1, hx⟩).1 = y := by
    change wU.emb x.1 = wW.emb y ↔ _
    constructor
    · intro hxy
      have hmem : wU.emb x.1 ∈ m.shape.ogp.bdryFull (OGP.map wU.emb (OGP.map ι.emb ⊤)) := by
        rw [← hs.inf_eq]
        exact ⟨wU.mem_image_apply x.1, by rw [hxy]; exact wW.mem_image_apply y⟩
      rw [← map_bdryFull, apply_mem_map_iff] at hmem
      exact ⟨hmem, IsInclusion.injective (f := wW.emb) ((hrig' x.1 hmem).trans hxy)⟩
    · rintro ⟨hx, rfl⟩
      exact (hrig' x.1 hx).symm
  have hR' : OGP.map i ⊤ ⊔ OGP.map wW.emb ⊤ = OGP.map (m.shape.subIncl hR) ⊤ := by
    rw [hi_img, m.shape.map_subIncl_top hR]
    exact hs.eq_sup.symm
  have hcomm : realize.map (RDCpx.ofInclusion (P := substInlRDC u ι hι) (Q := m.shape.rdc) i) ≫
      m.map = realize.map (RDCpx.ofInclusion (P := substInlRDC u ι hι)
        (Q := (substShape u ι hι w hw).rdc) (substInlEmb u ι hι w hw)) ≫
          (u.substitute ι hι w hw).map := by
    have E : RDCpx.ofInclusion (P := substInlRDC u ι hι) (Q := m.shape.rdc) i =
        u.shape.rdc.restrictIncl hι.complement ≫
          RDCpx.ofInclusion (P := u.shape.rdc) (Q := m.shape.rdc) wU.emb := by
      ext x
      rfl
    rw [E]
    exact (realize.map_comp_assoc _ _ _).trans
      ((congrArg (realize.map (u.shape.rdc.restrictIncl hι.complement) ≫ ·) wU.comm).trans
        (ofInclusion_coverDesc_left (R := (substShape u ι hι w hw).rdc)
          (U := substInlRDC u ι hι) (V := w.shape.rdc) _ _
          (map_substInlEmb_sup_map_substInrEmb u ι hι w hw) _ _ _).symm)
  exact exists_iso_of_covers (a := m.restrictTo hR) (b := u.substitute ι hι w hw)
    (C := m.shape.rdc) (P := substInlRDC u ι hι) (Q := w.shape.rdc) m.map
    (m.shape.subIncl hR) rfl i wW.emb hR' (substInlEmb u ι hι w hw) (substInrEmb u ι hι w hw)
    (map_substInlEmb_sup_map_substInrEmb u ι hι w hw)
    (fun x y => (hamb x y).trans (hglue x y).symm) hcomm
    (wW.comm.trans (ofInclusion_coverDesc_right (R := (substShape u ι hι w hw).rdc)
      (U := substInlRDC u ι hι) (V := w.shape.rdc) _ _
      (map_substInlEmb_sup_map_substInrEmb u ι hι w hw) _ _ _).symm)

theorem equiv_substitute_of_within
    (hs : m.shape.ogp.IsSubstitutionIn wU.image (ι.trans wU).image wW.image R)
    (hR : IsMoleculeIn m.shape.ogp R) : (u.substitute ι hι w hw).Equiv (m.restrictTo hR) :=
  (exists_iso_substitute_of_within ι hι w hw wU wW hs hR).elim fun Θ hΘ =>
    PastingDiagram.Equiv.symm ⟨Θ, hΘ.1⟩

theorem apply_iso_substInlEmb_and_substInrEmb_of_within
    (hs : m.shape.ogp.IsSubstitutionIn wU.image (ι.trans wU).image wW.image R)
    (hR : IsMoleculeIn m.shape.ogp R) (e : (u.substitute ι hι w hw).Equiv (m.restrictTo hR)) :
    (∀ x, m.shape.subIncl hR (e.iso.hom (substInlEmb u ι hι w hw x)) = wU.emb x.1) ∧
      ∀ y, m.shape.subIncl hR (e.iso.hom (substInrEmb u ι hι w hw y)) = wW.emb y := by
  obtain ⟨Θ, -, hl, hr⟩ := exists_iso_substitute_of_within ι hι w hw wU wW hs hR
  have : e.iso = Θ.symm := (substShape u ι hι w hw).isMolecule.subsingleton_iso.elim _ _
  rw [this]
  exact ⟨hl, hr⟩

end Substitute

end Atoms.Diagrammatic.PastingDiagram
