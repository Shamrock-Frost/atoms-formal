import Atoms.Diagrammatic.Pasting.CylinderDiagram
import Atoms.Diagrammatic.Context.Pasting
import Atoms.Diagrammatic.Equivalence.Degenerate

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section Occ

variable (k : ℕ) (α : Bool) {z V : PastingDiagram X} (ι : Within V z)

open Classical in
noncomputable def occSet (c : PastingDiagram X) : LowerSet c.shape.ogp :=
  if hs : (c.boundary k α).Equiv z then
    (ι.trans (sideWithin (Within.refl c) k α hs)).image
  else ⊥

variable {k α ι}

theorem occSet_of {c : PastingDiagram X} (hs : (c.boundary k α).Equiv z) :
    occSet k α ι c = (ι.trans (sideWithin (Within.refl c) k α hs)).image :=
  dif_pos hs

theorem image_occSet {c m : PastingDiagram X} (w : Within c m)
    (hb : m.shape.ogp.boundary w.image k α = m.shape.ogp.boundary ⊤ k α)
    (hs : (c.boundary k α).Equiv z) (hs' : (m.boundary k α).Equiv z) :
    OGP.map w.emb (occSet k α ι c) = occSet k α ι m := by
  have hW : (sideWithin (Within.refl c) k α hs).trans w = sideWithin (Within.refl m) k α hs' :=
    Within.ext_of_image_eq _ _ (by
      rw [Within.image_trans, image_sideWithin, image_sideWithin, Within.image_refl,
        Within.image_refl, ← hb, w.boundary_image])
  rw [occSet_of hs, occSet_of hs', ← hW, Within.image_trans_assoc]

theorem isSubmoleculeOf_occSet (hι : z.shape.ogp.IsSubmoleculeOf ι.image ⊤)
    {c : PastingDiagram X} (hs : (c.boundary k α).Equiv z) :
    c.shape.ogp.IsSubmoleculeOf (occSet k α ι c) (c.shape.ogp.boundary ⊤ k α) := by
  have e : OGP.map (sideWithin (Within.refl c) k α hs).emb ⊤ = c.shape.ogp.boundary ⊤ k α := by
    rw [← Within.image, image_sideWithin, Within.image_refl]
  rw [occSet_of hs, Within.image_trans, ← e]
  exact (isSubmoleculeOf_map_iff _).2 hι

theorem krullDim_occSet {c : PastingDiagram X} (hs : (c.boundary k α).Equiv z) :
    krullDim (occSet k α ι c) = V.dim := by
  rw [occSet_of hs, Within.krullDim_image]

end Occ

structure CylSpec (X : DiagSet.{u}) where
  k : ℕ
  α : Bool
  z : PastingDiagram X
  occ : Option ((V : PastingDiagram X) ×
    {ι : Within V z // z.shape.ogp.IsRewritableSubmolecule ι.image ⊤})

namespace CylSpec

variable (d : CylSpec X)

noncomputable def V (c : PastingDiagram X) : LowerSet c.shape.ogp :=
  d.occ.elim ⊥ fun ι => occSet d.k d.α ι.2.1 c

def K (c : PastingDiagram X) : LowerSet c.shape.ogp :=
  lowerClosure
    ((c.shape.ogp.boundaryFull ⊤ d.k : Set c.shape.ogp) \ c.shape.ogp.interior (d.V c))

noncomputable instance decidableMemK (c : PastingDiagram X) : DecidablePred (· ∈ d.K c) :=
  Classical.decPred _

noncomputable def fam (c : PastingDiagram X) : PastingDiagram X :=
  cylDiagram c (d.K c)

variable {d}

theorem fam_def (c : PastingDiagram X) : d.fam c = cylDiagram c (d.K c) :=
  rfl

theorem K_le_boundaryFull (c : PastingDiagram X) : d.K c ≤ c.shape.ogp.boundaryFull ⊤ d.k :=
  lowerClosure_le.2 Set.sdiff_subset

theorem K_of_none (hι : d.occ = none) (c : PastingDiagram X) :
    d.K c = c.shape.ogp.boundaryFull ⊤ d.k := by
  have hV : d.V c = ⊥ := by rw [V, hι]; rfl
  rw [K, hV, OGP.interior, LowerSet.coe_bot, Set.empty_sdiff, Set.sdiff_empty]
  exact LowerSet.lowerClosure _

structure Fits (d : CylSpec X) (c : PastingDiagram X) : Prop where
  isRound : c.IsRound
  lt_dim : d.k < c.dim
  side : (c.boundary d.k d.α).Equiv d.z

theorem Fits.of_equiv {c c' : PastingDiagram X} (h : d.Fits c) (e : c.Equiv c') : d.Fits c' :=
  ⟨e.isRound_iff.1 h.isRound, dim_eq_of_equiv e ▸ h.lt_dim,
    (e.boundary _ _).symm.trans h.side⟩

theorem Fits.boundary {c : PastingDiagram X} (h : d.Fits c) {n : ℕ} (hkn : d.k < n)
    (hn : n ≤ c.dim) (γ : Bool) : d.Fits (c.boundary n γ) :=
  ⟨isRound_boundary_of_isRound h.isRound n γ, (dim_boundary c hn γ).symm ▸ hkn,
    (equiv_boundary_boundary c hkn γ d.α).trans h.side⟩

theorem Fits.lt_krullDim_top {c : PastingDiagram X} (h : d.Fits c) :
    (d.k : WithBot ℕ∞) < krullDim (⊤ : LowerSet c.shape.ogp) := by
  rw [LowerSet.krullDim_top, c.shape.krullDim_eq_dimension]
  exact_mod_cast h.lt_dim

theorem Fits.occ {c : PastingDiagram X} (h : d.Fits c)
    {ι : (V : PastingDiagram X) ×
      {ι : Within V d.z // d.z.shape.ogp.IsRewritableSubmolecule ι.image ⊤}}
    (hι : d.occ = some ι) :
    d.V c = occSet d.k d.α ι.2.1 c ∧
      c.shape.ogp.IsSubmoleculeOf (d.V c) (c.shape.ogp.boundary ⊤ d.k d.α) ∧
      krullDim (d.V c) = krullDim (c.shape.ogp.boundary ⊤ d.k d.α) := by
  have hV : d.V c = occSet d.k d.α ι.2.1 c := by rw [V, hι]; rfl
  refine ⟨hV, hV ▸ isSubmoleculeOf_occSet ι.2.2.isSubmoleculeOf h.side, ?_⟩
  rw [hV, krullDim_occSet h.side, IsMoleculeIn.krullDim_boundary c.shape.isMolecule
      h.lt_krullDim_top.le d.α, (ι.2.1.isRewritableSubmolecule_image_iff.1 ι.2.2).2.2,
    ← dim_eq_of_equiv h.side, dim_boundary c h.lt_dim.le d.α]

theorem Fits.coe_K {c : PastingDiagram X} (h : d.Fits c) :
    (d.K c : Set c.shape.ogp) =
      (c.shape.ogp.boundaryFull ⊤ d.k : Set c.shape.ogp) \ c.shape.ogp.interior (d.V c) := by
  refine IsLowerSet.lowerClosure ?_
  rcases hι : d.occ with _ | ι
  · have hV : d.V c = ⊥ := by rw [V, hι]; rfl
    rw [hV, OGP.interior, LowerSet.coe_bot, Set.empty_sdiff, Set.sdiff_empty]
    exact (c.shape.ogp.boundaryFull ⊤ d.k).lower
  · obtain ⟨-, hV, hdV⟩ := h.occ hι
    exact (hV.hornSetAt c.shape.isMolecule (c.shape.isRound_iff.1 h.isRound) h.lt_krullDim_top
      hdV).lower

theorem Fits.K_eq_hornSetAt {c : PastingDiagram X} (h : d.Fits c)
    {ι : (V : PastingDiagram X) ×
      {ι : Within V d.z // d.z.shape.ogp.IsRewritableSubmolecule ι.image ⊤}}
    (hι : d.occ = some ι) :
    d.K c = (h.occ hι).2.1.hornSetAt c.shape.isMolecule (c.shape.isRound_iff.1 h.isRound)
      h.lt_krullDim_top (h.occ hι).2.2 :=
  SetLike.coe_injective h.coe_K

theorem Fits.boundary_le_K {c : PastingDiagram X} (h : d.Fits c) {β : Bool}
    (hβ : β = d.α ∨ d.occ = none) : c.shape.ogp.boundary ⊤ d.k (!β) ≤ d.K c := by
  rcases hι : d.occ with _ | ι
  · rw [K_of_none hι c]
    exact boundary_le_boundaryFull _ _ _
  · rcases hβ with rfl | hn
    · rw [h.K_eq_hornSetAt hι]
      exact IsSubmoleculeOf.boundary_not_le_hornSetAt _ _ _ _ _
    · exact absurd (hι.symm.trans hn) (Option.some_ne_none _)

theorem Fits.K_le_bdryFull {c : PastingDiagram X} (h : d.Fits c) :
    d.K c ≤ c.shape.ogp.bdryFull ⊤ :=
  (K_le_boundaryFull c).trans ((boundaryFull_le_properBoundary h.lt_krullDim_top).trans
    (IsMoleculeIn.properBoundary_eq_bdryFull c.shape.isMolecule).le)

theorem Fits.fam_spec {c : PastingDiagram X} (h : d.Fits c) :
    ∃ hr : (d.fam c).IsRound, (⟨d.fam c, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
      (d.fam c).dim = c.dim + 1 :=
  ⟨isRound_cylDiagram c (d.K c) h.isRound h.K_le_bdryFull,
    mem_equivalences_of_isDegenerate _ (isDegenerate_cylDiagram c (d.K c) h.K_le_bdryFull),
    dim_cylDiagram c (d.K c) h.K_le_bdryFull⟩

theorem mem_K_iff_of_within {c m : PastingDiagram X} (w : Within c m) (hc : d.Fits c)
    (hm : d.Fits m)
    (hb : ∀ γ, m.shape.ogp.boundary w.image d.k γ = m.shape.ogp.boundary ⊤ d.k γ)
    (y : c.shape.ogp) : w.emb y ∈ d.K m ↔ y ∈ d.K c := by
  have hV : OGP.map w.emb (d.V c) = d.V m := by
    rcases hι : d.occ with _ | ι
    · rw [V, V, hι]
      exact map_bot w.emb
    · rw [V, V, hι]
      exact image_occSet w (hb d.α) hc.side hm.side
  have hF : m.shape.ogp.boundaryFull ⊤ d.k = OGP.map w.emb (c.shape.ogp.boundaryFull ⊤ d.k) := by
    rw [map_boundaryFull, ← Within.image, boundaryFull, boundaryFull, hb true, hb false]
  rw [← SetLike.mem_coe, hm.coe_K, ← SetLike.mem_coe, hc.coe_K, ← hV, ← image_interior, hF,
    Set.mem_sdiff, Set.mem_sdiff, SetLike.mem_coe, SetLike.mem_coe, apply_mem_map_iff,
    IsInclusion.injective.mem_set_image]

theorem exists_within_fam {c m : PastingDiagram X} (w : Within c m) (hc : d.Fits c)
    (hm : d.Fits m)
    (hb : ∀ γ, m.shape.ogp.boundary w.image d.k γ = m.shape.ogp.boundary ⊤ d.k γ) :
    ∃ w' : Within (d.fam c) (cylDiagram m (d.K m)),
      w'.image = cylImage m (PartialCylinder.over (d.K m) w.image) :=
  ⟨Within.cyl m (d.K m) w (mem_K_iff_of_within w hc hm hb), image_cyl m (d.K m) w _⟩

theorem exists_within_fam_boundary {c : PastingDiagram X} (hc : d.Fits c) {n : ℕ}
    (hkn : d.k < n) (hn : n ≤ c.dim) (γ : Bool) :
    ∃ w' : Within (d.fam (c.boundary n γ)) (cylDiagram c (d.K c)),
      w'.image = cylImage c (PartialCylinder.over (d.K c) (c.shape.ogp.boundary ⊤ n γ)) := by
  have hb : ∀ γ', c.shape.ogp.boundary (Within.boundary c n γ).image d.k γ' =
      c.shape.ogp.boundary ⊤ d.k γ' := fun γ' => by
    rw [Within.image_boundary]
    exact IsMoleculeIn.isGlobular c.shape.isMolecule d.k n hkn γ' γ
  have h := exists_within_fam (Within.boundary c n γ) (hc.boundary hkn hn γ) hc hb
  rwa [Within.image_boundary] at h

theorem fam_equiv {c c' : PastingDiagram X} (hc : d.Fits c) (e : c.Equiv c') :
    (d.fam c).Equiv (d.fam c') := by
  have hc' := hc.of_equiv e
  have hb : ∀ γ, c'.shape.ogp.boundary (Within.ofEquiv e).image d.k γ =
      c'.shape.ogp.boundary ⊤ d.k γ := fun γ => by rw [Within.image_ofEquiv]
  obtain ⟨w, hw⟩ := exists_within_fam (Within.ofEquiv e) hc hc' hb
  rw [Within.image_ofEquiv, PartialCylinder.over_top, cylImage_top] at hw
  exact PastingDiagram.Equiv.trans
    (w.equiv_restrictTo_of_eq hw (cylDiagram c' (d.K c')).shape.isMolecule)
    (equiv_restrictTo_univ _)

def AtEnd (d : CylSpec X) (β : Bool) (n : ℕ) (c x : PastingDiagram X) : Prop :=
  ∃ w : Within x (cylDiagram c (d.K c)),
    w.image = cylImage c (PartialCylinder.endSet (d.K c) β n)

theorem AtEnd.of_equiv {β : Bool} {n : ℕ} {c x x' : PastingDiagram X} (h : d.AtEnd β n c x)
    (e : x'.Equiv x) : d.AtEnd β n c x' := by
  obtain ⟨w, hw⟩ := h
  exact ⟨(Within.ofEquiv e).trans w, (Within.image_ofEquiv_trans e w).trans hw⟩

theorem Fits.atEnd_self {c : PastingDiagram X} (h : d.Fits c) {β : Bool}
    (hβ : β = d.α ∨ d.occ = none) : d.AtEnd β d.k c c :=
  ⟨Within.cylCopy c (d.K c) β, by
    rw [image_cylCopy, PartialCylinder.endSet_eq_copy (h.boundary_le_K hβ)]⟩

theorem Fits.endStatement {c : PastingDiagram X} (h : d.Fits c) (β : Bool) {n : ℕ}
    (hn : d.k ≤ n) : PartialCylinder.EndStatement (d.K c) β n := by
  refine PartialCylinder.endStatement_of_le c.shape.isMolecule ?_ n hn
  by_cases hβ : β = d.α ∨ d.occ = none
  · exact PartialCylinder.endStatement_of_subset c.shape.isMolecule (h.boundary_le_K hβ)
  · push Not at hβ
    obtain ⟨ι, hι⟩ := Option.ne_none_iff_exists'.1 hβ.2
    obtain rfl : β = !d.α := by
      cases β <;> cases hα : d.α <;> simp_all only [ne_eq, not_true_eq_false, reduceCtorEq,
          not_false_eq_true, and_true, Bool.false_eq_true, and_self, Bool.not_true,
          Bool.true_eq_false, Bool.not_false]
    rw [h.K_eq_hornSetAt hι]
    exact PartialCylinder.endStatement_not c.shape.isMolecule _ _ _ _

theorem Fits.atEnd_sidePaste_unit {c : PastingDiagram X} (h : d.Fits c)
    {ι : (V : PastingDiagram X) ×
      {ι : Within V d.z // d.z.shape.ogp.IsRewritableSubmolecule ι.image ⊤}}
    (hι : d.occ = some ι) (hu : (ι.1.unit.boundary d.k (!d.α)).Equiv ι.1) :
    d.AtEnd (!d.α) d.k c (sidePaste d.α ι.1.unit d.k ι.2.1 ι.2.2.isSubmoleculeOf hu c) := by
  classical
  obtain ⟨hV, hVs, hdV⟩ := h.occ hι
  have hKe := h.K_eq_hornSetAt hι
  let S := sideWithin (Within.refl c) d.k d.α h.side
  let occW : Within ι.1 c := ι.2.1.trans S
  have hocc : occW.image = d.V c := by rw [hV, occSet_of h.side]
  have hf : ∀ y, occW.emb y ∈ d.K c ↔ y ∈ ι.1.shape.ogp.bdryFull ⊤ := by
    intro y
    have hy : occW.emb y ∈ d.V c := hocc ▸ occW.mem_image_apply y
    rw [hKe, IsSubmoleculeOf.mem_hornSetAt_iff_of_mem _ _ _ _ _ hy, ← hocc, Within.image,
      ← map_bdryFull, apply_mem_map_iff]
  let wU : Within ι.1.unit (cylDiagram c (d.K c)) := Within.cyl c (d.K c) occW hf
  let wQ := Within.cylCopy c (d.K c) (!d.α)
  have hU : wU.image = cylImage c (PartialCylinder.over (d.K c) (d.V c)) := by
    rw [← hocc]
    exact image_cyl c (d.K c) occW hf
  have hQ : wQ.image = cylImage c (PartialCylinder.copy (d.K c) (!d.α) ⊤) :=
    image_cylCopy c (d.K c) _
  have hc : (cylDiagram c (d.K c)).shape.ogp.IsPastingAtIn d.k d.α wU.image wQ.image
      (cylImage c (PartialCylinder.endSet (d.K c) (!d.α) d.k)) := by
    rw [hU, hQ]
    refine isPastingAtIn_cylImage ?_
    rw [hKe]
    exact PartialCylinder.isPastingAtIn_endSet_not c.shape.isMolecule _ _ hVs hdV
  have hSQ : sideWithin wQ d.k d.α h.side = S.trans wQ :=
    Within.ext_of_image_eq _ _ (by
      rw [image_sideWithin, Within.image_trans, image_sideWithin, Within.image_refl,
        wQ.boundary_image])
  have hoc : (ι.2.1.trans (sideWithin wQ d.k d.α h.side)).image = wU.image ⊓ wQ.image := by
    have e2 : OGP.map wQ.emb (d.V c) =
        cylImage c (PartialCylinder.copy (d.K c) (!d.α) (d.V c)) := by
      change OGP.map (partialCylinderEndpoint c.shape.ogp (d.K c) (!d.α) ≫
        (cylShapeIso c.shape (d.K c)).hom) (d.V c) = _
      rw [map_comp, PartialCylinder.map_partialCylinderEndpoint]
      rfl
    rw [hSQ, Within.image_trans_assoc, hocc, e2, hU, hQ, ← cylImage_inf, inf_comm,
      PartialCylinder.copy_inf_over, top_inf_eq]
  have hR := isMoleculeIn_cylImage (h.endStatement (!d.α) le_rfl).1
  have e := sidePaste_equiv_restrictTo (hι := ι.2.2.isSubmoleculeOf) (h := hu) wU wQ h.side hc
    hoc hR
  exact ⟨(Within.ofEquiv e).trans (Within.restrictTo _ hR), by
    rw [Within.image_ofEquiv_trans, Within.image_restrictTo]⟩

theorem AtEnd.equiv_boundary {β : Bool} {n : ℕ} {c x : PastingDiagram X} (h : d.AtEnd β n c x)
    (hdc : c.dim = n + 1) : x.Equiv ((d.fam c).boundary (n + 1) β) := by
  obtain ⟨w, hw⟩ := h
  have he : krullDim c.shape.ogp = ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [c.shape.krullDim_eq_dimension]
    exact_mod_cast hdc
  rw [fam_def]
  refine Within.equiv_of_image_eq w (Within.boundary _ (n + 1) β) ?_
  rw [hw, image_boundary_cylDiagram, boundary_partialCylinder_eq (d.K c) c.shape.isMolecule he β]
  rfl

theorem lt_krullDim_over (c : PastingDiagram X) {n : ℕ} (hkn : d.k < n) (hn : n ≤ c.dim)
    (γ : Bool) :
    (n : WithBot ℕ∞) <
      krullDim (PartialCylinder.over (d.K c) (c.shape.ogp.boundary ⊤ n γ)) := by
  have hdB : krullDim (c.shape.ogp.boundary ⊤ n γ) = n :=
    IsMoleculeIn.krullDim_boundary c.shape.isMolecule
      (by rw [LowerSet.krullDim_top, c.shape.krullDim_eq_dimension]; exact_mod_cast hn) γ
  obtain ⟨⟨x, hxB⟩, hx⟩ := exists_grade_eq_of_krullDim_eq hdB
  have hxd : grade ℕ x = n := hx
  have hxK : x ∉ d.K c := fun hxK => by
    obtain ⟨β, hβ⟩ := mem_boundaryFull.1 (K_le_boundaryFull c hxK)
    have := grade_le_of_mem_boundary hβ
    omega
  have h2 := PartialCylinder.grade_add_one_le_krullDim_over (K := d.K c) hxB hxK
  rw [hxd] at h2
  exact (by exact_mod_cast n.lt_succ_self : (n : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞)).trans_le
    h2

theorem le_krullDim_endSet (c : PastingDiagram X) (β : Bool) (n : ℕ) :
    (c.dim : WithBot ℕ∞) ≤ krullDim (PartialCylinder.endSet (d.K c) β n) := by
  have e : krullDim (PartialCylinder.copy (d.K c) β ⊤) = c.dim := by
    rw [PartialCylinder.krullDim_copy, LowerSet.krullDim_top, c.shape.krullDim_eq_dimension]
    rfl
  exact e ▸ LowerSet.krullDim_mono le_sup_left

theorem AtEnd.paste (β : Bool) {n : ℕ} {c x y : PastingDiagram X} (hc : d.Fits c)
    (hx : d.AtEnd β n c x) (hkn : d.k ≤ n) (hn : n + 1 < c.dim)
    (wy : Within y (cylDiagram c (d.K c)))
    (hwy : wy.image = cylImage c
      (PartialCylinder.over (d.K c) (c.shape.ogp.boundary ⊤ (n + 1) (!β)))) :
    ∃ hp : (cond β y x).Pastable (cond β x y) (n + 1),
      d.AtEnd β (n + 1) c ((cond β y x).paste (cond β x y) (n + 1) hp) := by
  classical
  obtain ⟨wx, hwx⟩ := hx
  have hp0 := isPastingIn_cylImage (PartialCylinder.isPastingIn_endSet_succ
    c.shape.isMolecule (hc.endStatement β hkn))
  have hR := isMoleculeIn_cylImage (hc.endStatement β (Nat.le_succ_of_le hkn)).1
  have hdx : n + 1 < x.dim := by
    have h1 : ((n + 1 : ℕ) : WithBot ℕ∞) < x.dim := by
      rw [← wx.krullDim_image, hwx, krullDim_cylImage]
      exact (by exact_mod_cast hn : ((n + 1 : ℕ) : WithBot ℕ∞) < c.dim).trans_le
        (le_krullDim_endSet c β n)
    exact_mod_cast h1
  have hdy : n + 1 < y.dim := by
    have h1 : ((n + 1 : ℕ) : WithBot ℕ∞) < y.dim := by
      rw [← wy.krullDim_image, hwy, krullDim_cylImage]
      exact lt_krullDim_over c (by omega) hn.le (!β)
    exact_mod_cast h1
  simp only [Bool.apply_cond (cylImage c)] at hp0
  rw [← hwx, ← hwy] at hp0
  have hp := pastable_cond_of_isPastingIn β wy wx hp0 hdy hdx
  exact ⟨hp, (Within.ofEquiv (equiv_paste_cond_of_within β wy wx hp0 hR hp)).trans
    (Within.restrictTo _ hR), by rw [Within.image_ofEquiv_trans, Within.image_restrictTo]⟩

end CylSpec

end Atoms.Diagrammatic
