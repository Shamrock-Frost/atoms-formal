import Atoms.Diagrammatic.Context.NaturalEquivalence

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure IsCylTriple (d : CylSpec X) (τ : CtxTriple X) : Prop where
  valid : τ.Valid
  le_k : d.k ≤ τ.dom.k
  fits : ∀ c, InHom τ.dom c → c.IsRound → d.Fits c
  comp_equiv : ∀ a, IsRoundIn τ.dom a → (τ.ϑ a).Equiv (d.fam a)
  atEnd_F : ∀ c, InHom τ.dom c → c.IsRound → d.AtEnd false τ.dom.k c (τ.F.app c)
  atEnd_G : ∀ c, InHom τ.dom c → c.IsRound → d.AtEnd true τ.dom.k c (τ.G.app c)

def cylTriples (X : DiagSet.{u}) : Set (CtxTriple X) :=
  {τ | ∃ d : CylSpec X, IsCylTriple d τ}

theorem IsCylTriple.of_atEnd {d : CylSpec X} {τ : CtxTriple X}
    (hF : IsRoundCtxOn τ.dom τ.cod τ.F) (hG : IsRoundCtxOn τ.dom τ.cod τ.G)
    (hk : d.k ≤ τ.dom.k) (hfits : ∀ c, InHom τ.dom c → c.IsRound → d.Fits c)
    (hϑ : ∀ a, IsRoundIn τ.dom a → (τ.ϑ a).Equiv (d.fam a))
    (hFe : ∀ c, InHom τ.dom c → c.IsRound → d.AtEnd false τ.dom.k c (τ.F.app c))
    (hGe : ∀ c, InHom τ.dom c → c.IsRound → d.AtEnd true τ.dom.k c (τ.G.app c)) :
    IsCylTriple d τ := by
  refine ⟨⟨hF, hG, fun a ha => ?_⟩, hk, hfits, hϑ, hFe, hGe⟩
  have hfa := hfits a ha.inHom ha.isRound
  obtain ⟨hr, he, hd⟩ := hfa.fam_spec
  have eq := (hϑ a ha).symm
  have hs := (hFe a ha.inHom ha.isRound).equiv_boundary ha.dim_eq
  have ht := (hGe a ha.inHom ha.isRound).equiv_boundary ha.dim_eq
  have hdf : (d.fam a).dim = τ.dom.k + 1 + 1 := hd.trans (congrArg (· + 1) ha.dim_eq)
  have hdb : ∀ β, ((d.fam a).boundary (τ.dom.k + 1) β).dim = τ.dom.k + 1 := fun β =>
    dim_boundary _ (by omega) β
  have hr' : (τ.ϑ a).IsRound := eq.isRound_iff.1 hr
  refine ⟨hr', mem_equivalences_of_equiv (e := ⟨d.fam a, hr⟩) (e' := ⟨τ.ϑ a, hr'⟩) eq he,
    ⟨(dim_eq_of_equiv eq).symm.trans hdf, (dim_eq_of_equiv hs).trans (hdb false),
      (dim_eq_of_equiv ht).trans (hdb true), ?_, ?_⟩⟩
  · exact (eq.symm.boundary _ _).trans
      (hs.symm)
  · exact (eq.symm.boundary _ _).trans
      (ht.symm)

theorem IsCylTriple.next {d : CylSpec X} {τ : CtxTriple X} (h : IsCylTriple d τ)
    {a b : PastingDiagram X} (ha : IsRoundIn τ.dom a) (hb : IsRoundIn τ.dom b) :
    IsCylTriple d ⟨RoundHom.ofIsRoundIn ha hb, ⟨τ.dom.k + 1, τ.F.app a, τ.G.app b⟩, τ.nextF b,
      τ.nextG a, d.fam⟩ := by
  have hin : ∀ c, InHom ⟨τ.dom.k + 1, a, b⟩ c → InHom τ.dom c := fun c hc =>
    hc.of_inHom_succ ha.inHom hb.inHom
  have hkn : d.k < τ.dom.k + 1 := Nat.lt_succ_of_le h.le_k
  refine IsCylTriple.of_atEnd
    (h.valid.isRoundCtxOn_nextF ha hb) (h.valid.isRoundCtxOn_nextG ha hb)
    (Nat.le_succ_of_le h.le_k) (fun c hc hcr => h.fits c (hin c hc) hcr)
    (fun _ _ => .refl _) (fun c hc hcr => ?_) (fun c hc hcr => ?_)
  · have hfc := h.fits c (hin c hc) hcr
    obtain ⟨wy, hwy⟩ := CylSpec.exists_within_fam_boundary hfc hkn hc.lt_dim.le true
    have e : (τ.ϑ b).Equiv (d.fam (c.boundary (τ.dom.k + 1) true)) :=
      (h.comp_equiv b hb).trans
        (CylSpec.fam_equiv (h.fits b hb.inHom hb.isRound) (hc.target.symm))
    obtain ⟨hp, hend⟩ := (h.atEnd_F c (hin c hc) hcr).paste false hfc h.le_k hc.lt_dim
      ((Within.ofEquiv e).trans wy) ((Within.image_ofEquiv_trans e wy).trans hwy)
    exact hend.of_equiv (CtxExpr.paste_app true hp)
  · have hfc := h.fits c (hin c hc) hcr
    obtain ⟨wy, hwy⟩ := CylSpec.exists_within_fam_boundary hfc hkn hc.lt_dim.le false
    have e : (τ.ϑ a).Equiv (d.fam (c.boundary (τ.dom.k + 1) false)) :=
      (h.comp_equiv a ha).trans
        (CylSpec.fam_equiv (h.fits a ha.inHom ha.isRound) (hc.source.symm))
    obtain ⟨hp, hend⟩ := (h.atEnd_G c (hin c hc) hcr).paste true hfc h.le_k hc.lt_dim
      ((Within.ofEquiv e).trans wy) ((Within.image_ofEquiv_trans e wy).trans hwy)
    exact hend.of_equiv (CtxExpr.paste_app false hp)

theorem cylTriples_subset_natOp : cylTriples X ⊆ CtxTriple.natOp (cylTriples X) := by
  rintro τ ⟨d, h⟩
  exact ⟨h.valid, fun a b ha hb => ⟨_, ⟨d, h.next ha hb⟩, CtxTriple.realizes_self _⟩⟩

theorem cylTriples_subset_natEqv : cylTriples X ⊆ natEqv X :=
  subset_natEqv cylTriples_subset_natOp

theorem isCylTriple_unit (H : RoundHom X) :
    IsCylTriple ⟨H.k, false, H.v, none⟩ ⟨H, H, .id, .id, fun a => a.unit⟩ := by
  have hfits : ∀ c, InHom H c → c.IsRound →
      (⟨H.k, false, H.v, none⟩ : CylSpec X).Fits c := fun c hc hcr => ⟨hcr, hc.lt_dim, hc.source⟩
  refine IsCylTriple.of_atEnd isRoundCtxOn_id isRoundCtxOn_id le_rfl hfits (fun a ha => ?_)
    (fun c hc hcr => (hfits c hc hcr).atEnd_self (Or.inr rfl))
    (fun c hc hcr => (hfits c hc hcr).atEnd_self (Or.inr rfl))
  have hda : krullDim (⊤ : LowerSet a.shape.ogp) = H.k + 1 := by
    rw [LowerSet.krullDim_top, a.shape.krullDim_eq_dimension]
    exact_mod_cast ha.dim_eq
  have hK : (⟨H.k, false, H.v, none⟩ : CylSpec X).K a = a.shape.ogp.bdryFull ⊤ := by
    rw [CylSpec.K_of_none (d := ⟨H.k, false, H.v, none⟩) rfl a, bdryFull, bdry_eq_boundary hda,
      bdry_eq_boundary hda]
    rfl
  have e : a.unit = (⟨H.k, false, H.v, none⟩ : CylSpec X).fam a := by
    rw [CylSpec.fam_def, unit_eq_cylDiagram]
    exact cylDiagram_congr a hK.symm
  exact e ▸ .refl _

theorem equiv_boundary_sidePaste_unit {k : ℕ} {α : Bool} {z V : PastingDiagram X}
    (ι : Within V z) (hι : z.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hdz : z.dim = k) (hu : (V.unit.boundary k (!α)).Equiv V) :
    ((sidePaste α V.unit k ι hι.isSubmoleculeOf hu z).boundary k α).Equiv z := by
  have hVr := ι.round_image_iff.1 hι.isRound
  have hdk : V.dim = k := (ι.isRewritableSubmolecule_image_iff.1 hι).2.2.trans hdz
  have hr := isRound_unit hVr
  have hdu : V.unit.dim = k + 1 := by rw [dim_unit, hdk]
  have hw : Parallel ⟨V, hVr⟩ ⟨V.unit.boundary k α, isRound_boundary_of_isRound hr k α⟩ :=
    (parallel_boundary hr hdu (!α) α).of_equiv_left (hu.symm)
  exact (equiv_boundary_sidePaste_substitute (hι := hι.isSubmoleculeOf) (h := hu) hr hdu hι hw
    (equiv_boundary_dim z hdz.le α) hdz.ge).trans
    (equiv_substitute_of_equiv z ι hι _ hw (boundary_unit hdk α))

theorem isRoundCtxOn_unit (α : Bool) {H : PdHom X} {V : PastingDiagram X}
    (ι : Within V (H.side α))
    (hι : (H.side α).shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hdz : (H.side α).dim = H.k) (hu : (V.unit.boundary H.k (!α)).Equiv V) :
    IsRoundCtxOn H H (.side α V.unit H.k ι hι.isSubmoleculeOf hu) := by
  have hr := isRound_unit (ι.round_image_iff.1 hι.isRound)
  have hdu : V.unit.dim = H.k + 1 := by
    rw [dim_unit, (ι.isRewritableSubmolecule_image_iff.1 hι).2.2, hdz]
  have ht : ∀ {q : Prop},
      (CtxExpr.side α V.unit H.k ι hι.isSubmoleculeOf hu).Typed Set.univ q H H :=
    fun {_} => .side α ⟨V.unit, hr⟩ (Set.mem_univ _) hdu ι hι hu (.refl _)
      (H.equiv_setSide (equiv_boundary_sidePaste_unit ι hι hdz hu).symm).symm
  exact ⟨ht, isRoundCtx_of_trim ht⟩

theorem isCylTriple_unitor (α : Bool) (H : RoundHom X) {V : PastingDiagram X}
    (ι : Within V (H.side α)) (hι : (H.side α).shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hu : (V.unit.boundary H.k (!α)).Equiv V) :
    IsCylTriple ⟨H.k, α, H.side α, some ⟨V, ι, hι⟩⟩
      ⟨H, H, cond α (.side α V.unit H.k ι hι.isSubmoleculeOf hu) .id,
        cond α .id (.side α V.unit H.k ι hι.isSubmoleculeOf hu),
        (⟨H.k, α, H.side α, some ⟨V, ι, hι⟩⟩ : CylSpec X).fam⟩ := by
  have hfits : ∀ c, InHom H c → c.IsRound →
      (⟨H.k, α, H.side α, some ⟨V, ι, hι⟩⟩ : CylSpec X).Fits c := fun c hc hcr =>
    ⟨hcr, hc.lt_dim, hc.side α⟩
  have hs := isRoundCtxOn_unit (H := H.toPdHom) α ι hι
    (Bool.cond_rec_prop (p := fun x : PastingDiagram X => x.dim = H.k) α H.dim_w H.dim_v) hu
  refine IsCylTriple.of_atEnd (Bool.cond_rec_prop α hs isRoundCtxOn_id)
    (Bool.cond_rec_prop α isRoundCtxOn_id hs) le_rfl hfits (fun _ _ => .refl _)
    (fun c hc hcr => ?_) (fun c hc hcr => ?_) <;> cases α
  exacts [(hfits c hc hcr).atEnd_self (Or.inl rfl), (hfits c hc hcr).atEnd_sidePaste_unit rfl hu,
    (hfits c hc hcr).atEnd_sidePaste_unit rfl hu, (hfits c hc hcr).atEnd_self (Or.inl rfl)]

theorem isCylTriple_leftUnitor (H : RoundHom X) {V : PastingDiagram X} (ι : Within V H.v)
    (hι : H.v.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hu : (V.unit.boundary H.k true).Equiv V) :
    IsCylTriple ⟨H.k, false, H.v, some ⟨V, ι, hι⟩⟩
      ⟨H, H, .id, .side false V.unit H.k ι hι.isSubmoleculeOf hu,
        (⟨H.k, false, H.v, some ⟨V, ι, hι⟩⟩ : CylSpec X).fam⟩ :=
  isCylTriple_unitor false H ι hι hu

theorem isCylTriple_rightUnitor (H : RoundHom X) {V : PastingDiagram X} (ι : Within V H.w)
    (hι : H.w.shape.ogp.IsRewritableSubmolecule ι.image ⊤)
    (hu : (V.unit.boundary H.k false).Equiv V) :
    IsCylTriple ⟨H.k, true, H.w, some ⟨V, ι, hι⟩⟩
      ⟨H, H, .side true V.unit H.k ι hι.isSubmoleculeOf hu, .id,
        (⟨H.k, true, H.w, some ⟨V, ι, hι⟩⟩ : CylSpec X).fam⟩ :=
  isCylTriple_unitor true H ι hι hu

end Atoms.Diagrammatic
