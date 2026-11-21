import Atoms.Diagrammatic.Context.Syntax
import Atoms.Diagrammatic.Equivalence.BiInvertible

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Molecule.MoleculeShape

variable (J : ℕ → Bool) (S : MoleculeShape)

theorem boundary_map_dualIso (W : LowerSet S.ogp) (k : ℕ) (γ : Bool) :
    (S.dual J).ogp.boundary (OGP.map (P := OGP.dual S.ogp J) (S.dualIso J).hom W) k γ =
      OGP.map (P := OGP.dual S.ogp J) (S.dualIso J).hom
        (S.ogp.boundary W k (xor (J (k + 1)) γ)) := by
  rw [← map_boundary, boundary_dual]

theorem boundary_top_dual (k : ℕ) (γ : Bool) :
    (S.dual J).ogp.boundary ⊤ k γ =
      OGP.map (P := OGP.dual S.ogp J) (S.dualIso J).hom
        (S.ogp.boundary ⊤ k (xor (J (k + 1)) γ)) := by
  rw [← boundary_map_dualIso, map_top_of_isIso]

theorem map_boundary_top_dualIso (k : ℕ) (γ : Bool) :
    OGP.map (P := OGP.dual S.ogp J) (S.dualIso J).hom (S.ogp.boundary ⊤ k γ) =
      (S.dual J).ogp.boundary ⊤ k (xor (J (k + 1)) γ) := by
  rw [boundary_top_dual, Bool.xor_xor_cancel_left]

theorem map_map_dualIso_dualIso (E : ((S.dual J).dual J).ogp ≅ S.ogp) (W : LowerSet S.ogp) :
    OGP.map E.hom (OGP.map (P := OGP.dual (S.dual J).ogp J) ((S.dual J).dualIso J).hom
      (OGP.map (P := OGP.dual S.ogp J) (Q := (S.dual J).ogp) (S.dualIso J).hom W)) = W := by
  have hE : E = S.dualDualIso J :=
    @Subsingleton.elim _ (IsMolecule.subsingleton_iso ((S.dual J).dual J).isMolecule) _ _
  subst hE
  refine SetLike.coe_injective ?_
  simp only [coe_map, Set.image_image, dualDualIso_hom_apply, Iso.hom_inv_id_apply,
    Set.image_id']

end Atoms.Molecule.MoleculeShape

namespace Atoms.Diagrammatic

namespace PastingDiagram

variable {X Y : DiagSet.{u}}

theorem Within.ofEquiv_boundary_trans {a b : PastingDiagram X} (E : a.Equiv b) (k : ℕ)
    (α : Bool) :
    (Within.ofEquiv (E.boundary k α)).trans (Within.boundary b k α) =
      (Within.boundary a k α).trans (Within.ofEquiv E) :=
  Within.ext_of_image_eq _ _ (((Within.image_trans _ _).trans
    ((congrArg (OGP.map (Within.boundary b k α).emb) (Within.image_ofEquiv _)).trans
      (Within.image_boundary b k α))).trans ((Within.image_trans _ _).trans (by
        rw [Within.image_boundary, map_boundary, ← Within.image, Within.image_ofEquiv])).symm)

theorem Within.ofEquiv_boundary_mapTo_trans (u : PastingDiagram X) (f : X ⟶ Y) (k : ℕ) (α : Bool)
    (B : ((u.boundary k α).mapTo f).Equiv ((u.mapTo f).boundary k α)) :
    (Within.ofEquiv B).trans (Within.boundary (u.mapTo f) k α) = (Within.boundary u k α).mapTo f :=
  Within.ext_of_image_eq _ _ (by
    rw [Within.image_trans, Within.image_ofEquiv]
    exact (Within.image_boundary (u.mapTo f) k α).trans (Within.image_boundary u k α).symm)

variable (J : ℕ → Bool)

theorem Within.dual_trans {a m n : PastingDiagram X} (w : Within a m) (w' : Within m n) :
    (w.trans w').dual J = (w.dual J).trans (w'.dual J) :=
  Within.ext_of_image_eq _ _ (by
    rw [Within.image_dual, Within.image_trans, Within.image_trans, Within.image_dual,
      Within.map_emb_dual])

theorem Within.isRewritableSubmolecule_image_dual_iff {a m : PastingDiagram X} (w : Within a m) :
    (m.dual J).shape.ogp.IsRewritableSubmolecule (w.dual J).image ⊤ ↔
      m.shape.ogp.IsRewritableSubmolecule w.image ⊤ := by
  rw [Within.image_dual, ← map_top_of_isIso (m.shape.dualIso J).hom,
    isRewritableSubmolecule_map_iff]
  exact isRewritableSubmolecule_dual J

theorem Within.ofEquiv_trans_boundary_dual (u : PastingDiagram X) (k : ℕ) {α α' : Bool}
    (hα : xor (J (k + 1)) α = α') (E : ((u.boundary k α).dual J).Equiv ((u.dual J).boundary k α')) :
    (Within.ofEquiv E).trans (Within.boundary (u.dual J) k α') = (Within.boundary u k α).dual J :=
  Within.ext_of_image_eq _ _ (by
    subst hα
    have h1 := MoleculeShape.boundary_top_dual J u.shape k (xor (J (k + 1)) α)
    rw [Bool.xor_xor_cancel_left] at h1
    exact ((Within.image_trans _ _).trans ((congrArg (OGP.map _) (Within.image_ofEquiv _)).trans
      ((Within.image_boundary (u.dual J) k _).trans h1))).trans
        (by rw [Within.image_dual, Within.image_boundary]))

noncomputable def Within.dualBoundary {s u : PastingDiagram X} {k : ℕ} {α : Bool}
    (occ : Within s (u.boundary k α)) (α' : Bool) (hα : xor (J (k + 1)) α = α') :
    Within (s.dual J) ((u.dual J).boundary k α') :=
  (occ.dual J).trans (Within.ofEquiv (by subst hα; exact (equiv_boundary_dual_xor J u k α).symm))

theorem Within.dualBoundary_trans {s u : PastingDiagram X} {k : ℕ} {α : Bool}
    (occ : Within s (u.boundary k α)) (α' : Bool) (hα : xor (J (k + 1)) α = α') :
    (occ.dualBoundary J α' hα).trans (Within.boundary (u.dual J) k α') =
      (occ.trans (Within.boundary u k α)).dual J := by
  rw [Within.dualBoundary, Within.trans_assoc, Within.ofEquiv_trans_boundary_dual J u k hα,
    Within.dual_trans]

theorem Within.isRewritableSubmolecule_dualBoundary {s u : PastingDiagram X} {k : ℕ} {α : Bool}
    (occ : Within s (u.boundary k α)) (α' : Bool) (hα : xor (J (k + 1)) α = α')
    (h : (u.boundary k α).shape.ogp.IsRewritableSubmolecule occ.image ⊤) :
    ((u.dual J).boundary k α').shape.ogp.IsRewritableSubmolecule
      (occ.dualBoundary J α' hα).image ⊤ :=
  ((occ.dual J).isRewritableSubmolecule_image_trans_ofEquiv_iff _).2
    ((occ.isRewritableSubmolecule_image_dual_iff J).2 h)

end PastingDiagram

variable {X Y : DiagSet.{u}} (J : ℕ → Bool)

noncomputable def Equation.dual {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    (eq : Equation α n e u) (α' : Bool) (hα : xor (J (n + 1)) α = α') :
    Equation α' n (e.dual J) (u.dual J) where
  dim_e := (dim_dual J _).trans eq.dim_e
  dim_u := (dim_dual J _).trans eq.dim_u
  sub := eq.sub.dual J
  occ := eq.occ.dualBoundary J α' hα
  rewritable := eq.occ.isRewritableSubmolecule_dualBoundary J α' hα eq.rewritable
  equiv := by
    subst hα
    exact (eq.equiv.dual J).trans (equiv_boundary_dual_xor J e.toPastingDiagram n α).symm

noncomputable def PasteAtData.dual {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X}
    (d : PasteAtData α n e u') (α' : Bool) (hα : xor (J (n + 1)) α = α') :
    PasteAtData α' n (e.dual J) (u'.dual J) where
  dim_e := (dim_dual J _).trans d.dim_e
  dim_u' := (dim_dual J _).trans d.dim_u'
  sub := d.sub.dual J
  occ := d.occ.dualBoundary J α' hα
  rewritable := d.occ.isRewritableSubmolecule_dualBoundary J α' hα d.rewritable
  equiv := by
    subst hα
    rw [← Bool.xor_not]
    exact (equiv_boundary_dual_xor J e.toPastingDiagram n (!α)).trans (d.equiv.dual J)

namespace PasteAtData

variable {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X} (d : PasteAtData α n e u') (α' : Bool)
  (hα : xor (J (n + 1)) α = α')

include hα in
theorem isPastingAtIn_dual :
    (d.pasting.dual J).shape.ogp.IsPastingAtIn n α'
      ((Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J).image
      ((Within.pasteAtInr e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J).image ⊤ := by
  subst hα
  rw [Within.image_dual, Within.image_dual, ← map_top_of_isIso (d.pasting.shape.dualIso J).hom]
  refine IsPastingAtIn.map (d.pasting.shape.dualIso J).hom ((isPastingAtIn_dual J).2 ?_)
  rw [Bool.xor_xor_cancel_left]
  exact Within.isPastingAtIn_pasteAt _ _ n α d.occ d.rewritable.isSubmoleculeOf d.equiv

theorem image_dual_occ_trans :
    ((d.dual J α' hα).occ.trans ((Within.boundary (u'.toPastingDiagram.dual J) n α').trans
      ((Within.pasteAtInr e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J))).image =
      ((Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J).image ⊓
      ((Within.pasteAtInr e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J).image := by
  change ((d.occ.dualBoundary J α' hα).trans _).image = _
  rw [← Within.trans_assoc, Within.dualBoundary_trans, ← Within.dual_trans, Within.image_dual,
    Within.trans_assoc, image_occurrence_pasteAt, map_inf, Within.image_dual, Within.image_dual]

noncomputable def dualWithin : Within (d.dual J α' hα).pasting (d.pasting.dual J) :=
  Within.pasteAtOfWithin _ _ (d.isPastingAtIn_dual J α' hα) (d.dual J α' hα).occ
    (d.dual J α' hα).rewritable.isSubmoleculeOf (d.image_dual_occ_trans J α' hα)
    (d.dual J α' hα).equiv

theorem image_dualWithin : (d.dualWithin J α' hα).image = ⊤ :=
  Within.image_pasteAtOfWithin _ _ (d.isPastingAtIn_dual J α' hα) _ _
    (d.image_dual_occ_trans J α' hα) _

theorem equiv_dual_pasting : (d.pasting.dual J).Equiv (d.dual J α' hα).pasting :=
  (Within.equiv_of_image_eq (d.dualWithin J α' hα) (Within.refl _)
    ((d.image_dualWithin J α' hα).trans (Within.image_refl _).symm)).symm

theorem pasteAtInl_trans_dualWithin :
    (Within.pasteAtInl (e.dual J).toPastingDiagram (u'.dual J).toPastingDiagram n α'
        (d.dual J α' hα).occ (d.dual J α' hα).rewritable.isSubmoleculeOf
        (d.dual J α' hα).equiv).trans (d.dualWithin J α' hα) =
      (Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
        d.rewritable.isSubmoleculeOf d.equiv).dual J :=
  (Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin _ _ (d.isPastingAtIn_dual J α' hα) _ _
    (d.image_dual_occ_trans J α' hα) _).1

end PasteAtData

namespace Geometry

variable {α : Bool} {n : ℕ} {e u' u w : RoundPastingDiagram X} {d : PasteAtData α n e u'}
  {β : Bool}

noncomputable def dual (g : Geometry d u w β) (α' : Bool) (hα : xor (J (n + 1)) α = α') :
    Geometry (d.dual J α' hα) (u.dual J) (w.dual J) (xor (J (n + 1 + 1)) β) where
  wP := (d.dualWithin J α' hα).trans (g.wP.dual J)
  wU := g.wU.dual J
  image_wP := (Within.image_trans _ _).trans
    ((congrArg (OGP.map _) (d.image_dualWithin J α' hα)).trans
      (((Within.image_dual J g.wP).trans (congrArg (OGP.map _) g.image_wP)).trans
        (MoleculeShape.map_boundary_top_dualIso J w.shape (n + 1) β)))
  image_wU := ((Within.image_dual J g.wU).trans (congrArg (OGP.map _) g.image_wU)).trans
    ((MoleculeShape.map_boundary_top_dualIso J w.shape (n + 1) (!β)).trans
      (by rw [Bool.xor_not]; rfl))
  dim_w := (dim_dual J _).trans g.dim_w

theorem withinE_dual (g : Geometry d u w β) (α' : Bool) (hα : xor (J (n + 1)) α = α') :
    (g.dual J α' hα).withinE = g.withinE.dual J :=
  (Within.trans_assoc _ _ _).symm.trans ((congrArg (·.trans (g.wP.dual J))
    (d.pasteAtInl_trans_dualWithin J α' hα)).trans (Within.dual_trans J _ _).symm)

end Geometry

theorem Compat.dual {α : Bool} {n : ℕ} {e u u' w : RoundPastingDiagram X} {β : Bool}
    {eq : Equation α n e u} {d : PasteAtData α n e u'} (hc : Compat eq d) (g : Geometry d u w β)
    (α' : Bool) (hα : xor (J (n + 1)) α = α') : Compat (eq.dual J α' hα) (d.dual J α' hα) := by
  refine (g.dual J α' hα).compat_of_image ?_
  have hL : ((eq.occ.dualBoundary J α' hα).trans
      ((Within.boundary (u.toPastingDiagram.dual J) n α').trans (g.wU.dual J))).image =
      OGP.map (w.shape.dualIso J).hom (w.shape.ogp.boundary g.withinE.image n α) := by
    rw [← Within.trans_assoc, Within.dualBoundary_trans, ← Within.dual_trans, Within.image_dual,
      Within.trans_assoc, g.compat_image hc]
  have hR : (w.toPastingDiagram.dual J).shape.ogp.boundary (g.withinE.dual J).image n α' =
      OGP.map (w.shape.dualIso J).hom (w.shape.ogp.boundary g.withinE.image n α) := by
    rw [Within.image_dual]
    exact (MoleculeShape.boundary_map_dualIso J w.shape _ n α').trans
      (by subst hα; rw [Bool.xor_xor_cancel_left])
  exact hL.trans (hR.symm.trans (congrArg (fun W : Within (e.toPastingDiagram.dual J)
    (w.toPastingDiagram.dual J) => (w.toPastingDiagram.dual J).shape.ogp.boundary W.image n α')
      (g.withinE_dual J α' hα).symm))

noncomputable def UnbiasedSolution.dualLax {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} {eq : Equation α n e u} (s : UnbiasedSolution A eq) (α' : Bool)
    (hα : xor (J (n + 1)) α = α') :
    LaxSolution (RoundPastingDiagram.dual J '' A) (eq.dual J α' hα) where
  sol := s.sol.dual J
  data := s.data.dual J α' hα
  compat := s.compat.dual J (s.side false).geometry α' hα
  lax :=
    { witness := (s.side (J (n + 1 + 1))).witness.dual J
      mem := ⟨_, (s.side _).mem, rfl⟩
      hasBdry := by
        have t := (s.side (J (n + 1 + 1))).hasBdry.dual J
        rw [Bool.xor_self] at t
        exact t.of_equiv_side (s.data.equiv_dual_pasting J α' hα) }

noncomputable def Equation.mapToOf {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    (eq : Equation α n e u) (f : X ⟶ Y) {e' : RoundPastingDiagram Y} (he' : e'.dim = n + 1)
    (h : ((e.toPastingDiagram.mapTo f).boundary n α).Equiv (e'.boundary n α)) :
    Equation α n e' (u.mapTo f) where
  dim_e := he'
  dim_u := eq.dim_u
  sub := eq.sub.mapTo f
  occ := (eq.occ.mapTo f).trans
    (Within.ofEquiv ((PastingDiagram.Equiv.refl _).mapTo_boundary f).symm)
  rewritable := ((eq.occ.mapTo f).isRewritableSubmolecule_image_trans_ofEquiv_iff _).2
    eq.rewritable
  equiv := (eq.equiv.mapTo f).trans (((PastingDiagram.Equiv.refl _).mapTo_boundary f).symm.trans h)

theorem Equation.image_mapToOf_occ_trans {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    (eq : Equation α n e u) (f : X ⟶ Y) {e' : RoundPastingDiagram Y} (he' : e'.dim = n + 1)
    (h : ((e.toPastingDiagram.mapTo f).boundary n α).Equiv (e'.boundary n α)) :
    ((eq.mapToOf f he' h).occ.trans (Within.boundary (u.mapTo f).toPastingDiagram n α)).image =
      (eq.occ.trans (Within.boundary u.toPastingDiagram n α)).image :=
  (congrArg Within.image (Within.trans_assoc (eq.occ.mapTo f) _ _)).trans
    (congrArg (fun W => ((eq.occ.mapTo f).trans W).image)
      (Within.ofEquiv_boundary_mapTo_trans u.toPastingDiagram f n α _))

noncomputable def LaxSolution.ofEquivTarget {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e u₁ u₂ : RoundPastingDiagram X} {eq₁ : Equation α n e u₁} {eq₂ : Equation α n e u₂}
    (E : u₁.toPastingDiagram.Equiv u₂.toPastingDiagram)
    (h : (eq₁.occ.trans (Within.ofEquiv (E.boundary n α))).image = eq₂.occ.image)
    (s : LaxSolution A eq₁) : LaxSolution A eq₂ where
  sol := s.sol
  data := s.data
  compat hb := by
    have hb₁ := hb.trans (E.boundary n α).symm
    have hiso : hb₁.iso ≪≫ (E.boundary n α).iso = hb.iso :=
      @Subsingleton.elim _
        (IsMolecule.subsingleton_iso (s.data.pasting.boundary n α).shape.isMolecule) _ _
    rw [← h, Within.image_trans, s.compat hb₁, PasteAtData.occIn_image, PasteAtData.occIn_image,
      ← map_comp, ← hiso]
    rfl
  lax := ⟨s.lax.witness, s.lax.mem, s.lax.hasBdry.of_equiv_other E⟩

theorem eqvSolutions_dual {e : RoundPastingDiagram X} (he : e ∈ eqvSolutions X) :
    e.dual J ∈ eqvSolutions ((DiagSet.dual J).obj X) := by
  refine subset_eqvSolutions (A := RoundPastingDiagram.dual J '' eqvSolutions X) ?_ ⟨e, he, rfl⟩
  rintro _ ⟨e, he, rfl⟩
  refine ⟨(pos_dim_of_mem_eqvSolutions he).trans_eq (dim_dual J _).symm, fun α n u eq => ?_⟩
  let φ := (DiagSet.dualDualIso J X).hom
  let w : RoundPastingDiagram X := ⟨(u.toPastingDiagram.dual J).mapTo φ, (u.dual J).isRound⟩
  have hdim : e.dim = n + 1 := (dim_dual J _).symm.trans eq.dim_e
  let eq₂ : Equation (xor (J (n + 1)) α) n e w :=
    (eq.dual J _ rfl).mapToOf φ hdim ((equiv_mapTo_dualDual J e.toPastingDiagram).boundary n _)
  obtain ⟨s⟩ := unbiased_tClosure_eqvSolutions he _ n w eq₂
  rw [tClosure_eqvSolutions_eq] at s
  have E := equiv_dual_mapTo_dual J u.toPastingDiagram
  refine ⟨(s.dualLax J α (by rw [Bool.xor_xor_cancel_left])).ofEquivTarget E ?_⟩
  refine map_injective (Within.boundary u.toPastingDiagram n α).emb ?_
  rw [← Within.image_trans, ← Within.image_trans, Within.trans_assoc,
    Within.ofEquiv_boundary_trans, ← Within.trans_assoc, Within.image_trans]
  change OGP.map E.iso.hom (((eq₂.occ.dualBoundary J α (by rw [Bool.xor_xor_cancel_left])).trans
    (Within.boundary (w.toPastingDiagram.dual J) n α)).image) = _
  have h2 : (eq₂.occ.trans (Within.boundary w.toPastingDiagram n (xor (J (n + 1)) α))).image =
      ((eq.occ.dualBoundary J _ rfl).trans
        (Within.boundary (u.toPastingDiagram.dual J) n (xor (J (n + 1)) α))).image :=
    Equation.image_mapToOf_occ_trans _ _ _ _
  rw [Within.dualBoundary_trans, Within.image_dual, h2, Within.dualBoundary_trans,
    Within.image_dual]
  exact MoleculeShape.map_map_dualIso_dualIso J u.shape E.iso _

theorem mem_equivalences_dual (J : ℕ → Bool) {e : RoundPastingDiagram X}
    (he : e ∈ equivalences X) : e.dual J ∈ equivalences ((DiagSet.dual J).obj X) := by
  rw [← eqvSolutions_eq_equivalences] at he ⊢
  exact eqvSolutions_dual J he

theorem mem_equivalences_dual_iff (J : ℕ → Bool) {e : RoundPastingDiagram X} :
    e.dual J ∈ equivalences ((DiagSet.dual J).obj X) ↔ e ∈ equivalences X :=
  ⟨fun h => mem_equivalences_of_equiv (PastingDiagram.equiv_mapTo_dualDual J e.toPastingDiagram)
    (mapTo_mem_equivalences (DiagSet.dualDualIso J X).hom (mem_equivalences_dual J h)),
    mem_equivalences_dual J⟩

end Atoms.Diagrammatic
