import Atoms.Diagrammatic.Pasting.Dual
import Atoms.Diagrammatic.Equivalence.Degenerate

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure HasBdry (β : Bool) (n : ℕ) (h a b : PastingDiagram X) : Prop where
  dim_h : h.dim = n + 1
  dim_a : a.dim = n
  dim_b : b.dim = n
  side : (h.boundary n β).Equiv a
  other : (h.boundary n (!β)).Equiv b

namespace HasBdry

variable {β : Bool} {n : ℕ} {h a b : PastingDiagram X}

theorem of_dim_eq {k : ℕ} (hk : k = n) (hh : h.dim = k + 1) (ha : a.dim = n) (hb : b.dim = n)
    (side : (h.boundary k β).Equiv a) (other : (h.boundary k (!β)).Equiv b) :
    HasBdry β n h a b := by
  subst hk
  exact ⟨hh, ha, hb, side, other⟩

theorem symm (t : HasBdry β n h a b) : HasBdry (!β) n h b a :=
  ⟨t.dim_h, t.dim_b, t.dim_a, t.other, by rw [Bool.not_not]; exact t.side⟩

theorem of_equiv_side (t : HasBdry β n h a b) {a' : PastingDiagram X} (e : a.Equiv a') :
    HasBdry β n h a' b :=
  ⟨t.dim_h, (dim_eq_of_equiv e).symm.trans t.dim_a, t.dim_b, t.side.trans e,
    t.other⟩

theorem of_equiv_other (t : HasBdry β n h a b) {b' : PastingDiagram X} (e : b.Equiv b') :
    HasBdry β n h a b' :=
  ⟨t.dim_h, t.dim_a, (dim_eq_of_equiv e).symm.trans t.dim_b, t.side,
    t.other.trans e⟩

theorem dual (t : HasBdry β n h a b) (J : ℕ → Bool) :
    HasBdry (xor (J (n + 1)) β) n (h.dual J) (a.dual J) (b.dual J) :=
  ⟨(dim_dual J h).trans t.dim_h, (dim_dual J a).trans t.dim_a, (dim_dual J b).trans t.dim_b,
    (equiv_boundary_dual_xor J h n β).trans (t.side.dual J), by
      rw [← Bool.xor_not]
      exact (equiv_boundary_dual_xor J h n (!β)).trans (t.other.dual J)⟩

theorem equiv_boundary (t : HasBdry β n h a b) {j : ℕ} (hj : j < n) (γ : Bool) :
    (a.boundary j γ).Equiv (b.boundary j γ) :=
  (t.side.boundary j γ).symm.trans
    ((equiv_boundary_boundary h hj β γ).trans
      ((equiv_boundary_boundary h hj (!β) γ).symm.trans
        (t.other.boundary j γ)))

theorem pastable {n : ℕ} {θ θ' x y y' z : PastingDiagram X} (hθ : HasBdry false n θ x y)
    (hθ' : HasBdry false n θ' y' z) (e : y.Equiv y') : θ.Pastable θ' n :=
  ⟨hθ.other.trans
      (e.trans (hθ'.side.symm)),
    by rw [hθ.dim_h, hθ'.dim_h]; omega⟩

theorem pasteOr {n : ℕ} {θ θ' x y y' z : PastingDiagram X} (hθ : HasBdry false n θ x y)
    (hθ' : HasBdry false n θ' y' z) (e : y.Equiv y') : HasBdry false n (θ.pasteOr θ' n) x z := by
  have hp := hθ.pastable hθ' e
  rw [PastingDiagram.pasteOr_of hp]
  exact ⟨by rw [dim_paste, hθ.dim_h, hθ'.dim_h, max_self], hθ.dim_a, hθ'.dim_b,
    (equiv_boundary_paste hp false).trans hθ.side,
    (equiv_boundary_paste hp true).trans hθ'.other⟩

theorem isRound_pasteOr {n : ℕ} {θ θ' x y y' z : PastingDiagram X}
    (hθ : HasBdry false n θ x y) (hθ' : HasBdry false n θ' y' z) (e : y.Equiv y') (hr : θ.IsRound)
    (hr' : θ'.IsRound) : (θ.pasteOr θ' n).IsRound := by
  have hp := hθ.pastable hθ' e
  rw [PastingDiagram.pasteOr_of hp]
  exact isRound_paste_of_dim ⟨θ, hr⟩ ⟨θ', hr'⟩ hθ.dim_h hθ'.dim_h hp

theorem parallel {n : ℕ} {θ θ' x y x' y' : PastingDiagram X} (hθ : HasBdry false n θ x y)
    (hθ' : HasBdry false n θ' x' y') (ex : x.Equiv x') (ey : y.Equiv y') (hr : θ.IsRound)
    (hr' : θ'.IsRound) : Parallel ⟨θ, hr⟩ ⟨θ', hr'⟩ :=
  ⟨hθ.dim_h.trans hθ'.dim_h.symm, Or.inr fun α => by
    change (θ.boundary (θ.dim - 1) α).Equiv (θ'.boundary (θ'.dim - 1) α)
    rw [hθ.dim_h, hθ'.dim_h, Nat.add_sub_cancel]
    cases α
    · exact hθ.side.trans (ex.trans
        (hθ'.side.symm))
    · exact hθ.other.trans (ey.trans
        (hθ'.other.symm))⟩

end HasBdry

theorem hasType_unit {u : PastingDiagram X} {n : ℕ} (hn : u.dim = n) :
    HasBdry false n u.unit u u :=
  ⟨by rw [dim_unit, hn], hn, hn, boundary_unit hn false,
    boundary_unit hn true⟩

structure PasteAtData (α : Bool) (n : ℕ) (e u' : RoundPastingDiagram X) where
  dim_e : e.dim = n + 1
  dim_u' : u'.dim = n + 1
  sub : PastingDiagram X
  occ : Within sub (u'.boundary n α)
  rewritable : (u'.boundary n α).shape.ogp.IsRewritableSubmolecule occ.image ⊤
  equiv : (e.boundary n (!α)).Equiv sub

def PasteAtData.ofBoundary {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X} (he : e.dim = n + 1)
    (hu : u'.dim = n + 1) (h : (e.boundary n (!α)).Equiv (u'.boundary n α)) :
    PasteAtData α n e u' :=
  ⟨he, hu, _, Within.refl _, (Within.refl _).isRewritableSubmolecule_image_iff.2
    ⟨Within.isSubmoleculeOf_image_refl _, isRound_boundary_of_isRound u'.isRound n α, rfl⟩, h⟩

namespace PasteAtData

variable {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X} (d : PasteAtData α n e u')

noncomputable abbrev pasting : PastingDiagram X :=
  pasteAtBoundary e.toPastingDiagram u'.toPastingDiagram n α d.occ d.rewritable.isSubmoleculeOf
      d.equiv

theorem dim_pasting : d.pasting.dim = n + 1 := by
  rw [pasting, dim_pasteAtBoundary, d.dim_e, d.dim_u', max_self]

theorem isRound_pasting : d.pasting.IsRound :=
  isRound_pasteAtBoundary e.toPastingDiagram u'.toPastingDiagram n α d.occ
      d.rewritable.isSubmoleculeOf d.equiv u'.isRound
    (d.dim_e.trans d.dim_u'.symm) (by have := d.dim_u'; omega)

noncomputable def round : RoundPastingDiagram X := ⟨d.pasting, d.isRound_pasting⟩

theorem equiv_boundary_not : (d.pasting.boundary n (!α)).Equiv (u'.boundary n (!α)) :=
  equiv_boundary_not_pasteAtBoundary e.toPastingDiagram u'.toPastingDiagram n α d.occ
    d.rewritable.isSubmoleculeOf d.equiv

theorem isSubmoleculeOf_boundary_inl :
    IsSubmoleculeOf d.pasting.shape.ogp
      (d.pasting.shape.ogp.boundary
        (Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
            d.rewritable.isSubmoleculeOf d.equiv).image n α)
      (d.pasting.shape.ogp.boundary (Within.refl d.pasting).image n α) := by
  rw [Within.image_refl]
  exact (Within.isPastingAtIn_pasteAt e.toPastingDiagram u'.toPastingDiagram n α d.occ
      d.rewritable.isSubmoleculeOf d.equiv).isSubmoleculeOf_boundary_left

noncomputable def copySub :
    Within (occurrenceDiagram (Within.refl d.pasting) n α d.isSubmoleculeOf_boundary_inl)
      (d.pasting.boundary n α) :=
  occurrence (Within.refl d.pasting) n α d.isSubmoleculeOf_boundary_inl

noncomputable def occIn (u : RoundPastingDiagram X)
    (hb : (d.pasting.boundary n α).Equiv (u.boundary n α)) :
    Within (occurrenceDiagram (Within.refl d.pasting) n α d.isSubmoleculeOf_boundary_inl)
      (u.boundary n α) :=
  d.copySub.trans (Within.ofEquiv hb)

theorem isPastingAtIn_trans {m : PastingDiagram X} (W : Within d.pasting m) :
    IsPastingAtIn m.shape.ogp n α
      ((Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
          d.rewritable.isSubmoleculeOf d.equiv).trans W).image
      ((Within.pasteAtInr e.toPastingDiagram u'.toPastingDiagram n α d.occ
          d.rewritable.isSubmoleculeOf d.equiv).trans W).image
      W.image := by
  rw [Within.image_trans, Within.image_trans]
  exact (Within.isPastingAtIn_pasteAt e.toPastingDiagram u'.toPastingDiagram n α d.occ
      d.rewritable.isSubmoleculeOf d.equiv).map W.emb

theorem occIn_image (u : RoundPastingDiagram X)
    (hb : (d.pasting.boundary n α).Equiv (u.boundary n α)) :
    (d.occIn u hb).image = OGP.map hb.iso.hom d.copySub.image :=
  Within.image_trans _ _

end PasteAtData

structure Geometry {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X} (d : PasteAtData α n e u')
    (u w : RoundPastingDiagram X) (β : Bool) where
  wP : Within d.pasting w.toPastingDiagram
  wU : Within u.toPastingDiagram w.toPastingDiagram
  image_wP : wP.image = w.shape.ogp.boundary ⊤ (n + 1) β
  image_wU : wU.image = w.shape.ogp.boundary ⊤ (n + 1) (!β)
  dim_w : w.dim = n + 2

namespace Geometry

variable {α : Bool} {n : ℕ} {e u' u w : RoundPastingDiagram X} {d : PasteAtData α n e u'} {β : Bool}

noncomputable def ofHasBdry
    (ht : HasBdry β (n + 1) w.toPastingDiagram d.pasting u.toPastingDiagram) :
    Geometry d u w β where
  wP := (Within.ofEquiv (ht.side.symm)).trans
    (Within.boundary w.toPastingDiagram (n + 1) β)
  wU := (Within.ofEquiv (ht.other.symm)).trans
    (Within.boundary w.toPastingDiagram (n + 1) (!β))
  image_wP := by
    rw [Within.image_trans, Within.image_ofEquiv]; exact Within.image_boundary _ _ _
  image_wU := by
    rw [Within.image_trans, Within.image_ofEquiv]; exact Within.image_boundary _ _ _
  dim_w := ht.dim_h

variable (g : Geometry d u w β)

noncomputable def withinE : Within e.toPastingDiagram w.toPastingDiagram :=
  (Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ d.rewritable.isSubmoleculeOf
      d.equiv).trans g.wP

noncomputable def withinSol : Within u'.toPastingDiagram w.toPastingDiagram :=
  (Within.pasteAtInr e.toPastingDiagram u'.toPastingDiagram n α d.occ d.rewritable.isSubmoleculeOf
      d.equiv).trans g.wP

theorem isPastingAtIn :
    IsPastingAtIn w.shape.ogp n α g.withinE.image g.withinSol.image
      (w.shape.ogp.boundary ⊤ (n + 1) β) := by
  rw [← g.image_wP]
  exact d.isPastingAtIn_trans g.wP

theorem boundary_image_wU :
    w.shape.ogp.boundary g.wU.image n α =
      w.shape.ogp.boundary (w.shape.ogp.boundary ⊤ (n + 1) β) n α := by
  have hg := IsMoleculeIn.isGlobular w.shape.isMolecule
  rw [g.image_wU, hg n (n + 1) (Nat.lt_succ_self n) α (!β), hg n (n + 1) (Nat.lt_succ_self n) α β]

theorem isSubmoleculeOf_boundary_withinE :
    IsSubmoleculeOf w.shape.ogp (w.shape.ogp.boundary g.withinE.image n α)
      (w.shape.ogp.boundary g.wU.image n α) := by
  rw [g.boundary_image_wU]
  exact g.isPastingAtIn.isSubmoleculeOf_boundary_left

noncomputable def occ :
    Within (occurrenceDiagram g.wU n α g.isSubmoleculeOf_boundary_withinE) (u.boundary n α) :=
  occurrence g.wU n α g.isSubmoleculeOf_boundary_withinE

theorem image_occ :
    (g.occ.trans ((Within.boundary u.toPastingDiagram n α).trans g.wU)).image
      = w.shape.ogp.boundary g.withinE.image n α :=
  image_occurrence g.wU n α g.isSubmoleculeOf_boundary_withinE

include g in
theorem equiv_boundary_not_sol : (u'.boundary n (!α)).Equiv (u.boundary n (!α)) := by
  have hb := g.isPastingAtIn.boundary_not
  refine Within.equiv_of_image_eq ((Within.boundary u'.toPastingDiagram n (!α)).trans g.withinSol)
    ((Within.boundary u.toPastingDiagram n (!α)).trans g.wU) ?_
  have hg := IsMoleculeIn.isGlobular w.shape.isMolecule
  rw [Within.image_boundary_trans, Within.image_boundary_trans, ← hb, g.image_wU,
    hg n (n + 1) (Nat.lt_succ_self n) (!α) β, hg n (n + 1) (Nat.lt_succ_self n) (!α) (!β)]

theorem equiv_boundary_sol {J : PastingDiagram X} (j : Within J (u.boundary n α))
    (hj : (u.boundary n α).shape.ogp.IsRewritableSubmolecule j.image ⊤)
    (hje : J.Equiv (e.boundary n α))
    (hJ : (j.trans ((Within.boundary u.toPastingDiagram n α).trans g.wU)).image =
        w.shape.ogp.boundary g.withinE.image n α) :
    (u'.boundary n α).Equiv ((u.boundary n α).substitute j hj
      ⟨e.boundary n (!α), isRound_boundary_of_isRound e.isRound n (!α)⟩
      ((parallel_boundary e.isRound d.dim_e α (!α)).of_equiv_left hje)) := by
  have hc := g.isPastingAtIn
  have hs := hc.isSubstitutionIn_boundary (g.withinE.round_image_iff.2 e.isRound)
    (by rw [g.withinE.krullDim_image]; exact_mod_cast d.dim_e)
    (by rw [g.withinSol.krullDim_image, d.dim_u']; exact_mod_cast n.le_succ)
  rw [← g.boundary_image_wU, ← hJ] at hs
  have hs' := hs.symm
  rw [hc.inf_eq] at hs'
  refine PastingDiagram.Equiv.trans
    (((Within.boundary u'.toPastingDiagram n α).trans g.withinSol).equiv_restrictTo_of_eq
      (Within.image_boundary_trans _ _ _)
      (g.withinSol.isMoleculeIn_image.boundary n α))
    ((equiv_substitute_of_within j hj _ _
      ((Within.boundary u.toPastingDiagram n α).trans g.wU)
      ((Within.boundary e.toPastingDiagram n (!α)).trans g.withinE) ?_ _).symm)
  rw [Within.image_boundary_trans, Within.image_boundary_trans]
  exact hs'

include g in
theorem hb : (d.pasting.boundary n α).Equiv (u.boundary n α) :=
  Within.equiv_of_image_eq ((Within.boundary d.pasting n α).trans g.wP)
    ((Within.boundary u.toPastingDiagram n α).trans g.wU) (by
      have hg := IsMoleculeIn.isGlobular w.shape.isMolecule
      rw [Within.image_boundary_trans, Within.image_boundary_trans, g.image_wP, g.image_wU,
        hg n (n + 1) (Nat.lt_succ_self n) α β, hg n (n + 1) (Nat.lt_succ_self n) α (!β)])

theorem occ_image : g.occ.image = (d.occIn u g.hb).image := by
  have hg := IsMoleculeIn.isGlobular w.shape.isMolecule
  have hiso : ∀ x, ((Within.boundary u.toPastingDiagram n α).trans g.wU).emb (g.hb.iso.hom x) =
      ((Within.boundary d.pasting n α).trans g.wP).emb x :=
    Within.emb_apply_eq_of_image_eq
      ((Within.ofEquiv g.hb).trans ((Within.boundary u.toPastingDiagram n α).trans g.wU))
      ((Within.boundary d.pasting n α).trans g.wP) (by
        rw [Within.image_trans, Within.image_ofEquiv, ← Within.image,
          Within.image_boundary_trans, Within.image_boundary_trans, g.image_wP, g.image_wU,
          hg n (n + 1) (Nat.lt_succ_self n) α (!β), hg n (n + 1) (Nat.lt_succ_self n) α β])
  have hEw : w.shape.ogp.boundary g.withinE.image n α =
      OGP.map g.wP.emb (d.pasting.shape.ogp.boundary
        (Within.pasteAtInl e.toPastingDiagram u'.toPastingDiagram n α d.occ
            d.rewritable.isSubmoleculeOf d.equiv).image n α) := by
    rw [withinE, Within.image_trans, map_boundary]
  rw [PasteAtData.occIn_image, occ, image_occurrence_eq_comap, PasteAtData.copySub,
    image_occurrence_eq_comap, hEw]
  refine SetLike.ext fun y => ⟨fun hy => ?_, ?_⟩
  · obtain ⟨z, hz, hzy⟩ := mem_map.1 (mem_comap.1 hy)
    refine mem_map.2 ⟨g.hb.iso.inv y, mem_comap.2 ?_, Iso.inv_hom_id_apply _ _⟩
    rw [← Iso.inv_hom_id_apply g.hb.iso y, hiso] at hzy
    convert hz using 1
    exact (IsInclusion.injective (f := g.wP.emb) hzy).symm
  · rintro ⟨x, hx, rfl⟩
    exact mem_comap.2 (mem_map.2 ⟨_, mem_comap.1 hx, (hiso x).symm⟩)

end Geometry

structure Equation (α : Bool) (n : ℕ) (e u : RoundPastingDiagram X) where
  dim_e : e.dim = n + 1
  dim_u : u.dim = n + 1
  sub : PastingDiagram X
  occ : Within sub (u.boundary n α)
  rewritable : (u.boundary n α).shape.ogp.IsRewritableSubmolecule occ.image ⊤
  equiv : sub.Equiv (e.boundary n α)

theorem Equation.parallel_occ {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    (eq : Equation α n e u) :
    Parallel ⟨eq.sub, eq.occ.round_image_iff.1 eq.rewritable.isRound⟩
      ⟨e.boundary n (!α), isRound_boundary_of_isRound e.isRound n (!α)⟩ :=
  (parallel_boundary e.isRound eq.dim_e α (!α)).of_equiv_left eq.equiv

def Equation.ofBoundary {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (he : e.dim = n + 1)
    (hu : u.dim = n + 1) (h : (u.boundary n α).Equiv (e.boundary n α)) : Equation α n e u :=
  ⟨he, hu, _, Within.refl _, (Within.refl _).isRewritableSubmolecule_image_iff.2
    ⟨Within.isSubmoleculeOf_image_refl _, isRound_boundary_of_isRound u.isRound n α, rfl⟩, h⟩

def Equation.ofEquiv {α : Bool} {n : ℕ} {e u P : RoundPastingDiagram X} (eq : Equation α n e u)
    (hP : P.dim = n + 1) (h : (e.boundary n α).Equiv (P.boundary n α)) : Equation α n P u :=
  ⟨hP, eq.dim_u, eq.sub, eq.occ, eq.rewritable, eq.equiv.trans h⟩

def Compat {α : Bool} {n : ℕ} {e u u' : RoundPastingDiagram X} (eq : Equation α n e u)
    (d : PasteAtData α n e u') : Prop :=
  ∀ hb : (d.pasting.boundary n α).Equiv (u.boundary n α), eq.occ.image = (d.occIn u hb).image

theorem Geometry.compat_image {α : Bool} {n : ℕ} {e u u' w : RoundPastingDiagram X} {β : Bool}
    {d : PasteAtData α n e u'} {eq : Equation α n e u} (g : Geometry d u w β) (hc : Compat eq d) :
    (eq.occ.trans ((Within.boundary u.toPastingDiagram n α).trans g.wU)).image
      = w.shape.ogp.boundary g.withinE.image n α := by
  rw [Within.image_trans, hc g.hb, ← g.occ_image, ← Within.image_trans]
  exact g.image_occ

theorem Geometry.compat_of_image {α : Bool} {n : ℕ} {e u u' w : RoundPastingDiagram X} {β : Bool}
    {d : PasteAtData α n e u'} {eq : Equation α n e u} (g : Geometry d u w β)
    (hJ : (eq.occ.trans ((Within.boundary u.toPastingDiagram n α).trans g.wU)).image =
        w.shape.ogp.boundary g.withinE.image n α) : Compat eq d := by
  intro hb
  have hiso : hb.iso = g.hb.iso :=
    @Subsingleton.elim _ (IsMolecule.subsingleton_iso (d.pasting.boundary n α).shape.isMolecule)
      _ _
  rw [PasteAtData.occIn_image, hiso, ← PasteAtData.occIn_image, ← g.occ_image]
  have h1 := hJ.trans g.image_occ.symm
  rw [Within.image_trans, Within.image_trans] at h1
  exact map_injective ((Within.boundary u.toPastingDiagram n α).trans g.wU).emb h1

theorem Geometry.equiv_boundary_sol_of_compat {α : Bool} {n : ℕ} {e u u' w : RoundPastingDiagram X}
    {β : Bool} {d : PasteAtData α n e u'} {eq : Equation α n e u} (g : Geometry d u w β)
    (hc : Compat eq d) :
    (u'.boundary n α).Equiv ((u.boundary n α).substitute eq.occ eq.rewritable
      ⟨e.boundary n (!α), isRound_boundary_of_isRound e.isRound n (!α)⟩ eq.parallel_occ) :=
  g.equiv_boundary_sol eq.occ eq.rewritable eq.equiv (g.compat_image hc)

structure SideWitness (β : Bool) (A : Set (RoundPastingDiagram X)) {α : Bool} {n : ℕ}
    {e u' : RoundPastingDiagram X} (d : PasteAtData α n e u') (u : RoundPastingDiagram X) where
  witness : RoundPastingDiagram X
  mem : witness ∈ A
  hasBdry : HasBdry β (n + 1) witness.toPastingDiagram d.pasting u.toPastingDiagram

namespace SideWitness

variable {β : Bool} {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
  {e u' : RoundPastingDiagram X} {d : PasteAtData α n e u'} {u : RoundPastingDiagram X}

def mono {B : Set (RoundPastingDiagram X)} (hAB : A ⊆ B) (s : SideWitness β A d u) :
    SideWitness β B d u :=
  { s with mem := hAB s.mem }

noncomputable def geometry (s : SideWitness β A d u) : Geometry d u s.witness β :=
  Geometry.ofHasBdry s.hasBdry

end SideWitness

structure LaxSolution (A : Set (RoundPastingDiagram X)) {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} (eq : Equation α n e u) where
  sol : RoundPastingDiagram X
  data : PasteAtData α n e sol
  compat : Compat eq data
  lax : SideWitness false A data u

structure UnbiasedSolution (A : Set (RoundPastingDiagram X)) {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} (eq : Equation α n e u) where
  sol : RoundPastingDiagram X
  data : PasteAtData α n e sol
  compat : Compat eq data
  side : ∀ β, SideWitness β A data u

def UnbiasedSolution.toLax {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} {eq : Equation α n e u} (s : UnbiasedSolution A eq) :
    LaxSolution A eq :=
  ⟨s.sol, s.data, s.compat, s.side false⟩

def UnbiasedSolution.ofSides {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} {eq : Equation α n e u} (sol : RoundPastingDiagram X)
    (data : PasteAtData α n e sol) (compat : Compat eq data) {β : Bool}
    (s₁ : SideWitness β A data u) (s₂ : SideWitness (!β) A data u) : UnbiasedSolution A eq :=
  ⟨sol, data, compat, fun γ => if h : γ = β then h ▸ s₁ else Bool.eq_not.2 h ▸ s₂⟩

def UnbiasedSolution.mono {A B : Set (RoundPastingDiagram X)} (hAB : A ⊆ B) {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} {eq : Equation α n e u} (s : UnbiasedSolution A eq) :
    UnbiasedSolution B eq :=
  ⟨s.sol, s.data, s.compat, fun β => (s.side β).mono hAB⟩

def LaxSolution.mono {A B : Set (RoundPastingDiagram X)} (hAB : A ⊆ B) {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} {eq : Equation α n e u} (s : LaxSolution A eq) :
    LaxSolution B eq :=
  ⟨s.sol, s.data, s.compat, s.lax.mono hAB⟩

def solutionOperator (X : DiagSet.{u}) :
    Set (RoundPastingDiagram X) →o Set (RoundPastingDiagram X) where
  toFun A := {e | 0 < e.dim ∧ ∀ (α : Bool) (n : ℕ) (u : RoundPastingDiagram X)
    (eq : Equation α n e u), Nonempty (LaxSolution A eq)}
  monotone' _ _ hAB _ he := ⟨he.1, fun α n u eq => (he.2 α n u eq).elim fun s => ⟨s.mono hAB⟩⟩

def eqvSolutions (X : DiagSet.{u}) : Set (RoundPastingDiagram X) := (solutionOperator X).gfp

theorem solutionOperator_eqvSolutions :
    solutionOperator X (eqvSolutions X) = eqvSolutions X :=
  (solutionOperator X).map_gfp

theorem subset_eqvSolutions {A : Set (RoundPastingDiagram X)} (h : A ⊆ solutionOperator X A) :
    A ⊆ eqvSolutions X :=
  (solutionOperator X).le_gfp h

def UnbiasedSide (B : Set (RoundPastingDiagram X)) (α : Bool) (e : RoundPastingDiagram X) :
    Prop :=
  ∀ (n : ℕ) (u : RoundPastingDiagram X) (eq : Equation α n e u), Nonempty (UnbiasedSolution B eq)

def Unbiased (A : Set (RoundPastingDiagram X)) (e : RoundPastingDiagram X) : Prop :=
  ∀ α : Bool, UnbiasedSide A α e

inductive TClosure (A : Set (RoundPastingDiagram X)) : Set (RoundPastingDiagram X)
  | base {a : RoundPastingDiagram X} (ha : a ∈ A) : TClosure A a
  | comp {h u v w : RoundPastingDiagram X} {n : ℕ} {α : Bool} (d : PasteAtData α n u v)
      (ht : HasBdry false (n + 1) h.toPastingDiagram d.pasting w.toPastingDiagram)
      (hh : TClosure A h) (hu : TClosure A u) (hv : TClosure A v) : TClosure A w
  | div {h u v w : RoundPastingDiagram X} {n : ℕ} {α : Bool} (d : PasteAtData α n u v)
      (ht : HasBdry false (n + 1) h.toPastingDiagram d.pasting w.toPastingDiagram)
      (hh : TClosure A h) (hu : TClosure A u) (hw : TClosure A w) : TClosure A v

theorem TClosure.mono {A B : Set (RoundPastingDiagram X)} (hAB : A ⊆ B) :
    TClosure A ⊆ TClosure B := by
  intro a h
  induction h with
  | base ha => exact .base (hAB ha)
  | comp d ht _ _ _ ih1 ih2 ih3 => exact .comp d ht ih1 ih2 ih3
  | div d ht _ _ _ ih1 ih2 ih3 => exact .div d ht ih1 ih2 ih3

theorem subset_tClosure (A : Set (RoundPastingDiagram X)) : A ⊆ TClosure A :=
  fun _ ha => .base ha

theorem TClosure.trans {A : Set (RoundPastingDiagram X)} :
    TClosure (TClosure A) ⊆ TClosure A := by
  intro a h
  induction h with
  | base ha => exact ha
  | comp d ht _ _ _ ih1 ih2 ih3 => exact .comp d ht ih1 ih2 ih3
  | div d ht _ _ _ ih1 ih2 ih3 => exact .div d ht ih1 ih2 ih3

theorem exists_inverse_of_mem_solutionOperator {A : Set (RoundPastingDiagram X)}
    {e : RoundPastingDiagram X} (he : e ∈ A) (hE : e ∈ solutionOperator X A) {n : ℕ}
    (hn : e.dim = n + 1) :
    ∃ e' : RoundPastingDiagram X, TClosure A e' ∧
      HasBdry false n e'.toPastingDiagram (e.boundary n true) (e.boundary n false) := by
  have hr₀ : (e.boundary n false).IsRound := isRound_boundary_of_isRound e.isRound n false
  let eq₁ : Equation false n e e :=
    ⟨hn, hn, _, Within.refl _, (Within.refl _).isRewritableSubmolecule_image_iff.2
      ⟨Within.isSubmoleculeOf_image_refl _, hr₀, rfl⟩, .refl _⟩
  obtain ⟨s₁⟩ := hE.2 false n e eq₁
  have hu₁ : TClosure A s₁.sol :=
    TClosure.div s₁.data (s₁.lax.hasBdry) (.base s₁.lax.mem)
      (.base he) (.base he)
  have e₂ : (s₁.sol.boundary n true).Equiv (e.boundary n true) :=
    s₁.lax.geometry.equiv_boundary_not_sol
  have e₁ : (s₁.sol.boundary n false).Equiv (e.boundary n true) :=
    (s₁.lax.geometry.equiv_boundary_sol_of_compat s₁.compat).trans
      (equiv_substitute_of_image_eq_univ _ _ _ _ (Within.image_refl _))
  let eq₂ : Equation true n e s₁.sol :=
    ⟨hn, s₁.data.dim_u', _, (Within.refl _).trans (Within.ofEquiv e₂.symm),
      ((Within.refl _).isRewritableSubmolecule_image_trans_ofEquiv_iff _).2
        ((Within.refl _).isRewritableSubmolecule_image_iff.2
          ⟨Within.isSubmoleculeOf_image_refl _, isRound_boundary_of_isRound e.isRound n true,
            rfl⟩),
      .refl _⟩
  obtain ⟨s₂⟩ := hE.2 true n s₁.sol eq₂
  refine ⟨s₂.sol, TClosure.div s₂.data (s₂.lax.hasBdry)
    (.base s₂.lax.mem) (.base he) hu₁, s₂.data.dim_u',
    dim_boundary e.toPastingDiagram (by omega) true,
    dim_boundary e.toPastingDiagram (by omega) false, ?_, ?_⟩
  · exact s₂.lax.geometry.equiv_boundary_not_sol.trans e₁
  · refine (s₂.lax.geometry.equiv_boundary_sol_of_compat s₂.compat).trans
      (equiv_substitute_of_image_eq_univ _ _ _ _ ?_)
    change ((Within.refl _).trans (Within.ofEquiv e₂.symm)).image = ⊤
    rw [Within.image_trans, Within.image_refl]
    exact Within.image_ofEquiv _

theorem TClosure.pasteAt {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {u v : RoundPastingDiagram X}
    {n : ℕ} {α : Bool} (d : PasteAtData α n u v) (hu : TClosure A u) (hv : TClosure A v) :
    TClosure A d.round :=
  TClosure.comp d (h := d.isRound_pasting.unit)
    (hasType_unit d.dim_pasting) (.base (hDgn _ (isDegenerate_unit _))) hu hv

theorem eqvSolutions_subset_solutionOperator_tClosure :
    eqvSolutions X ⊆ solutionOperator X (TClosure (eqvSolutions X)) := by
  have h := (solutionOperator X).monotone (subset_tClosure (eqvSolutions X))
  rw [solutionOperator_eqvSolutions] at h
  exact h

theorem unbiased_tClosure_eqvSolutions {e : RoundPastingDiagram X} (he : e ∈ eqvSolutions X) :
    Unbiased (TClosure (eqvSolutions X)) e := by
  intro α n u eq
  have hE : e ∈ solutionOperator X (eqvSolutions X) := by
    rw [solutionOperator_eqvSolutions]; exact he
  obtain ⟨s⟩ := hE.2 α n u eq
  have hh : s.lax.witness ∈ solutionOperator X (eqvSolutions X) := by
    rw [solutionOperator_eqvSolutions]; exact s.lax.mem
  obtain ⟨h', hT, ht'⟩ :=
    exists_inverse_of_mem_solutionOperator s.lax.mem hh s.lax.hasBdry.dim_h
  refine ⟨UnbiasedSolution.ofSides s.sol s.data s.compat (β := false) (s.lax.mono
    (subset_tClosure _)) ⟨h', hT, ht'.symm.of_equiv_side s.lax.hasBdry.side
      |>.of_equiv_other s.lax.hasBdry.other⟩⟩

end Atoms.Diagrammatic
