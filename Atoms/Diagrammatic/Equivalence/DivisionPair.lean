import Atoms.Diagrammatic.Equivalence.Composition
import Atoms.Diagrammatic.Equivalence.Inverse

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def Equation.trivial (e : RoundPastingDiagram X) {n : ℕ} (he : e.dim = n + 1) (α : Bool) :
    Equation α n e e :=
  Equation.ofBoundary he he (.refl _)

namespace PasteAtData

variable {α : Bool} {n : ℕ} {v e : RoundPastingDiagram X} (d : PasteAtData α n v e)

def unitPasting : PasteAtData α n (d.occ.round_image_iff.1 d.rewritable.isRound).unit e :=
  have hn : d.sub.dim = n :=
    Within.dim_eq_of_isRewritableSubmolecule_boundary d.rewritable (by rw [d.dim_u']; omega)
  ⟨by change d.sub.unit.dim = n + 1; rw [dim_unit, hn], d.dim_u', d.sub, d.occ,
    d.rewritable, boundary_unit hn (!α)⟩

end PasteAtData

structure UnitAmbient {α : Bool} {n : ℕ} {v e : RoundPastingDiagram X} (d : PasteAtData α n v e)
    where
  side : Bool
  K : RoundPastingDiagram X
  hasBdry : HasBdry side (n + 1) K.toPastingDiagram d.unitPasting.pasting e.toPastingDiagram

structure PairMember {α : Bool} {n : ℕ} {v e : RoundPastingDiagram X} (d : PasteAtData α n v e)
    (w : RoundPastingDiagram X) (β : Bool) where
  k : RoundPastingDiagram X
  hasBdry : HasBdry β (n + 1) k.toPastingDiagram w.toPastingDiagram d.pasting

namespace DivisionPair

variable {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ} {v e w : RoundPastingDiagram X}
  (d : PasteAtData α n v e)
  (s : UnbiasedSolution (TClosure A) (inverseEquation v d.dim_e (!α)))
  (hwd : w.dim = n + 1) (hw : (w.boundary n α).Equiv (d.pasting.boundary n α))

noncomputable def occW :
    Within ((Equation.trivial w hwd α).sub.restrictTo
      (ComposePair.isSubmoleculeOf_comap (Equation.trivial w hwd α) d hw).isMoleculeIn)
      (w.boundary n α) :=
  ComposePair.κOf (Equation.trivial w hwd α) d hw

noncomputable def inversePasting : PasteAtData α n s.sol w :=
  ⟨s.data.dim_u', hwd, _, occW d hwd hw,
    ComposePair.isRewritableSubmolecule_image_κOf (Equation.trivial w hwd α) d hw,
    (InverseSolution.equiv_boundary_sol d.dim_e α s).trans
      (ComposePair.equiv_κOf (Equation.trivial w hwd α) d hw).symm⟩

abbrev composite : PasteAtData α n s.sol v :=
  compositeData (α := α) s.data.dim_u' (InverseSolution.hasType_inverse d.dim_e α s)

abbrev invData :
    InvertorData (TClosure A)
      (Equation.trivial s.sol s.data.dim_u' α) :=
  InverseSolution.invertorData d.dim_e α s (Equation.trivial s.sol s.data.dim_u' α)

theorem equiv_unit_occ : (s.sol.boundary n α).unit.Equiv
    (d.occ.round_image_iff.1 d.rewritable.isRound).unit.toPastingDiagram :=
  ((InverseSolution.equiv_boundary_not_sol d.dim_e α s).trans d.equiv).unit

variable (U : UnitAmbient d)

private noncomputable def wP₀ : Within d.unitPasting.pasting U.K.toPastingDiagram :=
  (Within.ofEquiv (U.hasBdry.side.symm)).trans
    (Within.boundary U.K.toPastingDiagram (n + 1) U.side)

private theorem image_wP₀ :
    (wP₀ d U).image = U.K.shape.ogp.boundary ⊤ (n + 1) U.side := by
  change ((Within.ofEquiv (U.hasBdry.side.symm)).trans
    (Within.boundary U.K.toPastingDiagram (n + 1) U.side)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary _ _ _

private noncomputable def wU₀ : Within
    (d.occ.round_image_iff.1 d.rewritable.isRound).unit.toPastingDiagram U.K.toPastingDiagram :=
  d.unitPasting.pasteAtInl.trans (wP₀ d U)

private noncomputable def wE₀ : Within e.toPastingDiagram U.K.toPastingDiagram :=
  d.unitPasting.pasteAtInr.trans (wP₀ d U)

private theorem image_wU₀ :
    (wU₀ d U).image = OGP.map (wP₀ d U).emb d.unitPasting.pasteAtInl.image :=
  Within.image_trans _ _

private theorem image_wE₀ :
    (wE₀ d U).image = OGP.map (wP₀ d U).emb d.unitPasting.pasteAtInr.image :=
  Within.image_trans _ _

private theorem isPastingAtIn_wU₀ :
    IsPastingAtIn U.K.shape.ogp n α (wU₀ d U).image (wE₀ d U).image
      (U.K.shape.ogp.boundary ⊤ (n + 1) U.side) := by
  rw [← image_wP₀]
  exact d.unitPasting.isPastingAtIn_trans (wP₀ d U)

private theorem image_occ_wE₀ :
    (d.occ.trans
      ((Within.boundary e.toPastingDiagram n α).trans (wE₀ d U))).image =
      (wU₀ d U).image ⊓ (wE₀ d U).image := by
  have h : (d.occ.trans
      ((Within.boundary e.toPastingDiagram n α).trans d.unitPasting.pasteAtInr)).image =
      d.unitPasting.pasteAtInl.image ⊓ d.unitPasting.pasteAtInr.image :=
    d.unitPasting.image_occ_pasteAtInr
  have e1 : (d.occ.trans
      ((Within.boundary e.toPastingDiagram n α).trans (wE₀ d U))).image =
      OGP.map (wP₀ d U).emb (d.occ.trans
        ((Within.boundary e.toPastingDiagram n α).trans d.unitPasting.pasteAtInr)).image := by
    rw [← Within.image_trans]
    rfl
  rw [e1, h, OGP.map_inf, ← image_wU₀, ← image_wE₀]

private noncomputable def wU₀' : Within (s.sol.boundary n α).unit U.K.toPastingDiagram :=
  (Within.ofEquiv (equiv_unit_occ d s)).trans (wU₀ d U)

private theorem image_wU₀' : (wU₀' d s U).image = (wU₀ d U).image :=
  Within.image_ofEquiv_trans _ _

private theorem isSubmoleculeOf_wU₀' :
    IsSubmoleculeOf U.K.shape.ogp (wU₀' d s U).image
      (U.K.shape.ogp.boundary ⊤ (n + 1) U.side) := by
  rw [image_wU₀']
  exact (isPastingAtIn_wU₀ d U).isSubmoleculeOf_left

private noncomputable def glue₁ :
    GlueStep (wU₀' d s U) ((invData d s).z U.side) (composite d s).pasting U.side n :=
  glueStep U.hasBdry.dim_h (isSubmoleculeOf_wU₀' d s U) ((invData d s).hasBdry U.side)

private noncomputable abbrev K₁ : RoundPastingDiagram X := (glue₁ d s U).K'

private noncomputable def wE₁ : Within e.toPastingDiagram (K₁ d s U).toPastingDiagram :=
  (wE₀ d U).trans (glue₁ d s U).wK

private noncomputable def wU₁ : Within (s.sol.boundary n α).unit (K₁ d s U).toPastingDiagram :=
  (wU₀' d s U).trans (glue₁ d s U).wK

private noncomputable def wInv₁ : Within s.sol.toPastingDiagram (K₁ d s U).toPastingDiagram :=
  (composite d s).pasteAtInl.trans (glue₁ d s U).wP

private noncomputable def wV₁ : Within v.toPastingDiagram (K₁ d s U).toPastingDiagram :=
  (composite d s).pasteAtInr.trans (glue₁ d s U).wP

private theorem image_wE₁ : (wE₁ d s U).image = OGP.map (glue₁ d s U).wK.emb (wE₀ d U).image :=
  Within.image_trans _ _

private theorem image_wU₁ : (wU₁ d s U).image = OGP.map (glue₁ d s U).wK.emb (wU₀' d s U).image :=
  Within.image_trans _ _

private theorem image_wInv₁ :
    (wInv₁ d s U).image = OGP.map (glue₁ d s U).wP.emb (composite d s).pasteAtInl.image :=
  Within.image_trans _ _

private theorem image_wV₁ :
    (wV₁ d s U).image = OGP.map (glue₁ d s U).wP.emb (composite d s).pasteAtInr.image :=
  Within.image_trans _ _

private theorem krullDim_wU₁ : krullDim (wU₁ d s U).image = n + 1 := by
  rw [Within.krullDim_image, dim_unit,
    dim_boundary s.sol.toPastingDiagram (by rw [s.data.dim_u']; omega) α]
  norm_cast

private theorem isPastingAtIn_wP₁_wE₁ :
    IsPastingAtIn (K₁ d s U).shape.ogp n α (glue₁ d s U).wP.image (wE₁ d s U).image
      ((K₁ d s U).shape.ogp.boundary ⊤ (n + 1) U.side) := by
  have h := (isPastingAtIn_wU₀ d U).map (glue₁ d s U).wK.emb
  rw [← image_wE₁, ← (glue₁ d s U).wK.boundary_image, ← image_wU₀'] at h
  exact h.subst_left_self (glue₁ d s U).subst
    (by rw [← image_wU₁, krullDim_wU₁]; exact_mod_cast n.lt_succ_self)

private theorem isPastingAtIn_wInv₁_wV₁ :
    IsPastingAtIn (K₁ d s U).shape.ogp n α (wInv₁ d s U).image (wV₁ d s U).image
      (glue₁ d s U).wP.image := by
  exact (composite d s).isPastingAtIn_trans (glue₁ d s U).wP

private theorem image_wP₁ : (glue₁ d s U).wP.image = (wInv₁ d s U).image ⊔ (wV₁ d s U).image :=
  (isPastingAtIn_wInv₁_wV₁ d s U).eq_sup

private theorem inter_wInv₁_wV₁ :
    (wInv₁ d s U).image ⊓ (wV₁ d s U).image =
      (K₁ d s U).shape.ogp.boundary (wV₁ d s U).image n α := by
  have h := congrArg (OGP.map (glue₁ d s U).wP.emb)
    (inter_eq_boundary_pasteAt_of_image_univ _ _ n α (composite d s).occ
      (composite d s).rewritable.isSubmoleculeOf (Within.image_refl _) (composite d s).equiv)
  rw [OGP.map_inf, map_boundary, ← image_wInv₁, ← image_wV₁] at h
  exact h

private theorem assoc₁ :
    IsPastingAtIn (K₁ d s U).shape.ogp n α (wV₁ d s U).image (wE₁ d s U).image
        ((wV₁ d s U).image ⊔ (wE₁ d s U).image) ∧
      IsPastingAtIn (K₁ d s U).shape.ogp n α (wInv₁ d s U).image
        ((wV₁ d s U).image ⊔ (wE₁ d s U).image)
        ((K₁ d s U).shape.ogp.boundary ⊤ (n + 1) U.side) := by
  have h₁ : IsPastingAtIn (K₁ d s U).shape.ogp n α (wInv₁ d s U).image (wV₁ d s U).image
      ((wInv₁ d s U).image ⊔ (wV₁ d s U).image) := by
    rw [← image_wP₁]; exact isPastingAtIn_wInv₁_wV₁ d s U
  have h₂ : IsPastingAtIn (K₁ d s U).shape.ogp n α ((wInv₁ d s U).image ⊔ (wV₁ d s U).image)
      (wE₁ d s U).image ((K₁ d s U).shape.ogp.boundary ⊤ (n + 1) U.side) := by
    rw [← image_wP₁]; exact isPastingAtIn_wP₁_wE₁ d s U
  exact h₁.assoc_right h₂

private theorem boundary_wU₁_eq :
    (K₁ d s U).shape.ogp.boundary (wU₁ d s U).image n (!α) =
      (K₁ d s U).shape.ogp.boundary (wV₁ d s U).image n (!α) := by
  have hb := (glue₁ d s U).subst.bdry_eq (!α)
  have hdP : krullDim (glue₁ d s U).wP.image = n + 1 := by
    rw [(glue₁ d s U).wP.krullDim_image]; exact_mod_cast (composite d s).dim_pasting
  have hdU : krullDim (OGP.map (glue₁ d s U).wK.emb (wU₀' d s U).image) = n + 1 := by
    rw [← image_wU₁, krullDim_wU₁]
  rw [bdry_eq_boundary hdP, bdry_eq_boundary hdU, ← image_wU₁] at hb
  rw [← hb]
  exact (isPastingAtIn_wInv₁_wV₁ d s U).boundary_not

private theorem image_occ_wE₁ :
    (d.occ.trans
      ((Within.boundary e.toPastingDiagram n α).trans (wE₁ d s U))).image =
      (wV₁ d s U).image ⊓ (wE₁ d s U).image := by
  have e1 : (d.occ.trans
      ((Within.boundary e.toPastingDiagram n α).trans (wE₁ d s U))).image =
      OGP.map (glue₁ d s U).wK.emb (d.occ.trans
        ((Within.boundary e.toPastingDiagram n α).trans (wE₀ d U))).image := by
    rw [← Within.image_trans]
    rfl
  rw [e1, image_occ_wE₀, OGP.map_inf, ← image_wE₁, ← image_wU₀', ← image_wU₁]
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU, hxE⟩ := LowerSet.mem_inf_iff.1 hx
    refine LowerSet.mem_inf_iff.2 ⟨?_, hxE⟩
    have h1 : x ∈ (K₁ d s U).shape.ogp.boundary (wU₁ d s U).image n (!α) := by
      have h2 : x ∈ (wU₁ d s U).image ⊓ (wE₁ d s U).image := LowerSet.mem_inf_iff.2 ⟨hxU, hxE⟩
      rw [image_wU₁, image_wE₁, ← OGP.map_inf, image_wU₀', (isPastingAtIn_wU₀ d U).inf_eq,
        map_boundary, ← image_wU₀', ← image_wU₁] at h2
      exact h2
    rw [boundary_wU₁_eq] at h1
    exact boundary_le _ _ _ h1
  · intro x hx
    obtain ⟨hxV, hxE⟩ := LowerSet.mem_inf_iff.1 hx
    refine LowerSet.mem_inf_iff.2 ⟨?_, hxE⟩
    have hk : x ∈ (glue₁ d s U).wk.image := by
      have h1 : x ∈ (glue₁ d s U).wP.image := by
        rw [image_wP₁]; exact LowerSet.mem_sup_iff.2 (Or.inr hxV)
      rw [(glue₁ d s U).image_wP] at h1
      exact boundary_le _ _ _ h1
    have hK : x ∈ (glue₁ d s U).wK.image := by
      rw [image_wE₁] at hxE
      obtain ⟨y, -, rfl⟩ := hxE
      exact (glue₁ d s U).wK.mem_image_apply y
    have h := LowerSet.mem_inf_iff.2 ⟨hk, hK⟩
    rw [(glue₁ d s U).inter, ← image_wU₁] at h
    exact h

private noncomputable def wVE₁ : Within d.pasting (K₁ d s U).toPastingDiagram :=
  Within.pasteAtOfWithin (wV₁ d s U) (wE₁ d s U)
      (assoc₁ d s U).1 d.occ d.rewritable.isSubmoleculeOf (image_occ_wE₁ d s U) d.equiv

private theorem image_wVE₁ : (wVE₁ d s U).image = (wV₁ d s U).image ⊔ (wE₁ d s U).image :=
  Within.image_pasteAtOfWithin (wV₁ d s U) (wE₁ d s U)
      (assoc₁ d s U).1 d.occ d.rewritable.isSubmoleculeOf
    (image_occ_wE₁ d s U) d.equiv

private theorem withinLeft_trans_wVE₁ : d.pasteAtInl.trans (wVE₁ d s U) = wV₁ d s U :=
  (Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin (wV₁ d s U) (wE₁ d s U)
      (assoc₁ d s U).1 d.occ d.rewritable.isSubmoleculeOf
    (image_occ_wE₁ d s U) d.equiv).1

private theorem isSubmoleculeOf_wVE₁ :
    IsSubmoleculeOf (K₁ d s U).shape.ogp (wVE₁ d s U).image
      ((K₁ d s U).shape.ogp.boundary ⊤ (n + 1) U.side) := by
  rw [image_wVE₁]
  exact (assoc₁ d s U).2.isSubmoleculeOf_right

variable (P : PairMember d w U.side)

private noncomputable def glue₂ : GlueStep (wVE₁ d s U) P.k w.toPastingDiagram U.side n :=
  glueStep (glue₁ d s U).dimK' (isSubmoleculeOf_wVE₁ d s U) P.hasBdry

private noncomputable abbrev K₂ : RoundPastingDiagram X := (glue₂ d s U P).K'

private noncomputable def wInv₂ : Within s.sol.toPastingDiagram (K₂ d s U P).toPastingDiagram :=
  (wInv₁ d s U).trans (glue₂ d s U P).wK

private noncomputable def wV₂ : Within v.toPastingDiagram (K₂ d s U P).toPastingDiagram :=
  (wV₁ d s U).trans (glue₂ d s U P).wK

private theorem image_wInv₂ :
    (wInv₂ d s U P).image = OGP.map (glue₂ d s U P).wK.emb (wInv₁ d s U).image :=
  Within.image_trans _ _

private theorem image_wV₂ :
    (wV₂ d s U P).image = OGP.map (glue₂ d s U P).wK.emb (wV₁ d s U).image :=
  Within.image_trans _ _

private theorem krullDim_wP₂ : krullDim (glue₂ d s U P).wP.image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast P.hasBdry.dim_a

private theorem krullDim_wVE₁_image :
    krullDim (OGP.map (glue₂ d s U P).wK.emb (wVE₁ d s U).image) = n + 1 := by
  rw [← Within.image_trans, Within.krullDim_image]; exact_mod_cast d.dim_pasting

private theorem isPastingAtIn_wInv₂_wP₂ :
    IsPastingAtIn (K₂ d s U P).shape.ogp n α (wInv₂ d s U P).image (glue₂ d s U P).wP.image
      ((K₂ d s U P).shape.ogp.boundary ⊤ (n + 1) U.side) := by
  have h := (assoc₁ d s U).2.map (glue₂ d s U P).wK.emb
  rw [← image_wInv₂, ← (glue₂ d s U P).wK.boundary_image, ← image_wVE₁] at h
  exact h.subst_right_self (glue₂ d s U P).subst
    (by rw [krullDim_wVE₁_image]; exact_mod_cast n.lt_succ_self)

private theorem boundary_wP₂_eq :
    (K₂ d s U P).shape.ogp.boundary (glue₂ d s U P).wP.image n α =
      (K₂ d s U P).shape.ogp.boundary (OGP.map (glue₂ d s U P).wK.emb (wVE₁ d s U).image) n α := by
  have hb := (glue₂ d s U P).subst.bdry_eq α
  rw [bdry_eq_boundary (krullDim_wP₂ d s U P), bdry_eq_boundary (krullDim_wVE₁_image d s U P)] at hb
  exact hb

private theorem image_occW_wP₂ :
    ((occW d hwd hw).trans
      ((Within.boundary w.toPastingDiagram n α).trans (glue₂ d s U P).wP)).image =
      (wInv₂ d s U P).image ⊓ (glue₂ d s U P).wP.image := by
  let L₁ : Within (w.boundary n α) (K₂ d s U P).toPastingDiagram :=
    (Within.boundary w.toPastingDiagram n α).trans (glue₂ d s U P).wP
  let L₂ : Within (w.boundary n α) (K₂ d s U P).toPastingDiagram :=
    (ComposePair.withinOcc (Equation.trivial w hwd α) d hw).trans
      ((wVE₁ d s U).trans (glue₂ d s U P).wK)
  have hL₁ : L₁.image = (K₂ d s U P).shape.ogp.boundary (glue₂ d s U P).wP.image n α :=
    Within.image_boundary_trans _ _ _
  have hL₂ : L₂.image = (K₂ d s U P).shape.ogp.boundary (glue₂ d s U P).wP.image n α := by
    change ((ComposePair.withinOcc (Equation.trivial w hwd α) d hw).trans
      ((wVE₁ d s U).trans (glue₂ d s U P).wK)).image = _
    rw [Within.image_trans, ComposePair.image_withinOcc, map_boundary,
      show OGP.map ((wVE₁ d s U).trans (glue₂ d s U P).wK).emb ⊤ =
        ((wVE₁ d s U).trans (glue₂ d s U P).wK).image from rfl,
      Within.image_trans, boundary_wP₂_eq]
  have hL : L₁ = L₂ := Within.ext_of_image_eq _ _ (hL₁.trans hL₂.symm)
  have h2 : ((occW d hwd hw).trans L₂).image =
      (K₂ d s U P).shape.ogp.boundary (wV₂ d s U P).image n α := by
    change ((ComposePair.κOf (Equation.trivial w hwd α) d hw).trans
      ((ComposePair.withinOcc (Equation.trivial w hwd α) d hw).trans
        ((wVE₁ d s U).trans (glue₂ d s U P).wK))).image = _
    rw [Within.image_trans_assoc, ComposePair.image_κOf_trans, map_boundary,
      ← Within.image_trans, Within.image_trans_assoc, withinLeft_trans_wVE₁, ← Within.image_trans]
    rfl
  have h1 : ((occW d hwd hw).trans L₁).image =
      ((occW d hwd hw).trans L₂).image := by
    exact congrArg (fun L => ((occW d hwd hw).trans L).image) hL
  rw [(isPastingAtIn_wInv₂_wP₂ d s U P).inf_eq]
  have h3 : (K₂ d s U P).shape.ogp.boundary (wInv₂ d s U P).image n (!α) =
      (K₂ d s U P).shape.ogp.boundary (wV₂ d s U P).image n α := by
    have h := congrArg (OGP.map (glue₂ d s U P).wK.emb) (inter_wInv₁_wV₁ d s U)
    rw [OGP.map_inf, map_boundary, ← image_wInv₂, ← image_wV₂] at h
    have hc := (isPastingAtIn_wInv₁_wV₁ d s U).map (glue₂ d s U P).wK.emb
    rw [← image_wInv₂, ← image_wV₂] at hc
    rw [← hc.inf_eq]
    exact h
  exact h1.trans (h2.trans h3.symm)

private theorem isMoleculeIn_boundary_K₂ :
    IsMoleculeIn (K₂ d s U P).shape.ogp
      ((K₂ d s U P).shape.ogp.boundary ⊤ (n + 1) U.side) :=
  IsMoleculeIn.boundary (K₂ d s U P).shape.isMolecule _ _

private theorem equiv_inversePasting_restrictTo :
    (inversePasting d s hwd hw).pasting.Equiv
      ((K₂ d s U P).toPastingDiagram.restrictTo (isMoleculeIn_boundary_K₂ d s U P)) :=
  equiv_pasteAtBoundary_of_within (wInv₂ d s U P) (glue₂ d s U P).wP
    (isPastingAtIn_wInv₂_wP₂ d s U P) (occW d hwd hw)
    (inversePasting d s hwd hw).rewritable.isSubmoleculeOf (image_occW_wP₂ d s hwd hw U P)
    (inversePasting d s hwd hw).equiv

private theorem hasBdry_K₂ :
    HasBdry U.side (n + 1) (K₂ d s U P).toPastingDiagram (inversePasting d s hwd hw).pasting
      e.toPastingDiagram where
  dim_h := (glue₂ d s U P).dimK'
  dim_a := (inversePasting d s hwd hw).dim_pasting
  dim_b := d.dim_u'
  side := PastingDiagram.Equiv.trans
    (Within.equiv_restrictTo_of_eq (Within.boundary (K₂ d s U P).toPastingDiagram (n + 1) U.side)
      (Within.image_boundary _ _ _) (isMoleculeIn_boundary_K₂ d s U P))
    ((equiv_inversePasting_restrictTo d s hwd hw U P).symm)
  other := Within.equiv_of_image_eq
    (Within.boundary (K₂ d s U P).toPastingDiagram (n + 1) (!U.side))
    ((Within.ofEquiv (U.hasBdry.other.symm)).trans
      ((Within.boundary U.K.toPastingDiagram (n + 1) (!U.side)).trans
        ((glue₁ d s U).wK.trans (glue₂ d s U P).wK))) (by
    rw [Within.image_boundary, Within.image_ofEquiv_trans, Within.image_boundary_trans,
      Within.image_trans, ← map_boundary, (glue₁ d s U).wK.boundary_image,
      (glue₂ d s U P).boundary_not, (glue₁ d s U).boundary_not])

private theorem tClosure_K₂ (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A)
    (hK : TClosure A U.K) (hk : TClosure A P.k) : TClosure A (K₂ d s U P) :=
  (glue₂ d s U P).mem hDgn hk
    ((glue₁ d s U).mem hDgn (TClosure.trans ((invData d s).mem U.side)) hK)

theorem exists_hasBdry_inversePasting (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A)
    (hK : TClosure A U.K) (hk : TClosure A P.k) :
    ∃ K : RoundPastingDiagram X, TClosure A K ∧
      HasBdry (!U.side) (n + 1) K.toPastingDiagram e.toPastingDiagram
        (inversePasting d s hwd hw).pasting :=
  ⟨K₂ d s U P, tClosure_K₂ d s U P hDgn hK hk, (hasBdry_K₂ d s hwd hw U P).symm⟩

end DivisionPair

end Atoms.Diagrammatic
