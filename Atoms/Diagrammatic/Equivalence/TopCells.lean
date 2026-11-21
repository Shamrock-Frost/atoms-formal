import Atoms.Diagrammatic.Equivalence.BiInvertible

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace PasteAtData

variable {m : PastingDiagram X} {α : Bool} {n : ℕ} {e u' : RoundPastingDiagram X}
  (wE : Within e.toPastingDiagram m) (wU : Within u'.toPastingDiagram m)
  {R : LowerSet m.shape.ogp} (hc : m.shape.ogp.IsPastingAtIn n α wE.image wU.image R)

def occOfWithin :
    Within (occurrenceDiagram wU n α hc.isSubmoleculeOf_inf) (u'.boundary n α) :=
  occurrence wU n α hc.isSubmoleculeOf_inf

theorem equiv_occOfWithin :
    (e.boundary n (!α)).Equiv (occurrenceDiagram wU n α hc.isSubmoleculeOf_inf) :=
  equiv_boundary_occurrence wU n α hc.isSubmoleculeOf_inf wE hc.inf_eq.symm

theorem image_occOfWithin_trans :
    ((occOfWithin wE wU hc).trans ((Within.boundary u'.toPastingDiagram n α).trans wU)).image =
      wE.image ⊓ wU.image :=
  image_occurrence wU n α hc.isSubmoleculeOf_inf

variable (hde : e.dim = n + 1) (hdu : u'.dim = n + 1)

include hde hdu in
theorem isRewritableSubmolecule_image_occOfWithin :
    (u'.boundary n α).shape.ogp.IsRewritableSubmolecule (occOfWithin wE wU hc).image ⊤ :=
  Within.isRewritableSubmolecule_of_equiv_boundary (isSubmoleculeOf_image_occurrence _ _ _ _)
    (equiv_occOfWithin wE wU hc).symm hde
    (dim_boundary u'.toPastingDiagram (by omega) α)

def ofWithin : PasteAtData α n e u' :=
  ⟨hde, hdu, _, occOfWithin wE wU hc, isRewritableSubmolecule_image_occOfWithin wE wU hc hde hdu,
    equiv_occOfWithin wE wU hc⟩

noncomputable def withinOfWithin :
    Within (ofWithin wE wU hc hde hdu).round.toPastingDiagram m :=
  Within.pasteAtOfWithin wE wU hc (occOfWithin wE wU hc)
    (isSubmoleculeOf_image_occurrence _ _ _ _) (image_occOfWithin_trans wE wU hc)
    (equiv_occOfWithin wE wU hc)

theorem image_withinOfWithin :
    (withinOfWithin wE wU hc hde hdu).image = R :=
  Within.image_pasteAtOfWithin wE wU hc (occOfWithin wE wU hc)
    (isSubmoleculeOf_image_occurrence _ _ _ _) (image_occOfWithin_trans wE wU hc)
    (equiv_occOfWithin wE wU hc)

end PasteAtData

namespace TopCells

section Stages

variable {u : RoundPastingDiagram X} {m : PastingDiagram X} (wu : Within u.toPastingDiagram m)
  (E : LowerSet m.shape.ogp) (L : List (LowerSet u.shape.ogp)) (n : ℕ)

def stage (j : ℕ) : LowerSet m.shape.ogp :=
  E ⊔ OGP.map wu.emb (layerPrefix ⊤ n L j)

abbrev StageClaim (j : ℕ) : Prop :=
  (∃ e ∈ equivalences X, e.dim = n + 1 ∧
    ∃ w : Within e.toPastingDiagram m, w.image = stage wu E L n j) ∧
  m.shape.ogp.boundary (stage wu E L n j) n true =
    OGP.map wu.emb (u.shape.ogp.boundary (layerPrefix ⊤ n L j) n true)

noncomputable def cellWithin (t : u.shape.ogp) :
    Within (cellRound (u.cellAt t)).toPastingDiagram m :=
  (Within.ofEquiv (u.equiv_ofCell_cellAt t)).trans
    ((Within.restrictTo u.toPastingDiagram
      ((u.shape.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := t))).1)).trans wu)

theorem image_cellWithin (t : u.shape.ogp) :
    (cellWithin wu t).image = OGP.map wu.emb (.Iic t) := by
  change ((Within.ofEquiv (u.equiv_ofCell_cellAt t)).trans
    ((Within.restrictTo u.toPastingDiagram _).trans wu)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  change ((Within.restrictTo u.toPastingDiagram _).trans wu).image = _
  rw [Within.image_trans, Within.image_restrictTo]

theorem dim_cellRound {t : u.shape.ogp} (hdt : grade ℕ t = n + 1) :
    (cellRound (u.cellAt t)).dim = n + 1 := by
  have h := dim_restrictTo u.toPastingDiagram
    ((u.shape.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := t))).1)
  rw [← dim_eq_of_equiv (u.equiv_ofCell_cellAt t), LowerSet.krullDim_Iic, hdt] at h
  exact_mod_cast h

variable {L} {n} (hL : IsLayering u.shape.ogp n ⊤ L)
  (hU : krullDim (⊤ : LowerSet u.shape.ogp) = (n + 1 : ℕ))
  (hEU : E ⊓ wu.image ≤ OGP.map wu.emb (u.shape.ogp.boundary ⊤ n false))

include hL hU hEU in
theorem map_Iic_inf_stage {j : ℕ} (hj : j < L.length) {t : u.shape.ogp}
    (ht : t ∈ L.getD j ⊥) (hdt : grade ℕ t = n + 1) :
    OGP.map wu.emb (.Iic t) ⊓ stage wu E L n j =
      OGP.map wu.emb (u.shape.ogp.boundary (.Iic t) n false) := by
  rw [← hL.Iic_inf_layerPrefix hU hj ht hdt, OGP.map_inf]
  refine le_antisymm ?_ (inf_le_inf_left _ le_sup_right)
  rw [stage, inf_sup_left]
  refine sup_le (le_inf inf_le_left ?_) le_rfl
  calc OGP.map wu.emb (.Iic t) ⊓ E ≤ E ⊓ wu.image := by
        rw [inf_comm]; exact inf_le_inf_left _ (map_mono _ le_top)
    _ ≤ _ := hEU
    _ ≤ _ := map_mono _ (hL.boundary_le_layerPrefix (by omega))

variable (htop : ∀ t : u.shape.ogp, grade ℕ t = n + 1 → cellRound (u.cellAt t) ∈ equivalences X)

include hL hU hEU htop in
theorem stageClaim_succ {j : ℕ} (hj : j < L.length) (h : StageClaim wu E L n j) :
    StageClaim wu E L n (j + 1) := by
  obtain ⟨⟨e, he, hde, w, hw⟩, hb⟩ := h
  obtain ⟨t, ht, hdt, -, -⟩ := hL.exists_top_getD hU hj
  have hinter : (cellWithin wu t).image ⊓ w.image =
      OGP.map wu.emb (u.shape.ogp.boundary (.Iic t) n false) := by
    rw [image_cellWithin, hw]; exact map_Iic_inf_stage wu E hL hU hEU hj ht hdt
  have hdC := dim_cellRound n hdt
  have hc : m.shape.ogp.IsPastingAtIn n true (cellWithin wu t).image w.image
      (stage wu E L n (j + 1)) := by
    refine ⟨(cellWithin wu t).isMoleculeIn_image, w.isMoleculeIn_image, ?_, ?_, ?_⟩
    · rw [image_cellWithin, hw, stage, stage, hL.layerPrefix_succ hU hj ht hdt, map_sup]
      ac_rfl
    · rw [hinter, image_cellWithin, map_boundary]
      rfl
    · rw [hinter, hw, hb]
      exact (isSubmoleculeOf_map_iff wu.emb).2
        (hL.isSubmoleculeOf_boundary_Iic_layerPrefix hU hj ht hdt)
  let d := PasteAtData.ofWithin (cellWithin wu t) w hc hdC hde
  have hmem : d.round ∈ equivalences X := (pasteAt_mem_equivalences_iff d (htop t hdt)).2 he
  refine ⟨⟨d.round, hmem, d.dim_pasting,
    PasteAtData.withinOfWithin (cellWithin wu t) w hc hdC hde,
    PasteAtData.image_withinOfWithin (cellWithin wu t) w hc hdC hde⟩, ?_⟩
  have hkC : (n : WithBot ℕ∞) ≤ krullDim (cellWithin wu t).image := by
    rw [Within.krullDim_image, hdC]; exact_mod_cast n.le_succ
  have hkW : (n : WithBot ℕ∞) ≤ krullDim w.image := by
    rw [Within.krullDim_image, hde]; exact_mod_cast n.le_succ
  apply SetLike.coe_injective
  rw [hc.coe_boundary_eq hkC hkW, hinter, hw, hb, image_cellWithin, ← map_boundary,
    ← image_interior, coe_map, coe_map, coe_map, hL.boundary_layerPrefix_succ hU hj ht hdt,
    Set.image_union, Set.image_sdiff IsInclusion.injective]

include hL hU hEU htop in
theorem stageClaim_of_le (h0 : StageClaim wu E L n 0) :
    ∀ j ≤ L.length, StageClaim wu E L n j := by
  intro j
  induction j with
  | zero => exact fun _ => h0
  | succ j ih =>
    intro hj
    exact stageClaim_succ wu E hL hU hEU htop (by omega) (ih (by omega))

end Stages

section Ambient

variable (u : RoundPastingDiagram X) (n : ℕ) (hn : u.dim = n + 1)

abbrev inputUnit : RoundPastingDiagram X :=
  (isRound_boundary_of_isRound u.isRound n false).unit

include hn in
def ambientData : PasteAtData false n (inputUnit u n) u :=
  PasteAtData.ofBoundary (by
    change (u.boundary n false).unit.dim = n + 1
    rw [PastingDiagram.dim_unit, dim_boundary u.toPastingDiagram (by omega) false]) hn
   (boundary_unit
     (dim_boundary u.toPastingDiagram (by omega) false) true)

theorem inf_pasteAtInl_pasteAtInr :
    (ambientData u n hn).pasteAtInl.image ⊓ (ambientData u n hn).pasteAtInr.image =
      OGP.map (ambientData u n hn).pasteAtInr.emb (u.shape.ogp.boundary ⊤ n false) := by
  rw [← (ambientData u n hn).image_occ_pasteAtInr, Within.image_trans]
  change OGP.map ((Within.boundary u.toPastingDiagram n false).trans
    (ambientData u n hn).pasteAtInr).emb (Within.refl (u.boundary n false)).image = _
  rw [Within.image_refl]
  change ((Within.boundary u.toPastingDiagram n false).trans
    (ambientData u n hn).pasteAtInr).image = _
  rw [Within.image_trans, Within.image_boundary]

include hn in
theorem stageClaim_zero (L : List (LowerSet u.shape.ogp)) :
    StageClaim (ambientData u n hn).pasteAtInr (ambientData u n hn).pasteAtInl.image L n 0 := by
  have hE : stage (ambientData u n hn).pasteAtInr (ambientData u n hn).pasteAtInl.image L n 0 =
      (ambientData u n hn).pasteAtInl.image := by
    rw [stage]
    change _ ⊔ OGP.map _ (u.shape.ogp.boundary ⊤ n false) = _
    rw [← inf_pasteAtInl_pasteAtInr u n hn]
    exact sup_eq_left.2 inf_le_left
  refine ⟨⟨inputUnit u n,
    unit_mem_equivalences ⟨u.boundary n false, isRound_boundary_of_isRound u.isRound n false⟩,
    (ambientData u n hn).dim_e, (ambientData u n hn).pasteAtInl, hE.symm⟩, ?_⟩
  rw [hE]
  have h1 := (ambientData u n hn).isPastingAtIn_pasteAtInl.inf_eq
  rw [Bool.not_false] at h1
  rw [← h1, inf_pasteAtInl_pasteAtInr u n hn]
  change _ = OGP.map _ (u.shape.ogp.boundary (u.shape.ogp.boundary ⊤ n false) n true)
  rw [boundary_eq_self (krullDim_boundary_le ⊤ n false) true]

end Ambient

end TopCells

open TopCells in
theorem mem_equivalences_of_forall_cellAt (u : RoundPastingDiagram X) (hpos : 0 < u.dim)
    (htop : ∀ t : u.shape.ogp, grade ℕ t = u.dim →
      cellRound (u.cellAt t) ∈ equivalences X) : u ∈ equivalences X := by
  obtain ⟨n, hn⟩ : ∃ n, u.dim = n + 1 := ⟨u.dim - 1, by omega⟩
  have hU : krullDim (⊤ : LowerSet u.shape.ogp) = (n + 1 : ℕ) := by
    rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]
    exact_mod_cast hn
  obtain ⟨L, hL⟩ := admitsLayering_pred_krullDim u.shape.isMolecule hU (by omega)
  rw [Nat.add_sub_cancel] at hL
  obtain ⟨⟨e, he, -, w, hw⟩, -⟩ := stageClaim_of_le (ambientData u n hn).pasteAtInr
    (ambientData u n hn).pasteAtInl.image hL hU (inf_pasteAtInl_pasteAtInr u n hn).le
    (fun t ht => htop t (ht.trans hn.symm)) (stageClaim_zero u n hn L) L.length le_rfl
  have hfull : stage (ambientData u n hn).pasteAtInr (ambientData u n hn).pasteAtInl.image L n
      L.length = ⊤ := by
    rw [stage, hL.layerPrefix_length]
    exact (ambientData u n hn).isPastingAtIn_pasteAtInl.eq_sup.symm
  have hequiv : e.toPastingDiagram.Equiv (ambientData u n hn).pasting :=
    Within.equiv_of_image_eq w (Within.refl _) (hw.trans (hfull.trans (Within.image_refl _).symm))
  have hround : (ambientData u n hn).round ∈ equivalences X := mem_equivalences_of_equiv hequiv he
  exact (pasteAt_mem_equivalences_iff (ambientData u n hn) (unit_mem_equivalences
    ⟨u.boundary n false, isRound_boundary_of_isRound u.isRound n false⟩)).1 hround

end Atoms.Diagrammatic
