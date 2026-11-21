import Atoms.Diagrammatic.Context.Round

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Order Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def PastingDiagram.cellOf (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) : PastingDiagram X :=
  ℓ.restrictTo
    (IsMoleculeIn.isAtomIn_Iic ℓ.shape.isMolecule (LowerSet.mem_top (a := t))).isMoleculeIn

theorem PastingDiagram.isRound_cellOf (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) :
    (ℓ.cellOf t).IsRound :=
  (ℓ.isRound_restrictTo_iff _).2
    (IsMoleculeIn.isAtomIn_Iic ℓ.shape.isMolecule (LowerSet.mem_top (a := t))).isRound

theorem PastingDiagram.dim_cellOf (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) :
    (ℓ.cellOf t).dim = grade ℕ t := by
  have h := ℓ.dim_restrictTo
    (IsMoleculeIn.isAtomIn_Iic ℓ.shape.isMolecule (LowerSet.mem_top (a := t))).isMoleculeIn
  rw [LowerSet.krullDim_Iic] at h
  exact_mod_cast h

theorem PastingDiagram.isAtom_cellOf (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) :
    (ℓ.cellOf t).shape.ogp.IsAtom := by
  have h := IsMoleculeIn.isAtomIn_Iic ℓ.shape.isMolecule (LowerSet.mem_top (a := t))
  rw [← Within.image_restrictTo ℓ h.isMoleculeIn] at h
  exact (isAtomIn_map_iff (Within.restrictTo ℓ _).emb).1 h

def PastingDiagram.cellWithin (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) :
    Within (ℓ.cellOf t) ℓ :=
  Within.restrictTo ℓ _

theorem PastingDiagram.image_cellWithin (ℓ : PastingDiagram X) (t : ℓ.shape.ogp) :
    (ℓ.cellWithin t).image = LowerSet.Iic t :=
  Within.image_restrictTo _ _

theorem PastingDiagram.krullDim_top_shape {ℓ : PastingDiagram X} {k : ℕ} (hd : ℓ.dim = k + 1) :
    krullDim (⊤ : LowerSet ℓ.shape.ogp) = (k + 1 : ℕ) := by
  rw [LowerSet.krullDim_top, ℓ.shape.krullDim_eq_dimension]
  exact_mod_cast hd

structure PieceFrame (ℓ : PastingDiagram X) (k : ℕ) (α : Bool) where
  length : ℕ
  piece : ∀ i, i < length → RoundPastingDiagram X
  pieceWithin : ∀ i (hi : i < length), Within (piece i hi).toPastingDiagram ℓ
  stage : ℕ → LowerSet ℓ.shape.ogp
  dim_piece : ∀ i (hi : i < length), (piece i hi).dim = k + 1
  stage_zero : stage 0 = ℓ.shape.ogp.boundary ⊤ k (!α)
  stage_length : stage length = ⊤
  isPastingAtIn : ∀ i (hi : i < length),
    ℓ.shape.ogp.IsPastingAtIn k α (pieceWithin i hi).image (stage i) (stage (i + 1))

namespace PieceFrame

variable {ℓ : PastingDiagram X} {k : ℕ} {α : Bool} (F : PieceFrame ℓ k α)

theorem isMoleculeIn_stage : ∀ i, i ≤ F.length → IsMoleculeIn ℓ.shape.ogp (F.stage i)
  | 0, _ => F.stage_zero ▸ ℓ.shape.isMolecule.boundary k (!α)
  | i + 1, hi => (F.isPastingAtIn i hi).isMoleculeIn

theorem boundary_stage_not : ∀ i, i ≤ F.length →
    ℓ.shape.ogp.boundary (F.stage i) k (!α) = ℓ.shape.ogp.boundary ⊤ k (!α)
  | 0, _ => by rw [F.stage_zero]; exact boundary_eq_self (krullDim_boundary_le _ _ _) _
  | i + 1, hi => (F.isPastingAtIn i hi).boundary_not.trans (boundary_stage_not i (by omega))

theorem stage_zero_le : ∀ i, i ≤ F.length → F.stage 0 ≤ F.stage i
  | 0, _ => le_rfl
  | i + 1, hi => (stage_zero_le i (by omega)).trans (F.isPastingAtIn i hi).right_le

theorem le_krullDim_stage (i : ℕ) (hi : i < F.length) :
    (k : WithBot ℕ∞) ≤ krullDim (F.stage i) := by
  have hc := F.isPastingAtIn i hi
  have h := hc.isMoleculeIn_left.krullDim_boundary (n := k)
    (by rw [(F.pieceWithin i hi).krullDim_image, F.dim_piece i hi]; exact_mod_cast k.le_succ) (!α)
  rw [← hc.inf_eq] at h
  exact h.symm.le.trans (LowerSet.krullDim_mono inf_le_right)

variable [∀ i, DecidablePred (· ∈ F.stage i)]

abbrev stageDiagram (i : ℕ) (hi : i ≤ F.length) : PastingDiagram X :=
  ℓ.restrictTo (F.isMoleculeIn_stage i hi)

theorem dim_boundary_stageDiagram (i : ℕ) (hi : i < F.length) :
    ((F.stageDiagram i hi.le).boundary k α).dim = k :=
  dim_boundary _ (by
    have h := F.le_krullDim_stage i hi
    rw [← dim_restrictTo ℓ (F.isMoleculeIn_stage i hi.le)] at h
    exact_mod_cast h) α

noncomputable abbrev occDiagram (i : ℕ) (hi : i < F.length) : PastingDiagram X :=
  occurrenceDiagram (Within.restrictTo ℓ (F.isMoleculeIn_stage i hi.le)) k α (by
    rw [Within.image_restrictTo]
    exact (F.isPastingAtIn i hi).isSubmoleculeOf_boundary)

noncomputable def occ (i : ℕ) (hi : i < F.length) :
    Within (F.occDiagram i hi) ((F.stageDiagram i hi.le).boundary k α) :=
  occurrence (Within.restrictTo ℓ (F.isMoleculeIn_stage i hi.le)) k α (by
    rw [Within.image_restrictTo]
    exact (F.isPastingAtIn i hi).isSubmoleculeOf_boundary)

theorem equiv_occ (i : ℕ) (hi : i < F.length) :
    ((F.piece i hi).toPastingDiagram.boundary k (!α)).Equiv (F.occDiagram i hi) :=
  equiv_occurrence_of_image_eq _ k α _
    ((Within.boundary _ k (!α)).trans (F.pieceWithin i hi)) (Within.image_boundary_trans _ _ _)

theorem isRewritableSubmolecule_image_occ (i : ℕ) (hi : i < F.length) :
    ((F.stageDiagram i hi.le).boundary k α).shape.ogp.IsRewritableSubmolecule
      (F.occ i hi).image ⊤ := by
  have e := F.equiv_occ i hi
  refine (F.occ i hi).isRewritableSubmolecule_image_iff.2
    ⟨isSubmoleculeOf_image_occurrence _ _ _ _,
      e.isRound_iff.1 (isRound_boundary_of_isRound (F.piece i hi).isRound k (!α)), ?_⟩
  rw [← dim_eq_of_equiv e, dim_boundary _ (by rw [F.dim_piece i hi]; omega),
    F.dim_boundary_stageDiagram i hi]

noncomputable def step (i : ℕ) (hi : i < F.length) : CtxExpr X :=
  .side α (F.piece i hi).toPastingDiagram k (F.occ i hi)
    (isSubmoleculeOf_image_occurrence _ _ _ _) (F.equiv_occ i hi)

noncomputable def ctx : ℕ → CtxExpr X
  | 0 => .id
  | i + 1 => if hi : i < F.length then .comp (F.step i hi) (ctx i) else ctx i

theorem ctx_succ {i : ℕ} (hi : i < F.length) : F.ctx (i + 1) = .comp (F.step i hi) (F.ctx i) := by
  rw [ctx, dif_pos hi]

theorem ctx_succ_of_not {i : ℕ} (hi : ¬ i < F.length) : F.ctx (i + 1) = F.ctx i := by
  rw [ctx, dif_neg hi]

theorem equiv_boundary_step (i : ℕ) (hi : i < F.length) :
    ((sidePaste α (F.piece i hi).toPastingDiagram k (F.occ i hi)
        (isSubmoleculeOf_image_occurrence _ _ _ _) (F.equiv_occ i hi)
        ((F.stageDiagram i hi.le).boundary k α)).boundary k α).Equiv
      ((F.stageDiagram (i + 1) hi).boundary k α) := by
  have hcell := (F.piece i hi).isRound
  have hdc := F.dim_piece i hi
  have hr := F.isRewritableSubmolecule_image_occ i hi
  have hw : Parallel ⟨F.occDiagram i hi, (F.occ i hi).round_image_iff.1 hr.isRound⟩
      ⟨(F.piece i hi).toPastingDiagram.boundary k α, isRound_boundary_of_isRound hcell k α⟩ :=
    (parallel_boundary hcell hdc (!α) α).of_equiv_left (F.equiv_occ i hi).symm
  have hdv := F.dim_boundary_stageDiagram i hi
  have e₁ := equiv_boundary_sidePaste_substitute (hι := isSubmoleculeOf_image_occurrence _ _ _ _)
    (h := F.equiv_occ i hi) hcell hdc hr hw (equiv_boundary_dim _ hdv.le α) hdv.ge
  have hc0 := F.isPastingAtIn i hi
  have hsub := hc0.isSubstitutionIn_boundary ((F.pieceWithin i hi).round_image_iff.2 hcell)
    (by rw [(F.pieceWithin i hi).krullDim_image, hdc]; push_cast; rfl) (F.le_krullDim_stage i hi)
  rw [hc0.inf_eq] at hsub
  have hsub' : ℓ.shape.ogp.IsSubstitutionIn
      ((Within.boundary (F.stageDiagram i hi.le) k α).trans
        (Within.restrictTo ℓ (F.isMoleculeIn_stage i hi.le))).image
      ((F.occ i hi).trans ((Within.boundary (F.stageDiagram i hi.le) k α).trans
        (Within.restrictTo ℓ (F.isMoleculeIn_stage i hi.le)))).image
      ((Within.boundary (F.piece i hi).toPastingDiagram k α).trans (F.pieceWithin i hi)).image
      (ℓ.shape.ogp.boundary (F.stage (i + 1)) k α) := by
    rw [occ, image_occurrence, Within.image_boundary_trans, Within.image_boundary_trans,
      Within.image_restrictTo]
    exact hsub
  have e₂ := equiv_substitute_of_within (F.occ i hi) hr _ hw _ _ hsub'
    ((F.isMoleculeIn_stage (i + 1) hi).boundary k α)
  exact e₁.trans (e₂.trans ((ℓ.equiv_boundary_restrictTo _ k α).symm))

theorem typed_ctx {A : Set (RoundPastingDiagram X)} (hA : ∀ i (hi : i < F.length), F.piece i hi ∈ A)
    {H : PdHom X} (hk : H.k = k)
    (hs : (H.side α).Equiv ((F.stageDiagram 0 (Nat.zero_le _)).boundary k α)) :
    ∀ i (hi : i ≤ F.length), (F.ctx i).Typed A False H
      (H.setSide α ((F.stageDiagram i hi).boundary k α)) := by
  obtain ⟨k', v, w⟩ := H
  change k' = k at hk
  subst k'
  intro i
  induction i with
  | zero => exact fun _ => .id (PdHom.equiv_setSide _ hs)
  | succ i ih =>
    intro hi
    have hi' : i < F.length := by omega
    rw [F.ctx_succ hi']
    refine .comp (ih hi'.le) (.side
      (H := PdHom.setSide ⟨k, v, w⟩ α ((F.stageDiagram i hi'.le).boundary k α)) α
      (F.piece i hi') (hA i hi') (F.dim_piece i hi') (F.occ i hi')
      (F.isRewritableSubmolecule_image_occ i hi') (F.equiv_occ i hi')
      (by rw [PdHom.side_setSide_self]) ?_)
    rw [PdHom.setSide_setSide]
    exact (PdHom.Equiv.refl _).setSide α (F.equiv_boundary_step i hi')

theorem ctx_app_equiv_restrictTo_stage {m x : PastingDiagram X} (wX : Within x m)
    (wℓ : Within ℓ m)
    (hpm : m.shape.ogp.IsPastingIn k (cond α wX.image wℓ.image) (cond α wℓ.image wX.image) ⊤) :
    ∀ i, i ≤ F.length → ∃ hS : IsMoleculeIn m.shape.ogp (wX.image ⊔ OGP.map wℓ.emb (F.stage i)),
      ((F.ctx i).app x).Equiv (m.restrictTo hS) := by
  obtain ⟨hU, hXℓ, -⟩ := (isPastingIn_cond_iff α).1 hpm
  have hpU : m.shape.ogp.IsPastingIn k (cond α wX.image wℓ.image) (cond α wℓ.image wX.image)
      (wX.image ⊔ wℓ.image) := hU ▸ hpm
  have hSm : ∀ i, i ≤ F.length → IsMoleculeIn m.shape.ogp (OGP.map wℓ.emb (F.stage i)) :=
    fun i hi => (isMoleculeIn_map_iff wℓ.emb _).2 (F.isMoleculeIn_stage i hi)
  have hpre : ∀ i, i ≤ F.length → m.shape.ogp.IsPastingIn k
      (cond α wX.image (OGP.map wℓ.emb (F.stage i)))
      (cond α (OGP.map wℓ.emb (F.stage i)) wX.image)
      (wX.image ⊔ OGP.map wℓ.emb (F.stage i)) := fun i hi =>
    isPastingIn_sup_of_le_factor α hpU (map_mono wℓ.emb le_top)
      (by rw [← map_boundary, F.boundary_stage_not i hi, wℓ.boundary_image])
  have hmol : ∀ i, i ≤ F.length → ∀ β : Bool,
      IsMoleculeIn m.shape.ogp (cond β wX.image (OGP.map wℓ.emb (F.stage i))) ∧
        IsMoleculeIn m.shape.ogp (cond β (OGP.map wℓ.emb (F.stage i)) wX.image) :=
    fun i hi β => by
      cases β
      · exact ⟨hSm i hi, wX.isMoleculeIn_image⟩
      · exact ⟨wX.isMoleculeIn_image, hSm i hi⟩
  intro i
  induction i with
  | zero =>
    intro _
    have hst : wX.image ⊔ OGP.map wℓ.emb (F.stage 0) = wX.image := by
      rw [F.stage_zero, ← wℓ.boundary_image, ← hXℓ]
      exact sup_eq_left.2 inf_le_left
    have hS : IsMoleculeIn m.shape.ogp (wX.image ⊔ OGP.map wℓ.emb (F.stage 0)) := by
      rw [hst]; exact wX.isMoleculeIn_image
    exact ⟨hS, Within.equiv_restrictTo_of_eq wX hst.symm hS⟩
  | succ i ih =>
    intro hi
    have hi' : i < F.length := by omega
    obtain ⟨hS, e⟩ := ih hi'.le
    have hb : m.shape.ogp.boundary (wX.image ⊔ OGP.map wℓ.emb (F.stage i)) k α =
        m.shape.ogp.boundary (OGP.map wℓ.emb (F.stage i)) k α :=
      (hpre i hi'.le).boundary_cond α
    have hc : m.shape.ogp.IsPastingAtIn k α (OGP.map wℓ.emb (F.pieceWithin i hi').image)
        (wX.image ⊔ OGP.map wℓ.emb (F.stage i))
        (wX.image ⊔ OGP.map wℓ.emb (F.stage (i + 1))) := by
      refine ((F.isPastingAtIn i hi').map wℓ.emb).sup_right hS ?_ ?_
      · calc OGP.map wℓ.emb (F.pieceWithin i hi').image ⊓ wX.image
            ≤ wX.image ⊓ wℓ.image := by
              rw [inf_comm]; exact inf_le_inf_left _ (map_mono wℓ.emb le_top)
          _ = OGP.map wℓ.emb (F.stage 0) := by rw [hXℓ, wℓ.boundary_image, F.stage_zero]
          _ ≤ OGP.map wℓ.emb (F.stage i) := map_mono wℓ.emb (F.stage_zero_le i hi'.le)
      · rw [hb]
        exact IsSubmoleculeOf.refl ((hSm i hi'.le).boundary k α)
    let wU := (F.pieceWithin i hi').trans wℓ
    have hwU : wU.image = OGP.map wℓ.emb (F.pieceWithin i hi').image := Within.image_trans _ _
    let wQ := Within.restrictTo m hS
    have hc' : m.shape.ogp.IsPastingAtIn k α wU.image wQ.image
        (wX.image ⊔ OGP.map wℓ.emb (F.stage (i + 1))) := by
      rw [hwU, Within.image_restrictTo]; exact hc
    let W₀ := (Within.boundary (F.stageDiagram i hi'.le) k α).trans
      (Within.restrictTo ℓ (F.isMoleculeIn_stage i hi'.le))
    have hbS : m.shape.ogp.boundary wQ.image k α = (W₀.trans wℓ).image := by
      rw [Within.image_restrictTo, hb, Within.image_trans, Within.image_boundary_trans,
        Within.image_restrictTo, map_boundary]
    have hsQ : ((m.restrictTo hS).boundary k α).Equiv
        ((F.stageDiagram i hi'.le).boundary k α) :=
      Within.equiv_of_image_eq ((Within.boundary _ k α).trans wQ) (W₀.trans wℓ)
        ((Within.image_boundary_trans _ _ _).trans hbS)
    have hside : sideWithin wQ k α hsQ = W₀.trans wℓ :=
      Within.ext_of_image_eq _ _ ((image_sideWithin wQ k α hsQ).trans hbS)
    have hocc : ((F.occ i hi').trans (sideWithin wQ k α hsQ)).image = wU.image ⊓ wQ.image := by
      rw [hside, Within.image_trans_assoc, occ, image_occurrence, map_boundary, ← hwU,
        ← hc'.inf_eq]
    have hR' : IsMoleculeIn m.shape.ogp (wX.image ⊔ OGP.map wℓ.emb (F.stage (i + 1))) :=
      (hpre (i + 1) hi).isMoleculeIn (hmol (i + 1) hi α).1 (hmol (i + 1) hi α).2
    refine ⟨hR', ?_⟩
    rw [F.ctx_succ hi']
    exact PastingDiagram.Equiv.trans
      (sidePaste_equiv (hι := isSubmoleculeOf_image_occurrence _ _ _ _)
        (h := F.equiv_occ i hi') ((e.boundary k α).trans hsQ) e)
      (sidePaste_equiv_restrictTo (hι := isSubmoleculeOf_image_occurrence _ _ _ _)
        (h := F.equiv_occ i hi') wU wQ hsQ hc' hocc hR')

theorem ctx_app_of_within {m x : PastingDiagram X} (wX : Within x m) (wℓ : Within ℓ m)
    (hpm : m.shape.ogp.IsPastingIn k (cond α wX.image wℓ.image) (cond α wℓ.image wX.image) ⊤) :
    ((F.ctx F.length).app x).Equiv m := by
  obtain ⟨hU, -, -⟩ := (isPastingIn_cond_iff α).1 hpm
  obtain ⟨hS, e⟩ := F.ctx_app_equiv_restrictTo_stage wX wℓ hpm F.length le_rfl
  have hst : wX.image ⊔ OGP.map wℓ.emb (F.stage F.length) = ⊤ := by
    rw [F.stage_length]
    exact hU
  exact e.trans (PastingDiagram.Equiv.trans
    (m.equiv_restrictTo_of_eq hS m.shape.isMolecule hst) (equiv_restrictTo_univ _))

theorem ctx_app (x : PastingDiagram X) (hp : (cond α x ℓ).Pastable (cond α ℓ x) k) :
    ((F.ctx F.length).app x).Equiv ((cond α x ℓ).paste (cond α ℓ x) k hp) := by
  obtain ⟨wx, hpst⟩ := Within.exists_isPastingIn_pasteIn α hp
  exact F.ctx_app_of_within wx (Within.pasteIn α hp) hpst

end PieceFrame

section Frame

variable {ℓ : PastingDiagram X} {k : ℕ} {L : List (LowerSet ℓ.shape.ogp)}
  (hL : IsLayering ℓ.shape.ogp k ⊤ L) (hd : krullDim (⊤ : LowerSet ℓ.shape.ogp) = (k + 1 : ℕ))

noncomputable def layerTop (j : ℕ) (hj : j < L.length) : ℓ.shape.ogp :=
  (hL.exists_top_getD hd hj).choose

theorem layerTop_spec (j : ℕ) (hj : j < L.length) :
    layerTop hL hd j hj ∈ L.getD j ⊥ ∧ grade ℕ (layerTop hL hd j hj) = k + 1 ∧
      krullDim (L.getD j ⊥) = (k + 1 : ℕ) ∧
        ∀ y ∈ L.getD j ⊥, grade ℕ y = k + 1 → y = layerTop hL hd j hj :=
  (hL.exists_top_getD hd hj).choose_spec

theorem dim_cellOf_layerTop (j : ℕ) (hj : j < L.length) :
    (ℓ.cellOf (layerTop hL hd j hj)).dim = k + 1 :=
  (ℓ.dim_cellOf _).trans (layerTop_spec hL hd j hj).2.1

variable (α : Bool)

noncomputable abbrev stepTop (i : ℕ) (hi : i < L.length) : ℓ.shape.ogp :=
  layerTop hL hd (layerIndex α L i) (layerIndex_lt α hi)

theorem isPastingAtIn_stepTop (i : ℕ) (hi : i < L.length) :
    ℓ.shape.ogp.IsPastingAtIn k α (.Iic (stepTop hL hd α i hi))
      (layerStage α ⊤ k L i) (layerStage α ⊤ k L (i + 1)) := by
  obtain ⟨ht, hdt, hdl, huniq⟩ := layerTop_spec hL hd _ (layerIndex_lt α hi)
  exact isPastingAtIn_Iic_of_isPastingIn (hL.isMoleculeIn_getD (layerIndex_lt α hi)) ht hdt hdl
    huniq α (hL.isPastingIn_layerStage α hi) (hL.isMoleculeIn_layerStage α hi.le)

noncomputable abbrev layerFrame : PieceFrame ℓ k α where
  length := L.length
  piece i hi := ⟨ℓ.cellOf (stepTop hL hd α i hi), ℓ.isRound_cellOf _⟩
  pieceWithin i hi := ℓ.cellWithin (stepTop hL hd α i hi)
  stage := layerStage α ⊤ k L
  dim_piece _ _ := dim_cellOf_layerTop hL hd _ _
  stage_zero := layerStage_zero α
  stage_length := hL.layerStage_length α
  isPastingAtIn i hi := by
    rw [image_cellWithin]
    exact isPastingAtIn_stepTop hL hd α i hi

variable [∀ (β : Bool) (i : ℕ), DecidablePred (· ∈ layerStage β (⊤ : LowerSet ℓ.shape.ogp) k L i)]

abbrev stageDiagram (i : ℕ) (hi : i ≤ L.length) : PastingDiagram X :=
  ℓ.restrictTo (hL.isMoleculeIn_layerStage α hi)

noncomputable def frame (i : ℕ) : CtxExpr X :=
  (layerFrame hL hd α).ctx i

theorem typed_frame {A : Set (RoundPastingDiagram X)}
    (hA : ∀ j (hj : j < L.length),
      (⟨ℓ.cellOf (layerTop hL hd j hj), ℓ.isRound_cellOf _⟩ : RoundPastingDiagram X) ∈ A)
    {H : PdHom X} (hk : H.k = k)
    (hs : (H.side α).Equiv ((stageDiagram hL α 0 (Nat.zero_le _)).boundary k α)) :
    ∀ i (hi : i ≤ L.length), (frame hL hd α i).Typed A False H
      (H.setSide α ((stageDiagram hL α i hi).boundary k α)) :=
  (layerFrame hL hd α).typed_ctx (fun _ _ => hA _ _) hk hs

theorem frame_app_equiv_restrictTo_stage {m x : PastingDiagram X} (wX : Within x m)
    (wℓ : Within ℓ m)
    (hpm : m.shape.ogp.IsPastingIn k (cond α wX.image wℓ.image) (cond α wℓ.image wX.image) ⊤) :
    ∀ i, i ≤ L.length → ∃ hS : IsMoleculeIn m.shape.ogp
        (wX.image ⊔ OGP.map wℓ.emb (layerStage α ⊤ k L i)),
      ((frame hL hd α i).app x).Equiv (m.restrictTo hS) :=
  (layerFrame hL hd α).ctx_app_equiv_restrictTo_stage wX wℓ hpm

end Frame

def PastingDiagram.topCells (ℓ : PastingDiagram X) (k : ℕ) : Set (RoundPastingDiagram X) :=
  {u | ∃ t : ℓ.shape.ogp, grade ℕ t = k + 1 ∧ u.toPastingDiagram = ℓ.cellOf t}

theorem PastingDiagram.admitsLayering {ℓ : PastingDiagram X} {k : ℕ} (hd : ℓ.dim = k + 1) :
    AdmitsLayering ℓ.shape.ogp k ⊤ := by
  have h := admitsLayering_pred_krullDim ℓ.shape.isMolecule (krullDim_top_shape hd) k.succ_pos
  rwa [Nat.add_sub_cancel] at h

open Classical in
noncomputable def PastingDiagram.frameCtx (ℓ : PastingDiagram X) (α : Bool) {k : ℕ}
    (hd : ℓ.dim = k + 1) : CtxExpr X :=
  frame (PastingDiagram.admitsLayering hd).choose_spec (krullDim_top_shape hd) α
    (PastingDiagram.admitsLayering hd).choose.length

theorem PastingDiagram.typed_frameCtx (ℓ : PastingDiagram X) (α : Bool) {H : PdHom X}
    (hd : ℓ.dim = H.k + 1) (hs : (H.side α).Equiv (ℓ.boundary H.k (!α))) :
    (ℓ.frameCtx α hd).Typed (ℓ.topCells H.k) False H (H.setSide α (ℓ.boundary H.k α)) := by
  classical
  have hd' := krullDim_top_shape hd
  have hL := (PastingDiagram.admitsLayering hd).choose_spec
  set L := (PastingDiagram.admitsLayering hd).choose
  have h0 : ((stageDiagram hL α 0 (Nat.zero_le _)).boundary H.k α).Equiv
      (ℓ.boundary H.k (!α)) :=
    Within.equiv_of_image_eq ((Within.boundary _ H.k α).trans (Within.restrictTo ℓ _))
      (Within.boundary ℓ H.k (!α)) (by
        rw [Within.image_boundary_trans, Within.image_restrictTo, Within.image_boundary,
          layerStage_zero]
        exact boundary_eq_self (krullDim_boundary_le _ _ _) α)
  have hlen : ((stageDiagram hL α L.length le_rfl).boundary H.k α).Equiv (ℓ.boundary H.k α) :=
    Within.equiv_of_image_eq ((Within.boundary _ H.k α).trans (Within.restrictTo ℓ _))
      (Within.boundary ℓ H.k α) (by
        rw [Within.image_boundary_trans, Within.image_restrictTo, Within.image_boundary,
          hL.layerStage_length])
  exact (typed_frame hL hd' α (A := ℓ.topCells H.k)
    (fun j hj => ⟨_, (layerTop_spec hL hd' j hj).2.1, rfl⟩) rfl
    (hs.trans h0.symm) L.length le_rfl).congr_codomain ((PdHom.Equiv.refl H).setSide α hlen)

theorem PastingDiagram.frameCtx_app (ℓ : PastingDiagram X) (α : Bool) {k : ℕ}
    (hd : ℓ.dim = k + 1) (x : PastingDiagram X) (hp : (cond α x ℓ).Pastable (cond α ℓ x) k) :
    ((ℓ.frameCtx α hd).app x).Equiv ((cond α x ℓ).paste (cond α ℓ x) k hp) := by
  classical
  exact (layerFrame _ (krullDim_top_shape hd) α).ctx_app x hp

section MapTo

variable {Y : DiagSet.{u}} (g : X ⟶ Y)

theorem frame_mapTo {ℓ : PastingDiagram X} {k : ℕ} {L : List (LowerSet ℓ.shape.ogp)}
    (hL : IsLayering ℓ.shape.ogp k ⊤ L) (hd : krullDim (⊤ : LowerSet ℓ.shape.ogp) = (k + 1 : ℕ))
    [∀ (β : Bool) (i : ℕ), DecidablePred (· ∈ layerStage β (⊤ : LowerSet ℓ.shape.ogp) k L i)]
    (α : Bool) : ∀ i, (frame hL hd α i).mapTo g = frame (ℓ := ℓ.mapTo g) hL hd α i
  | 0 => rfl
  | i + 1 => by
    by_cases hi : i < L.length
    · rw [frame, frame, PieceFrame.ctx_succ _ hi, PieceFrame.ctx_succ (ℓ := ℓ.mapTo g) _ hi]
      change CtxExpr.comp (((layerFrame hL hd α).step i hi).mapTo g)
        ((frame hL hd α i).mapTo g) = _
      rw [frame_mapTo hL hd α i]
      rfl
    · rw [frame, frame, PieceFrame.ctx_succ_of_not _ hi,
        PieceFrame.ctx_succ_of_not (ℓ := ℓ.mapTo g) _ hi]
      exact frame_mapTo hL hd α i

end MapTo

namespace CtxExpr

def paste (α : Bool) (u : PastingDiagram X) (n : ℕ) : CtxExpr X :=
  .side α u n (Within.refl (u.boundary n (!α))) (Within.isSubmoleculeOf_image_refl _) (.refl _)

theorem image_sideOcc_of_image_top {α : Bool} {n : ℕ} {a v V : PastingDiagram X}
    {ι : Within V v} (hι : ι.image = ⊤) (hs : (a.boundary n α).Equiv v) :
    (sideOcc α n ι hs).image = ⊤ := by
  rw [sideOcc, Within.image_trans, hι]
  exact Within.image_ofEquiv _

theorem sidePaste_equiv_paste (α : Bool) {u x v V : PastingDiagram X} {n : ℕ}
    {ι : Within V v} {hι : IsSubmoleculeOf v.shape.ogp ι.image ⊤}
    (hιu : ι.image = ⊤) (h : (u.boundary n (!α)).Equiv V)
    (hs : (x.boundary n α).Equiv v) (hp : (cond α x u).Pastable (cond α u x) n) :
    (sidePaste α u n ι hι h x).Equiv ((cond α x u).paste (cond α u x) n hp) := by
  rw [sidePaste_of hs]
  have hc := Within.isPastingAtIn_pasteAt u x n α _ (isSubmoleculeOf_image_sideOcc α n ι hι hs) h
  have hi := inter_eq_boundary_pasteAt_of_image_univ u x n α _
    (isSubmoleculeOf_image_sideOcc α n ι hι hs) (image_sideOcc_of_image_top hιu hs) h
  exact ((equiv_paste_cond_of_within α _ _ (hc.isPastingIn_of_inf_eq hi)
    (pasteAtBoundary _ _ _ _ _ _ _).shape.isMolecule hp).trans (equiv_restrictTo_univ _)).symm

theorem paste_app (α : Bool) {u x : PastingDiagram X} {n : ℕ}
    (hp : (cond α x u).Pastable (cond α u x) n) :
    ((paste α u n).app x).Equiv ((cond α x u).paste (cond α u x) n hp) :=
  sidePaste_equiv_paste α (Within.image_refl _) (.refl _) hp.side hp

theorem paste_app_not (α : Bool) {u x : PastingDiagram X} {n : ℕ}
    (hp : (cond α x u).Pastable (cond α u x) n) :
    ((paste α u n).app x).Equiv ((paste (!α) x n).app u) := by
  cases α
  · exact (paste_app false hp).trans (paste_app true hp).symm
  · exact (paste_app true hp).trans (paste_app false hp).symm

variable {A : Set (RoundPastingDiagram X)} {p : Prop}

theorem typed_paste (α : Bool) {u : RoundPastingDiagram X} (hu : u ∈ A) {H : PdHom X}
    (hdu : u.dim = H.k + 1) (hs : (H.side α).Equiv (u.boundary H.k (!α))) :
    (paste α u.toPastingDiagram H.k).Typed A p H (H.setSide α (u.boundary H.k α)) := by
  have hr := isRound_boundary_of_isRound u.isRound H.k (!α)
  have hrw : (u.boundary H.k (!α)).shape.ogp.IsRewritableSubmolecule
      (Within.refl (u.boundary H.k (!α))).image ⊤ :=
    (Within.refl _).isRewritableSubmolecule_image_iff.2
      ⟨Within.isSubmoleculeOf_image_refl _, hr, rfl⟩
  have hw' : Parallel ⟨u.boundary H.k (!α), (Within.refl _).round_image_iff.1 hrw.isRound⟩
      ⟨u.boundary H.k α, isRound_boundary_of_isRound u.isRound H.k α⟩ :=
    parallel_boundary u.isRound hdu (!α) α
  have hdk : (u.boundary H.k (!α)).dim = H.k := dim_boundary _ (by omega) (!α)
  exact .side α u hu hdu _ hrw _ hs.symm ((PdHom.Equiv.refl H).setSide α
    ((equiv_boundary_sidePaste_substitute u.isRound hdu hrw hw'
      (equiv_boundary_dim _ hdk.le α) hdk.ge).trans
      (equiv_substitute_of_image_eq_univ _ hrw _ hw' (Within.image_refl _))))

end CtxExpr

end Atoms.Diagrammatic
