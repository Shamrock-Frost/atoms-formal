import Atoms.Diagrammatic.GrayTensor.Pasting
import Atoms.Diagrammatic.Context.Syntax
import Atoms.Diagrammatic.Context.OfFrames

open CategoryTheory Atoms.Molecule Atoms.Molecule.OGP Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

structure Staircase (X : DiagSet.{u}) where
  ambient : PastingDiagram X
  inner : PastingDiagram X
  innerWithin : Within inner ambient
  level : ℕ
  side : ℕ → Bool
  sign : ℕ → Bool
  length : ℕ
  piece : ℕ → RoundPastingDiagram X
  pieceWithin : ∀ j, Within (piece j).toPastingDiagram ambient
  stage : ℕ → ℕ → LowerSet ambient.shape.ogp
  dim_piece : ∀ j < length, (piece j).dim = level + j + 1
  stage_zero : ∀ n,
    stage n 0 = ambient.shape.ogp.boundary innerWithin.image (level + 1 + n) (sign n)
  isPastingAtIn_stage_self : ∀ j < length,
    ambient.shape.ogp.IsPastingAtIn (level + j) (side j) (pieceWithin j).image (stage j j)
      (stage j (j + 1))
  inf_stage : ∀ n j, j ≤ n → j < length →
    (pieceWithin j).image ⊓ stage n j = (pieceWithin j).image ⊓ stage j j
  stage_succ : ∀ n j, j ≤ n → j < length → stage n (j + 1) = (pieceWithin j).image ⊔ stage n j
  stage_succ_of_le : ∀ n j, j ≤ n → length ≤ j → stage n (j + 1) = stage n j

namespace Staircase

variable (S : Staircase X)

theorem image_argWithin (n : ℕ) :
    ((Within.boundary S.inner (S.level + 1 + n) (S.sign n)).trans S.innerWithin).image =
      S.stage n 0 := by
  rw [Within.image_boundary_trans, S.stage_zero]

private theorem boundary_stage_of_le {j n : ℕ} (hjn : j ≤ n)
    (hc : ∀ i < j, i < S.length → ∀ n', i ≤ n' → S.ambient.shape.ogp.IsPastingAtIn (S.level + i)
      (S.side i) (S.pieceWithin i).image (S.stage n' i) (S.stage n' (i + 1))) :
    ∀ i ≤ j, S.ambient.shape.ogp.boundary (S.stage n i) (S.level + j) (S.side j) =
      S.ambient.shape.ogp.boundary (S.stage j i) (S.level + j) (S.side j) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hg := S.innerWithin.isMoleculeIn_image.isGlobular
    rw [S.stage_zero, S.stage_zero, hg _ _ (by omega), hg _ _ (by omega)]
  | succ i ih =>
    intro hi
    by_cases hiL : i < S.length
    · have hd : Order.krullDim (S.pieceWithin i).image ≤ (S.level + j : ℕ) := by
        rw [Within.krullDim_image, S.dim_piece i hiL]
        exact_mod_cast (by omega : S.level + i + 1 ≤ S.level + j)
      rw [(hc i (by omega) hiL n (by omega)).boundary_eq_sup_of_lt (by omega) hd,
        (hc i (by omega) hiL j (by omega)).boundary_eq_sup_of_lt (by omega) hd, ih (by omega)]
    · rw [S.stage_succ_of_le n i (by omega) (by omega),
        S.stage_succ_of_le j i (by omega) (by omega), ih (by omega)]

theorem isPastingAtIn_stage : ∀ j < S.length, ∀ n, j ≤ n →
    S.ambient.shape.ogp.IsPastingAtIn (S.level + j) (S.side j) (S.pieceWithin j).image (S.stage n j)
      (S.stage n (j + 1)) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hj n hjn
    have hd := S.isPastingAtIn_stage_self j hj
    have hb := S.boundary_stage_of_le hjn (fun i hi hiL n' hn' => IH i hi hiL n' hn') j le_rfl
    have hm : IsMoleculeIn S.ambient.shape.ogp (S.stage n j) := by
      rcases j with _ | j
      · rw [S.stage_zero]; exact S.innerWithin.isMoleculeIn_image.boundary _ _
      · exact (IH j (by omega) (by omega) n (by omega)).isMoleculeIn
    refine ⟨hd.isMoleculeIn_left, hm, S.stage_succ n j hjn hj, ?_, ?_⟩
    · rw [S.inf_stage n j hjn hj]; exact hd.inf_eq
    · rw [S.inf_stage n j hjn hj, hb]; exact hd.isSubmoleculeOf_inf

theorem boundary_stage (j n : ℕ) (hjn : j ≤ n) :
    S.ambient.shape.ogp.boundary (S.stage n j) (S.level + j) (S.side j) =
      S.ambient.shape.ogp.boundary (S.stage j j) (S.level + j) (S.side j) :=
  S.boundary_stage_of_le hjn (fun i _ hiL n' hn' => S.isPastingAtIn_stage i hiL n' hn') j le_rfl

theorem isMoleculeIn_stage (n : ℕ) : ∀ j, j ≤ n + 1 → IsMoleculeIn S.ambient.shape.ogp (S.stage n j)
  | 0, _ => by rw [S.stage_zero]; exact S.innerWithin.isMoleculeIn_image.boundary _ _
  | j + 1, hj => by
    by_cases hjL : j < S.length
    · exact (S.isPastingAtIn_stage j hjL n (by omega)).isMoleculeIn
    · rw [S.stage_succ_of_le n j (by omega) (by omega)]
      exact isMoleculeIn_stage n j (by omega)

theorem isMoleculeIn_boundary_stage_self (j : ℕ) :
    IsMoleculeIn S.ambient.shape.ogp
      (S.ambient.shape.ogp.boundary (S.stage j j) (S.level + j) (S.side j)) :=
  (S.isMoleculeIn_stage j j (by omega)).boundary _ _

open Classical in
noncomputable def sideDiagram (j : ℕ) : PastingDiagram X :=
  S.ambient.restrictTo (S.isMoleculeIn_boundary_stage_self j)

open Classical in
noncomputable def sideWithin (j : ℕ) : Within (S.sideDiagram j) S.ambient :=
  Within.restrictTo S.ambient (S.isMoleculeIn_boundary_stage_self j)

theorem image_sideWithin (j : ℕ) :
    (S.sideWithin j).image =
      S.ambient.shape.ogp.boundary (S.stage j j) (S.level + j) (S.side j) := by
  classical
  exact Within.image_restrictTo _ _

noncomputable def occ (j : ℕ) (hj : j < S.length) :
    Within ((S.piece j).toPastingDiagram.boundary (S.level + j) (!S.side j)) (S.sideDiagram j) :=
  ((Within.boundary _ _ _).trans (S.pieceWithin j)).ofImageLE (S.sideWithin j) (by
    rw [Within.image_boundary_trans, image_sideWithin]
    exact (S.isPastingAtIn_stage_self j hj).isSubmoleculeOf_boundary.le)

theorem image_occ_trans (j : ℕ) (hj : j < S.length) :
    ((S.occ j hj).trans (S.sideWithin j)).image =
      S.ambient.shape.ogp.boundary (S.pieceWithin j).image (S.level + j) (!S.side j) := by
  rw [occ, Within.image_ofImageLE_trans, Within.image_boundary_trans]

theorem dim_sideDiagram (j : ℕ) (hj : j < S.length) : (S.sideDiagram j).dim = S.level + j := by
  have hd := S.dim_piece j hj
  have hb : Order.krullDim (S.ambient.shape.ogp.boundary (S.pieceWithin j).image (S.level + j)
      (!S.side j)) = (S.level + j : ℕ) := by
    rw [← Within.image_boundary_trans, Within.krullDim_image,
      dim_boundary _ (by rw [hd]; omega)]
  have h := (S.sideWithin j).krullDim_image
  rw [image_sideWithin] at h
  refine Nat.cast_injective (R := WithBot ℕ∞) (h.symm.trans (le_antisymm
    (krullDim_boundary_le _ _ _) ?_))
  rw [← hb]
  exact LowerSet.krullDim_mono (S.isPastingAtIn_stage_self j hj).isSubmoleculeOf_boundary.le

theorem isRewritableSubmolecule_occ (j : ℕ) (hj : j < S.length) :
    (S.sideDiagram j).shape.ogp.IsRewritableSubmolecule (S.occ j hj).image ⊤ := by
  have hd := S.dim_piece j hj
  refine (S.occ j hj).isRewritableSubmolecule_image_iff.2
    ⟨?_, isRound_boundary_of_isRound (S.piece j).isRound _ _, ?_⟩
  · rw [← isSubmoleculeOf_map_iff (S.sideWithin j).emb, ← Within.image_trans, image_occ_trans]
    change S.ambient.shape.ogp.IsSubmoleculeOf _ (S.sideWithin j).image
    rw [image_sideWithin]
    exact (S.isPastingAtIn_stage_self j hj).isSubmoleculeOf_boundary
  · rw [S.dim_sideDiagram j hj, dim_boundary _ (by rw [hd]; omega)]

noncomputable def step (j : ℕ) (hj : j < S.length) : CtxExpr X :=
  .side (S.side j) (S.piece j).toPastingDiagram (S.level + j) (S.occ j hj)
    (S.isRewritableSubmolecule_occ j hj).isSubmoleculeOf (.refl _)

noncomputable def ctx : ℕ → CtxExpr X
  | 0 => .id
  | j + 1 => if hj : j < S.length then .comp (S.step j hj) (ctx j) else ctx j

theorem ctx_succ {j : ℕ} (hj : j < S.length) : S.ctx (j + 1) = .comp (S.step j hj) (S.ctx j) := by
  rw [ctx, dif_pos hj]

theorem ctx_succ_of_le {j : ℕ} (hj : S.length ≤ j) : S.ctx (j + 1) = S.ctx j := by
  rw [ctx, dif_neg (by omega)]

open Classical in
theorem sidePaste_stage_equiv {j n : ℕ} (hj : j < S.length) (hjn : j ≤ n) :
    (sidePaste (S.side j) (S.piece j).toPastingDiagram (S.level + j) (S.occ j hj)
        (S.isRewritableSubmolecule_occ j hj).isSubmoleculeOf (.refl _)
        (S.ambient.restrictTo (S.isMoleculeIn_stage n j (by omega)))).Equiv
      (S.ambient.restrictTo (S.isMoleculeIn_stage n (j + 1) (by omega))) := by
  have hc := S.isPastingAtIn_stage j hj n hjn
  have hm := S.isMoleculeIn_stage n j (by omega)
  have hb : S.ambient.shape.ogp.boundary (Within.restrictTo S.ambient hm).image (S.level + j)
      (S.side j) = (S.sideWithin j).image := by
    rw [Within.image_restrictTo, image_sideWithin, S.boundary_stage j n hjn]
  have hsQ : ((S.ambient.restrictTo hm).boundary (S.level + j) (S.side j)).Equiv
      (S.sideDiagram j) :=
    Within.equiv_of_image_eq ((Within.boundary _ _ _).trans (Within.restrictTo S.ambient hm))
      (S.sideWithin j) ((Within.image_boundary_trans _ _ _).trans hb)
  have hW : Diagrammatic.sideWithin (Within.restrictTo S.ambient hm) (S.level + j) (S.side j) hsQ =
      S.sideWithin j :=
    Within.ext_of_image_eq _ _ ((Diagrammatic.image_sideWithin _ _ _ hsQ).trans hb)
  refine sidePaste_equiv_restrictTo (S.pieceWithin j) (Within.restrictTo S.ambient hm) hsQ
    (by rw [Within.image_restrictTo]; exact hc) ?_ _
  rw [hW, image_occ_trans, Within.image_restrictTo, hc.inf_eq]

open Classical in
theorem app_equiv_restrictTo_stage : ∀ j n (hjn : j ≤ n + 1),
    ((S.ctx j).app (S.inner.boundary (S.level + 1 + n) (S.sign n))).Equiv
      (S.ambient.restrictTo (S.isMoleculeIn_stage n j hjn))
  | 0, n, _ => Within.equiv_restrictTo_of_eq _ (S.image_argWithin n) _
  | j + 1, n, hjn => by
    by_cases hj : j < S.length
    · have e := app_equiv_restrictTo_stage j n (by omega)
      rw [ctx_succ S hj]
      refine PastingDiagram.Equiv.trans ?_ (S.sidePaste_stage_equiv hj (by omega))
      refine sidePaste_equiv ((e.boundary _ _).trans ?_) e
      have hm := S.isMoleculeIn_stage n j (by omega)
      exact Within.equiv_of_image_eq
        ((Within.boundary _ _ _).trans (Within.restrictTo S.ambient hm)) (S.sideWithin j) (by
          rw [Within.image_boundary_trans, Within.image_restrictTo, image_sideWithin,
            S.boundary_stage j n (by omega)])
    · rw [ctx_succ_of_le S (by omega)]
      exact (app_equiv_restrictTo_stage j n (by omega)).trans
        (S.ambient.equiv_restrictTo_of_eq _ _ (S.stage_succ_of_le n j (by omega) (by omega)).symm)

noncomputable def promHom (j : ℕ) : PdHom X :=
  ⟨S.level + j, (S.ctx j).app (S.inner.boundary (S.level + j) false),
    (S.ctx j).app (S.inner.boundary (S.level + j) true)⟩

@[simp]
theorem side_promHom (j : ℕ) (β : Bool) :
    (S.promHom j).side β = (S.ctx j).app (S.inner.boundary (S.level + j) β) := by
  cases β <;> rfl

open Classical in
private theorem side_promHom_equiv {j : ℕ}
    (hL : (((S.ctx j).app (S.inner.boundary (S.level + 1 + j) (S.sign j))).boundary (S.level + j)
      (S.side j)).Equiv ((S.ctx j).app ((S.inner.boundary (S.level + 1 + j) (S.sign j)).boundary
        (S.level + j) (S.side j)))) :
    ((S.promHom j).side (S.side j)).Equiv (S.sideDiagram j) := by
  rw [side_promHom]
  refine (CtxExpr.app_equiv _ (equiv_boundary_boundary S.inner (by omega) _ _).symm).trans
    (hL.symm.trans (((S.app_equiv_restrictTo_stage j j (by omega)).boundary _ _).trans
      (S.ambient.equiv_boundary_restrictTo _ _ _)))

open Classical in
private theorem typed_step {A : Set (RoundPastingDiagram X)} {p : Prop} {j : ℕ}
    (hj : j < S.length) (hA : S.piece j ∈ A)
    (hL : (((S.ctx j).app (S.inner.boundary (S.level + 1 + j) (S.sign j))).boundary (S.level + j)
      (S.side j)).Equiv ((S.ctx j).app ((S.inner.boundary (S.level + 1 + j) (S.sign j)).boundary
        (S.level + j) (S.side j)))) :
    (S.step j hj).Typed A p (S.promHom j)
      ((S.promHom j).setSide (S.side j) (S.ambient.restrictTo
        ((S.isMoleculeIn_stage j (j + 1) (by omega)).boundary (S.level + j) (S.side j)))) := by
  have eα := S.side_promHom_equiv hL
  have hd := S.dim_piece j hj
  have hr := S.isRewritableSubmolecule_occ j hj
  have hd0 := S.dim_sideDiagram j hj
  have hm := S.isMoleculeIn_stage j j (by omega)
  have hsj : ((S.ambient.restrictTo hm).boundary (S.level + j) (S.side j)).Equiv
      (S.sideDiagram j) :=
    (S.ambient.equiv_boundary_restrictTo _ _ _).trans
      (S.ambient.equiv_restrictTo_of_eq _ _ rfl)
  have hdm : S.level + j ≤ (S.ambient.restrictTo hm).dim := by
    by_contra h
    have e := equiv_boundary_dim (S.ambient.restrictTo hm) (k := S.level + j) (by omega)
      (S.side j)
    have := (dim_eq_of_equiv e).symm.trans ((dim_eq_of_equiv hsj).trans hd0)
    omega
  refine .side (H := S.promHom j) (S.side j) (S.piece j) hA hd (S.occ j hj) hr
    (.refl _) eα.symm ((PdHom.Equiv.refl _).setSide (S.side j) ?_)
  refine (equiv_boundary_sidePaste_of_side (S.piece j).isRound hd hr
    (equiv_boundary_dim _ hd0.le _) hsj hd0.ge hdm).trans ?_
  exact ((S.sidePaste_stage_equiv hj le_rfl).boundary _ _).trans
    (S.ambient.equiv_boundary_restrictTo _ _ _)

open Classical in
private theorem typed_ctx_step {A : Set (RoundPastingDiagram X)} (j : ℕ)
    (hA : j < S.length → S.piece j ∈ A)
    (tp : (S.ctx j).Typed A True (S.inner.homAt (S.level + j)) (S.promHom j))
    (hL : (((S.ctx j).app (S.inner.boundary (S.level + 1 + j) (S.sign j))).boundary (S.level + j)
      (S.side j)).Equiv ((S.ctx j).app ((S.inner.boundary (S.level + 1 + j) (S.sign j)).boundary
        (S.level + j) (S.side j)))) :
    (S.ctx (j + 1)).Typed A True (S.inner.homAt (S.level + j))
      ((S.promHom j).setSide (S.side j) (S.ambient.restrictTo
        ((S.isMoleculeIn_stage j (j + 1) (by omega)).boundary (S.level + j) (S.side j)))) := by
  by_cases hj : j < S.length
  · rw [ctx_succ S hj]
    exact .comp tp (S.typed_step hj (hA hj) hL)
  · rw [ctx_succ_of_le S (by omega)]
    exact tp.congr_codomain (PdHom.equiv_setSide _ ((S.side_promHom_equiv hL).trans
      (S.ambient.equiv_restrictTo_of_eq _ _
        (congrArg (S.ambient.shape.ogp.boundary · (S.level + j) (S.side j))
          (S.stage_succ_of_le j j le_rfl (by omega)).symm))))

private theorem boundary_app_ctx_succ_equiv {A : Set (RoundPastingDiagram X)} {j : ℕ}
    {H' : PdHom X} (ht : (S.ctx (j + 1)).Typed A True (S.inner.homAt (S.level + j)) H')
    (hx : S.level + (j + 1) < S.inner.dim) :
    (((S.ctx (j + 1)).app (S.inner.boundary (S.level + 1 + (j + 1)) (S.sign (j + 1)))).boundary
      (S.level + (j + 1)) (S.side (j + 1))).Equiv ((S.ctx (j + 1)).app
        ((S.inner.boundary (S.level + 1 + (j + 1)) (S.sign (j + 1))).boundary (S.level + (j + 1))
          (S.side (j + 1)))) :=
  ht.ctxLaws.boundary _ (S.inner.inHom_homAt_boundary (by omega) (by omega) (S.sign (j + 1)))
    (by rw [k_homAt]; omega) (by rw [dim_boundary _ (by omega)]; omega) (S.side (j + 1))

open Classical in
theorem typed_ctx {A : Set (RoundPastingDiagram X)} {j : ℕ}
    (hA : ∀ i ≤ j, i < S.length → S.piece i ∈ A) (hx : S.level + j < S.inner.dim) :
    (S.ctx (j + 1)).Typed A True (S.inner.homAt (S.level + j))
      ((S.promHom j).setSide (S.side j) (S.ambient.restrictTo
        ((S.isMoleculeIn_stage j (j + 1) (by omega)).boundary (S.level + j) (S.side j)))) := by
  induction j with
  | zero => exact S.typed_ctx_step 0 (hA 0 le_rfl) (.id (PdHom.Equiv.refl _)) (.refl _)
  | succ j ih =>
    have ht := ih (fun i hi => hA i (by omega)) (by omega)
    have tp : (S.ctx (j + 1)).Typed A True (S.inner.homAt (S.level + (j + 1)))
        (S.promHom (j + 1)) :=
      .promote trivial (k := S.level + j) (by rw [k_homAt]; omega)
        ((S.inner.inHom_homAt_boundary (by omega) (by omega) false).congr
          (S.inner.homAt_boundary_equiv (by omega)).symm)
        ((S.inner.inHom_homAt_boundary (by omega) (by omega) true).congr
          (S.inner.homAt_boundary_equiv (by omega)).symm)
        (ht.congr_domain (S.inner.homAt_boundary_equiv (by omega)).symm) (.refl _)
    exact S.typed_ctx_step (j + 1) (hA (j + 1) le_rfl) tp (S.boundary_app_ctx_succ_equiv ht hx)

theorem exists_typed_step {j : ℕ} (hj : j < S.length) (hx : S.level + j < S.inner.dim) :
    ∃ D : PdHom X, (S.step j hj).Typed Set.univ False (S.promHom j) D := by
  rcases j with _ | j
  · exact ⟨_, S.typed_step hj trivial (.refl _)⟩
  · exact ⟨_, S.typed_step hj trivial (S.boundary_app_ctx_succ_equiv
      (S.typed_ctx (A := Set.univ) (fun _ _ _ => trivial) (by omega)) hx)⟩

open Classical in
theorem app_ctx_succ_equiv_boundary
    (hst : ∀ i, S.stage i (i + 1) =
      S.ambient.shape.ogp.boundary ⊤ (S.level + 1 + i) (S.sign i)) (j : ℕ) :
    ((S.ctx (j + 1)).app (S.inner.boundary (S.level + 1 + j) (S.sign j))).Equiv
      (S.ambient.boundary (S.level + 1 + j) (S.sign j)) :=
  (S.app_equiv_restrictTo_stage (j + 1) j le_rfl).trans
    (Within.equiv_restrictTo_of_eq (Within.boundary _ _ _)
      (by rw [Within.image_boundary, hst]) _).symm

open Classical in
theorem typed_ctx_homAt {A : Set (RoundPastingDiagram X)} {j : ℕ}
    (hA : ∀ i ≤ j, i < S.length → S.piece i ∈ A)
    (hst : ∀ i, S.stage i (i + 1) =
      S.ambient.shape.ogp.boundary ⊤ (S.level + 1 + i) (S.sign i))
    (hsign : ∀ i, S.sign i = !S.side (i + 1))
    (h0 : ((Within.boundary S.inner S.level (!S.side 0)).trans S.innerWithin).image =
      S.ambient.shape.ogp.boundary ⊤ S.level (!S.side 0))
    (hx : S.level + j < S.inner.dim) :
    (S.ctx (j + 1)).Typed A True (S.inner.homAt (S.level + j))
      (S.ambient.homAt (S.level + j)) := by
  refine (S.typed_ctx hA hx).congr_codomain (.of_side (S.side j) rfl ?_ ?_)
  · rw [PdHom.side_setSide_self, side_homAt]
    refine (Within.equiv_restrictTo_of_eq (Within.boundary _ _ _) ?_ _).symm
    rw [Within.image_boundary, hst, S.ambient.shape.isMolecule.isGlobular _ _ (by omega)]
  · rw [PdHom.side_setSide_not, side_promHom, side_homAt]
    rcases j with _ | j
    · exact Within.equiv_of_image_eq _ (Within.boundary S.ambient _ _)
        (h0.trans (Within.image_boundary _ _ _).symm)
    · rw [← hsign, show S.level + (j + 1) = S.level + 1 + j by omega]
      exact S.app_ctx_succ_equiv_boundary hst j

theorem isRoundCtx_ctx (hM : S.ambient.IsRound) (hI : S.inner.IsRound)
    (hst : ∀ i, S.stage i (i + 1) =
      S.ambient.shape.ogp.boundary ⊤ (S.level + 1 + i) (S.sign i))
    {j : ℕ} (hx : S.level + j < S.inner.dim) :
    IsRoundCtx (S.inner.homAt (S.level + j)) (S.ctx (j + 1)) := by
  have ht := S.typed_ctx (A := Set.univ) (fun _ _ _ => trivial) hx
  have hin := S.inner.inHom_homAt_boundary (n := S.level + j) (N := S.level + 1 + j) (by omega)
    (by omega) (S.sign j)
  refine isRoundCtx_of_isRound_app ht ⟨hin.mapTo (Limits.terminal.from X),
    (dim_boundary S.inner (by omega : S.level + 1 + j ≤ S.inner.dim) (S.sign j)).trans
      (Nat.add_right_comm _ _ _), isRound_boundary_of_isRound hI _ _⟩ ?_
  exact (ht.app_mapTo (Limits.terminal.from X) _ hin).isRound_iff.2
    ((S.app_ctx_succ_equiv_boundary hst j).isRound_iff.2 (isRound_boundary_of_isRound hM _ _))

open Classical in
theorem exists_typed_homAt {A : Set (RoundPastingDiagram X)} (hA : ∀ j < S.length, S.piece j ∈ A)
    (hst : ∀ j, S.stage j (j + 1) =
      S.ambient.shape.ogp.boundary ⊤ (S.level + 1 + j) (S.sign j))
    (hsign : ∀ j, S.sign j = !S.side (j + 1))
    (h0 : ((Within.boundary S.inner S.level (!S.side 0)).trans S.innerWithin).image =
      S.ambient.shape.ogp.boundary ⊤ S.level (!S.side 0))
    {ℓ : ℕ} (hℓ : S.level + ℓ < S.inner.dim) :
    ∃ R : CtxExpr X, R.Typed A True (S.inner.homAt (S.level + ℓ)) (S.ambient.homAt (S.level + ℓ)) ∧
      (R.app (S.inner.boundary (S.level + 1 + ℓ) (S.sign ℓ))).Equiv
        (S.ambient.boundary (S.level + 1 + ℓ) (S.sign ℓ)) :=
  ⟨S.ctx (ℓ + 1), S.typed_ctx_homAt (fun i _ hi => hA i hi) hst hsign h0 hℓ,
    S.app_ctx_succ_equiv_boundary hst ℓ⟩

end Staircase

section Shape

variable {P Q : OGP.{0}} {k : ℕ} {α : Bool} {W U : LowerSet P} {V : LowerSet Q}

variable (hc : P.IsPastingAtIn k α W U (W ⊔ U)) (hV : IsMoleculeIn Q V)
  (hdW : Order.krullDim W ≤ (k + 1 : ℕ))
include hc

private theorem boundary_not_sup_of_le {i : ℕ} (hi : i ≤ k) :
    P.boundary (W ⊔ U) i (!α) = P.boundary U i (!α) := by
  rcases hi.lt_or_eq with hi | rfl
  · rw [← hc.isMoleculeIn.isGlobular i k hi (!α) (!α), hc.boundary_not,
      hc.isMoleculeIn_right.isGlobular i k hi (!α) (!α)]
  · exact hc.boundary_not

include hV

private theorem boundary_prod_sup_eq :
    (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) k (!α) =
      (grayProduct P Q).boundary (U ×ˢ V) k (!α) :=
  boundary_prod_congr hc.isMoleculeIn.isGlobular hc.isMoleculeIn_right.isGlobular hV.isGlobular
    hV.isGlobular (fun _ hi => boundary_not_sup_of_le hc hi) (fun _ _ => rfl)

private theorem boundary_prod_sup_le_boundary_prod (n : ℕ) :
    (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) k (!α) ≤
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) := by
  rw [boundary_prod_sup_eq hc hV]
  exact (isGlobular_prod hc.isMoleculeIn_right.isGlobular hV.isGlobular).boundary_le_boundary
    (by omega) _ _

include hdW

private theorem boundary_prod_sup_succ (j : ℕ) :
    (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + (j + 1)) (!α) =
      W ×ˢ Q.boundary V j (xor (k + 1).bodd (!α)) ⊔
        (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α) := by
  rw [show k + (j + 1) = k + 1 + j by omega]
  exact boundary_prod_eq_prod_sup_of_le hc.isMoleculeIn_right.isGlobular hc.isMoleculeIn.isGlobular
    hV.isGlobular (fun i hi => boundary_not_sup_of_le hc hi)
    (fun i hi => hc.boundary_eq_sup_of_lt hi (hdW.trans (by exact_mod_cast hi)) (!α))

private theorem prod_inf_stage {j n : ℕ} (hjn : j ≤ n) :
    W ×ˢ Q.boundary V j (xor (k + 1).bodd (!α)) ⊓
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) ⊔
          (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + j) (!α)) =
      (grayProduct P Q).boundary (W ×ˢ Q.boundary V j (xor (k + 1).bodd (!α))) (k + j) (!α) := by
  have hgW := hc.isMoleculeIn_left.isGlobular
  have hgU := hc.isMoleculeIn_right.isGlobular
  have hgM := hc.isMoleculeIn.isGlobular
  have hgV := hV.isGlobular
  have hgY := hgV.boundary j (xor (k + 1).bodd (!α))
  have hYn : Q.boundary V j (xor (k + 1).bodd (!α)) ≤ Q.boundary V n (xor (k + 1).bodd (!α)) := by
    rcases hjn.lt_or_eq with h | rfl
    · exact hgV.boundary_le_boundary h _ _
    · exact le_rfl
  refine le_antisymm ?_ ?_
  · rw [inf_sup_left]
    refine sup_le ?_ ?_
    · rintro ⟨a, b⟩ ⟨⟨ha, hb⟩, h⟩
      obtain ⟨i, -, hai, -⟩ := (mem_boundary_prod_of_isGlobular hgU hgV).1 h
      have haW : a ∈ P.boundary W k (!α) := by
        rw [← hc.inf_eq]; exact ⟨ha, boundary_le U i _ hai⟩
      refine (mem_boundary_prod_of_isGlobular hgW hgY).2 ⟨k, by omega, haW, ?_⟩
      rwa [Nat.add_sub_cancel_left, boundary_eq_self (krullDim_boundary_le V j _)]
    · exact inf_boundary_prod_le hgW hgM hgY hgV
        (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β)
        (fun i β => (hV.boundary_isSubmoleculeOf j _).inf_boundary_le i β) (k + j) (!α)
  · rintro ⟨a, b⟩ h
    obtain ⟨i, hi, hai, hbi⟩ := (mem_boundary_prod_of_isGlobular hgW hgY).1 h
    have hbY := boundary_le _ _ _ hbi
    refine ⟨⟨boundary_le W i _ hai, hbY⟩, ?_⟩
    by_cases hik : i ≤ k
    · refine Or.inl ?_
      have ha : a ∈ P.boundary W k (!α) := by
        rcases hik.lt_or_eq with h' | rfl
        · exact hgW.boundary_le_boundary h' _ _ hai
        · exact hai
      rw [← hc.inf_eq] at ha
      have hmem : ((a, b) : grayProduct P Q) ∈
          ((W ⊓ U) ×ˢ Q.boundary V n (xor (k + 1).bodd (!α)) : LowerSet (grayProduct P Q)) :=
        ⟨ha, hYn hbY⟩
      exact ((prod_inf_boundary_prod (ℓ := n) hgU hgV hc.inf_le_boundary).symm.le hmem).2
    · refine Or.inr ((mem_boundary_prod_of_isGlobular hgM hgV).2 ⟨i, hi, ?_, ?_⟩)
      · rw [hc.boundary_eq_sup_of_lt (by omega) (hdW.trans (by exact_mod_cast (by omega))) (!α)]
        exact Or.inl (boundary_le W i _ hai)
      · rwa [hgV.boundary_boundary_eq_of_le (by omega) (Or.inl (by omega))] at hbi

private theorem stage_succ_prod {j n : ℕ} (hjn : j ≤ n) :
    (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) ⊔
        (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + (j + 1)) (!α) =
      W ×ˢ Q.boundary V j (xor (k + 1).bodd (!α)) ⊔
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) ⊔
          (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + j) (!α)) := by
  have hgS := isGlobular_prod hc.isMoleculeIn_right.isGlobular hV.isGlobular
  have hS : (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α) ≤
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) := by
    rcases hjn.lt_or_eq with h | rfl
    · exact hgS.boundary_le_boundary (by omega) _ _
    · exact le_rfl
  have hE := (isGlobular_prod hc.isMoleculeIn.isGlobular hV.isGlobular).boundary_le_boundary
    (show k + j < k + (j + 1) by omega) (!α) (!α)
  rw [boundary_prod_sup_succ hc hV hdW j] at hE ⊢
  exact le_antisymm
    (sup_le (le_sup_of_le_right le_sup_left)
      (sup_le le_sup_left (hS.trans (le_sup_of_le_right le_sup_left))))
    (sup_le (le_sup_of_le_right le_sup_left) (sup_le le_sup_left
      (hE.trans (sup_le (le_sup_of_le_right le_sup_left) (hS.trans le_sup_left)))))

private theorem stage_succ_prod_of_le {j n : ℕ} (hV' : Order.krullDim V ≤ j) (hjn : j + 1 ≤ n) :
    (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) ⊔
        (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + (j + 1 + 1)) (!α) =
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) ⊔
        (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + (j + 1)) (!α) := by
  have hgS := isGlobular_prod hc.isMoleculeIn_right.isGlobular hV.isGlobular
  have hle (i : ℕ) (hi : i ≤ n) : (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + i) (!α) ≤
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (!α) := by
    rcases hi.lt_or_eq with h | rfl
    · exact hgS.boundary_le_boundary (by omega) _ _
    · exact le_rfl
  rw [boundary_prod_sup_succ hc hV hdW (j + 1), boundary_prod_sup_succ hc hV hdW j,
    boundary_eq_self (hV'.trans (by exact_mod_cast j.le_succ)), boundary_eq_self hV',
    sup_left_comm, sup_eq_left.2 (hle _ hjn), sup_left_comm, sup_eq_left.2 (hle _ (by omega))]

private theorem isPastingAtIn_prod_stage (j : ℕ) :
    (grayProduct P Q).IsPastingAtIn (k + j) α (W ×ˢ Q.boundary V j (xor (k + 1).bodd (!α)))
      ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α) ⊔
        (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + j) (!α))
      ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α) ⊔
        (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + (j + 1)) (!α)) := by
  have hgW := hc.isMoleculeIn_left.isGlobular
  have hgU := hc.isMoleculeIn_right.isGlobular
  have hgV := hV.isGlobular
  have hgY := hgV.boundary j (xor (k + 1).bodd (!α))
  have hgM := isGlobular_prod hc.isMoleculeIn.isGlobular hgV
  have hmA := isMoleculeIn_prod hc.isMoleculeIn_left (hV.boundary j (xor (k + 1).bodd (!α)))
  have hmB := (isMoleculeIn_prod hc.isMoleculeIn_right hV).boundary (k + 1 + j) (!α)
  have hT := boundary_prod_sup_succ hc hV hdW j
  obtain ⟨g1, g2, g3, g4⟩ := IsGenPastingIn.cond_parts
    (isGenPastingIn_prod_pasteAt (ℓ := j) α hc.isMoleculeIn_left hc.isMoleculeIn_right hV hdW hc)
  rw [← hT, hgM _ _ (by omega)] at g3 g4
  have hpc := isPastingIn_sup_boundary_cond α g1.le g2.le
  rw [← hT, hgM _ _ (by omega), hgM _ _ (by omega)] at hpc
  obtain ⟨-, hm1, hm2⟩ := (isPastingIn_cond_iff α).1 hpc
  have hBE : (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α) ⊓
      (grayProduct P Q).boundary ((W ⊔ U) ×ˢ V) (k + j) (!α) ≤
        (grayProduct P Q).boundary ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (!α))
          (k + j) (!α) := by
    rw [isGlobular_prod hgU hgV _ _ (by omega)]
    exact (inf_le_inf_right _ (boundary_le _ _ _)).trans (inf_boundary_prod_le hgU
      hc.isMoleculeIn.isGlobular hgV hgV (fun i β => hc.isSubmoleculeOf_right.inf_boundary_le i β)
      (fun _ _ => inf_le_right) (k + j) (!α))
  refine ⟨hmA, (g4.isSubmoleculeOf_sup hmB (krullDim_boundary_le _ _ _) hBE).isMoleculeIn_right,
    stage_succ_prod hc hV hdW le_rfl, prod_inf_stage hc hV hdW le_rfl, ?_⟩
  rw [prod_inf_stage hc hV hdW le_rfl, ← hm2, hm1]
  exact g3.boundary_isSubmoleculeOf_boundary_sup hmA (krullDim_boundary_le _ _ _)
    (inf_boundary_prod_le hgW hc.isMoleculeIn.isGlobular hgY hgV
      (fun i β => hc.isSubmoleculeOf_left.inf_boundary_le i β)
      (fun i β => (hV.boundary_isSubmoleculeOf j _).inf_boundary_le i β) (k + j) α)

end Shape

section ShapeRight

variable {P Q : OGP.{0}} {k : ℕ} {α : Bool} {W V : LowerSet Q} {U : LowerSet P}
  (hc : Q.IsPastingAtIn k α W V (W ⊔ V)) (hU : IsMoleculeIn P U)
include hc hU

private theorem boundary_prod_sup_eq_right :
    (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) k (!α) =
      (grayProduct P Q).boundary (U ×ˢ V) k (!α) := by
  have h := congrArg (OGP.map (grayProductSwap P Q).inv)
    (boundary_prod_sup_eq (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU))
  simp only [map_grayProductSwap_inv_boundary_prod] at h
  simp only [Nat.bodd_succ, Bool.not_xor, Bool.not_not, Bool.xor_self, Bool.xor_false,
    Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

private theorem boundary_prod_sup_le_boundary_prod_right (n : ℕ) :
    (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) k (!α) ≤
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) := by
  have h := OGP.map_mono (grayProductSwap P Q).inv (boundary_prod_sup_le_boundary_prod
    (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU) n)
  simp only [map_grayProductSwap_inv_boundary_prod] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

variable (hdW : Order.krullDim W ≤ (k + 1 : ℕ))
include hdW

private theorem prod_inf_stage_right {j n : ℕ} (hjn : j ≤ n) :
    P.boundary U j (xor j.bodd α) ×ˢ W ⊓
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) ⊔
          (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + j) (!xor j.bodd α)) =
      (grayProduct P Q).boundary (P.boundary U j (xor j.bodd α) ×ˢ W) (k + j)
        (!xor j.bodd α) := by
  have h := congrArg (OGP.map (grayProductSwap P Q).inv) (prod_inf_stage
    (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU) hdW hjn)
  rw [OGP.map_inf, OGP.map_sup] at h
  simp only [map_grayProductSwap_inv_boundary_prod, map_grayProductSwap_inv_prod,
    boundary_dual] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

private theorem stage_succ_prod_right {j n : ℕ} (hjn : j ≤ n) :
    (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) ⊔
        (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + (j + 1)) (!xor (j + 1).bodd α) =
      P.boundary U j (xor j.bodd α) ×ˢ W ⊔
        ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) ⊔
          (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + j) (!xor j.bodd α)) := by
  have h := congrArg (OGP.map (grayProductSwap P Q).inv) (stage_succ_prod
    (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU) hdW hjn)
  repeat rw [OGP.map_sup] at h
  simp only [map_grayProductSwap_inv_boundary_prod, map_grayProductSwap_inv_prod,
    boundary_dual] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

private theorem stage_succ_prod_of_le_right {j n : ℕ} (hU' : Order.krullDim U ≤ j)
    (hjn : j + 1 ≤ n) :
    (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) ⊔
        (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + (j + 1 + 1)) (!xor (j + 1 + 1).bodd α) =
      (grayProduct P Q).boundary (U ×ˢ V) (k + 1 + n) (xor n.bodd α) ⊔
        (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + (j + 1)) (!xor (j + 1).bodd α) := by
  have h := congrArg (OGP.map (grayProductSwap P Q).inv) (stage_succ_prod_of_le
    (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU) hdW hU' hjn)
  rw [OGP.map_sup, OGP.map_sup] at h
  simp only [map_grayProductSwap_inv_boundary_prod] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

private theorem isPastingAtIn_prod_stage_right (j : ℕ) :
    (grayProduct P Q).IsPastingAtIn (k + j) (xor j.bodd α) (P.boundary U j (xor j.bodd α) ×ˢ W)
      ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (xor j.bodd α) ⊔
        (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + j) (!xor j.bodd α))
      ((grayProduct P Q).boundary (U ×ˢ V) (k + 1 + j) (xor j.bodd α) ⊔
        (grayProduct P Q).boundary (U ×ˢ (W ⊔ V)) (k + (j + 1)) (!xor (j + 1).bodd α)) := by
  have h := (isPastingAtIn_dual Nat.bodd).1 ((isPastingAtIn_prod_stage
    (isPastingAtIn_dual_bodd hc) ((isMoleculeIn_dual Nat.bodd).2 hU) hdW j).map
      (grayProductSwap P Q).inv)
  repeat rw [OGP.map_sup] at h
  simp only [map_grayProductSwap_inv_boundary_prod, map_grayProductSwap_inv_prod,
    boundary_dual] at h
  simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_xor, Bool.xor_not, Bool.not_not, Bool.xor_assoc,
    Bool.xor_self, Bool.xor_false, Bool.xor_left_comm k.bodd, Bool.xor_comm k.bodd] at h ⊢
  exact h

end ShapeRight

namespace PastingDiagram.Within

variable {m u : PastingDiagram X} {w : RoundPastingDiagram X} (ww : Within w.toPastingDiagram m)
  (wu : Within u m) {k : ℕ} {α : Bool}

private theorem map_boundary_sup_prod_top (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤)
    (v : PastingDiagram Y) (n : ℕ) (β : Bool) :
    OGP.map (m.shape.grayProductIso v.shape).hom ((grayProduct _ _).boundary
        ((ww.image ⊔ wu.image) ×ˢ (⊤ : LowerSet v.shape.ogp)) n β) =
      (m.grayTensor v).shape.ogp.boundary ⊤ n β := by
  rw [← hc.eq_sup, LowerSet.top_prod_top, map_boundary, map_top_of_isIso]
  rfl

noncomputable def grayStaircase
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤) (hw : w.dim = k + 1)
    (v : RoundPastingDiagram Y) : Staircase (Diagrammatic.grayTensor X Y) where
  ambient := m.grayTensor v.toPastingDiagram
  inner := u.grayTensor v.toPastingDiagram
  innerWithin := wu.grayTensor (refl _)
  level := k
  side _ := α
  sign _ := !α
  length := v.dim + 1
  piece j := ⟨w.toPastingDiagram.grayTensor (v.toPastingDiagram.boundary j (xor (k + 1).bodd (!α))),
    isRound_grayTensor w.isRound (isRound_boundary_of_isRound v.isRound _ _)⟩
  pieceWithin j := pastePiece ww α v.toPastingDiagram j
  stage n j := OGP.map (m.shape.grayProductIso v.shape).hom
    ((grayProduct _ _).boundary (wu.image ×ˢ (⊤ : LowerSet v.shape.ogp)) (k + 1 + n) (!α) ⊔
      (grayProduct _ _).boundary ((ww.image ⊔ wu.image) ×ˢ (⊤ : LowerSet v.shape.ogp)) (k + j)
        (!α))
  dim_piece j hj := by
    change (w.toPastingDiagram.grayTensor _).dim = _
    rw [dim_grayTensor, dim_boundary _ (by omega)]
    omega
  stage_zero n := by
    rw [image_grayTensor, image_refl, ← map_boundary]
    exact congrArg _ (sup_eq_left.2 (boundary_prod_sup_le_boundary_prod { hc with eq_sup := rfl }
      v.shape.isMolecule n))
  isPastingAtIn_stage_self j _ := by
    rw [image_pastePiece]
    exact (isPastingAtIn_prod_stage { hc with eq_sup := rfl } v.shape.isMolecule
      (by rw [ww.krullDim_image, hw]) j).map _
  inf_stage n j hjn _ := by
    rw [image_pastePiece, ← OGP.map_inf, ← OGP.map_inf,
      prod_inf_stage { hc with eq_sup := rfl } v.shape.isMolecule
        (by rw [ww.krullDim_image, hw]) hjn,
      prod_inf_stage { hc with eq_sup := rfl } v.shape.isMolecule
        (by rw [ww.krullDim_image, hw]) le_rfl]
  stage_succ n j hjn _ := by
    rw [image_pastePiece, ← OGP.map_sup, stage_succ_prod { hc with eq_sup := rfl }
      v.shape.isMolecule (by rw [ww.krullDim_image, hw]) hjn]
  stage_succ_of_le n j hjn hL := by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact congrArg _ (stage_succ_prod_of_le { hc with eq_sup := rfl } v.shape.isMolecule
      (by rw [ww.krullDim_image, hw])
      (by rw [LowerSet.krullDim_top, v.shape.krullDim_eq_dimension]; exact_mod_cast (by
        change v.dim ≤ j; omega)) hjn)

section GrayStaircase

variable (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤) (hw : w.dim = k + 1)
  (v : RoundPastingDiagram Y)

@[simp]
theorem grayStaircase_ambient :
    (grayStaircase ww wu hc hw v).ambient = m.grayTensor v.toPastingDiagram :=
  rfl

@[simp]
theorem grayStaircase_inner :
    (grayStaircase ww wu hc hw v).inner = u.grayTensor v.toPastingDiagram :=
  rfl

@[simp]
theorem grayStaircase_level : (grayStaircase ww wu hc hw v).level = k :=
  rfl

@[simp]
theorem grayStaircase_side (j : ℕ) : (grayStaircase ww wu hc hw v).side j = α :=
  rfl

@[simp]
theorem grayStaircase_sign (j : ℕ) : (grayStaircase ww wu hc hw v).sign j = !α :=
  rfl

@[simp]
theorem grayStaircase_length : (grayStaircase ww wu hc hw v).length = v.dim + 1 :=
  rfl

@[simp]
theorem grayStaircase_piece (j : ℕ) :
    (grayStaircase ww wu hc hw v).piece j =
      w.grayTensor ⟨v.toPastingDiagram.boundary j (xor (k + 1).bodd (!α)),
        isRound_boundary_of_isRound v.isRound _ _⟩ :=
  rfl

theorem stage_succ_self_grayStaircase (j : ℕ) :
    (grayStaircase ww wu hc hw v).stage j (j + 1) =
      (grayStaircase ww wu hc hw v).ambient.shape.ogp.boundary ⊤
        ((grayStaircase ww wu hc hw v).level + 1 + j) ((grayStaircase ww wu hc hw v).sign j) := by
  have hc' : m.shape.ogp.IsPastingAtIn k α ww.image wu.image (ww.image ⊔ wu.image) :=
    { hc with eq_sup := rfl }
  have hdW : Order.krullDim ww.image ≤ (k + 1 : ℕ) := by rw [ww.krullDim_image, hw]
  change OGP.map _ (_ ⊔ _) = _
  rw [boundary_prod_sup_succ hc' v.shape.isMolecule hdW j, sup_eq_right.2 le_sup_right,
    ← boundary_prod_sup_succ hc' v.shape.isMolecule hdW j, map_boundary_sup_prod_top ww wu hc,
    show k + (j + 1) = k + 1 + j by omega]
  rfl

theorem sign_grayStaircase (j : ℕ) :
    (grayStaircase ww wu hc hw v).sign j = !(grayStaircase ww wu hc hw v).side (j + 1) :=
  rfl

theorem image_boundary_level_grayStaircase :
    ((Within.boundary (grayStaircase ww wu hc hw v).inner (grayStaircase ww wu hc hw v).level
        (!(grayStaircase ww wu hc hw v).side 0)).trans
          (grayStaircase ww wu hc hw v).innerWithin).image =
      (grayStaircase ww wu hc hw v).ambient.shape.ogp.boundary ⊤
        (grayStaircase ww wu hc hw v).level (!(grayStaircase ww wu hc hw v).side 0) := by
  have hc' : m.shape.ogp.IsPastingAtIn k α ww.image wu.image (ww.image ⊔ wu.image) :=
    { hc with eq_sup := rfl }
  change ((boundary (u.grayTensor v.toPastingDiagram) k (!α)).trans
    (wu.grayTensor (refl _))).image = _
  rw [image_boundary_trans, image_grayTensor, image_refl, ← map_boundary,
    ← boundary_prod_sup_eq hc' v.shape.isMolecule, map_boundary_sup_prod_top ww wu hc]
  rfl

end GrayStaircase

theorem exists_typed_grayTensor_pasteAt
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wu.image ⊤) (hw : w.dim = k + 1)
    (v : RoundPastingDiagram Y) {A : Set (RoundPastingDiagram (Diagrammatic.grayTensor X Y))}
    (hA : ∀ j, w.grayTensor ⟨v.toPastingDiagram.boundary j (xor (k + 1).bodd (!α)),
      isRound_boundary_of_isRound v.isRound _ _⟩ ∈ A) {ℓ : ℕ} (hℓ : k + ℓ < u.dim + v.dim) :
    ∃ R : CtxExpr (Diagrammatic.grayTensor X Y),
      R.Typed A True ((u.grayTensor v.toPastingDiagram).homAt (k + ℓ))
        ((m.grayTensor v.toPastingDiagram).homAt (k + ℓ)) ∧
      (R.app ((u.grayTensor v.toPastingDiagram).boundary (k + 1 + ℓ) (!α))).Equiv
        ((m.grayTensor v.toPastingDiagram).boundary (k + 1 + ℓ) (!α)) :=
  ⟨_, (grayStaircase ww wu hc hw v).typed_ctx_homAt (fun i _ _ => hA i)
      (stage_succ_self_grayStaircase ww wu hc hw v) (sign_grayStaircase ww wu hc hw v)
      (image_boundary_level_grayStaircase ww wu hc hw v)
      (by rw [grayStaircase_level, grayStaircase_inner, dim_grayTensor]; exact hℓ),
    (grayStaircase ww wu hc hw v).app_ctx_succ_equiv_boundary
      (stage_succ_self_grayStaircase ww wu hc hw v) ℓ⟩

end PastingDiagram.Within

namespace PastingDiagram.Within

variable {m v : PastingDiagram Y} {w : RoundPastingDiagram Y} (ww : Within w.toPastingDiagram m)
  (wv : Within v m) {k : ℕ} {α : Bool}

private theorem map_boundary_prod_sup_top
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wv.image ⊤) (u : PastingDiagram X) (n : ℕ)
    (β : Bool) :
    OGP.map (u.shape.grayProductIso m.shape).hom ((grayProduct _ _).boundary
        ((⊤ : LowerSet u.shape.ogp) ×ˢ (ww.image ⊔ wv.image)) n β) =
      (u.grayTensor m).shape.ogp.boundary ⊤ n β := by
  rw [← hc.eq_sup, LowerSet.top_prod_top, map_boundary, map_top_of_isIso]
  rfl

private noncomputable def grayStaircaseRight
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wv.image ⊤) (hw : w.dim = k + 1)
    (u : RoundPastingDiagram X) : Staircase (Diagrammatic.grayTensor X Y) where
  ambient := u.toPastingDiagram.grayTensor m
  inner := u.toPastingDiagram.grayTensor v
  innerWithin := (refl _).grayTensor wv
  level := k
  side j := xor j.bodd α
  sign n := xor n.bodd α
  length := u.dim + 1
  piece j := ⟨(u.toPastingDiagram.boundary j (xor j.bodd α)).grayTensor w.toPastingDiagram,
    isRound_grayTensor (isRound_boundary_of_isRound u.isRound _ _) w.isRound⟩
  pieceWithin j := pastePieceRight ww α u.toPastingDiagram j
  stage n j := OGP.map (u.shape.grayProductIso m.shape).hom
    ((grayProduct _ _).boundary ((⊤ : LowerSet u.shape.ogp) ×ˢ wv.image) (k + 1 + n)
      (xor n.bodd α) ⊔
    (grayProduct _ _).boundary ((⊤ : LowerSet u.shape.ogp) ×ˢ (ww.image ⊔ wv.image)) (k + j)
      (!xor j.bodd α))
  dim_piece j hj := by
    change ((u.toPastingDiagram.boundary j _).grayTensor w.toPastingDiagram).dim = _
    rw [dim_grayTensor, dim_boundary _ (by omega)]
    omega
  stage_zero n := by
    rw [image_grayTensor, image_refl, ← map_boundary, Nat.bodd_zero, Bool.false_xor,
      Nat.add_zero]
    exact congrArg _ (sup_eq_left.2 (boundary_prod_sup_le_boundary_prod_right
      { hc with eq_sup := rfl } u.shape.isMolecule n))
  isPastingAtIn_stage_self j _ := by
    rw [image_pastePieceRight]
    exact (isPastingAtIn_prod_stage_right { hc with eq_sup := rfl } u.shape.isMolecule
      (by rw [ww.krullDim_image, hw]) j).map _
  inf_stage n j hjn _ := by
    rw [image_pastePieceRight, ← OGP.map_inf, ← OGP.map_inf,
      prod_inf_stage_right { hc with eq_sup := rfl } u.shape.isMolecule
        (by rw [ww.krullDim_image, hw]) hjn,
      prod_inf_stage_right { hc with eq_sup := rfl } u.shape.isMolecule
        (by rw [ww.krullDim_image, hw]) le_rfl]
  stage_succ n j hjn _ := by
    rw [image_pastePieceRight, ← OGP.map_sup, stage_succ_prod_right { hc with eq_sup := rfl }
      u.shape.isMolecule (by rw [ww.krullDim_image, hw]) hjn]
  stage_succ_of_le n j hjn hL := by
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact congrArg _ (stage_succ_prod_of_le_right { hc with eq_sup := rfl } u.shape.isMolecule
      (by rw [ww.krullDim_image, hw])
      (by rw [LowerSet.krullDim_top, u.shape.krullDim_eq_dimension]; exact_mod_cast (by
        change u.dim ≤ j; omega)) hjn)

theorem exists_typed_grayTensor_pasteAt_right
    (hc : m.shape.ogp.IsPastingAtIn k α ww.image wv.image ⊤) (hw : w.dim = k + 1)
    (u : RoundPastingDiagram X) {A : Set (RoundPastingDiagram (Diagrammatic.grayTensor X Y))}
    (hA : ∀ j, RoundPastingDiagram.grayTensor ⟨u.toPastingDiagram.boundary j (xor j.bodd α),
      isRound_boundary_of_isRound u.isRound _ _⟩ w ∈ A) {ℓ : ℕ} (hℓ : k + ℓ < u.dim + v.dim) :
    ∃ R : CtxExpr (Diagrammatic.grayTensor X Y),
      R.Typed A True ((u.toPastingDiagram.grayTensor v).homAt (k + ℓ))
        ((u.toPastingDiagram.grayTensor m).homAt (k + ℓ)) ∧
      (R.app ((u.toPastingDiagram.grayTensor v).boundary (k + 1 + ℓ) (xor ℓ.bodd α))).Equiv
        ((u.toPastingDiagram.grayTensor m).boundary (k + 1 + ℓ) (xor ℓ.bodd α)) := by
  classical
  have hc' : m.shape.ogp.IsPastingAtIn k α ww.image wv.image (ww.image ⊔ wv.image) :=
    { hc with eq_sup := rfl }
  have hdW : Order.krullDim ww.image ≤ (k + 1 : ℕ) := by rw [ww.krullDim_image, hw]
  have hs (j : ℕ) : (!xor (j + 1).bodd α) = xor j.bodd α := by
    rw [Nat.bodd_succ, Bool.not_xor, Bool.not_not]
  let S := grayStaircaseRight ww wv hc hw u
  refine S.exists_typed_homAt (A := A) (fun j _ => hA j) (fun j => ?_) (fun j => (hs j).symm) ?_
    (by change k + ℓ < (u.toPastingDiagram.grayTensor v).dim; rw [dim_grayTensor]; exact hℓ)
  · change OGP.map _ (_ ⊔ _) = _
    rw [hs, show k + (j + 1) = k + 1 + j by omega,
      boundary_prod_pasteAt_right u.shape.isMolecule hdW hc', sup_eq_right.2 le_sup_right,
      ← boundary_prod_pasteAt_right u.shape.isMolecule hdW hc', map_boundary_prod_sup_top ww wv hc]
    rfl
  · change ((boundary (u.toPastingDiagram.grayTensor v) k (!xor (0 : ℕ).bodd α)).trans
      ((refl _).grayTensor wv)).image =
        (u.toPastingDiagram.grayTensor m).shape.ogp.boundary ⊤ k (!xor (0 : ℕ).bodd α)
    rw [Nat.bodd_zero, Bool.false_xor, image_boundary_trans, image_grayTensor, image_refl,
      ← map_boundary, ← boundary_prod_sup_eq_right hc' u.shape.isMolecule,
      map_boundary_prod_sup_top ww wv hc]

end PastingDiagram.Within

namespace PastingDiagram

theorem isPastingAtIn_refl_boundary (u : PastingDiagram X) (k : ℕ) (α : Bool) :
    u.shape.ogp.IsPastingAtIn k α (Within.refl u).image (Within.boundary u k (!α)).image ⊤ := by
  rw [Within.image_refl, Within.image_boundary]
  have hb := u.shape.isMolecule.boundary k (!α)
  refine ⟨u.shape.isMolecule, hb, (top_sup_eq _).symm, top_inf_eq _, ?_⟩
  rw [top_inf_eq, boundary_eq_self (krullDim_boundary_le _ _ _)]
  exact IsSubmoleculeOf.refl hb

theorem exists_typed_grayTensor_self (u : RoundPastingDiagram X) {k : ℕ} (hu : u.dim = k + 1)
    (α : Bool) (v : RoundPastingDiagram Y)
    {A : Set (RoundPastingDiagram (Diagrammatic.grayTensor X Y))}
    (hA : ∀ j, u.grayTensor ⟨v.toPastingDiagram.boundary j (xor (k + 1).bodd (!α)),
      isRound_boundary_of_isRound v.isRound _ _⟩ ∈ A) {ℓ : ℕ} (hℓ : ℓ < v.dim) :
    ∃ R : CtxExpr (Diagrammatic.grayTensor X Y),
      R.Typed A True (((u.boundary k (!α)).grayTensor v.toPastingDiagram).homAt (k + ℓ))
        ((u.grayTensor v).toPastingDiagram.homAt (k + ℓ)) ∧
      (R.app (((u.boundary k (!α)).grayTensor v.toPastingDiagram).boundary (k + 1 + ℓ) (!α))).Equiv
        ((u.grayTensor v).toPastingDiagram.boundary (k + 1 + ℓ) (!α)) :=
  Within.exists_typed_grayTensor_pasteAt (Within.refl u.toPastingDiagram) (Within.boundary _ k (!α))
    (isPastingAtIn_refl_boundary _ k α) hu v hA
    (by rw [dim_boundary _ (by rw [hu]; omega)]; omega)

theorem exists_typed_grayTensor_self_right (u : RoundPastingDiagram X)
    (v : RoundPastingDiagram Y) {k : ℕ} (hv : v.dim = k + 1) (α : Bool)
    {A : Set (RoundPastingDiagram (Diagrammatic.grayTensor X Y))}
    (hA : ∀ j, RoundPastingDiagram.grayTensor ⟨u.toPastingDiagram.boundary j (xor j.bodd α),
      isRound_boundary_of_isRound u.isRound _ _⟩ v ∈ A) {ℓ : ℕ} (hℓ : ℓ < u.dim) :
    ∃ R : CtxExpr (Diagrammatic.grayTensor X Y),
      R.Typed A True ((u.toPastingDiagram.grayTensor (v.boundary k (!α))).homAt (k + ℓ))
        ((u.grayTensor v).toPastingDiagram.homAt (k + ℓ)) ∧
      (R.app ((u.toPastingDiagram.grayTensor (v.boundary k (!α))).boundary (k + 1 + ℓ)
        (xor ℓ.bodd α))).Equiv
        ((u.grayTensor v).toPastingDiagram.boundary (k + 1 + ℓ) (xor ℓ.bodd α)) :=
  Within.exists_typed_grayTensor_pasteAt_right (Within.refl v.toPastingDiagram)
    (Within.boundary _ k (!α)) (isPastingAtIn_refl_boundary _ k α) hv u hA
    (by rw [dim_boundary _ (by rw [hv]; omega)]; omega)

end PastingDiagram

end Atoms.Diagrammatic
