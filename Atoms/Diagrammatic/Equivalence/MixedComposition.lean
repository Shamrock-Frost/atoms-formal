import Atoms.Diagrammatic.Equivalence.Glue

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace MixedPair

variable {α : Bool} {n : ℕ} {e u F₁ F₂ : RoundPastingDiagram X} (eq : Equation α n e u)
  (d : PasteAtData (!α) n F₂ F₁) (hb : (e.boundary n α).Equiv (F₁.boundary n α))

abbrev hostEquation : Equation α n F₁ u := eq.ofEquiv d.dim_u' hb

variable {B : Set (RoundPastingDiagram X)} (s₁ : UnbiasedSolution B (hostEquation eq d hb))

noncomputable def gluedOcc : Within d.sub (s₁.sol.boundary n α) :=
  (d.occ.trans (Within.ofEquiv s₁.data.equiv)).trans s₁.data.occ

theorem equiv_gluedOcc : d.sub.Equiv (F₂.boundary n α) := by
  have h := d.equiv.symm
  rw [Bool.not_not] at h
  exact h

theorem isRewritableSubmolecule_image_gluedOcc :
    (s₁.sol.boundary n α).shape.ogp.IsRewritableSubmolecule (gluedOcc eq d hb s₁).image ⊤ := by
  have hd := (d.occ.isRewritableSubmolecule_image_iff.1 d.rewritable).2
  refine (gluedOcc eq d hb s₁).isRewritableSubmolecule_image_iff.2
    ⟨Within.isSubmoleculeOf_image_trans
      ((d.occ.isSubmoleculeOf_image_trans_ofEquiv_iff s₁.data.equiv).2
        d.rewritable.isSubmoleculeOf) s₁.data.rewritable.isSubmoleculeOf, hd.1, ?_⟩
  rw [hd.2, dim_boundary F₁.toPastingDiagram (by rw [d.dim_u']; omega) (!α),
    dim_boundary s₁.sol.toPastingDiagram (by rw [s₁.data.dim_u']; omega) α]

noncomputable abbrev gluedEquation : Equation α n F₂ s₁.sol :=
  ⟨d.dim_e, s₁.data.dim_u', d.sub, gluedOcc eq d hb s₁,
    isRewritableSubmolecule_image_gluedOcc eq d hb s₁, equiv_gluedOcc d⟩

variable (s₂ : UnbiasedSolution B (gluedEquation eq d hb s₁)) (β : Bool)

private theorem image_dataOcc_glueSol₁ :
    (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β))).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α) := by
  have e : (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β))).image =
      OGP.map (glueSolutions s₁ s₂ β).wK.emb (s₁.data.occ.trans
        ((Within.boundary s₁.sol.toPastingDiagram n α).trans
          (SolutionAmbient.ofSolution s₁ β).wSol)).image := by
    rw [← Within.image_trans]
    rfl
  have e' : (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans
        (SolutionAmbient.ofSolution s₁ β).wSol)).image =
      OGP.map (s₁.side β).geometry.wP.emb (s₁.data.occ.trans
        ((Within.boundary s₁.sol.toPastingDiagram n α).trans
          (Within.pasteAtInr F₁.toPastingDiagram s₁.sol.toPastingDiagram n α s₁.data.occ
            s₁.data.rewritable.isSubmoleculeOf s₁.data.equiv))).image := by
    rw [← Within.image_trans]
    rfl
  have h1 : (SolutionAmbient.ofSolution s₁ β).wE.image =
      OGP.map (s₁.side β).geometry.wP.emb
        (Within.pasteAtInl F₁.toPastingDiagram s₁.sol.toPastingDiagram n α s₁.data.occ
          s₁.data.rewritable.isSubmoleculeOf s₁.data.equiv).image := Within.image_trans _ _
  have h2 : (SolutionAmbient.ofSolution s₁ β).wSol.image =
      OGP.map (s₁.side β).geometry.wP.emb
        (Within.pasteAtInr F₁.toPastingDiagram s₁.sol.toPastingDiagram n α s₁.data.occ
          s₁.data.rewritable.isSubmoleculeOf s₁.data.equiv).image := Within.image_trans _ _
  have h3 : (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans
        (SolutionAmbient.ofSolution s₁ β).wSol)).image =
      (SolutionAmbient.ofSolution s₁ β).wE.image ⊓
        (SolutionAmbient.ofSolution s₁ β).wSol.image := by
    rw [e', image_occurrence_pasteAt, OGP.map_inf, h1, h2]
    rfl
  rw [e, h3, (SolutionAmbient.ofSolution s₁ β).config.inf_eq, map_boundary, ← image_glueFirst]

private theorem image_gluedOcc_glueSol₁ :
    ((gluedOcc eq d hb s₁).trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β))).image =
      (d.occ.trans
        ((Within.boundary F₁.toPastingDiagram n (!α)).trans (glueFirst s₁ s₂ β))).image := by
  let L₁ : Within (F₁.boundary n (!α)) (glueAmbient s₁ s₂ β).toPastingDiagram :=
    (Within.ofEquiv s₁.data.equiv).trans (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β)))
  let L₂ : Within (F₁.boundary n (!α)) (glueAmbient s₁ s₂ β).toPastingDiagram :=
    (Within.boundary F₁.toPastingDiagram n (!α)).trans (glueFirst s₁ s₂ β)
  have hL₁ : L₁.image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α) := by
    change ((Within.ofEquiv s₁.data.equiv).trans (s₁.data.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β)))).image = _
    rw [Within.image_trans, Within.image_ofEquiv]
    exact image_dataOcc_glueSol₁ eq d hb s₁ s₂ β
  have hL₂ : L₂.image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α) :=
    Within.image_boundary_trans _ _ _
  have hL := Within.emb_apply_eq_of_image_eq L₁ L₂ (hL₁.trans hL₂.symm)
  refine congrArg (fun f => OGP.map f ⊤) ?_
  ext y
  exact hL (d.occ.emb y)

theorem image_occ_glueFirst :
    (d.occ.trans
      ((Within.boundary F₁.toPastingDiagram n (!α)).trans (glueFirst s₁ s₂ β))).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  rw [← image_occ_glueFirstSol s₁ s₂ β]
  exact (image_gluedOcc_glueSol₁ eq d hb s₁ s₂ β).symm

theorem isSubmoleculeOf_boundary_glueSecond :
    IsSubmoleculeOf (glueAmbient s₁ s₂ β).shape.ogp
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α)
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α)) := by
  rw [← image_occ_glueFirst eq d hb s₁ s₂ β,
    ← Within.image_boundary_trans (glueFirst s₁ s₂ β) n (!α), Within.image_trans]
  exact (isSubmoleculeOf_map_iff ((Within.boundary F₁.toPastingDiagram n (!α)).trans
    (glueFirst s₁ s₂ β)).emb).2 d.rewritable.isSubmoleculeOf

theorem inter_glueSecond_glueFirst :
    (glueSecond s₁ s₂ β).image ⊓ (glueFirst s₁ s₂ β).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxW, hxV⟩ := LowerSet.mem_inf_iff.1 hx
    have h1 : x ∈ (glueFirst s₁ s₂ β).image ⊓ (glueSolutions s₁ s₂ β).wP.image :=
      LowerSet.mem_inf_iff.2 ⟨hxV, by
        rw [image_wP_glueSolutions]; exact LowerSet.mem_sup_iff.2 (Or.inl hxW)⟩
    rw [(isPastingAtIn_glueFirst s₁ s₂ β).inf_eq] at h1
    have h2 := (isPastingAtIn_glueFirst s₁ s₂ β).isSubmoleculeOf_boundary.le h1
    have h3 : x ∈ (glueSecond s₁ s₂ β).image ⊓
        (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSolutions s₁ s₂ β).wP.image n α :=
      LowerSet.mem_inf_iff.2 ⟨hxW, h2⟩
    rw [(isPastingAtIn_glueSecond s₁ s₂ β).inf_boundary_eq_left
      (by rw [krullDim_glueSecond]; exact_mod_cast n.le_succ)
      (by rw [krullDim_glueSecondSol]; exact_mod_cast n.le_succ)] at h3
    exact h3
  · intro x hx
    exact LowerSet.mem_inf_iff.2 ⟨boundary_le _ _ _ hx,
      boundary_le _ _ _ ((isSubmoleculeOf_boundary_glueSecond eq d hb s₁ s₂ β).le hx)⟩

theorem isPastingAtIn_glueSecond_glueFirst :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n (!α) (glueSecond s₁ s₂ β).image
      (glueFirst s₁ s₂ β).image ((glueSecond s₁ s₂ β).image ⊔ (glueFirst s₁ s₂ β).image) :=
  ⟨(glueSecond s₁ s₂ β).isMoleculeIn_image, (glueFirst s₁ s₂ β).isMoleculeIn_image, rfl, by
      rw [Bool.not_not]; exact inter_glueSecond_glueFirst eq d hb s₁ s₂ β, by
      rw [inter_glueSecond_glueFirst eq d hb s₁ s₂ β]
      exact isSubmoleculeOf_boundary_glueSecond eq d hb s₁ s₂ β⟩

theorem isPastingAtIn_glueUnion :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α
      ((glueSecond s₁ s₂ β).image ⊔ (glueFirst s₁ s₂ β).image) (glueSecondSol s₁ s₂ β).image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) := by
  have h₃ : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueSecond s₁ s₂ β).image
      (glueSecondSol s₁ s₂ β).image
      ((glueSecond s₁ s₂ β).image ⊔ (glueSecondSol s₁ s₂ β).image) := by
    rw [← image_wP_glueSolutions]; exact isPastingAtIn_glueSecond s₁ s₂ β
  have h₂ : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueFirst s₁ s₂ β).image
      ((glueSecond s₁ s₂ β).image ⊔ (glueSecondSol s₁ s₂ β).image)
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) := by
    rw [← image_wP_glueSolutions]; exact isPastingAtIn_glueFirst s₁ s₂ β
  exact (isPastingAtIn_glueSecond_glueFirst eq d hb s₁ s₂ β).assoc_mixed_left h₃ h₂
    ((glueSecond s₁ s₂ β).round_image_iff.2 F₂.isRound) (krullDim_glueSecond s₁ s₂ β)
    (by rw [krullDim_glueFirst]; exact_mod_cast n.le_succ)
    (by rw [krullDim_glueSecondSol]; exact_mod_cast n.le_succ)

theorem image_occ_glueU_eq_boundary :
    (eq.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans (glueU s₁ s₂ β))).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary
        ((glueSecond s₁ s₂ β).image ⊔ (glueFirst s₁ s₂ β).image) n α := by
  have h := (isPastingAtIn_glueSecond_glueFirst eq d hb s₁ s₂ β).boundary_not
  rw [Bool.not_not] at h
  rw [h]
  exact image_occ_glueU s₁ s₂ β

end MixedPair

theorem nonempty_unbiasedSolution_compose_mixed {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {e u F₁ F₂ : RoundPastingDiagram X} (eq : Equation α n e u) (d : PasteAtData (!α) n F₂ F₁)
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram e.toPastingDiagram d.pasting)
    (h₁ : UnbiasedSide (TClosure A) α F₁)
    (h₂ : UnbiasedSide (TClosure A) α F₂) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨k₀, -, hk₀⟩ := pair false
  have hb₀ : (e.boundary n α).Equiv (d.pasting.boundary n α) :=
    hk₀.equiv_boundary (Nat.lt_succ_self n) α
  have hb₁ : (d.pasting.boundary n α).Equiv (F₁.boundary n α) := by
    simpa only [Bool.not_not] using d.equiv_boundary_not
  have hb : (e.boundary n α).Equiv (F₁.boundary n α) := hb₀.trans hb₁
  obtain ⟨s₁⟩ := h₁ n u (MixedPair.hostEquation eq d hb)
  obtain ⟨s₂⟩ := h₂ n s₁.sol (MixedPair.gluedEquation eq d hb s₁)
  let eq' : Equation α n d.round u := eq.ofEquiv d.dim_pasting hb₀
  let SA β := SolutionAmbient.ofGlue s₁ s₂ β d _ _
    (MixedPair.isPastingAtIn_glueSecond_glueFirst eq d hb s₁ s₂ β)
    ((MixedPair.image_occ_glueFirst eq d hb s₁ s₂ β).trans
      (MixedPair.inter_glueSecond_glueFirst eq d hb s₁ s₂ β).symm)
    (MixedPair.isPastingAtIn_glueUnion eq d hb s₁ s₂ β) eq'
    (MixedPair.image_occ_glueU_eq_boundary eq d hb s₁ s₂ β)
  exact nonempty_unbiasedSolution_of_pair hDgn eq (P := d.round) d.dim_pasting hb₀ pair
    (UnbiasedSolution.ofAmbients (SA false) (SA true)
      (tClosure_glueAmbient s₁ s₂ false hDgn fun _ h => h)
      (tClosure_glueAmbient s₁ s₂ true hDgn fun _ h => h))

end Atoms.Diagrammatic
