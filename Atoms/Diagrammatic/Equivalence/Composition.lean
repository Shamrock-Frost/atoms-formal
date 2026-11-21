import Atoms.Diagrammatic.Equivalence.Glue

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

structure ComposePair {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (eq : Equation α n e u)
    (F₁ F₂ : RoundPastingDiagram X) where
  dim_F₁ : F₁.dim = n + 1
  dim_F₂ : F₂.dim = n + 1
  sub : PastingDiagram X
  κ : Within sub eq.sub
  rewritable : eq.sub.shape.ogp.IsRewritableSubmolecule κ.image ⊤
  equiv₁ : sub.Equiv (F₁.boundary n α)
  equiv₂ : (eq.sub.substitute κ rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
    (Equation.ofTrans dim_F₁ eq.dim_u eq.occ eq.rewritable κ rewritable equiv₁).parallel_occ).Equiv
      (F₂.boundary n α)

namespace ComposePair

variable {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} {eq : Equation α n e u}
  {F₁ F₂ : RoundPastingDiagram X} (c : ComposePair eq F₁ F₂)

abbrev first : Equation α n F₁ u :=
  Equation.ofTrans c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable c.equiv₁

noncomputable abbrev occ : Within (F₁.boundary n (!α)) (F₂.boundary n α) :=
  (Within.substitute c.κ c.rewritable _ _).trans (Within.ofEquiv c.equiv₂)

variable {B : Set (RoundPastingDiagram X)} (s₁ : UnbiasedSolution B c.first)

theorem equiv_substOcc_boundary :
    (substOccDiagram c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable c.equiv₁ s₁).Equiv
      (F₂.boundary n α) :=
  PastingDiagram.Equiv.trans
    (equiv_substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable c.equiv₁ s₁) c.equiv₂

theorem isRewritableSubmolecule_image_substOcc :
    (s₁.sol.boundary n α).shape.ogp.IsRewritableSubmolecule
      (substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable c.equiv₁ s₁).image ⊤ :=
  Within.isRewritableSubmolecule_of_equiv_boundary (isSubmoleculeOf_image_occurrence _ _ _ _)
    (c.equiv_substOcc_boundary s₁) c.dim_F₂
    (dim_boundary s₁.sol.toPastingDiagram (by rw [s₁.data.dim_u']; omega) α)

noncomputable abbrev second : Equation α n F₂ s₁.sol :=
  ⟨c.dim_F₂, s₁.data.dim_u', _, substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable
    c.equiv₁ s₁, c.isRewritableSubmolecule_image_substOcc s₁, c.equiv_substOcc_boundary s₁⟩

variable (s₂ : UnbiasedSolution B (c.second s₁)) (β : Bool)

noncomputable abbrev substImage : LowerSet (SolutionAmbient.ofSolution s₁ β).K.shape.ogp :=
  ((SolutionAmbient.ofSolution s₁ β).isRewritableSubmolecule_imageJκ c.dim_F₁ eq.dim_u eq.occ
      eq.rewritable c.κ c.rewritable c.equiv₁).complement ⊔
    (SolutionAmbient.ofSolution s₁ β).K.shape.ogp.boundary
      (SolutionAmbient.ofSolution s₁ β).wE.image n (!α)

theorem image_substImage :
    OGP.map (glueSolutions s₁ s₂ β).wK.emb (c.substImage s₁ β) =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  have e : (((substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
      c.rewritable c.equiv₁ s₁)).trans ((Within.boundary s₁.sol.toPastingDiagram n α).trans
        ((SolutionAmbient.ofSolution s₁ β).wSol.trans (glueSolutions s₁ s₂ β).wK))).image =
      OGP.map (glueSolutions s₁ s₂ β).wK.emb ((substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
        c.rewritable c.equiv₁ s₁).trans ((Within.boundary s₁.sol.toPastingDiagram n α).trans
          (SolutionAmbient.ofSolution s₁ β).wSol)).image := by
    rw [← Within.image_trans]
    rfl
  rw [← image_occ_glueFirstSol s₁ s₂ β]
  change _ = (((substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
    c.rewritable c.equiv₁ s₁)).trans ((Within.boundary s₁.sol.toPastingDiagram n α).trans
      ((SolutionAmbient.ofSolution s₁ β).wSol.trans (glueSolutions s₁ s₂ β).wK))).image
  rw [e, image_substOcc c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ c.rewritable c.equiv₁ s₁
    (SolutionAmbient.ofSolution s₁ β)]

theorem inter_glueFirst_glueSecond :
    (glueFirst s₁ s₂ β).image ⊓ (glueSecond s₁ s₂ β).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxV, hxW⟩ := LowerSet.mem_inf_iff.1 hx
    have h : x ∈ (glueFirst s₁ s₂ β).image ⊓ (glueSolutions s₁ s₂ β).wP.image :=
      LowerSet.mem_inf_iff.2 ⟨hxV, by
        rw [image_wP_glueSolutions]; exact LowerSet.mem_sup_iff.2 (Or.inl hxW)⟩
    rw [(isPastingAtIn_glueFirst s₁ s₂ β).inf_eq] at h
    exact h
  · intro x hx
    refine LowerSet.mem_inf_iff.2 ⟨boundary_le _ _ _ hx, ?_⟩
    have h1 : x ∈ OGP.map (glueSolutions s₁ s₂ β).wK.emb
        ((SolutionAmbient.ofSolution s₁ β).K.shape.ogp.boundary
          (SolutionAmbient.ofSolution s₁ β).wE.image n (!α)) := by
      rw [map_boundary, ← image_glueFirst]
      exact hx
    have h2 : x ∈ OGP.map (glueSolutions s₁ s₂ β).wK.emb (c.substImage s₁ β) :=
      map_mono _ le_sup_right h1
    rw [c.image_substImage s₁ s₂ β] at h2
    exact boundary_le _ _ _ h2

theorem isSubmoleculeOf_boundary_glueFirst :
    IsSubmoleculeOf (glueAmbient s₁ s₂ β).shape.ogp
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α))
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α) := by
  have h := (isSubmoleculeOf_map_iff (glueSolutions s₁ s₂ β).wK.emb).2
    ((SolutionAmbient.ofSolution s₁ β).isSubstitutionIn_substImage c.dim_F₁ eq.dim_u eq.occ
      eq.rewritable c.κ c.rewritable c.equiv₁ s₁).isSubmoleculeOf_target
  rw [c.image_substImage s₁ s₂ β, map_boundary, ← image_glueFirst] at h
  exact h

theorem isPastingAtIn_glueFirst_glueSecond :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueFirst s₁ s₂ β).image
      (glueSecond s₁ s₂ β).image ((glueFirst s₁ s₂ β).image ⊔ (glueSecond s₁ s₂ β).image) :=
  ⟨(glueFirst s₁ s₂ β).isMoleculeIn_image, (glueSecond s₁ s₂ β).isMoleculeIn_image, rfl,
    c.inter_glueFirst_glueSecond s₁ s₂ β, by
      rw [c.inter_glueFirst_glueSecond s₁ s₂ β]
      exact c.isSubmoleculeOf_boundary_glueFirst s₁ s₂ β⟩

theorem isPastingAtIn_glueUnion :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α
      ((glueFirst s₁ s₂ β).image ⊔ (glueSecond s₁ s₂ β).image) (glueSecondSol s₁ s₂ β).image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) := by
  have h₃ : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueSecond s₁ s₂ β).image
      (glueSecondSol s₁ s₂ β).image
      ((glueSecond s₁ s₂ β).image ⊔ (glueSecondSol s₁ s₂ β).image) := by
    rw [← image_wP_glueSolutions]; exact isPastingAtIn_glueSecond s₁ s₂ β
  have h₂ : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueFirst s₁ s₂ β).image
      ((glueSecond s₁ s₂ β).image ⊔ (glueSecondSol s₁ s₂ β).image)
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) := by
    rw [← image_wP_glueSolutions]; exact isPastingAtIn_glueFirst s₁ s₂ β
  exact (c.isPastingAtIn_glueFirst_glueSecond s₁ s₂ β).assoc_left h₃ h₂

noncomputable def glueJ : Within eq.sub (glueAmbient s₁ s₂ β).toPastingDiagram :=
  eq.occ.trans
    ((Within.boundary u.toPastingDiagram n α).trans (glueU s₁ s₂ β))

noncomputable def glueBdryFirst :
    Within (F₁.boundary n (!α)) (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (Within.boundary F₁.toPastingDiagram n (!α)).trans (glueFirst s₁ s₂ β)

theorem image_glueJ :
    (c.glueJ s₁ s₂ β).image =
      OGP.map (glueSolutions s₁ s₂ β).wK.emb
        ((SolutionAmbient.ofSolution s₁ β).imageJ c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
          c.rewritable c.equiv₁) :=
  Within.image_trans (eq.occ.trans ((Within.boundary u.toPastingDiagram n α).trans
    (SolutionAmbient.ofSolution s₁ β).wU)) (glueSolutions s₁ s₂ β).wK

theorem image_glueJκ :
    (c.κ.trans (c.glueJ s₁ s₂ β)).image =
      OGP.map (glueSolutions s₁ s₂ β).wK.emb
        ((SolutionAmbient.ofSolution s₁ β).imageJκ c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
          c.rewritable c.equiv₁) :=
  Within.image_trans ((c.κ.trans eq.occ).trans ((Within.boundary u.toPastingDiagram n α).trans
    (SolutionAmbient.ofSolution s₁ β).wU)) (glueSolutions s₁ s₂ β).wK

theorem image_glueBdryFirst :
    (c.glueBdryFirst s₁ s₂ β).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n (!α) :=
  Within.image_boundary_trans _ _ _

theorem isSubstitutionIn_glueJ :
    IsSubstitutionIn (glueAmbient s₁ s₂ β).shape.ogp (c.glueJ s₁ s₂ β).image
      (c.κ.trans (c.glueJ s₁ s₂ β)).image (c.glueBdryFirst s₁ s₂ β).image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α) := by
  have h := ((SolutionAmbient.ofSolution s₁ β).isSubstitutionIn_substImage c.dim_F₁ eq.dim_u
    eq.occ eq.rewritable c.κ c.rewritable c.equiv₁ s₁).map (glueSolutions s₁ s₂ β).wK.emb
  rw [← c.image_glueJ, ← c.image_glueJκ, c.image_substImage s₁ s₂ β, map_boundary,
    ← image_glueFirst, ← c.image_glueBdryFirst] at h
  exact h

theorem equiv_substitute_glue :
    (eq.sub.substitute c.κ c.rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
      c.first.parallel_occ).Equiv
      ((glueAmbient s₁ s₂ β).toPastingDiagram.restrictTo
        (isMoleculeIn_boundary_glueSecond s₁ s₂ β)) :=
  equiv_substitute_of_within c.κ c.rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
    c.first.parallel_occ (c.glueJ s₁ s₂ β) (c.glueBdryFirst s₁ s₂ β)
    (c.isSubstitutionIn_glueJ s₁ s₂ β) (isMoleculeIn_boundary_glueSecond s₁ s₂ β)

private noncomputable def glueSubst₀ :
    Within (eq.sub.substitute c.κ c.rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
      c.first.parallel_occ) (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (Within.ofEquiv c.equiv₂).trans
    ((Within.boundary F₂.toPastingDiagram n α).trans (glueSecond s₁ s₂ β))

private noncomputable def glueSubst₁ :
    Within (eq.sub.substitute c.κ c.rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
      c.first.parallel_occ) (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (Within.ofEquiv (c.equiv_substitute_glue s₁ s₂ β)).trans
    (Within.restrictTo _ (isMoleculeIn_boundary_glueSecond s₁ s₂ β))

private theorem image_glueSubst₀ : (c.glueSubst₀ s₁ s₂ β).image =
    (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  change ((Within.ofEquiv c.equiv₂).trans
    ((Within.boundary F₂.toPastingDiagram n α).trans (glueSecond s₁ s₂ β))).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary_trans _ _ _

private theorem image_glueSubst₁ : (c.glueSubst₁ s₁ s₂ β).image =
    (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  change ((Within.ofEquiv (c.equiv_substitute_glue s₁ s₂ β)).trans
    (Within.restrictTo _ (isMoleculeIn_boundary_glueSecond s₁ s₂ β))).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_restrictTo _ _

private theorem glueSubst_apply_eq (y) :
    (c.glueSubst₀ s₁ s₂ β).emb y = (c.glueSubst₁ s₁ s₂ β).emb y :=
  Within.emb_apply_eq_of_image_eq _ _
    ((c.image_glueSubst₀ s₁ s₂ β).trans (c.image_glueSubst₁ s₁ s₂ β).symm) y

theorem subIncl_iso_substInrEmb (y : (F₁.boundary n (!α)).shape.ogp) :
    (glueAmbient s₁ s₂ β).toPastingDiagram.shape.subIncl
      (isMoleculeIn_boundary_glueSecond s₁ s₂ β) ((c.equiv_substitute_glue s₁ s₂ β).iso.hom
        (substInrEmb eq.sub c.κ c.rewritable
          (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) c.first.parallel_occ y)) =
      (c.glueBdryFirst s₁ s₂ β).emb y :=
  (apply_iso_substInlEmb_and_substInrEmb_of_within c.κ c.rewritable
    (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) c.first.parallel_occ (c.glueJ s₁ s₂ β)
    (c.glueBdryFirst s₁ s₂ β) (c.isSubstitutionIn_glueJ s₁ s₂ β)
    (isMoleculeIn_boundary_glueSecond s₁ s₂ β) (c.equiv_substitute_glue s₁ s₂ β)).2 y

private theorem glueSubst₀_substRightEmb (y : (F₁.boundary n (!α)).shape.ogp) :
    (c.glueSubst₀ s₁ s₂ β).emb (substInrEmb eq.sub c.κ c.rewritable
      (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) c.first.parallel_occ y) =
      (c.glueBdryFirst s₁ s₂ β).emb y :=
  (c.glueSubst_apply_eq s₁ s₂ β _).trans (c.subIncl_iso_substInrEmb s₁ s₂ β y)

private theorem image_occ_glueSecond_eq (d : PasteAtData α n F₁ F₂)
    (hd : d.occ.image = c.occ.image) :
    (d.occ.trans
      ((Within.boundary F₂.toPastingDiagram n α).trans (glueSecond s₁ s₂ β))).image =
      ((Within.substitute c.κ c.rewritable (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
        c.first.parallel_occ).trans (c.glueSubst₀ s₁ s₂ β)).image := by
  rw [Within.image_trans, hd, ← Within.image_trans]
  rfl

theorem image_occ_glueSecond (d : PasteAtData α n F₁ F₂) (hd : d.occ.image = c.occ.image) :
    (d.occ.trans
      ((Within.boundary F₂.toPastingDiagram n α).trans (glueSecond s₁ s₂ β))).image =
      (glueFirst s₁ s₂ β).image ⊓ (glueSecond s₁ s₂ β).image := by
  refine (c.image_occ_glueSecond_eq s₁ s₂ β d hd).trans (Eq.trans ?_
    ((c.image_glueBdryFirst s₁ s₂ β).trans (c.inter_glueFirst_glueSecond s₁ s₂ β).symm))
  refine congrArg (fun f => OGP.map f ⊤) ?_
  ext y
  exact c.glueSubst₀_substRightEmb s₁ s₂ β y

theorem image_glueJκ_eq_boundary :
    (c.κ.trans (c.glueJ s₁ s₂ β)).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n α := by
  have hoc : (SolutionAmbient.ofSolution s₁ β).imageJκ c.dim_F₁ eq.dim_u eq.occ eq.rewritable c.κ
      c.rewritable c.equiv₁ = (SolutionAmbient.ofSolution s₁ β).K.shape.ogp.boundary
        (SolutionAmbient.ofSolution s₁ β).wE.image n α :=
    (SolutionAmbient.ofSolution s₁ β).occ_eq
  rw [c.image_glueJκ, hoc, map_boundary, ← image_glueFirst]

theorem image_glueJ_eq_boundary :
    (c.glueJ s₁ s₂ β).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary
        ((glueFirst s₁ s₂ β).image ⊔ (glueSecond s₁ s₂ β).image) n α := by
  apply SetLike.coe_injective
  rw [(c.isPastingAtIn_glueFirst_glueSecond s₁ s₂ β).coe_boundary_eq
      (by rw [krullDim_glueFirst]; exact_mod_cast n.le_succ)
      (by rw [krullDim_glueSecond]; exact_mod_cast n.le_succ),
    c.inter_glueFirst_glueSecond s₁ s₂ β, (c.isSubstitutionIn_glueJ s₁ s₂ β).symm.eq_sup,
    LowerSet.coe_sup, IsSubmoleculeOf.coe_complement, c.image_glueJκ_eq_boundary,
    c.image_glueBdryFirst]

end ComposePair

namespace ComposePair

section OfPasteAtData

variable {α : Bool} {n : ℕ} {e u F₁ F₂ : RoundPastingDiagram X} (eq : Equation α n e u)
  (d : PasteAtData α n F₁ F₂) (h : (e.boundary n α).Equiv (d.pasting.boundary n α))

noncomputable def withinOcc : Within eq.sub d.pasting :=
  (Within.ofEquiv (eq.equiv.trans h)).trans (Within.boundary d.pasting n α)

theorem image_withinOcc :
    (withinOcc eq d h).image = d.pasting.shape.ogp.boundary ⊤ n α := by
  change ((Within.ofEquiv (eq.equiv.trans h)).trans
    (Within.boundary d.pasting n α)).image = _
  rw [Within.image_trans, Within.image_ofEquiv]
  exact Within.image_boundary _ _ _

theorem boundary_pasteAtInl_le :
    d.pasting.shape.ogp.boundary d.pasteAtInl.image n α ≤ (withinOcc eq d h).image := by
  rw [image_withinOcc]
  exact d.isSubmoleculeOf_boundary_pasteAtInl.le

theorem isSubmoleculeOf_comap :
    IsSubmoleculeOf eq.sub.shape.ogp
      (comap (withinOcc eq d h).emb (d.pasting.shape.ogp.boundary d.pasteAtInl.image n α)) ⊤ := by
  rw [← isSubmoleculeOf_map_iff (withinOcc eq d h).emb,
    map_comap_of_le _ (boundary_pasteAtInl_le eq d h)]
  change IsSubmoleculeOf _ _ (withinOcc eq d h).image
  rw [image_withinOcc]
  exact d.isSubmoleculeOf_boundary_pasteAtInl

noncomputable def κOf :
    Within (eq.sub.restrictTo (isSubmoleculeOf_comap eq d h).isMoleculeIn) eq.sub :=
  Within.restrictTo eq.sub (isSubmoleculeOf_comap eq d h).isMoleculeIn

theorem image_κOf_trans :
    ((κOf eq d h).trans (withinOcc eq d h)).image =
      d.pasting.shape.ogp.boundary d.pasteAtInl.image n α := by
  rw [Within.image_trans, κOf, Within.image_restrictTo]
  exact map_comap_of_le _ (boundary_pasteAtInl_le eq d h)

theorem equiv_κOf :
    (eq.sub.restrictTo (isSubmoleculeOf_comap eq d h).isMoleculeIn).Equiv (F₁.boundary n α) :=
  Within.equiv_of_image_eq ((κOf eq d h).trans (withinOcc eq d h))
    ((Within.boundary F₁.toPastingDiagram n α).trans d.pasteAtInl)
    ((image_κOf_trans eq d h).trans (Within.image_boundary_trans _ _ _).symm)

theorem isRewritableSubmolecule_image_κOf :
    eq.sub.shape.ogp.IsRewritableSubmolecule (κOf eq d h).image ⊤ :=
  Within.isRewritableSubmolecule_of_equiv_boundary
    (Within.isSubmoleculeOf_image_restrictTo _ (isSubmoleculeOf_comap eq d h))
    (equiv_κOf eq d h) d.dim_e
    (Within.dim_eq_of_isRewritableSubmolecule_boundary eq.rewritable (by rw [eq.dim_u]; omega))

theorem isSubstitutionIn_withinOcc :
    IsSubstitutionIn d.pasting.shape.ogp (withinOcc eq d h).image
      ((κOf eq d h).trans (withinOcc eq d h)).image d.boundaryPasteAtInl.image
      (d.pasting.shape.ogp.boundary d.pasteAtInr.image n α) := by
  rw [image_withinOcc, image_κOf_trans, d.image_boundaryPasteAtInl]
  exact d.isSubstitutionIn_boundary_pasteAtInr

theorem equiv_substitute_κOf :
    (eq.sub.substitute (κOf eq d h) (isRewritableSubmolecule_image_κOf eq d h)
      (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
      (Equation.ofTrans d.dim_e eq.dim_u eq.occ eq.rewritable (κOf eq d h)
        (isRewritableSubmolecule_image_κOf eq d h) (equiv_κOf eq d h)).parallel_occ).Equiv
      (d.pasting.restrictTo d.isMoleculeIn_boundary_pasteAtInr) :=
  equiv_substitute_of_within (κOf eq d h) (isRewritableSubmolecule_image_κOf eq d h)
    (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
    (Equation.ofTrans d.dim_e eq.dim_u eq.occ eq.rewritable (κOf eq d h)
      (isRewritableSubmolecule_image_κOf eq d h) (equiv_κOf eq d h)).parallel_occ
    (withinOcc eq d h) d.boundaryPasteAtInl (isSubstitutionIn_withinOcc eq d h)
    d.isMoleculeIn_boundary_pasteAtInr

noncomputable def ofPasteAtData : ComposePair eq F₁ F₂ where
  dim_F₁ := d.dim_e
  dim_F₂ := d.dim_u'
  κ := κOf eq d h
  sub := _
  rewritable := isRewritableSubmolecule_image_κOf eq d h
  equiv₁ := equiv_κOf eq d h
  equiv₂ := (equiv_substitute_κOf eq d h).trans
    d.equiv_restrictTo_boundary_pasteAtInr

theorem pasteAtInr_iso_substInrEmb (y : (F₁.boundary n (!α)).shape.ogp) :
    ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr).emb
      ((ofPasteAtData eq d h).equiv₂.iso.hom (substInrEmb eq.sub (κOf eq d h)
        (isRewritableSubmolecule_image_κOf eq d h) (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
        (Equation.ofTrans d.dim_e eq.dim_u eq.occ eq.rewritable (κOf eq d h)
          (isRewritableSubmolecule_image_κOf eq d h) (equiv_κOf eq d h)).parallel_occ y)) =
      d.boundaryPasteAtInl.emb y := by
  have hiso : (ofPasteAtData eq d h).equiv₂.iso =
      (equiv_substitute_κOf eq d h).iso.trans d.equiv_restrictTo_boundary_pasteAtInr.iso :=
    @Subsingleton.elim _ (IsMolecule.subsingleton_iso
      (eq.sub.substitute (κOf eq d h) (isRewritableSubmolecule_image_κOf eq d h)
        (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
        (Equation.ofTrans d.dim_e eq.dim_u eq.occ eq.rewritable (κOf eq d h)
          (isRewritableSubmolecule_image_κOf eq d h)
            (equiv_κOf eq d h)).parallel_occ).shape.isMolecule) _ _
  have h1 : ∀ x, ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr).emb
      (d.equiv_restrictTo_boundary_pasteAtInr.iso.hom x) =
        (Within.restrictTo d.pasting d.isMoleculeIn_boundary_pasteAtInr).emb x :=
    Within.emb_apply_eq_of_image_eq
      ((Within.ofEquiv d.equiv_restrictTo_boundary_pasteAtInr).trans
        ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr))
      (Within.restrictTo d.pasting d.isMoleculeIn_boundary_pasteAtInr)
      ((Within.image_ofEquiv_trans _ _).trans
        ((Within.image_boundary_trans _ _ _).trans (Within.image_restrictTo _ _).symm))
  rw [hiso]
  exact (h1 _).trans ((apply_iso_substInlEmb_and_substInrEmb_of_within (κOf eq d h)
      (isRewritableSubmolecule_image_κOf eq d h)
    (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) _ (withinOcc eq d h) d.boundaryPasteAtInl
    (isSubstitutionIn_withinOcc eq d h) d.isMoleculeIn_boundary_pasteAtInr
    (equiv_substitute_κOf eq d h)).2 y)

theorem image_occ_ofPasteAtData_pasteAtInr :
    OGP.map ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr).emb
      (ofPasteAtData eq d h).occ.image = d.boundaryPasteAtInl.image := by
  rw [← Within.image_trans]
  refine congrArg (fun f => OGP.map f ⊤) ?_
  ext y
  exact pasteAtInr_iso_substInrEmb eq d h y

theorem image_occ_ofPasteAtData : d.occ.image = (ofPasteAtData eq d h).occ.image := by
  refine map_injective ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr).emb ?_
  have h1 := d.image_occ_pasteAtInr
  rw [Within.image_trans] at h1
  rw [h1, image_occ_ofPasteAtData_pasteAtInr, d.image_boundaryPasteAtInl,
    d.isPastingAtIn_pasteAtInl.inf_eq]

end OfPasteAtData

end ComposePair

theorem nonempty_unbiasedSolution_compose {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {e u F₁ F₂ : RoundPastingDiagram X} (eq : Equation α n e u) (d : PasteAtData α n F₁ F₂)
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram e.toPastingDiagram d.pasting)
    (h₁ : UnbiasedSide (TClosure A) α F₁)
    (h₂ : UnbiasedSide (TClosure A) α F₂) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨k₀, -, hk₀⟩ := pair false
  have hb : (e.boundary n α).Equiv (d.pasting.boundary n α) :=
    hk₀.equiv_boundary (Nat.lt_succ_self n) α
  let c := ComposePair.ofPasteAtData eq d hb
  have hd := ComposePair.image_occ_ofPasteAtData eq d hb
  obtain ⟨s₁⟩ := h₁ n u c.first
  obtain ⟨s₂⟩ := h₂ n s₁.sol (c.second s₁)
  let eq' : Equation α n d.round u := eq.ofEquiv d.dim_pasting hb
  let SA β := SolutionAmbient.ofGlue s₁ s₂ β d _ _ (c.isPastingAtIn_glueFirst_glueSecond s₁ s₂ β)
    (c.image_occ_glueSecond s₁ s₂ β d hd) (c.isPastingAtIn_glueUnion s₁ s₂ β) eq'
    (c.image_glueJ_eq_boundary s₁ s₂ β)
  exact nonempty_unbiasedSolution_of_pair hDgn eq (P := d.round) d.dim_pasting hb pair
    (UnbiasedSolution.ofAmbients (SA false) (SA true)
      (tClosure_glueAmbient s₁ s₂ false hDgn fun _ h => h)
      (tClosure_glueAmbient s₁ s₂ true hDgn fun _ h => h))

end Atoms.Diagrammatic
