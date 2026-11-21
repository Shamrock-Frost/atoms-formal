import Atoms.Diagrammatic.Equivalence.Solve

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem exists_solutionAmbient_of_pair {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {P e u : RoundPastingDiagram X} (eq : Equation α n e u) (hP : P.dim = n + 1)
    (hbd : (e.boundary n α).Equiv (P.boundary n α))
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram e.toPastingDiagram P.toPastingDiagram)
    (s' : UnbiasedSolution (TClosure A) (eq.ofEquiv hP hbd)) (β : Bool) :
    ∃ SA : SolutionAmbient eq s'.sol β, TClosure A SA.K := by
  have he : e.dim = n + 1 := eq.dim_e
  obtain ⟨kβ, hkβ, htβ⟩ := pair β
  let sw := s'.side β
  let g' : Geometry s'.data u sw.witness β := sw.geometry
  have hP₀ : IsSubmoleculeOf sw.witness.shape.ogp g'.withinE.image
      (sw.witness.shape.ogp.boundary ⊤ (n + 1) β) :=
    g'.isPastingAtIn.isSubmoleculeOf_left
  let GS := glueStep (wP₀ := g'.withinE) g'.dim_w hP₀ htβ
  let wSol := g'.withinSol.trans GS.wK
  let wU := g'.wU.trans GS.wK
  have eS : wSol.image = OGP.map GS.wK.emb g'.withinSol.image := Within.image_trans _ _
  have eU : wU.image = OGP.map GS.wK.emb g'.wU.image := Within.image_trans _ _
  have eP₀ : (g'.withinE.trans GS.wK).image = OGP.map GS.wK.emb g'.withinE.image :=
    Within.image_trans _ _
  have hdE' : krullDim GS.wP.image = n + 1 := by
    rw [GS.wP.krullDim_image]; exact_mod_cast he
  have hdP' : krullDim (OGP.map GS.wK.emb g'.withinE.image) = n + 1 := by
    rw [← eP₀, (g'.withinE.trans GS.wK).krullDim_image]; exact_mod_cast hP
  have hc : IsPastingAtIn GS.K'.shape.ogp n α GS.wP.image wSol.image
      (GS.K'.shape.ogp.boundary ⊤ (n + 1) β) := by
    have h := g'.isPastingAtIn.map GS.wK.emb
    rw [← GS.wK.boundary_image, ← eS] at h
    exact h.subst_left_self GS.subst (by rw [hdP']; exact_mod_cast n.lt_succ_self)
  have himU : wU.image = GS.K'.shape.ogp.boundary ⊤ (n + 1) (!β) := by
    rw [eU, g'.image_wU, GS.boundary_not]
  have hocc' : (eq.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans wU)).image =
        GS.K'.shape.ogp.boundary GS.wP.image n α := by
    have hc' : (eq.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans g'.wU)).image =
          sw.witness.shape.ogp.boundary g'.withinE.image n α := g'.compat_image s'.compat
    have e5 : (eq.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans wU)).image =
          OGP.map GS.wK.emb (eq.occ.trans
            ((Within.boundary u.toPastingDiagram n α).trans g'.wU)).image := by
      rw [← Within.image_trans]
      rfl
    rw [e5, hc', map_boundary]
    have hb := GS.subst.bdry_eq α
    rw [bdry_eq_boundary hdE', bdry_eq_boundary hdP'] at hb
    exact hb.symm
  exact ⟨⟨⟨GS.K', GS.dimK', GS.wP, wU, himU, hocc'⟩, s'.data.dim_u', wSol, hc⟩,
    GS.mem hDgn hkβ sw.mem⟩

theorem nonempty_unbiasedSolution_of_pair {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {P e u : RoundPastingDiagram X} (eq : Equation α n e u) (hP : P.dim = n + 1)
    (hbd : (e.boundary n α).Equiv (P.boundary n α))
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram e.toPastingDiagram P.toPastingDiagram)
    (s' : UnbiasedSolution (TClosure A) (eq.ofEquiv hP hbd)) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨SA₀, h₀⟩ := exists_solutionAmbient_of_pair hDgn eq hP hbd pair s' false
  obtain ⟨SA₁, h₁⟩ := exists_solutionAmbient_of_pair hDgn eq hP hbd pair s' true
  exact ⟨UnbiasedSolution.ofAmbients SA₀ SA₁ h₀ h₁⟩

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

noncomputable def SolutionAmbient.ofSolution {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    {eq : Equation α n e u} {B : Set (RoundPastingDiagram X)} (s : UnbiasedSolution B eq)
    (β : Bool) : SolutionAmbient eq s.sol β :=
  ⟨⟨(s.side β).witness, (s.side β).geometry.dim_w, (s.side β).geometry.withinE,
    (s.side β).geometry.wU, (s.side β).geometry.image_wU,
    (s.side β).geometry.compat_image s.compat⟩, s.data.dim_u', (s.side β).geometry.withinSol,
    (s.side β).geometry.isPastingAtIn⟩

theorem SolutionAmbient.isSubmoleculeOf_wSol {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
    {eq : Equation α n e u} {sol : RoundPastingDiagram X} {β : Bool}
    (SA : SolutionAmbient eq sol β) :
    IsSubmoleculeOf SA.K.shape.ogp SA.wSol.image
      (SA.K.shape.ogp.boundary ⊤ (n + 1) β) :=
  SA.config.isSubmoleculeOf_right

section Factor

variable {α : Bool} {n : ℕ} {F₁ u : RoundPastingDiagram X} (hF₁ : F₁.dim = n + 1)
  (hu : u.dim = n + 1) {V : PastingDiagram X} (J : Within V (u.boundary n α))
  (hJ : (u.boundary n α).shape.ogp.IsRewritableSubmolecule J.image ⊤)
  {W : PastingDiagram X} (κ : Within W V)
  (hκ : V.shape.ogp.IsRewritableSubmolecule κ.image ⊤)
  (hκ₁ : W.Equiv (F₁.boundary n α))

abbrev Equation.ofTrans : Equation α n F₁ u :=
  ⟨hF₁, hu, W, κ.trans J, Within.isRewritableSubmolecule_image_trans hκ hJ, hκ₁⟩

abbrev notBoundaryRound : RoundPastingDiagram X :=
  ⟨F₁.boundary n (!α), isRound_boundary_of_isRound F₁.isRound n (!α)⟩

noncomputable def substAbs :
    LowerSet (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).solBoundary.shape.ogp :=
  OGP.map (substInlEmb (u.boundary n α) (κ.trans J)
      (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).rewritable
      (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
      (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).parallel_occ)
    (comap (incl _) J.image) ⊔
  OGP.map (substInrEmb (u.boundary n α) (κ.trans J)
    (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).rewritable
    (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
    (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).parallel_occ) ⊤

variable {sol : RoundPastingDiagram X} {β : Bool}

abbrev SolutionAmbient.imageJ
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) sol β) :
    LowerSet SA.K.shape.ogp :=
  (J.trans ((Within.boundary u.toPastingDiagram n α).trans SA.wU)).image

abbrev SolutionAmbient.imageJκ
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) sol β) :
    LowerSet SA.K.shape.ogp :=
  ((κ.trans J).trans ((Within.boundary u.toPastingDiagram n α).trans SA.wU)).image

theorem SolutionAmbient.isSubmoleculeOf_imageJ
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) sol β) :
    IsSubmoleculeOf SA.K.shape.ogp (SA.imageJ hF₁ hu J hJ κ hκ hκ₁)
      (SA.K.shape.ogp.boundary SA.wU.image n α) := by
  let wU' := (Within.boundary u.toPastingDiagram n α).trans SA.wU
  have h := (isSubmoleculeOf_map_iff wU'.emb).2 hJ.isSubmoleculeOf
  have hw : wU'.image = SA.K.shape.ogp.boundary SA.wU.image n α :=
    Within.image_boundary_trans _ _ _
  rw [← hw]
  change IsSubmoleculeOf _ (J.trans wU').image wU'.image
  rw [Within.image_trans]
  exact h

theorem SolutionAmbient.isRewritableSubmolecule_imageJκ
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) sol β) :
    SA.K.shape.ogp.IsRewritableSubmolecule (SA.imageJκ hF₁ hu J hJ κ hκ hκ₁)
      (SA.imageJ hF₁ hu J hJ κ hκ hκ₁) := by
  let wU' := (Within.boundary u.toPastingDiagram n α).trans SA.wU
  have e1 : SA.imageJκ hF₁ hu J hJ κ hκ hκ₁ = (κ.trans (J.trans wU')).image := rfl
  refine ⟨?_, ?_, ?_⟩
  · have h := (isSubmoleculeOf_map_iff (J.trans wU').emb).2 hκ.isSubmoleculeOf
    rw [e1]
    change IsSubmoleculeOf _ (κ.trans (J.trans wU')).image (J.trans wU').image
    rw [Within.image_trans]
    exact h
  · rw [e1, (κ.trans (J.trans wU')).krullDim_image, (J.trans wU').krullDim_image,
      (κ.isRewritableSubmolecule_image_iff.1 hκ).2.2]
  · rw [e1]
    exact (κ.trans (J.trans wU')).round_image_iff.2 (κ.round_image_iff.1 hκ.isRound)

theorem SolutionAmbient.image_substAbs
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) sol β) :
    OGP.map ((Within.ofEquiv SA.equiv_solBoundary_restrictTo).trans
        (Within.restrictTo _ SA.isMoleculeIn_boundary_wSol)).emb
      (substAbs hF₁ hu J hJ κ hκ hκ₁) =
      (SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁).complement ⊔
        SA.K.shape.ogp.boundary SA.wE.image n (!α) := by
  let eq₁ := Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁
  let wU' := (Within.boundary u.toPastingDiagram n α).trans SA.wU
  let wW := (Within.boundary F₁.toPastingDiagram n (!α)).trans SA.wE
  let W := (Within.ofEquiv SA.equiv_solBoundary_restrictTo).trans
    (Within.restrictTo _ SA.isMoleculeIn_boundary_wSol)
  have hs : IsSubstitutionIn SA.K.shape.ogp wU'.image
      (eq₁.occ.trans wU').image wW.image
      (SA.K.shape.ogp.boundary SA.wSol.image n α) := by
    change IsSubstitutionIn SA.K.shape.ogp
      ((Within.boundary u.toPastingDiagram n α).trans SA.wU).image
      (eq₁.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans SA.wU)).image
      ((Within.boundary F₁.toPastingDiagram n (!α)).trans SA.wE).image _
    rw [Within.image_boundary_trans, Within.image_boundary_trans]
    exact SA.isSubstitutionIn_boundary_wSol
  have hl : ∀ x, W.emb (substInlEmb (u.boundary n α) (κ.trans J) eq₁.rewritable
      (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) eq₁.parallel_occ x) = wU'.emb x.1 :=
    (apply_iso_substInlEmb_and_substInrEmb_of_within eq₁.occ eq₁.rewritable _
      eq₁.parallel_occ wU' wW hs SA.isMoleculeIn_boundary_wSol SA.equiv_solBoundary_restrictTo).1
  have hr : ∀ y, W.emb (substInrEmb (u.boundary n α) (κ.trans J) eq₁.rewritable
      (notBoundaryRound (α := α) (n := n) (F₁ := F₁)) eq₁.parallel_occ y) = wW.emb y :=
    (apply_iso_substInlEmb_and_substInrEmb_of_within eq₁.occ eq₁.rewritable _
      eq₁.parallel_occ wU' wW hs SA.isMoleculeIn_boundary_wSol SA.equiv_solBoundary_restrictTo).2
  have hJ' : SA.imageJ hF₁ hu J hJ κ hκ hκ₁ = OGP.map wU'.emb J.image := Within.image_trans _ _
  have hJκ : SA.imageJκ hF₁ hu J hJ κ hκ hκ₁ = OGP.map wU'.emb (κ.trans J).image :=
    Within.image_trans _ _
  have hW : SA.K.shape.ogp.boundary SA.wE.image n (!α) = wW.image :=
    (Within.image_boundary_trans _ _ _).symm
  refine SetLike.ext fun z => ?_
  rw [LowerSet.mem_sup_iff, IsSubmoleculeOf.mem_complement, hJ', hJκ, ← image_interior, hW]
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases LowerSet.mem_sup_iff.1 ha with ⟨x, hx, rfl⟩ | ⟨y, -, rfl⟩
    · refine Or.inl ⟨mem_map.2 ⟨x.1, mem_comap.1 hx, (hl x).symm⟩, ?_⟩
      rintro ⟨y, hy, hyz⟩
      rw [hl x] at hyz
      have hx2 := (IsSubmoleculeOf.mem_complement _ _).1 x.2
      exact hx2.2 (IsInclusion.injective (f := wU'.emb) hyz ▸ hy)
    · rw [hr y]
      exact Or.inr (wW.mem_image_apply y)
  · rintro (⟨⟨y, hy, rfl⟩, hyi⟩ | ⟨y, -, rfl⟩)
    · have hyC : y ∈ eq₁.rewritable.complement :=
        (IsSubmoleculeOf.mem_complement _ _).2 ⟨LowerSet.mem_top, fun h => hyi ⟨y, h, rfl⟩⟩
      exact ⟨_, LowerSet.mem_sup_iff.2 (Or.inl ⟨⟨y, hyC⟩, mem_comap.2 hy, rfl⟩), hl ⟨y, hyC⟩⟩
    · exact ⟨_, LowerSet.mem_sup_iff.2 (Or.inr ⟨y, LowerSet.mem_top, rfl⟩), hr y⟩

end Factor

section SubstOcc

variable {α : Bool} {n : ℕ} {F₁ u : RoundPastingDiagram X} (hF₁ : F₁.dim = n + 1)
  (hu : u.dim = n + 1) {V : PastingDiagram X} (J : Within V (u.boundary n α))
  (hJ : (u.boundary n α).shape.ogp.IsRewritableSubmolecule J.image ⊤)
  {W : PastingDiagram X} (κ : Within W V)
  (hκ : V.shape.ogp.IsRewritableSubmolecule κ.image ⊤)
  (hκ₁ : W.Equiv (F₁.boundary n α))
  {B : Set (RoundPastingDiagram X)} (s : UnbiasedSolution B (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁))

theorem SolutionAmbient.isSubmoleculeOf_substImage {β : Bool}
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) s.sol β) :
    IsSubmoleculeOf SA.K.shape.ogp
      ((SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁).complement ⊔
        SA.K.shape.ogp.boundary SA.wE.image n (!α))
      (SA.K.shape.ogp.boundary SA.wSol.image n α) :=
  SA.isSubstitutionIn_boundary_wSol.isSubmoleculeOf_of_isSubmoleculeOf
    (SA.isSubmoleculeOf_imageJ hF₁ hu J hJ κ hκ hκ₁)
    (SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁)

theorem SolutionAmbient.isSubstitutionIn_substImage {β : Bool}
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) s.sol β) :
    IsSubstitutionIn SA.K.shape.ogp (SA.imageJ hF₁ hu J hJ κ hκ hκ₁)
      (SA.imageJκ hF₁ hu J hJ κ hκ hκ₁) (SA.K.shape.ogp.boundary SA.wE.image n (!α))
      ((SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁).complement ⊔
        SA.K.shape.ogp.boundary SA.wE.image n (!α)) :=
  SA.isSubstitutionIn_boundary_wSol.ofIsSubmoleculeOf
    (SA.isSubmoleculeOf_imageJ hF₁ hu J hJ κ hκ hκ₁)
    (SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁)

noncomputable abbrev substOccDiagram : PastingDiagram X :=
  occurrenceDiagram (SolutionAmbient.ofSolution s false).wSol n α
    ((SolutionAmbient.ofSolution s false).isSubmoleculeOf_substImage hF₁ hu J hJ κ hκ hκ₁ s)

noncomputable def substOcc :
    Within (substOccDiagram hF₁ hu J hJ κ hκ hκ₁ s) (s.sol.boundary n α) :=
  occurrence (SolutionAmbient.ofSolution s false).wSol n α
    ((SolutionAmbient.ofSolution s false).isSubmoleculeOf_substImage hF₁ hu J hJ κ hκ hκ₁ s)

theorem equiv_substOcc :
    (substOccDiagram hF₁ hu J hJ κ hκ hκ₁ s).Equiv
      (V.substitute κ hκ (notBoundaryRound (α := α) (n := n) (F₁ := F₁))
        (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).parallel_occ) := by
  let SA := SolutionAmbient.ofSolution s false
  let wU' := (Within.boundary u.toPastingDiagram n α).trans SA.wU
  have hS := SA.isSubmoleculeOf_substImage hF₁ hu J hJ κ hκ hκ₁ s
  have hS' : IsMoleculeIn SA.K.shape.ogp _ := hS.isMoleculeIn
  refine (PastingDiagram.Equiv.symm
    (equiv_occurrence_of_image_eq SA.wSol n α hS (Within.restrictTo _ hS')
      (Within.image_restrictTo _ _))).trans (PastingDiagram.Equiv.symm ?_)
  refine equiv_substitute_of_within κ hκ _ _ (J.trans wU')
    ((Within.boundary F₁.toPastingDiagram n (!α)).trans SA.wE) ?_ hS'
  have h := SA.isSubstitutionIn_substImage hF₁ hu J hJ κ hκ hκ₁ s
  have hw : ((Within.boundary F₁.toPastingDiagram n (!α)).trans SA.wE).image =
      SA.K.shape.ogp.boundary SA.wE.image n (!α) := Within.image_boundary_trans _ _ _
  exact Eq.subst (motive := fun W => IsSubstitutionIn SA.K.shape.ogp
    (SA.imageJ hF₁ hu J hJ κ hκ hκ₁) (SA.imageJκ hF₁ hu J hJ κ hκ hκ₁) W
    ((SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁).complement ⊔
      SA.K.shape.ogp.boundary SA.wE.image n (!α))) hw.symm h

theorem image_substOcc {β : Bool}
    (SA : SolutionAmbient (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁) s.sol β) :
    ((substOcc hF₁ hu J hJ κ hκ hκ₁ s).trans
      ((Within.boundary s.sol.toPastingDiagram n α).trans SA.wSol)).image =
      (SA.isRewritableSubmolecule_imageJκ hF₁ hu J hJ κ hκ hκ₁).complement ⊔
        SA.K.shape.ogp.boundary SA.wE.image n (!α) := by
  have hb₀ := (SolutionAmbient.ofSolution s false).equiv_solBoundary
  have hb := SA.equiv_solBoundary
  have hiso : hb.iso = hb₀.iso :=
    @Subsingleton.elim _ (IsMolecule.subsingleton_iso
      (Equation.ofTrans hF₁ hu J hJ κ hκ hκ₁).solBoundary.shape.isMolecule) _ _
  have hW₀ :
      (Within.ofEquiv (SolutionAmbient.ofSolution s false).equiv_solBoundary_restrictTo).trans
        (Within.restrictTo _ (SolutionAmbient.ofSolution s false).isMoleculeIn_boundary_wSol) =
        (Within.ofEquiv hb₀).trans ((Within.boundary s.sol.toPastingDiagram n α).trans
          (SolutionAmbient.ofSolution s false).wSol) := by
    refine Within.ext_of_image_eq _ _ ?_
    rw [Within.image_ofEquiv_trans, Within.image_ofEquiv_trans]
    exact (Within.image_restrictTo _ _).trans (Within.image_boundary_trans _ _ _).symm
  have hW : (Within.ofEquiv SA.equiv_solBoundary_restrictTo).trans
      (Within.restrictTo _ SA.isMoleculeIn_boundary_wSol) =
        (Within.ofEquiv hb).trans ((Within.boundary s.sol.toPastingDiagram n α).trans SA.wSol) := by
    refine Within.ext_of_image_eq _ _ ?_
    rw [Within.image_ofEquiv_trans, Within.image_ofEquiv_trans]
    exact (Within.image_restrictTo _ _).trans (Within.image_boundary_trans _ _ _).symm
  have hocc : (substOcc hF₁ hu J hJ κ hκ hκ₁ s).image =
      OGP.map hb₀.iso.hom (substAbs hF₁ hu J hJ κ hκ hκ₁) := by
    refine map_injective ((Within.boundary s.sol.toPastingDiagram n α).trans
      (SolutionAmbient.ofSolution s false).wSol).emb ?_
    rw [← Within.image_trans, ← map_comp]
    change _ = OGP.map ((Within.ofEquiv hb₀).trans
      ((Within.boundary s.sol.toPastingDiagram n α).trans
        (SolutionAmbient.ofSolution s false).wSol)).emb _
    rw [← hW₀, (SolutionAmbient.ofSolution s false).image_substAbs hF₁ hu J hJ κ hκ hκ₁, substOcc]
    exact image_occurrence _ _ _ _
  rw [Within.image_trans, hocc, ← map_comp, ← hiso]
  change OGP.map ((Within.ofEquiv hb).trans
    ((Within.boundary s.sol.toPastingDiagram n α).trans SA.wSol)).emb _ = _
  rw [← hW]
  exact SA.image_substAbs hF₁ hu J hJ κ hκ hκ₁

end SubstOcc

section Glue

variable {B : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ} {F₁ u : RoundPastingDiagram X}
  {eq₁ : Equation α n F₁ u} (s₁ : UnbiasedSolution B eq₁) {F₂ : RoundPastingDiagram X}
  {eq₂ : Equation α n F₂ s₁.sol} (s₂ : UnbiasedSolution B eq₂) (β : Bool)

noncomputable def glueSolutions :
    GlueStep (SolutionAmbient.ofSolution s₁ β).wSol (s₂.side β).witness s₂.data.pasting β n :=
  glueStep (SolutionAmbient.ofSolution s₁ β).dimK
    (SolutionAmbient.ofSolution s₁ β).isSubmoleculeOf_wSol (s₂.side β).hasBdry

noncomputable abbrev glueAmbient : RoundPastingDiagram X := (glueSolutions s₁ s₂ β).K'

theorem tClosure_glueAmbient {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) (hB : ∀ a ∈ B, TClosure A a) :
    TClosure A (glueAmbient s₁ s₂ β) :=
  (glueSolutions s₁ s₂ β).mem hDgn (hB _ (s₂.side β).mem) (hB _ (s₁.side β).mem)

noncomputable def glueFirst :
    Within F₁.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (SolutionAmbient.ofSolution s₁ β).wE.trans (glueSolutions s₁ s₂ β).wK

noncomputable def glueU : Within u.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (SolutionAmbient.ofSolution s₁ β).wU.trans (glueSolutions s₁ s₂ β).wK

noncomputable def glueFirstSol :
    Within s₁.sol.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (SolutionAmbient.ofSolution s₁ β).wSol.trans (glueSolutions s₁ s₂ β).wK

noncomputable def glueSecond :
    Within F₂.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (Within.pasteAtInl F₂.toPastingDiagram s₂.sol.toPastingDiagram n α s₂.data.occ
      s₂.data.rewritable.isSubmoleculeOf
    s₂.data.equiv).trans (glueSolutions s₁ s₂ β).wP

noncomputable def glueSecondSol :
    Within s₂.sol.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
  (Within.pasteAtInr F₂.toPastingDiagram s₂.sol.toPastingDiagram n α s₂.data.occ
      s₂.data.rewritable.isSubmoleculeOf
    s₂.data.equiv).trans (glueSolutions s₁ s₂ β).wP

theorem image_glueFirst : (glueFirst s₁ s₂ β).image =
    OGP.map (glueSolutions s₁ s₂ β).wK.emb (SolutionAmbient.ofSolution s₁ β).wE.image :=
  Within.image_trans _ _

theorem image_glueU : (glueU s₁ s₂ β).image =
    OGP.map (glueSolutions s₁ s₂ β).wK.emb (SolutionAmbient.ofSolution s₁ β).wU.image :=
  Within.image_trans _ _

theorem image_glueFirstSol : (glueFirstSol s₁ s₂ β).image =
    OGP.map (glueSolutions s₁ s₂ β).wK.emb (SolutionAmbient.ofSolution s₁ β).wSol.image :=
  Within.image_trans _ _

theorem image_glueSecond : (glueSecond s₁ s₂ β).image =
    OGP.map (glueSolutions s₁ s₂ β).wP.emb
      (Within.pasteAtInl F₂.toPastingDiagram s₂.sol.toPastingDiagram n α s₂.data.occ
        s₂.data.rewritable.isSubmoleculeOf s₂.data.equiv).image :=
  Within.image_trans _ _

theorem krullDim_glueFirst : krullDim (glueFirst s₁ s₂ β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast eq₁.dim_e

theorem krullDim_glueFirstSol : krullDim (glueFirstSol s₁ s₂ β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast s₁.data.dim_u'

theorem krullDim_glueSecond : krullDim (glueSecond s₁ s₂ β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast eq₂.dim_e

theorem krullDim_glueSecondSol : krullDim (glueSecondSol s₁ s₂ β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast s₂.data.dim_u'

theorem isMoleculeIn_boundary_glueSecond :
    IsMoleculeIn (glueAmbient s₁ s₂ β).shape.ogp
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α) :=
  (glueSecond s₁ s₂ β).isMoleculeIn_image.boundary n α

theorem isPastingAtIn_glueSecond :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueSecond s₁ s₂ β).image
      (glueSecondSol s₁ s₂ β).image (glueSolutions s₁ s₂ β).wP.image := by
  exact s₂.data.isPastingAtIn_trans (glueSolutions s₁ s₂ β).wP

theorem image_wP_glueSolutions :
    (glueSolutions s₁ s₂ β).wP.image = (glueSecond s₁ s₂ β).image ⊔ (glueSecondSol s₁ s₂ β).image :=
  (isPastingAtIn_glueSecond s₁ s₂ β).eq_sup

theorem isPastingAtIn_glueFirst_glueFirstSol :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueFirst s₁ s₂ β).image
      (glueFirstSol s₁ s₂ β).image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSolutions s₁ s₂ β).wK.image (n + 1) β) := by
  have h := (SolutionAmbient.ofSolution s₁ β).config.map (glueSolutions s₁ s₂ β).wK.emb
  rw [← image_glueFirst, ← image_glueFirstSol, ← (glueSolutions s₁ s₂ β).wK.boundary_image] at h
  exact h

theorem isSubstitutionIn_glueSolutions :
    IsSubstitutionIn (glueAmbient s₁ s₂ β).shape.ogp
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSolutions s₁ s₂ β).wK.image (n + 1) β)
      (glueFirstSol s₁ s₂ β).image (glueSolutions s₁ s₂ β).wP.image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) := by
  have h := (glueSolutions s₁ s₂ β).subst
  rw [← image_glueFirstSol] at h
  exact h

theorem isPastingAtIn_glueFirst :
    IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (glueFirst s₁ s₂ β).image
      (glueSolutions s₁ s₂ β).wP.image
      ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β) :=
  (isPastingAtIn_glueFirst_glueFirstSol s₁ s₂ β).subst_right_self
    (isSubstitutionIn_glueSolutions s₁ s₂ β)
    (by rw [krullDim_glueFirstSol]; exact_mod_cast n.lt_succ_self)

theorem image_glueU_eq :
    (glueU s₁ s₂ β).image = (glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) (!β) := by
  rw [image_glueU, (SolutionAmbient.ofSolution s₁ β).image_wU,
    (glueSolutions s₁ s₂ β).boundary_not]

theorem glueFirstSol_eq :
    (s₂.side β).geometry.wU.trans (glueSolutions s₁ s₂ β).wk = glueFirstSol s₁ s₂ β := by
  refine Within.ext_of_image_eq _ _ ?_
  rw [Within.image_trans, (s₂.side β).geometry.image_wU,
    ← (glueSolutions s₁ s₂ β).wk.boundary_image, ← (glueSolutions s₁ s₂ β).config.inf_eq,
    (glueSolutions s₁ s₂ β).inter, image_glueFirstSol]

theorem wP_glueSolutions_eq :
    (glueSolutions s₁ s₂ β).wP = (s₂.side β).geometry.wP.trans (glueSolutions s₁ s₂ β).wk := by
  refine Within.ext_of_image_eq _ _ ?_
  rw [(glueSolutions s₁ s₂ β).image_wP, Within.image_trans, (s₂.side β).geometry.image_wP,
    (glueSolutions s₁ s₂ β).wk.boundary_image]

theorem image_glueSecond_eq :
    OGP.map (glueSolutions s₁ s₂ β).wk.emb (s₂.side β).geometry.withinE.image =
      (glueSecond s₁ s₂ β).image := by
  rw [image_glueSecond, wP_glueSolutions_eq, Geometry.withinE, Within.image_trans, ← map_comp]
  rfl

theorem image_occ_glueFirstSol :
    (eq₂.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans (glueFirstSol s₁ s₂ β))).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueSecond s₁ s₂ β).image n α := by
  have e : (eq₂.occ.trans
      ((Within.boundary s₁.sol.toPastingDiagram n α).trans
        ((s₂.side β).geometry.wU.trans (glueSolutions s₁ s₂ β).wk))).image =
      OGP.map (glueSolutions s₁ s₂ β).wk.emb (eq₂.occ.trans
        ((Within.boundary s₁.sol.toPastingDiagram n α).trans
          (s₂.side β).geometry.wU)).image := by
    rw [← Within.image_trans]
    rfl
  rw [← glueFirstSol_eq, e, (s₂.side β).geometry.compat_image s₂.compat, map_boundary,
    image_glueSecond_eq]

theorem image_occ_glueU :
    (eq₁.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans (glueU s₁ s₂ β))).image =
      (glueAmbient s₁ s₂ β).shape.ogp.boundary (glueFirst s₁ s₂ β).image n α := by
  have e : (eq₁.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans (glueU s₁ s₂ β))).image =
      OGP.map (glueSolutions s₁ s₂ β).wK.emb (eq₁.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans
          (SolutionAmbient.ofSolution s₁ β).wU)).image := by
    rw [← Within.image_trans]
    rfl
  rw [e, (SolutionAmbient.ofSolution s₁ β).occ_eq, map_boundary, image_glueFirst]

noncomputable def SolutionAmbient.ofGlue {γ : Bool} {G₁ G₂ : RoundPastingDiagram X}
    (d : PasteAtData γ n G₁ G₂)
    (w₁ : Within G₁.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram)
    (w₂ : Within G₂.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram)
    (config : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n γ w₁.image w₂.image
      (w₁.image ⊔ w₂.image))
    (hocc : (d.occ.trans
      ((Within.boundary G₂.toPastingDiagram n γ).trans w₂)).image = w₁.image ⊓ w₂.image)
    (config_sol : IsPastingAtIn (glueAmbient s₁ s₂ β).shape.ogp n α (w₁.image ⊔ w₂.image)
      (glueSecondSol s₁ s₂ β).image ((glueAmbient s₁ s₂ β).shape.ogp.boundary ⊤ (n + 1) β))
    (eq : Equation α n d.round u)
    (occ_eq : (eq.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans (glueU s₁ s₂ β))).image =
        (glueAmbient s₁ s₂ β).shape.ogp.boundary (w₁.image ⊔ w₂.image) n α) :
    SolutionAmbient eq s₂.sol β :=
  let wE : Within d.round.toPastingDiagram (glueAmbient s₁ s₂ β).toPastingDiagram :=
    Within.pasteAtOfWithin w₁ w₂ config d.occ d.rewritable.isSubmoleculeOf hocc d.equiv
  have hE : wE.image = w₁.image ⊔ w₂.image :=
    Within.image_pasteAtOfWithin w₁ w₂ config d.occ d.rewritable.isSubmoleculeOf hocc d.equiv
  { K := glueAmbient s₁ s₂ β
    dimK := (glueSolutions s₁ s₂ β).dimK'
    wE := wE
    wU := glueU s₁ s₂ β
    image_wU := image_glueU_eq s₁ s₂ β
    occ_eq := hE ▸ occ_eq
    dim_sol := s₂.data.dim_u'
    wSol := glueSecondSol s₁ s₂ β
    config := hE ▸ config_sol }

end Glue

namespace PasteAtData

variable {α : Bool} {n : ℕ} {F₁ F₂ : RoundPastingDiagram X} (d : PasteAtData α n F₁ F₂)

noncomputable abbrev pasteAtInl : Within F₁.toPastingDiagram d.pasting :=
  Within.pasteAtInl F₁.toPastingDiagram F₂.toPastingDiagram n α d.occ d.rewritable.isSubmoleculeOf
      d.equiv

noncomputable abbrev pasteAtInr : Within F₂.toPastingDiagram d.pasting :=
  Within.pasteAtInr F₁.toPastingDiagram F₂.toPastingDiagram n α d.occ d.rewritable.isSubmoleculeOf
      d.equiv

theorem isPastingAtIn_pasteAtInl :
    IsPastingAtIn d.pasting.shape.ogp n α d.pasteAtInl.image d.pasteAtInr.image ⊤ :=
  Within.isPastingAtIn_pasteAt _ _ n α d.occ d.rewritable.isSubmoleculeOf d.equiv

theorem krullDim_pasteAtInl : krullDim d.pasteAtInl.image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast d.dim_e

theorem krullDim_pasteAtInr : krullDim d.pasteAtInr.image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast d.dim_u'

theorem isSubmoleculeOf_boundary_pasteAtInl :
    IsSubmoleculeOf d.pasting.shape.ogp (d.pasting.shape.ogp.boundary d.pasteAtInl.image n α)
      (d.pasting.shape.ogp.boundary ⊤ n α) :=
  d.isPastingAtIn_pasteAtInl.isSubmoleculeOf_boundary_left

noncomputable abbrev boundaryPasteAtInl : Within (F₁.boundary n (!α)) d.pasting :=
  (Within.boundary F₁.toPastingDiagram n (!α)).trans d.pasteAtInl

theorem image_boundaryPasteAtInl :
    d.boundaryPasteAtInl.image = d.pasting.shape.ogp.boundary d.pasteAtInl.image n (!α) :=
  Within.image_boundary_trans _ _ _

theorem isSubstitutionIn_boundary_pasteAtInr :
    IsSubstitutionIn d.pasting.shape.ogp (d.pasting.shape.ogp.boundary ⊤ n α)
      (d.pasting.shape.ogp.boundary d.pasteAtInl.image n α)
      (d.pasting.shape.ogp.boundary d.pasteAtInl.image n (!α))
      (d.pasting.shape.ogp.boundary d.pasteAtInr.image n α) := by
  have h := (d.isPastingAtIn_pasteAtInl.isSubstitutionIn_boundary
    (d.pasteAtInl.round_image_iff.2 F₁.isRound) d.krullDim_pasteAtInl
    (by rw [krullDim_pasteAtInr]; exact_mod_cast n.le_succ)).symm
  rw [d.isPastingAtIn_pasteAtInl.inf_eq] at h
  exact h

theorem isMoleculeIn_boundary_pasteAtInr :
    IsMoleculeIn d.pasting.shape.ogp (d.pasting.shape.ogp.boundary d.pasteAtInr.image n α) :=
  d.pasteAtInr.isMoleculeIn_image.boundary n α

theorem equiv_restrictTo_boundary_pasteAtInr :
    (d.pasting.restrictTo d.isMoleculeIn_boundary_pasteAtInr).Equiv (F₂.boundary n α) :=
  (Within.equiv_restrictTo_of_eq
    ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr)
    (Within.image_boundary_trans _ _ _) _).symm

theorem image_occ_pasteAtInr :
    (d.occ.trans
      ((Within.boundary F₂.toPastingDiagram n α).trans d.pasteAtInr)).image =
      d.pasteAtInl.image ⊓ d.pasteAtInr.image :=
  image_occurrence_pasteAt _ _ n α d.occ d.rewritable.isSubmoleculeOf d.equiv

end PasteAtData

end Atoms.Diagrammatic
