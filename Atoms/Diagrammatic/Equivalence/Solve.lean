import Atoms.Diagrammatic.Equivalence.UnitSolution

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem HasBdry.equiv_boundary_of_inverse {n : ℕ} {e eInv : PastingDiagram X}
    (ht : HasBdry false n eInv (e.boundary n true) (e.boundary n false)) (α : Bool) :
    (eInv.boundary n α).Equiv (e.boundary n (!α)) := by
  cases α
  · exact ht.side
  · exact ht.other

theorem HasBdry.of_inverse {n : ℕ} {e eInv : PastingDiagram X} (hd : eInv.dim = n + 1)
    (he : n ≤ e.dim) (h : ∀ γ, (eInv.boundary n γ).Equiv (e.boundary n (!γ))) :
    HasBdry false n eInv (e.boundary n true) (e.boundary n false) :=
  ⟨hd, dim_boundary e he true, dim_boundary e he false, h false, h true⟩

theorem HasBdry.inverse {β : Bool} {n : ℕ} {z zL a b : PastingDiagram X} (t : HasBdry β n z a b)
    (ht : HasBdry false n zL (z.boundary n true) (z.boundary n false)) : HasBdry (!β) n zL a b :=
  ⟨ht.dim_h, t.dim_a, t.dim_b,
    (ht.equiv_boundary_of_inverse (!β)).trans (by rw [Bool.not_not]; exact t.side),
    by rw [Bool.not_not]; exact (ht.equiv_boundary_of_inverse β).trans t.other⟩

abbrev compositeData {α : Bool} {n : ℕ} {e eInv : RoundPastingDiagram X} (he : e.dim = n + 1)
    (ht : HasBdry false n eInv.toPastingDiagram (e.boundary n true) (e.boundary n false)) :
    PasteAtData α n e eInv :=
  PasteAtData.ofBoundary he ht.dim_h (ht.equiv_boundary_of_inverse α).symm

structure InvertorData (A : Set (RoundPastingDiagram X)) {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} (eq : Equation α n e u) where
  inv : RoundPastingDiagram X
  hasType : HasBdry false n inv.toPastingDiagram (e.boundary n true) (e.boundary n false)
  z : Bool → RoundPastingDiagram X
  mem : ∀ β, TClosure A (z β)
  hasBdry : ∀ β, HasBdry β (n + 1) (z β).toPastingDiagram
    (compositeData (α := α) eq.dim_e hasType).pasting (e.boundary n α).unit

namespace BiInvData

variable {A : Set (RoundPastingDiagram X)} {e : RoundPastingDiagram X} (D : BiInvData A e) {n : ℕ}
  (hn : e.dim = n + 1)

include hn in
theorem hasType_inverse (α : Bool) :
    HasBdry false n (D.inverse α).toPastingDiagram (e.boundary n true) (e.boundary n false) := by
  have hk : e.dim - 1 = n := by omega
  refine HasBdry.of_inverse ((D.dim_inverse α).trans hn) (by omega) fun γ => ?_
  have h := D.equiv_boundary_inverse α γ
  rw [PastingDiagram.boundary_congr _ hk, PastingDiagram.boundary_congr _ hk] at h
  exact h

include hn in
theorem hasBdry_invertor (α : Bool) :
    HasBdry α (n + 1) (D.invertor α).toPastingDiagram
      (compositeData (α := α) hn (D.hasType_inverse hn α)).pasting
      (e.boundary n α).unit := by
  obtain rfl : n = e.dim - 1 := by omega
  have hp := D.pastable α
  have hC := D.boundary_invertor_composite α
  refine HasBdry.of_dim_eq (k := e.dim) hn (by rw [D.dim_invertor, hn])
    (compositeData (α := α) hn _).dim_pasting
    (by rw [dim_unit, dim_boundary e.toPastingDiagram (by omega) α]) ?_
    (D.boundary_invertor_unit α)
  exact hC.trans (equiv_paste_pasteAtBoundary e.toPastingDiagram (D.inverse α).toPastingDiagram
    (e.dim - 1) α _ _ (Within.image_refl _) _ hp)

end BiInvData

section UnitSelf

variable {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (eq : Equation α n e u)

def Equation.unitSelf : Equation α n (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit u :=
  have hn : eq.sub.dim = n :=
    Within.dim_eq_of_isRewritableSubmolecule_boundary eq.rewritable (by rw [eq.dim_u]; omega)
  ⟨by change eq.sub.unit.dim = n + 1; rw [dim_unit, hn], eq.dim_u, eq.sub, eq.occ,
    eq.rewritable,
    (boundary_unit hn α).symm⟩

theorem Equation.nonempty_unbiasedSolution_unitSelf :
    Nonempty (UnbiasedSolution {a : RoundPastingDiagram X | a.IsDegenerate} eq.unitSelf) := by
  have hd : 0 < u.dim := by rw [eq.dim_u]; omega
  obtain rfl : n = u.dim - 1 := by have := eq.dim_u; omega
  exact ⟨unitSolution u hd α eq.occ eq.rewritable⟩

end UnitSelf

section SolutionData

variable {A B : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
  {eq : Equation α n e u} (D : InvertorData A eq) (s : UnbiasedSolution B eq.unitSelf)

abbrev innerData : PasteAtData α n D.inv s.sol :=
  ⟨D.hasType.dim_h, s.data.dim_u', s.data.sub, s.data.occ, s.data.rewritable, by
    have h1 : (D.inv.boundary n (!α)).Equiv (e.boundary n α) := by
      simpa only [Bool.not_not] using D.hasType.equiv_boundary_of_inverse (!α)
    exact h1.trans (eq.equiv.symm.trans
      (PastingDiagram.Equiv.trans
        ((boundary_unit
          (Within.dim_eq_of_isRewritableSubmolecule_boundary eq.rewritable
            (by rw [eq.dim_u]; omega)) (!α)).symm)
        s.data.equiv))⟩

end SolutionData

section Equation

variable {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (eq : Equation α n e u) (β : Bool)

structure EquationAmbient where
  K : RoundPastingDiagram X
  dimK : K.dim = n + 2
  wE : Within e.toPastingDiagram K.toPastingDiagram
  wU : Within u.toPastingDiagram K.toPastingDiagram
  image_wU : wU.image = K.shape.ogp.boundary ⊤ (n + 1) (!β)
  occ_eq : (eq.occ.trans
    ((Within.boundary u.toPastingDiagram n α).trans wU)).image =
      K.shape.ogp.boundary wE.image n α

namespace EquationAmbient

variable {eq β} (EA : EquationAmbient eq β)

theorem krullDim_wE : krullDim EA.wE.image = n + 1 := by
  rw [EA.wE.krullDim_image]; exact_mod_cast eq.dim_e

theorem isMoleculeIn_boundary_K :
    IsMoleculeIn EA.K.shape.ogp (EA.K.shape.ogp.boundary ⊤ (n + 1) β) :=
  IsMoleculeIn.boundary EA.K.shape.isMolecule _ _

variable {v : RoundPastingDiagram X} (d : PasteAtData α n e v)
  (wV : Within v.toPastingDiagram EA.K.toPastingDiagram)
  (config : IsPastingAtIn EA.K.shape.ogp n α EA.wE.image wV.image
    (EA.K.shape.ogp.boundary ⊤ (n + 1) β))
  (hocc : (d.occ.trans
    ((Within.boundary v.toPastingDiagram n α).trans wV)).image = EA.wE.image ⊓ wV.image)

include config hocc in
theorem equiv_pasting :
    d.pasting.Equiv (EA.K.toPastingDiagram.restrictTo EA.isMoleculeIn_boundary_K) :=
  equiv_pasteAtBoundary_of_within EA.wE wV config d.occ d.rewritable.isSubmoleculeOf hocc d.equiv

include wV config hocc in
theorem hasBdry : HasBdry β (n + 1) EA.K.toPastingDiagram d.pasting u.toPastingDiagram :=
  ⟨EA.dimK, d.dim_pasting, eq.dim_u, by
    rw [boundary_eq_restrictTo]; exact (EA.equiv_pasting d wV config hocc).symm,
    Within.equiv_of_image_eq (Within.boundary EA.K.toPastingDiagram (n + 1) (!β)) EA.wU
      (by rw [Within.image_boundary, EA.image_wU])⟩

include EA wV config hocc in
theorem compat : Compat eq d := by
  let g : Geometry d u EA.K β := Geometry.ofHasBdry (EA.hasBdry d wV config hocc)
  refine g.compat_of_image ?_
  have hwU : g.wU = EA.wU := Within.ext_of_image_eq _ _ (by rw [g.image_wU, EA.image_wU])
  have hwP : g.wP = Within.pasteAtOfWithin EA.wE wV config d.occ d.rewritable.isSubmoleculeOf
      hocc d.equiv := by
    refine Within.ext_of_image_eq _ _ ?_
    rw [g.image_wP, Within.image_pasteAtOfWithin]
  have hE : g.withinE = EA.wE := by
    rw [Geometry.withinE, hwP]
    exact (Within.pasteAtInl_and_pasteAtInr_trans_pasteAtOfWithin EA.wE wV config d.occ
      d.rewritable.isSubmoleculeOf hocc d.equiv).1
  rw [hwU, hE]
  exact EA.occ_eq

end EquationAmbient

end Equation

section Canon

variable {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (eq : Equation α n e u)
  (sol : RoundPastingDiagram X)

noncomputable abbrev Equation.solBoundary : PastingDiagram X :=
  (u.boundary n α).substitute eq.occ eq.rewritable
    ⟨e.boundary n (!α), isRound_boundary_of_isRound e.isRound n (!α)⟩ eq.parallel_occ

noncomputable def Equation.canonOcc (hb : eq.solBoundary.Equiv (sol.boundary n α)) :
    Within (e.boundary n (!α)) (sol.boundary n α) :=
  (Within.substitute eq.occ eq.rewritable
    ⟨e.boundary n (!α), isRound_boundary_of_isRound e.isRound n (!α)⟩ eq.parallel_occ).trans
    (Within.ofEquiv hb)

theorem Equation.isRewritableSubmolecule_image_canonOcc
    (hb : eq.solBoundary.Equiv (sol.boundary n α)) :
    (sol.boundary n α).shape.ogp.IsRewritableSubmolecule (eq.canonOcc sol hb).image ⊤ :=
  (Within.isRewritableSubmolecule_image_trans_ofEquiv_iff _ hb).2
    (Within.isRewritableSubmolecule_image_substitute _ _ _ _)

end Canon

section SolutionAmbients

variable {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X} (eq : Equation α n e u)
  (sol : RoundPastingDiagram X) (β : Bool)

structure SolutionAmbient extends EquationAmbient eq β where
  dim_sol : sol.dim = n + 1
  wSol : Within sol.toPastingDiagram K.toPastingDiagram
  config : IsPastingAtIn K.shape.ogp n α wE.image wSol.image
    (K.shape.ogp.boundary ⊤ (n + 1) β)

namespace SolutionAmbient

variable {eq sol β} (SA : SolutionAmbient eq sol β)

theorem krullDim_wSol : krullDim SA.wSol.image = n + 1 := by
  rw [SA.wSol.krullDim_image]; exact_mod_cast SA.dim_sol

theorem isMoleculeIn_boundary_wSol :
    IsMoleculeIn SA.K.shape.ogp (SA.K.shape.ogp.boundary SA.wSol.image n α) :=
  SA.wSol.isMoleculeIn_image.boundary n α

theorem isSubstitutionIn_boundary_wSol :
    IsSubstitutionIn SA.K.shape.ogp
      (SA.K.shape.ogp.boundary SA.wU.image n α)
      (eq.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans SA.wU)).image
      (SA.K.shape.ogp.boundary SA.wE.image n (!α))
      (SA.K.shape.ogp.boundary SA.wSol.image n α) := by
  have h := (SA.config.isSubstitutionIn_boundary (SA.wE.round_image_iff.2 e.isRound)
    SA.krullDim_wE (by rw [SA.krullDim_wSol]; exact_mod_cast n.le_succ)).symm
  have hg := IsMoleculeIn.isGlobular SA.K.shape.isMolecule
  rw [SA.config.inf_eq, ← SA.occ_eq, hg n (n + 1) (Nat.lt_succ_self n) α β,
    ← hg n (n + 1) (Nat.lt_succ_self n) α (!β), ← SA.image_wU] at h
  exact h

theorem equiv_solBoundary_restrictTo :
    eq.solBoundary.Equiv (SA.K.toPastingDiagram.restrictTo SA.isMoleculeIn_boundary_wSol) :=
  equiv_substitute_of_within eq.occ eq.rewritable _ eq.parallel_occ
    ((Within.boundary u.toPastingDiagram n α).trans SA.wU)
    ((Within.boundary e.toPastingDiagram n (!α)).trans SA.wE) (by
      rw [Within.image_boundary_trans, Within.image_boundary_trans]
      exact SA.isSubstitutionIn_boundary_wSol) _

include SA in
theorem equiv_solBoundary : eq.solBoundary.Equiv (sol.boundary n α) :=
  SA.equiv_solBoundary_restrictTo.trans
    ((((Within.boundary sol.toPastingDiagram n α).trans SA.wSol)
      |>.equiv_restrictTo_of_eq (Within.image_boundary_trans _ _ _) _).symm)

theorem image_canonOcc (hb : eq.solBoundary.Equiv (sol.boundary n α)) :
    ((eq.canonOcc sol hb).trans
      ((Within.boundary sol.toPastingDiagram n α).trans SA.wSol)).image =
        SA.wE.image ⊓ SA.wSol.image := by
  let W₀ : Within eq.solBoundary SA.K.toPastingDiagram :=
    (Within.ofEquiv hb).trans ((Within.boundary sol.toPastingDiagram n α).trans SA.wSol)
  let W₁ : Within eq.solBoundary SA.K.toPastingDiagram :=
    (Within.ofEquiv SA.equiv_solBoundary_restrictTo).trans
      (Within.restrictTo _ SA.isMoleculeIn_boundary_wSol)
  have hW : ∀ y, W₀.emb y = W₁.emb y := by
    refine Within.emb_apply_eq_of_image_eq W₀ W₁ ?_
    change ((Within.ofEquiv hb).trans ((Within.boundary sol.toPastingDiagram n α).trans
      SA.wSol)).image = ((Within.ofEquiv SA.equiv_solBoundary_restrictTo).trans
        (Within.restrictTo _ SA.isMoleculeIn_boundary_wSol)).image
    rw [Within.image_trans, Within.image_ofEquiv, Within.image_trans, Within.image_ofEquiv]
    exact (Within.image_boundary_trans _ _ _).trans (Within.image_restrictTo _ _).symm
  have hwW : ((Within.boundary e.toPastingDiagram n (!α)).trans SA.wE).image =
      SA.wE.image ⊓ SA.wSol.image := by
    rw [Within.image_boundary_trans, SA.config.inf_eq]
  rw [← hwW]
  refine congrArg (fun f => OGP.map f ⊤) ?_
  ext y
  exact (hW (substInrEmb (u.boundary n α) eq.occ eq.rewritable _ eq.parallel_occ y)).trans
    ((apply_iso_substInlEmb_and_substInrEmb_of_within eq.occ eq.rewritable _ eq.parallel_occ
      ((Within.boundary u.toPastingDiagram n α).trans SA.wU)
      ((Within.boundary e.toPastingDiagram n (!α)).trans SA.wE) (by
        rw [Within.image_boundary_trans, Within.image_boundary_trans]
        exact SA.isSubstitutionIn_boundary_wSol) _ SA.equiv_solBoundary_restrictTo).2 y)

noncomputable def data (hb : eq.solBoundary.Equiv (sol.boundary n α)) : PasteAtData α n e sol :=
  ⟨eq.dim_e, SA.dim_sol, _, eq.canonOcc sol hb, eq.isRewritableSubmolecule_image_canonOcc sol hb,
    .refl _⟩

end SolutionAmbient

variable {eq sol} in
noncomputable def UnbiasedSolution.ofAmbients {A : Set (RoundPastingDiagram X)}
    (SA₀ : SolutionAmbient eq sol false) (SA₁ : SolutionAmbient eq sol true)
    (h₀ : TClosure A SA₀.K) (h₁ : TClosure A SA₁.K) :
    UnbiasedSolution (TClosure A) eq :=
  UnbiasedSolution.ofSides sol (SA₀.data SA₀.equiv_solBoundary)
    (SA₀.compat _ SA₀.wSol SA₀.config (SA₀.image_canonOcc _)) (β := false)
    ⟨SA₀.K, h₀, SA₀.hasBdry _ SA₀.wSol SA₀.config (SA₀.image_canonOcc _)⟩
    ⟨SA₁.K, h₁, SA₁.hasBdry (SA₀.data SA₀.equiv_solBoundary) SA₁.wSol SA₁.config
      (SA₁.image_canonOcc _)⟩

end SolutionAmbients

section Glue

variable {K : RoundPastingDiagram X} {P₀ : PastingDiagram X} (wP₀ : Within P₀ K.toPastingDiagram)
  (k : RoundPastingDiagram X) (P : PastingDiagram X) (β : Bool) (n : ℕ)

structure GlueStep where
  K' : RoundPastingDiagram X
  dimK' : K'.dim = n + 2
  wK : Within K.toPastingDiagram K'.toPastingDiagram
  wk : Within k.toPastingDiagram K'.toPastingDiagram
  wP : Within P K'.toPastingDiagram
  config : IsPastingAtIn K'.shape.ogp (n + 1) β wk.image wK.image ⊤
  inter : wk.image ⊓ wK.image = OGP.map wK.emb wP₀.image
  image_wP : wP.image = K'.shape.ogp.boundary wk.image (n + 1) β
  subst : IsSubstitutionIn K'.shape.ogp (K'.shape.ogp.boundary wK.image (n + 1) β)
    (OGP.map wK.emb wP₀.image) wP.image (K'.shape.ogp.boundary ⊤ (n + 1) β)
  boundary_not : K'.shape.ogp.boundary ⊤ (n + 1) (!β) =
    OGP.map wK.emb (K.shape.ogp.boundary ⊤ (n + 1) (!β))
  mem : ∀ {A : Set (RoundPastingDiagram X)}, (∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) →
    TClosure A k → TClosure A K → TClosure A K'

variable {wP₀ k P β n}

@[irreducible] noncomputable def glueStep (hK : K.dim = n + 2)
    (hP₀ : IsSubmoleculeOf K.shape.ogp wP₀.image (K.shape.ogp.boundary ⊤ (n + 1) β))
    (hk : HasBdry β (n + 1) k.toPastingDiagram P P₀) : GlueStep wP₀ k P β n := by
  have hP₀' : IsSubmoleculeOf K.shape.ogp wP₀.image
      (K.shape.ogp.boundary (Within.refl K.toPastingDiagram).image (n + 1) β) := by
    rw [Within.image_refl]; exact hP₀
  let occ := occurrence (Within.refl K.toPastingDiagram) (n + 1) β hP₀'
  have hocc : P₀.Equiv (occurrenceDiagram (Within.refl K.toPastingDiagram) (n + 1) β hP₀') :=
    equiv_occurrence_of_image_eq (Within.refl K.toPastingDiagram) (n + 1) β hP₀' wP₀ rfl
  have hround : P₀.IsRound :=
    (Equiv.isRound_iff hk.other).1 (isRound_boundary_of_isRound k.isRound (n + 1) (!β))
  have hsub : IsSubmoleculeOf (K.boundary (n + 1) β).shape.ogp occ.image ⊤ :=
    isSubmoleculeOf_image_occurrence _ _ _ _
  have rew : (K.boundary (n + 1) β).shape.ogp.IsRewritableSubmolecule occ.image ⊤ :=
    occ.isRewritableSubmolecule_image_iff.2 ⟨hsub, (Equiv.isRound_iff hocc).1 hround, by
      rw [← dim_eq_of_equiv hocc, hk.dim_b, dim_boundary K.toPastingDiagram (by omega) β]⟩
  have equiv : (k.boundary (n + 1) (!β)).Equiv
      (occurrenceDiagram (Within.refl K.toPastingDiagram) (n + 1) β hP₀') :=
    hk.other.trans hocc
  let dK : PasteAtData β (n + 1) k K := ⟨hk.dim_h, hK, _, occ, rew, equiv⟩
  let wk := Within.pasteAtInl k.toPastingDiagram K.toPastingDiagram (n + 1) β occ hsub equiv
  let wK := Within.pasteAtInr k.toPastingDiagram K.toPastingDiagram (n + 1) β occ hsub equiv
  have C_K : IsPastingAtIn dK.pasting.shape.ogp (n + 1) β wk.image wK.image ⊤ :=
    Within.isPastingAtIn_pasteAt _ _ (n + 1) β occ hsub equiv
  have hinter : wk.image ⊓ wK.image = OGP.map wK.emb wP₀.image := by
    rw [← image_occurrence_pasteAt _ _ (n + 1) β occ hsub equiv]
    have h := image_occurrence (Within.refl K.toPastingDiagram) (n + 1) β hP₀'
    rw [Within.image_trans] at h
    change OGP.map ((Within.boundary K.toPastingDiagram (n + 1) β).emb ≫ 𝟙 _) occ.image = _ at h
    rw [Category.comp_id] at h
    rw [Within.image_trans_assoc, Within.image_trans, h]
  let wP : Within P dK.pasting :=
    (Within.ofEquiv (hk.side.symm)).trans
      ((Within.boundary k.toPastingDiagram (n + 1) β).trans wk)
  have image_wP : wP.image = dK.pasting.shape.ogp.boundary wk.image (n + 1) β := by
    change ((Within.ofEquiv (hk.side.symm)).trans
      ((Within.boundary k.toPastingDiagram (n + 1) β).trans wk)).image = _
    rw [Within.image_trans, Within.image_ofEquiv]
    exact Within.image_boundary_trans _ _ _
  have hsubst : IsSubstitutionIn dK.pasting.shape.ogp
      (dK.pasting.shape.ogp.boundary wK.image (n + 1) β) (OGP.map wK.emb wP₀.image) wP.image
      (dK.pasting.shape.ogp.boundary ⊤ (n + 1) β) := by
    have h := C_K.isSubstitutionIn_boundary (wk.round_image_iff.2 k.isRound)
      (by rw [wk.krullDim_image]; exact_mod_cast hk.dim_h)
      (by rw [wK.krullDim_image]; exact_mod_cast (show n + 1 ≤ K.dim by omega))
    rw [hinter, ← image_wP] at h
    exact h
  have hbn : dK.pasting.shape.ogp.boundary ⊤ (n + 1) (!β) =
      OGP.map wK.emb (K.shape.ogp.boundary ⊤ (n + 1) (!β)) := by
    rw [C_K.boundary_not, wK.boundary_image]
  exact ⟨dK.round, dK.dim_pasting, wK, wk, wP, C_K, hinter, image_wP, hsubst, hbn,
    fun hDgn hk' hK' => TClosure.pasteAt hDgn dK hk' hK'⟩

end Glue

section Ambient

variable {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ} {e u : RoundPastingDiagram X}
  {eq : Equation α n e u} (D : InvertorData A eq)
  (s : UnbiasedSolution (TClosure A) eq.unitSelf) (β : Bool)

structure SolveAmbient extends EquationAmbient eq β where
  memK : TClosure A K
  wI : Within D.inv.toPastingDiagram K.toPastingDiagram
  wS : Within s.sol.toPastingDiagram K.toPastingDiagram
  config_EI : IsPastingAtIn K.shape.ogp n α wE.image wI.image (wE.image ⊔ wI.image)
  config_mid : IsPastingAtIn K.shape.ogp n α (wE.image ⊔ wI.image) wS.image
    (K.shape.ogp.boundary ⊤ (n + 1) β)
  occ_inner : ((innerData D s).occ.trans
    ((Within.boundary s.sol.toPastingDiagram n α).trans wS)).image = wI.image ⊓ wS.image

namespace SolveAmbient

variable {D s β} (SA : SolveAmbient D s β)

theorem config_assoc :
    IsPastingAtIn SA.K.shape.ogp n α SA.wI.image SA.wS.image (SA.wI.image ⊔ SA.wS.image) ∧
      IsPastingAtIn SA.K.shape.ogp n α SA.wE.image (SA.wI.image ⊔ SA.wS.image)
        (SA.K.shape.ogp.boundary ⊤ (n + 1) β) :=
  SA.config_EI.assoc_right SA.config_mid

noncomputable def wInner : Within (innerData D s).pasting SA.K.toPastingDiagram :=
  Within.pasteAtOfWithin SA.wI SA.wS SA.config_assoc.1 (innerData D s).occ
    (innerData D s).rewritable.isSubmoleculeOf SA.occ_inner (innerData D s).equiv

theorem image_wInner : SA.wInner.image = SA.wI.image ⊔ SA.wS.image :=
  Within.image_pasteAtOfWithin SA.wI SA.wS SA.config_assoc.1 (innerData D s).occ
    (innerData D s).rewritable.isSubmoleculeOf SA.occ_inner (innerData D s).equiv

theorem config_outer :
    IsPastingAtIn SA.K.shape.ogp n α SA.wE.image SA.wInner.image
      (SA.K.shape.ogp.boundary ⊤ (n + 1) β) := by
  rw [SA.image_wInner]; exact SA.config_assoc.2

noncomputable def toSolutionAmbient : SolutionAmbient eq (innerData D s).round β where
  toEquationAmbient := SA.toEquationAmbient
  dim_sol := (innerData D s).dim_pasting
  wSol := SA.wInner
  config := SA.config_outer

end SolveAmbient

noncomputable def SolveAmbient.ofInvertor
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) : SolveAmbient D s β := by
  let sw := s.side β
  let gM : Geometry s.data u sw.witness β := sw.geometry
  have hzb := D.hasBdry β
  have hεd : (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit.dim = n + 1 := eq.unitSelf.dim_e
  let dc : PasteAtData α n e D.inv := compositeData eq.dim_e D.hasType
  have hsubc : IsSubmoleculeOf (D.inv.boundary n α).shape.ogp dc.occ.image ⊤ :=
    dc.rewritable.isSubmoleculeOf
  have hmeet := inter_eq_boundary_pasteAt_of_image_univ e.toPastingDiagram D.inv.toPastingDiagram
    n α dc.occ hsubc (Within.image_refl _) dc.equiv
  have hP₀ : IsSubmoleculeOf sw.witness.shape.ogp gM.withinE.image
      (sw.witness.shape.ogp.boundary ⊤ (n + 1) β) :=
    gM.isPastingAtIn.isSubmoleculeOf_left
  have hk : HasBdry β (n + 1) (D.z β).toPastingDiagram dc.pasting
      (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit.toPastingDiagram :=
    ⟨hzb.dim_h, hzb.dim_a, hεd, hzb.side, hzb.other.trans (Equiv.unit (eq.equiv.symm))⟩
  let GS := glueStep (wP₀ := gM.withinE) gM.dim_w hP₀ hk
  let wE := (Within.pasteAtInl e.toPastingDiagram D.inv.toPastingDiagram n α dc.occ hsubc
    dc.equiv).trans GS.wP
  let wI := (Within.pasteAtInr e.toPastingDiagram D.inv.toPastingDiagram n α dc.occ hsubc
    dc.equiv).trans GS.wP
  have eE : wE.image = OGP.map GS.wP.emb (Within.pasteAtInl e.toPastingDiagram
      D.inv.toPastingDiagram n α dc.occ hsubc dc.equiv).image := Within.image_trans _ _
  have eI : wI.image = OGP.map GS.wP.emb (Within.pasteAtInr e.toPastingDiagram
      D.inv.toPastingDiagram n α dc.occ hsubc dc.equiv).image := Within.image_trans _ _
  have C_z : IsPastingAtIn GS.K'.shape.ogp n α wE.image wI.image
      (GS.K'.shape.ogp.boundary GS.wk.image (n + 1) β) := by
    rw [← GS.image_wP]
    exact dc.isPastingAtIn_trans GS.wP
  have inter_EI : wE.image ⊓ wI.image = GS.K'.shape.ogp.boundary wI.image n α := by
    rw [eE, eI, ← OGP.map_inf, hmeet]
    exact map_boundary _ _ _ _
  let wV := gM.withinE.trans GS.wK
  let wS := gM.withinSol.trans GS.wK
  let wU := gM.wU.trans GS.wK
  have eV : wV.image = OGP.map GS.wK.emb gM.withinE.image := Within.image_trans _ _
  have eS : wS.image = OGP.map GS.wK.emb gM.withinSol.image := Within.image_trans _ _
  have eU : wU.image = OGP.map GS.wK.emb gM.wU.image := Within.image_trans _ _
  have C_M : IsPastingAtIn GS.K'.shape.ogp n α wV.image wS.image
      (GS.K'.shape.ogp.boundary GS.wK.image (n + 1) β) := by
    rw [eV, eS, GS.wK.boundary_image]
    exact gM.isPastingAtIn.map GS.wK.emb
  have image_wU : wU.image = GS.K'.shape.ogp.boundary ⊤ (n + 1) (!β) := by
    rw [eU, gM.image_wU, GS.boundary_not]
  have eVE : gM.withinE.image = OGP.map gM.wP.emb (Within.pasteAtInl
      (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit.toPastingDiagram
      s.sol.toPastingDiagram n α s.data.occ s.data.rewritable.isSubmoleculeOf
          s.data.equiv).image :=
    Within.image_trans _ _
  have eSS : gM.withinSol.image = OGP.map gM.wP.emb (Within.pasteAtInr
      (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit.toPastingDiagram
      s.sol.toPastingDiagram n α s.data.occ s.data.rewritable.isSubmoleculeOf
          s.data.equiv).image :=
    Within.image_trans _ _
  have hsub' : IsSubstitutionIn GS.K'.shape.ogp
      (GS.K'.shape.ogp.boundary GS.wK.image (n + 1) β) wV.image
      (GS.K'.shape.ogp.boundary GS.wk.image (n + 1) β)
      (GS.K'.shape.ogp.boundary ⊤ (n + 1) β) := by
    have h := GS.subst
    rw [GS.image_wP, ← eV] at h
    exact h
  have hdV : krullDim wV.image = n + 1 := by rw [wV.krullDim_image]; exact_mod_cast hεd
  have C_mid : IsPastingAtIn GS.K'.shape.ogp n α
      (GS.K'.shape.ogp.boundary GS.wk.image (n + 1) β) wS.image
      (GS.K'.shape.ogp.boundary ⊤ (n + 1) β) :=
    C_M.subst_left_self hsub' (by rw [hdV]; exact_mod_cast n.lt_succ_self)
  have C_EI : IsPastingAtIn GS.K'.shape.ogp n α wE.image wI.image (wE.image ⊔ wI.image) :=
    ⟨C_z.isMoleculeIn_left, C_z.isMoleculeIn_right, rfl, C_z.inf_eq, C_z.isSubmoleculeOf_inf⟩
  have hEI : GS.K'.shape.ogp.boundary GS.wk.image (n + 1) β = wE.image ⊔ wI.image :=
    C_z.eq_sup
  rw [hEI] at C_mid hsub'
  have hdEI : krullDim (wE.image ⊔ wI.image : LowerSet GS.K'.shape.ogp) = n + 1 :=
    hsub'.krullDim_target.trans hdV
  have occ_inner : (s.data.occ.trans
      ((Within.boundary s.sol.toPastingDiagram n α).trans wS)).image = wI.image ⊓ wS.image := by
    have h := image_occurrence_pasteAt
        (eq.occ.round_image_iff.1 eq.rewritable.isRound).unit.toPastingDiagram
      s.sol.toPastingDiagram n α s.data.occ s.data.rewritable.isSubmoleculeOf s.data.equiv
    have h1 : (s.data.occ.trans
        ((Within.boundary s.sol.toPastingDiagram n α).trans wS)).image = wV.image ⊓ wS.image := by
      rw [eV, eS, eVE, eSS, ← OGP.map_inf, ← OGP.map_inf, ← h, ← Within.image_trans,
        ← Within.image_trans]
      rfl
    have hVS : wV.image ⊓ wS.image = wI.image ⊓ wS.image := by
      rw [C_M.inf_eq, (C_EI.assoc_right C_mid).1.inf_eq]
      have hb := hsub'.bdry_eq (!α)
      rw [bdry_eq_boundary hdEI, bdry_eq_boundary hdV, C_EI.boundary_not] at hb
      exact hb.symm
    exact h1.trans hVS
  have occ_eq : (eq.occ.trans
      ((Within.boundary u.toPastingDiagram n α).trans wU)).image =
        GS.K'.shape.ogp.boundary wE.image n α := by
    have hc : (eq.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans gM.wU)).image =
          sw.witness.shape.ogp.boundary gM.withinE.image n α := gM.compat_image s.compat
    have e5 : (eq.occ.trans
        ((Within.boundary u.toPastingDiagram n α).trans wU)).image =
          OGP.map GS.wK.emb (eq.occ.trans
            ((Within.boundary u.toPastingDiagram n α).trans gM.wU)).image := by
      rw [← Within.image_trans]
      rfl
    rw [e5, hc, map_boundary, ← eV]
    have hb := hsub'.bdry_eq α
    rw [bdry_eq_boundary hdEI, bdry_eq_boundary hdV,
      C_EI.boundary_eq_left_of_inf_eq inter_EI] at hb
    exact hb.symm
  exact ⟨⟨GS.K', GS.dimK', wE, wU, image_wU, occ_eq⟩,
    GS.mem hDgn (D.mem β) sw.mem, wI, wS, C_EI, C_mid, occ_inner⟩

theorem InvertorData.nonempty_unbiasedSolution
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) (D : InvertorData A eq) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨s₀⟩ := eq.nonempty_unbiasedSolution_unitSelf
  let s : UnbiasedSolution (TClosure A) eq.unitSelf :=
    s₀.mono fun d hd => TClosure.base (hDgn d hd)
  let SA₀ := SolveAmbient.ofInvertor D s false hDgn
  let SA₁ := SolveAmbient.ofInvertor D s true hDgn
  exact ⟨UnbiasedSolution.ofAmbients SA₀.toSolutionAmbient SA₁.toSolutionAmbient SA₀.memK
    SA₁.memK⟩

end Ambient

def InvertorData.ofSides {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {e u : RoundPastingDiagram X} (eq : Equation α n e u) (inv : RoundPastingDiagram X)
    (hinv : HasBdry false n inv.toPastingDiagram (e.boundary n true) (e.boundary n false))
    {β : Bool} (z₁ z₂ : RoundPastingDiagram X) (h₁ : TClosure A z₁) (h₂ : TClosure A z₂)
    (b₁ : HasBdry β (n + 1) z₁.toPastingDiagram
      (compositeData (α := α) eq.dim_e hinv).pasting (e.boundary n α).unit)
    (b₂ : HasBdry (!β) (n + 1) z₂.toPastingDiagram
      (compositeData (α := α) eq.dim_e hinv).pasting (e.boundary n α).unit) :
    InvertorData A eq :=
  ⟨inv, hinv, fun γ => if γ = β then z₁ else z₂,
    fun γ => by split <;> assumption,
    fun γ => by
      split
      next h => subst h; exact b₁
      next h => rw [Bool.eq_not.2 h]; exact b₂⟩

section Degenerate

variable {e : RoundPastingDiagram X} (he : e.IsDegenerate)

include he in
theorem nonempty_invertorData_of_isDegenerate {α : Bool} {n : ℕ} {u : RoundPastingDiagram X}
    (eq : Equation α n e u) :
    Nonempty (InvertorData {a : RoundPastingDiagram X | a.IsDegenerate} eq) := by
  let D := BiInvData.ofIsDegenerate e he
  have hz := D.invertor_mem α
  let Dz := BiInvData.ofIsDegenerate (D.invertor α) hz
  have hdz : (D.invertor α).dim = n + 1 + 1 := by rw [D.dim_invertor, eq.dim_e]
  have t := D.hasBdry_invertor eq.dim_e α
  exact ⟨InvertorData.ofSides eq (D.inverse α) (D.hasType_inverse eq.dim_e α) (β := α)
    (D.invertor α) (Dz.inverse false) (.base hz) (.base (isDegenerate_reverse _ hz)) t
    (t.inverse (Dz.hasType_inverse hdz false))⟩

include he in
theorem nonempty_unbiasedSolution_of_isDegenerate {α : Bool} {n : ℕ} {u : RoundPastingDiagram X}
    (eq : Equation α n e u) :
    Nonempty (UnbiasedSolution (TClosure {a : RoundPastingDiagram X | a.IsDegenerate}) eq) :=
  (nonempty_invertorData_of_isDegenerate he eq).elim fun D =>
    D.nonempty_unbiasedSolution fun _ hd => hd

end Degenerate

end Atoms.Diagrammatic
