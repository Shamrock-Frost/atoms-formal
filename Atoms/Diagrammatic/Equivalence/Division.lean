import Atoms.Diagrammatic.Equivalence.DivisionPair

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace Reassociate

variable {α : Bool} {n : ℕ} {v e u : RoundPastingDiagram X} (d : PasteAtData (!α) n v e)
  {B : Set (RoundPastingDiagram X)} {eq' : Equation α n d.round u} (s' : UnbiasedSolution B eq')

noncomputable abbrev pastingEquation : Equation (!α) n d.round d.round :=
  Equation.trivial d.round d.dim_pasting (!α)

theorem occEquiv : (d.round.boundary n (!α)).Equiv (d.pasting.boundary n (!α)) :=
  .refl _

noncomputable abbrev occVDiagram : PastingDiagram X :=
  (pastingEquation d).sub.restrictTo
    (ComposePair.isSubmoleculeOf_comap (pastingEquation d) d (occEquiv d)).isMoleculeIn

noncomputable def occV : Within (occVDiagram d) (d.round.boundary n (!α)) :=
  ComposePair.κOf (pastingEquation d) d (occEquiv d)

noncomputable def occSol : Within (occVDiagram d) (s'.sol.boundary n α) :=
  ((occV d).trans (Within.ofEquiv s'.data.equiv)).trans s'.data.occ

theorem equiv_occSol : (occVDiagram d).Equiv (v.boundary n (!α)) :=
  ComposePair.equiv_κOf (pastingEquation d) d (occEquiv d)

theorem isRewritableSubmolecule_image_occSol :
    (s'.sol.boundary n α).shape.ogp.IsRewritableSubmolecule (occSol d s').image ⊤ :=
  Within.isRewritableSubmolecule_image_trans
    (((occV d).isRewritableSubmolecule_image_trans_ofEquiv_iff s'.data.equiv).2
      (ComposePair.isRewritableSubmolecule_image_κOf (pastingEquation d) d (occEquiv d)))
    s'.data.rewritable

noncomputable def pastingV : PasteAtData α n v s'.sol :=
  ⟨d.dim_e, s'.data.dim_u', occVDiagram d, occSol d s', isRewritableSubmolecule_image_occSol d s',
    (equiv_occSol d).symm⟩

variable (β : Bool)

noncomputable abbrev geom : Geometry s'.data u (s'.side β).witness β := (s'.side β).geometry

noncomputable def wPasting : Within d.pasting (s'.side β).witness.toPastingDiagram :=
  (geom d s' β).withinE

noncomputable def wV : Within v.toPastingDiagram (s'.side β).witness.toPastingDiagram :=
  d.pasteAtInl.trans (wPasting d s' β)

noncomputable def wE : Within e.toPastingDiagram (s'.side β).witness.toPastingDiagram :=
  d.pasteAtInr.trans (wPasting d s' β)

theorem image_wV : (wV d s' β).image = OGP.map (wPasting d s' β).emb d.pasteAtInl.image :=
  Within.image_trans _ _

theorem krullDim_wV : krullDim (wV d s' β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast d.dim_e

theorem krullDim_wE : krullDim (wE d s' β).image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast d.dim_u'

theorem krullDim_withinSol : krullDim (geom d s' β).withinSol.image = n + 1 := by
  rw [Within.krullDim_image]; exact_mod_cast s'.data.dim_u'

theorem image_withinE :
    (geom d s' β).withinE.image = (wV d s' β).image ⊔ (wE d s' β).image :=
  (d.isPastingAtIn_trans (geom d s' β).withinE).eq_sup

theorem isPastingAtIn_wV_wE :
    IsPastingAtIn (s'.side β).witness.shape.ogp n (!α) (wV d s' β).image (wE d s' β).image
      ((wV d s' β).image ⊔ (wE d s' β).image) := by
  rw [← image_withinE d s' β]
  exact d.isPastingAtIn_trans (geom d s' β).withinE

theorem assoc :
    IsPastingAtIn (s'.side β).witness.shape.ogp n α (wV d s' β).image (geom d s' β).withinSol.image
        ((wV d s' β).image ⊔ (geom d s' β).withinSol.image) ∧
      IsPastingAtIn (s'.side β).witness.shape.ogp n α (wE d s' β).image
        ((wV d s' β).image ⊔ (geom d s' β).withinSol.image)
        ((s'.side β).witness.shape.ogp.boundary ⊤ (n + 1) β) := by
  have h₂ := (geom d s' β).isPastingAtIn
  rw [image_withinE d s' β] at h₂
  exact (isPastingAtIn_wV_wE d s' β).assoc_mixed_right h₂
    ((wV d s' β).round_image_iff.2 v.isRound) (krullDim_wV d s' β)
    (by rw [krullDim_wE]; exact_mod_cast n.le_succ)
    (by rw [krullDim_withinSol]; exact_mod_cast n.le_succ)

theorem image_dataOcc_withinSol :
    (s'.data.occ.trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol)).image =
      (s'.side β).witness.shape.ogp.boundary (geom d s' β).withinE.image n (!α) := by
  have e' : (s'.data.occ.trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol)).image =
      OGP.map (geom d s' β).wP.emb (s'.data.occ.trans
        ((Within.boundary s'.sol.toPastingDiagram n α).trans
          (Within.pasteAtInr d.round.toPastingDiagram s'.sol.toPastingDiagram n α s'.data.occ
            s'.data.rewritable.isSubmoleculeOf s'.data.equiv))).image := by
    rw [← Within.image_trans]
    rfl
  have h1 : (geom d s' β).withinE.image =
      OGP.map (geom d s' β).wP.emb
        (Within.pasteAtInl d.round.toPastingDiagram s'.sol.toPastingDiagram n α s'.data.occ
          s'.data.rewritable.isSubmoleculeOf s'.data.equiv).image := Within.image_trans _ _
  have h2 : (geom d s' β).withinSol.image =
      OGP.map (geom d s' β).wP.emb
        (Within.pasteAtInr d.round.toPastingDiagram s'.sol.toPastingDiagram n α s'.data.occ
          s'.data.rewritable.isSubmoleculeOf s'.data.equiv).image := Within.image_trans _ _
  rw [e', image_occurrence_pasteAt, OGP.map_inf, ← (geom d s' β).isPastingAtIn.inf_eq]
  exact congrArg₂ (· ⊓ ·) h1.symm h2.symm

theorem image_occSol_withinSol :
    ((occSol d s').trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol)).image =
      (s'.side β).witness.shape.ogp.boundary (wV d s' β).image n (!α) := by
  let L₁ : Within (d.round.boundary n (!α)) (s'.side β).witness.toPastingDiagram :=
    (Within.ofEquiv s'.data.equiv).trans (s'.data.occ.trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol))
  let L₂ : Within (d.round.boundary n (!α)) (s'.side β).witness.toPastingDiagram :=
    (ComposePair.withinOcc (pastingEquation d) d (occEquiv d)).trans (wPasting d s' β)
  have hL₁ : L₁.image =
      (s'.side β).witness.shape.ogp.boundary (geom d s' β).withinE.image n (!α) := by
    change ((Within.ofEquiv s'.data.equiv).trans (s'.data.occ.trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol))).image = _
    rw [Within.image_trans, Within.image_ofEquiv]
    exact image_dataOcc_withinSol d s' β
  have hL₂ : L₂.image =
      (s'.side β).witness.shape.ogp.boundary (geom d s' β).withinE.image n (!α) := by
    change ((ComposePair.withinOcc (pastingEquation d) d (occEquiv d)).trans
      (wPasting d s' β)).image = _
    rw [Within.image_trans, ComposePair.image_withinOcc, map_boundary]
    rfl
  have hL : L₁ = L₂ := Within.ext_of_image_eq _ _ (hL₁.trans hL₂.symm)
  have h1 : ((occSol d s').trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol)).image =
      ((occV d).trans L₂).image := by
    exact congrArg (fun L => ((occV d).trans L).image) hL
  rw [h1]
  change ((ComposePair.κOf (pastingEquation d) d (occEquiv d)).trans
      ((ComposePair.withinOcc (pastingEquation d) d (occEquiv d)).trans
        (wPasting d s' β))).image = _
  rw [Within.image_trans_assoc, ComposePair.image_κOf_trans, map_boundary, ← image_wV]

theorem image_occSol_eq_inter :
    ((occSol d s').trans
      ((Within.boundary s'.sol.toPastingDiagram n α).trans (geom d s' β).withinSol)).image =
      (wV d s' β).image ⊓ (geom d s' β).withinSol.image := by
  rw [image_occSol_withinSol, (assoc d s' β).1.inf_eq]

noncomputable def wSol :
    Within (pastingV d s').round.toPastingDiagram (s'.side β).witness.toPastingDiagram :=
  Within.pasteAtOfWithin (wV d s' β) (geom d s' β).withinSol (assoc d s' β).1 (occSol d s')
    (isRewritableSubmolecule_image_occSol d s').isSubmoleculeOf (image_occSol_eq_inter d s' β)
    (pastingV d s').equiv

theorem image_wSol : (wSol d s' β).image = (wV d s' β).image ⊔ (geom d s' β).withinSol.image :=
  Within.image_pasteAtOfWithin (wV d s' β) (geom d s' β).withinSol (assoc d s' β).1 (occSol d s')
    (isRewritableSubmolecule_image_occSol d s').isSubmoleculeOf (image_occSol_eq_inter d s' β)
    (pastingV d s').equiv

theorem boundary_withinE_eq :
    (s'.side β).witness.shape.ogp.boundary (geom d s' β).withinE.image n α =
      (s'.side β).witness.shape.ogp.boundary (wE d s' β).image n α := by
  have h := (isPastingAtIn_wV_wE d s' β).boundary_not
  rw [Bool.not_not] at h
  rw [image_withinE]
  exact h

noncomputable def ambient (eq : Equation α n e u) (hocc : eq.occ.image = eq'.occ.image) :
    SolutionAmbient eq (pastingV d s').round β where
  K := (s'.side β).witness
  dimK := (geom d s' β).dim_w
  dim_sol := (pastingV d s').dim_pasting
  wE := wE d s' β
  wSol := wSol d s' β
  wU := (geom d s' β).wU
  image_wU := (geom d s' β).image_wU
  config := by
    rw [image_wSol]
    exact (assoc d s' β).2
  occ_eq := by
    rw [Within.image_trans, hocc, ← Within.image_trans, (geom d s' β).compat_image s'.compat,
      boundary_withinE_eq]

end Reassociate

noncomputable def Reassociate.unbiasedSolution {A : Set (RoundPastingDiagram X)} {α : Bool} {n : ℕ}
    {v e u : RoundPastingDiagram X} (d : PasteAtData (!α) n v e) {eq' : Equation α n d.round u}
    (s' : UnbiasedSolution (TClosure A) eq') (eq : Equation α n e u)
    (hocc : eq.occ.image = eq'.occ.image) : UnbiasedSolution (TClosure A) eq :=
  UnbiasedSolution.ofAmbients (Reassociate.ambient d s' false eq hocc)
    (Reassociate.ambient d s' true eq hocc) (s'.side false).mem (s'.side true).mem

end Atoms.Diagrammatic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Order Atoms.Shape Atoms.Diagrammatic.PastingDiagram

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

theorem exists_pair_inversePasting {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {v e w : RoundPastingDiagram X} (d : PasteAtData α n v e)
    (s : UnbiasedSolution (TClosure A)
      (inverseEquation v d.dim_e (!α)))
    (hwd : w.dim = n + 1) (hw : (w.boundary n α).Equiv (d.pasting.boundary n α))
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram w.toPastingDiagram d.pasting) :
    ∀ β, ∃ K : RoundPastingDiagram X, TClosure A K ∧
      HasBdry β (n + 1) K.toPastingDiagram e.toPastingDiagram
        (DivisionPair.inversePasting d s hwd hw).pasting := by
  have hd : 0 < e.dim := by rw [d.dim_u']; omega
  obtain rfl : n = e.dim - 1 := by have := d.dim_u'; omega
  let U₀ : UnitAmbient d :=
    ⟨!α, unitorRound e hd α d.occ d.rewritable, hasBdry_unitorRound e hd α d.occ d.rewritable⟩
  let U₁ : UnitAmbient d :=
    ⟨α, unitorReverseRound e hd α d.occ d.rewritable,
      hasBdry_unitorReverseRound e hd α d.occ d.rewritable⟩
  have hU₀ : TClosure A U₀.K := .base (hDgn _ (isDegenerate_unitorRound e hd α d.occ d.rewritable))
  have hU₁ : TClosure A U₁.K :=
    .base (hDgn _ (isDegenerate_unitorReverseRound e hd α d.occ d.rewritable))
  intro β
  obtain ⟨k, hk, hkb⟩ := pair (!β)
  cases β <;> cases α
  · exact DivisionPair.exists_hasBdry_inversePasting d s hwd hw U₀ ⟨k, hkb⟩ hDgn hU₀ hk
  · exact DivisionPair.exists_hasBdry_inversePasting d s hwd hw U₁ ⟨k, hkb⟩ hDgn hU₁ hk
  · exact DivisionPair.exists_hasBdry_inversePasting d s hwd hw U₁ ⟨k, hkb⟩ hDgn hU₁ hk
  · exact DivisionPair.exists_hasBdry_inversePasting d s hwd hw U₀ ⟨k, hkb⟩ hDgn hU₀ hk

theorem nonempty_unbiasedSolution_div_same {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {v e w u : RoundPastingDiagram X} (d : PasteAtData α n v e) (eq : Equation α n e u)
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram w.toPastingDiagram d.pasting)
    (hv : UnbiasedSide (TClosure A) (!α) v)
    (hw : UnbiasedSide (TClosure A) α w) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨s⟩ := hv n _ (inverseEquation v d.dim_e (!α))
  obtain ⟨k₀, -, hkb₀⟩ := pair false
  have hwd : w.dim = n + 1 := hkb₀.dim_a
  have hwb : (w.boundary n α).Equiv (d.pasting.boundary n α) :=
    hkb₀.equiv_boundary (Nat.lt_succ_self n) α
  have pairP := exists_pair_inversePasting hDgn d s hwd hwb pair
  exact nonempty_unbiasedSolution_compose hDgn eq (DivisionPair.inversePasting d s hwd hwb) pairP
    (InverseSolution.unbiasedSide_sol hDgn d.dim_e α s) hw

theorem nonempty_unbiasedSolution_div_mixed {A : Set (RoundPastingDiagram X)}
    (hDgn : ∀ d : RoundPastingDiagram X, d.IsDegenerate → d ∈ A) {α : Bool} {n : ℕ}
    {v e w u : RoundPastingDiagram X} (d : PasteAtData (!α) n v e) (eq : Equation α n e u)
    (pair : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram w.toPastingDiagram d.pasting)
    (hw : UnbiasedSide (TClosure A) α w) :
    Nonempty (UnbiasedSolution (TClosure A) eq) := by
  obtain ⟨k₀, -, hkb₀⟩ := pair false
  have hb : (d.pasting.boundary n α).Equiv (e.boundary n α) := by
    simpa only [Bool.not_not] using d.equiv_boundary_not
  let eq' : Equation α n d.round u := eq.ofEquiv d.dim_pasting hb.symm
  have hwb : (w.boundary n α).Equiv (d.pasting.boundary n α) :=
    hkb₀.equiv_boundary (Nat.lt_succ_self n) α
  let eqw : Equation α n w u := eq'.ofEquiv hkb₀.dim_a hwb.symm
  obtain ⟨sw⟩ := hw n u eqw
  have pair' : ∀ β, ∃ kβ : RoundPastingDiagram X, TClosure A kβ ∧
      HasBdry β (n + 1) kβ.toPastingDiagram d.round.toPastingDiagram w.toPastingDiagram := by
    intro β
    obtain ⟨k, hk, hkb⟩ := pair (!β)
    refine ⟨k, hk, ?_⟩
    have h := hkb.symm
    rw [Bool.not_not] at h
    exact h
  obtain ⟨s'⟩ := nonempty_unbiasedSolution_of_pair hDgn eq' hkb₀.dim_a hwb.symm pair' sw
  exact ⟨Reassociate.unbiasedSolution d s' eq rfl⟩

end Atoms.Diagrammatic
