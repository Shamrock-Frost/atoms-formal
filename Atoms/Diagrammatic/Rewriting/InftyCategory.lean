import Atoms.Diagrammatic.Rewriting.RoundReading

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

theorem Link.source_eq {d d' : Diagram S.Pt S.Ed S.Ce} : S.Link d d' → d'.source = d.source
  | .relation _ _ _ hd => (isSome_target_and_source_of_relationApply hd).2.2
  | .relationBackward _ _ _ _ hd => (isSome_target_and_source_of_relationApply hd).2.2.symm
  | .identification _ hd => (isSome_target_and_source_of_swap hd).2
  | .unit _ true _ hd => S.source_unitApply hd
  | .unit _ false _ hd => (S.source_unitApply hd).symm

theorem Link.isSome_target_of_isSome (hS : S.toSignature.WellFormed)
    {d d' : Diagram S.Pt S.Ed S.Ce} :
    S.Link d d' → (S.target d).isSome → (S.target d').isSome
  | .relation _ _ _ hd, _ => (isSome_target_and_source_of_relationApply hd).2.1
  | .relationBackward _ _ _ _ hd, _ => (isSome_target_and_source_of_relationApply hd).1
  | .identification _ hd, _ => (isSome_target_and_source_of_swap hd).1
  | .unit _ true _ hd, ht => (S.target_unitApply hS hd).symm ▸ ht
  | .unit _ false _ hd, ht => (S.target_unitApply hS hd) ▸ ht

variable {hS : S.WellFormed} {X : DiagSet.{u}} (I : S.Interp hS X)

theorem Link.equivalent_roundDiagram (hρ : ∀ r, IsEquivalence X (I.rel r).2)
    {d d' : Diagram S.Pt S.Ed S.Ce} (l : S.Link d d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) :
    Equivalent (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') :=
  match l with
  | .relation r _ _ hd => I.equivalent_roundDiagram_relation (hρ r) hd hq hsrc hq' hsrc'
  | .relationBackward r _ _ _ hd =>
    I.equivalent_roundDiagram_relationBackward (hρ r) hd hq hsrc hq' hsrc'
  | .identification _ hd => I.toInterp.equivalent_roundDiagram_swap hS.1 hd hq hsrc hq' hsrc'
  | .unit m true _ hd => I.toInterp.equivalent_roundDiagram_unitApply hS.1 m hd hq hsrc hq' hsrc'
  | .unit m false _ hd => equivalent_symm
    (I.toInterp.equivalent_roundDiagram_unitApply hS.1 m hd hq' hsrc' hq hsrc)

theorem RewriteChain.equivalent_roundDiagram (hρ : ∀ r, IsEquivalence X (I.rel r).2) :
    ∀ {d d' : Diagram S.Pt S.Ed S.Ce} (_ : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)}
      (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
      (hsrc' : d'.source ≠ []),
      Equivalent (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc')
  | _, _, .refl _, _, _, hq, _, hq', _ => by
    obtain rfl := Option.some.inj (hq.symm.trans hq')
    exact equivalent_refl _
  | _, _, .cons l p, _, _, hq, hsrc, hq', hsrc' => by
    obtain ⟨q₁, hq₁⟩ :=
      Option.isSome_iff_exists.1 (l.isSome_target_of_isSome hS.1 (by rw [hq]; rfl))
    have hsrc₁ := l.source_eq ▸ hsrc
    exact equivalent_trans (l.equivalent_roundDiagram I hρ hq hsrc hq₁ hsrc₁)
      (p.equivalent_roundDiagram hρ hq₁ hsrc₁ hq' hsrc')

theorem RewriteChain.equivalent_diagram (hX : IsInftyCategory 2 X)
    {d d' : Diagram S.Pt S.Ed S.Ce} (p : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) (hr : (I.diagram d hsrc).IsRound)
    (hr' : (I.diagram d' hsrc').IsRound) :
    Equivalent ⟨I.diagram d hsrc, hr⟩ ⟨I.diagram d' hsrc', hr'⟩ :=
  equivalent_trans (I.toInterp.equivalent_roundDiagram_of_isRound hS.1 hq hsrc hr)
    (equivalent_trans (p.equivalent_roundDiagram I
      (I.isEquivalence_rel_of_isInftyCategory hX le_rfl) hq hsrc hq' hsrc')
      (equivalent_symm (I.toInterp.equivalent_roundDiagram_of_isRound hS.1 hq' hsrc' hr')))

theorem RewriteChain.exists_equivalence_weakComposite (hX : IsInftyCategory 2 X)
    {d d' : Diagram S.Pt S.Ed S.Ce} (p : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ [])
    (c : diagram X (mergerAtomAll (I.toInterp.roundDiagram hS.1 hq hsrc).roundShape))
    (hc : Equivalent (I.toInterp.roundDiagram hS.1 hq hsrc) (cellRound c))
    (c' : diagram X (mergerAtomAll (I.toInterp.roundDiagram hS.1 hq' hsrc').roundShape))
    (hc' : Equivalent (I.toInterp.roundDiagram hS.1 hq' hsrc') (cellRound c')) :
    ∃ (U : Atom) (z : diagram X U), IsEquivalence X z ∧ U.dimension = 3 ∧
      ((PastingDiagram.ofCell z).boundary 2 false).Equiv (PastingDiagram.ofCell c) ∧
      ((PastingDiagram.ofCell z).boundary 2 true).Equiv (PastingDiagram.ofCell c') := by
  have h := equivalent_trans (equivalent_symm hc) (equivalent_trans (p.equivalent_roundDiagram I
    (I.isEquivalence_rel_of_isInftyCategory hX le_rfl) hq hsrc hq' hsrc') hc')
  have hd : (cellRound c).dim = 2 := (equivalent_symm hc).data.dim_eq.trans
    (I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc)
  obtain ⟨U, z, hz, hdU, hs, ht⟩ := exists_equivalence_cell_side hX.1 false _ _ h
  rw [hd] at hdU hs ht
  exact ⟨U, z, hz, hdU, hs, ht⟩

end RelSignature

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]
  {hS : S.WellFormed} {X : DiagSet.{u}}

noncomputable def Interp.ofEquivalent (hX : HasWeakComposites X) (J : S.toSignature.Interp X)
    (hJ : ∀ r, Equivalent (sideRound J hS r false) (sideRound J hS r true)) : S.Interp hS X where
  toInterp := J
  rel r := ⟨(exists_equivalence_cell_side hX false _ _ (hJ r)).choose,
    (exists_equivalence_cell_side hX false _ _ (hJ r)).choose_spec.choose⟩
  hasRoundType_rel r :=
    have h := (exists_equivalence_cell_side hX false _ _ (hJ r)).choose_spec.choose_spec
    ⟨h.2.1, (hJ r).data.dim_eq, h.2.2.1, h.2.2.2⟩

omit [DecidableEq S.Ce] in
@[simp] theorem Interp.ofEquivalent_toInterp (hX : HasWeakComposites X)
    (J : S.toSignature.Interp X)
    (hJ : ∀ r, Equivalent (sideRound J hS r false) (sideRound J hS r true)) :
    (Interp.ofEquivalent hX J hJ).toInterp = J :=
  rfl

omit [DecidableEq S.Ce] in
theorem Interp.isEquivalence_rel_ofEquivalent (hX : HasWeakComposites X)
    (J : S.toSignature.Interp X)
    (hJ : ∀ r, Equivalent (sideRound J hS r false) (sideRound J hS r true)) (r : S.Rel) :
    IsEquivalence X ((Interp.ofEquivalent hX J hJ).rel r).2 :=
  (exists_equivalence_cell_side hX false _ _ (hJ r)).choose_spec.choose_spec.1

theorem RewriteChain.equivalent_roundDiagram_of_equivalent (hX : HasWeakComposites X)
    (J : S.toSignature.Interp X)
    (hJ : ∀ r, Equivalent (sideRound J hS r false) (sideRound J hS r true))
    {d d' : Diagram S.Pt S.Ed S.Ce} (p : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) :
    Equivalent (J.roundDiagram hS.1 hq hsrc) (J.roundDiagram hS.1 hq' hsrc') :=
  p.equivalent_roundDiagram (Interp.ofEquivalent hX J hJ)
    (Interp.isEquivalence_rel_ofEquivalent hX J hJ) hq hsrc hq' hsrc'

end RelSignature

end Atoms.Diagrammatic.Layered
