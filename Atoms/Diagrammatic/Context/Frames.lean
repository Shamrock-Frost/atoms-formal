import Atoms.Diagrammatic.Context.Syntax
import Atoms.Diagrammatic.Equivalence.Basic

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

structure HasRoundType (a : PastingDiagram X) (v w : RoundPastingDiagram X) : Prop where
  dim_eq : a.dim = v.dim + 1
  dim_eq_dim : v.dim = w.dim
  source : (a.boundary v.dim false).Equiv v.toPastingDiagram
  target : (a.boundary v.dim true).Equiv w.toPastingDiagram

theorem HasRoundType.equiv_boundary_cond {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    (h : HasRoundType a v w) {k : ℕ} (hk : v.dim = k) (α : Bool) :
    (a.boundary k α).Equiv (cond α w v).toPastingDiagram := by
  subst hk
  cases α
  exacts [h.source, h.target]

theorem HasRoundType.parallel {c d : RoundPastingDiagram X} {v w : RoundPastingDiagram X}
    (hc : HasRoundType c.toPastingDiagram v w) (hd : HasRoundType d.toPastingDiagram v w) :
    Parallel c d := by
  have hc' : c.dim - 1 = v.dim := by rw [hc.dim_eq]; rfl
  have hd' : d.dim - 1 = v.dim := by rw [hd.dim_eq]; rfl
  refine ⟨hc.dim_eq.trans hd.dim_eq.symm, Or.inr fun α => ?_⟩
  rw [hc', hd']
  exact (hc.equiv_boundary_cond rfl α).trans (hd.equiv_boundary_cond rfl α).symm

theorem HasRoundType.of_equiv_boundary {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    {k : ℕ} (hv : v.dim = k) (hw : w.dim = k) (ha : a.dim = k + 1)
    (h : ∀ β, (a.boundary k β).Equiv (cond β w v).toPastingDiagram) : HasRoundType a v w := by
  subst hv
  exact ⟨ha, hw.symm, h false, h true⟩

theorem hasRoundType_unit (u : RoundPastingDiagram X) : HasRoundType u.unit u u :=
  .of_equiv_boundary rfl rfl (dim_unit _) fun β => by
    cases β <;> exact boundary_unit rfl _

theorem HasRoundType.pastable {a b : PastingDiagram X} {v w w' z : RoundPastingDiagram X}
    (ha : HasRoundType a v w) (hb : HasRoundType b w' z) (hw : w.Equiv w'.toPastingDiagram)
    {k : ℕ} (hk : v.dim = k) : a.Pastable b k := by
  subst hk
  have hd : w'.dim = v.dim := (dim_eq_of_equiv hw).symm.trans ha.dim_eq_dim.symm
  refine ⟨ha.target.trans (hw.trans ?_), ?_⟩
  · rw [← hd]
    exact hb.source.symm
  · rw [ha.dim_eq, hb.dim_eq, hd, min_self]
    exact Nat.lt_succ_self _

theorem HasRoundType.paste {a b : PastingDiagram X} {v w w' z : RoundPastingDiagram X}
    (ha : HasRoundType a v w) (hb : HasRoundType b w' z) (hw : w.Equiv w'.toPastingDiagram)
    {k : ℕ} (hk : v.dim = k) (h : a.Pastable b k) : HasRoundType (a.paste b k h) v z := by
  subst hk
  have hd : w'.dim = v.dim := (dim_eq_of_equiv hw).symm.trans ha.dim_eq_dim.symm
  refine .of_equiv_boundary rfl (hb.dim_eq_dim.symm.trans hd) ?_ fun β => ?_
  · rw [dim_paste, ha.dim_eq, hb.dim_eq, hd, max_self]
  · refine (equiv_boundary_paste h β).trans ?_
    cases β
    · exact ha.source
    · rw [← hd]
      exact hb.target

theorem HasRoundType.reverse {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    (h : HasRoundType a v w) (hd : a.IsDegenerate) : HasRoundType (a.reverse hd) w v := by
  have hk : a.dim - 1 = v.dim := by rw [h.dim_eq]; rfl
  refine .of_equiv_boundary h.dim_eq_dim.symm rfl ?_ fun β => ?_
  · rw [dim_reverse, h.dim_eq, h.dim_eq_dim]
  · have e := boundary_reverse a hd β
    rw [hk] at e
    refine e.trans ?_
    cases β
    · exact h.target
    · exact h.source

theorem HasRoundType.of_equiv {a : PastingDiagram X} {v w v' w' : RoundPastingDiagram X}
    (h : HasRoundType a v w) (hv : v.toPastingDiagram.Equiv v'.toPastingDiagram)
    (hw : w.toPastingDiagram.Equiv w'.toPastingDiagram) : HasRoundType a v' w' where
  dim_eq := h.dim_eq.trans (congrArg (· + 1) (dim_eq_of_equiv hv))
  dim_eq_dim := (dim_eq_of_equiv hv).symm.trans (h.dim_eq_dim.trans (dim_eq_of_equiv hw))
  source := by
    rw [← dim_eq_of_equiv hv]
    exact h.source.trans hv
  target := by
    rw [← dim_eq_of_equiv hv]
    exact h.target.trans hw

theorem HasRoundType.mapTo {a : PastingDiagram X} {v w : RoundPastingDiagram X}
    (h : HasRoundType a v w) (f : X ⟶ Y) : HasRoundType (a.mapTo f) (v.mapTo f) (w.mapTo f) where
  dim_eq := h.dim_eq
  dim_eq_dim := h.dim_eq_dim
  source := h.source.mapTo_boundary f
  target := h.target.mapTo_boundary f

theorem cellRound_app {X Y : DiagSet.{u}} (f : X ⟶ Y) {U : Atom} (x : diagram X U) :
    cellRound (f.app (op U) x) = (cellRound x).mapTo f :=
  RoundPastingDiagram.ext (PastingDiagram.ofCell_app f x)

private theorem boundary_ofCell_eq_of_sphereInclusion_comp_eq {U : Atom}
    {x y : ball.{u} U ⟶ X} (h : sphereInclusion U ≫ x = sphereInclusion U ≫ y) {k : ℕ}
    (hk : k < U.dimension) (α : Bool) :
    (PastingDiagram.ofCell (uliftYonedaEquiv x)).boundary k α =
      (PastingDiagram.ofCell (uliftYonedaEquiv y)).boundary k α := by
  refine congrArg (PastingDiagram.mk _) ?_
  rw [PastingDiagram.ofCell_map, PastingDiagram.ofCell_map, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]
  ext ⟨T⟩ ⟨c⟩
  have hc : ((realize.map (U.toMoleculeShape.boundaryInclRDC k α) ≫ (realizeAtomIso U).hom).app
      (op T) ⟨c⟩) ∈ (Homotopical.EZCategory.uliftBoundary.{u} U).obj (op T) := by
    rw [← closedSubpresheaf_univ_erase_top]
    intro t
    rw [U.mem_bdryFull_top_iff]
    intro ht
    have h1 := congrArg (grade ℕ) ht
    have h2 : grade ℕ (U.toMoleculeShape.boundaryIncl k α (ConcreteCategory.hom c.hom t)) ≤ k :=
      grade_le_of_mem_boundary (by
        rw [← U.toMoleculeShape.map_boundaryIncl_top]
        exact ⟨ConcreteCategory.hom c.hom t, LowerSet.mem_top, rfl⟩)
    rw [U.dimension_eq] at hk
    exact absurd (h1 ▸ h2) (not_le.2 hk)
  exact congrArg (fun φ : sphere.{u} U ⟶ X => φ.app (op T) ⟨_, hc⟩) h

theorem parallel_cellRound_of_sphereInclusion_comp_eq {U : Atom}
    {x y : ball.{u} U ⟶ X} (h : sphereInclusion U ≫ x = sphereInclusion U ≫ y) :
    Parallel (cellRound (uliftYonedaEquiv x)) (cellRound (uliftYonedaEquiv y)) := by
  refine ⟨rfl, (Nat.eq_zero_or_pos U.dimension).imp id fun hpos α => ?_⟩
  exact (congrArg (PastingDiagram.Equiv _) (boundary_ofCell_eq_of_sphereInclusion_comp_eq h
    (Nat.sub_lt hpos Nat.one_pos) α)).mp (PastingDiagram.Equiv.refl _)

abbrev ContextFrames (X : DiagSet.{u}) := List (PastingDiagram X × PastingDiagram X)

def EvalFrames : ContextFrames X → ℕ → PastingDiagram X → PastingDiagram X → Prop
  | [], _, a, b => a.Equiv b
  | (l, r) :: fs, k, a, b => ∃ c d, Pastes l a k c ∧ Pastes c r k d ∧ EvalFrames fs (k + 1) d b

def BoundedFrames (fs : ContextFrames X) : Prop :=
  ∀ (i : Fin fs.length), (fs.get i).1.dim ≤ i.val + 1 ∧ (fs.get i).2.dim ≤ i.val + 1

def FrameEquivalences (fs : ContextFrames X) : Prop :=
  ∀ (i : Fin fs.length) (p : PastingDiagram X), (p = (fs.get i).1 ∨ p = (fs.get i).2) →
    ∀ (U : Atom) (x : diagram X U), U.dimension = i.val + 1 →
      (∃ (v : PastingDiagram X) (ι : PastingDiagram.Within v p),
        p.shape.ogp.IsSubmoleculeOf ι.image ⊤ ∧ v.Equiv (PastingDiagram.ofCell x)) →
      IsEquivalence X x

def RoundContextEquation (fs : ContextFrames X) (v w b : RoundPastingDiagram X) : Prop :=
  Parallel v w ∧ fs.length = v.dim + 1 ∧ BoundedFrames fs ∧
    ∃ (Y : DiagSet.{u}) (f : X ⟶ Y), Mono f ∧
      ∃ (U : Atom) (a : diagram Y U) (c : RoundPastingDiagram Y),
        HasRoundType (PastingDiagram.ofCell a) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
          ⟨w.toPastingDiagram.mapTo f, w.isRound⟩ ∧
        EvalFrames (fs.map (fun p => (p.1.mapTo f, p.2.mapTo f))) 0
          (PastingDiagram.ofCell a) c.toPastingDiagram ∧
        Parallel c ⟨b.toPastingDiagram.mapTo f, b.isRound⟩

namespace EvalFrames

theorem of_equiv : ∀ {fs : ContextFrames X} {k : ℕ} {a a' b b' : PastingDiagram X},
    EvalFrames fs k a b → a.Equiv a' → b.Equiv b' → EvalFrames fs k a' b'
  | [], _, _, _, _, _, h, ea, eb =>
    ea.symm.trans (h.trans eb)
  | (_, _) :: _, _, _, _, _, _, ⟨c, d, h₁, h₂, h₃⟩, ea, eb =>
    ⟨c, d, h₁.of_equiv (.refl _) ea (.refl _), h₂, of_equiv h₃ (.refl _) eb⟩

theorem append_singleton : ∀ (fs : ContextFrames X) (x : PastingDiagram X × PastingDiagram X)
    {k : ℕ} {a b : PastingDiagram X}, EvalFrames (fs ++ [x]) k a b ↔
      ∃ d, EvalFrames fs k a d ∧ EvalFrames [x] (k + fs.length) d b
  | [], x, k, a, b => by
    refine ⟨fun h => ⟨a, .refl _, h⟩, fun ⟨d, e, h⟩ => ?_⟩
    exact of_equiv h (e.symm) (.refl _)
  | (l, r) :: fs, x, k, a, b => by
    change (∃ c d, Pastes l a k c ∧ Pastes c r k d ∧ EvalFrames (fs ++ [x]) (k + 1) d b) ↔
      ∃ d', (∃ c d, Pastes l a k c ∧ Pastes c r k d ∧ EvalFrames fs (k + 1) d d') ∧
        EvalFrames [x] (k + (fs.length + 1)) d' b
    rw [(by omega : k + (fs.length + 1) = k + 1 + fs.length)]
    constructor
    · rintro ⟨c, d, h₁, h₂, h₃⟩
      obtain ⟨d', h₄, h₅⟩ := (append_singleton fs x).1 h₃
      exact ⟨d', ⟨c, d, h₁, h₂, h₄⟩, h₅⟩
    · rintro ⟨d', ⟨c, d, h₁, h₂, h₄⟩, h₅⟩
      exact ⟨c, d, h₁, h₂, (append_singleton fs x).2 ⟨d', h₄, h₅⟩⟩

theorem unique : ∀ {fs : ContextFrames X} {k : ℕ} {a a' b b' : PastingDiagram X},
    EvalFrames fs k a b → EvalFrames fs k a' b' → a.Equiv a' → b.Equiv b'
  | [], _, _, _, _, _, h, h', e =>
    h.symm.trans (e.trans h')
  | (_, _) :: _, _, _, _, _, _, ⟨_, _, h₁, h₂, h₃⟩, ⟨_, _, h₁', h₂', h₃'⟩, e =>
    unique h₃ h₃' (h₂.unique (h₂'.of_equiv (PastingDiagram.Equiv.symm
      (h₁.unique (h₁'.of_equiv (.refl _) e.symm (.refl _)))) (.refl _) (.refl _)))

theorem mapTo {Y : DiagSet.{u}} (f : X ⟶ Y) :
    ∀ (fs : ContextFrames X) (k : ℕ) (a b : PastingDiagram X), EvalFrames fs k a b →
      EvalFrames (fs.map (fun p => (p.1.mapTo f, p.2.mapTo f))) k (a.mapTo f) (b.mapTo f)
  | [], _, a, b, h => PastingDiagram.Equiv.mapTo (u := a) (v := b) h f
  | (_, _) :: fs, k, _, _, ⟨c, d, h₁, h₂, h₃⟩ =>
    ⟨c.mapTo f, d.mapTo f, h₁.mapTo f, h₂.mapTo f, mapTo f fs (k + 1) d _ h₃⟩

end EvalFrames

end Atoms.Diagrammatic
