import Atoms.Diagrammatic.Rewriting.Chain
import Atoms.Diagrammatic.InftyCategory

open Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered

namespace Signature.Interp

variable {S : Signature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] {X : DiagSet.{u}}
  (I : S.Interp X) (hS : S.WellFormed)

noncomputable def roundDiagram {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hd : S.target d = some q) (hsrc : d.source ≠ []) : RoundPastingDiagram X :=
  ⟨I.diagram d.unitFirst hsrc, I.isRound_diagram_of_first hS
    ((S.target_unitFirst d).trans hd) hsrc rfl rfl⟩

theorem hasRoundType_roundDiagram {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hd : S.target d = some q) (hsrc : d.source ≠ []) :
    HasRoundType (I.roundDiagram hS hd hsrc).toPastingDiagram
      (I.pathRound _ (S.isPath_source_of_target hd)) (I.pathRound q (S.isPath_target hS hd)) :=
  I.hasRoundType_diagram hS ((S.target_unitFirst d).trans hd) hsrc

theorem exists_equiv_roundDiagram {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hd : S.target d = some q) (hsrc : d.source ≠ []) (hl : d.layers ≠ []) :
    ∃ h, (I.roundDiagram hS hd hsrc).Equiv
      ((I.path d.source hsrc).unit.paste (I.diagram d hsrc) 1 h) := by
  have hpath := S.isPath_source_of_target hd
  have hsome : (S.target d).isSome := by rw [hd]; rfl
  obtain ⟨h, e⟩ := I.equiv_diagram_append hS (d := ⟨d.source, [(.unit d.source, 0)]⟩) (d' := d)
    (S.target_singleton (l := (.unit d.source, 0)) hpath (S.applyLayer_unit_self hsrc)) rfl hsrc
    hsrc (List.cons_ne_nil _ _) hl hsome
  have eu := PastingDiagram.equiv_of_eq (I.diagram_unit_singleton hsrc)
  exact ⟨h.of_equiv eu (.refl _), (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans
    (e.trans (Equiv.paste eu (.refl _) h _))⟩

theorem equivalent_roundDiagram_of_isRound {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hd : S.target d = some q) (hsrc : d.source ≠ [])
    (hr : (I.diagram d hsrc).IsRound) :
    Equivalent ⟨I.diagram d hsrc, hr⟩ (I.roundDiagram hS hd hsrc) := by
  obtain ⟨src, ls⟩ := d
  obtain _ | ⟨l, ls⟩ := ls
  · refine equivalent_of_equiv (PastingDiagram.equiv_of_eq ?_)
    obtain _ | ⟨e, p⟩ := src
    · exact absurd rfl hsrc
    · exact (I.diagram_unit_singleton hsrc).symm
  obtain ⟨h, e⟩ := I.exists_equiv_roundDiagram hS hd hsrc (List.cons_ne_nil _ _)
  have ht := I.hasRoundType_diagram hS hd hsrc
  have hd1 := I.dim_path (S.isPath_source_of_target hd)
  have eb : ((I.diagram ⟨src, l :: ls⟩ hsrc).boundary 1 false).Equiv (I.path src hsrc) :=
    ht.equiv_boundary_cond hd1 false
  have hp : (cond false (I.diagram ⟨src, l :: ls⟩ hsrc)
      ((I.diagram ⟨src, l :: ls⟩ hsrc).boundary 1 false).unit).Pastable
      (cond false ((I.diagram ⟨src, l :: ls⟩ hsrc).boundary 1 false).unit
        (I.diagram ⟨src, l :: ls⟩ hsrc)) 1 := h.of_equiv eb.unit.symm (.refl _)
  have e' : ((cond false (I.diagram ⟨src, l :: ls⟩ hsrc)
      ((I.diagram ⟨src, l :: ls⟩ hsrc).boundary 1 false).unit).paste
      (cond false ((I.diagram ⟨src, l :: ls⟩ hsrc).boundary 1 false).unit
        (I.diagram ⟨src, l :: ls⟩ hsrc)) 1 hp).Equiv
      (I.roundDiagram hS hd hsrc).toPastingDiagram :=
    (Equiv.paste eb.unit (.refl _) hp h).trans e.symm
  exact equivalent_trans (equivalent_paste_unit_cond false ⟨_, hr⟩
    (I.dim_diagram hS hd hsrc) hp (e'.isRound_iff.2 (I.roundDiagram hS hd hsrc).isRound))
    (equivalent_of_equiv e')

end Signature.Interp

namespace Signature.PathInterp

variable {S : Signature.{v}} {X : DiagSet.{u}} (I : S.PathInterp X)

noncomputable def whiskerCtx (α : Bool) : List (Edge S.Pt S.Ed) → CtxExpr X
  | [] => .id
  | f :: w => CtxExpr.paste α (I.pathCons f w) 0

noncomputable def besideCtx (L R : List (Edge S.Pt S.Ed)) : CtxExpr X :=
  .comp (I.whiskerCtx false L) (I.whiskerCtx true R)

variable [DecidableEq S.Pt]

theorem whiskerCtx_app (α : Bool) {x : PastingDiagram X} {a b c : S.Pt} (hx : I.Spans x a b)
    {w : List (Edge S.Pt S.Ed)} (hw : S.walk (cond α b c) w = some (cond α c a)) :
    ((I.whiskerCtx α w).app x).Equiv (I.whisker α w x) := by
  obtain _ | ⟨f, w⟩ := w
  · exact .refl _
  rw [I.whisker_cons_of (hx.pastable_whisker α hw)]
  exact CtxExpr.paste_app α _

theorem besideCtx_app {x : PastingDiagram X} {a m n b : S.Pt} (hx : I.Spans x m n)
    {L R : List (Edge S.Pt S.Ed)} (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    ((I.besideCtx L R).app x).Equiv (I.whisker false L (I.whisker true R x)) :=
  (CtxExpr.app_equiv _ (I.whiskerCtx_app true hx (c := b) hR)).trans
    (I.whiskerCtx_app false (hx.whisker true (c := b) hR) (c := a) hL)

theorem exists_typed_whiskerCtx (α : Bool) {p : Prop} {H : PdHom X} (hk : H.k = 0) {b c : S.Pt}
    (hb : (H.side α).Equiv (PastingDiagram.ofCell (I.point b))) {w : List (Edge S.Pt S.Ed)}
    (hw : S.walk (cond α b c) w = some (cond α c b)) :
    ∃ H' : PdHom X, (I.whiskerCtx α w).Typed Set.univ p H H' ∧ H'.k = 0 ∧
      (H'.side α).Equiv (PastingDiagram.ofCell (I.point c)) ∧ H'.side (!α) = H.side (!α) := by
  obtain _ | ⟨f, w⟩ := w
  · have hbc : cond α b c = cond α c b := Option.some.inj hw
    obtain rfl : b = c := by cases α; exacts [hbc.symm, hbc]
    exact ⟨H, .id (.refl H), hk, hb, rfl⟩
  obtain ⟨hf, hw'⟩ := S.walk_cons_eq_some.1 hw
  have hsp := I.spans_pathCons hw'
  have hpath : S.IsPath (f :: w) := S.isPath_of_pathEnds (S.pathEnds_cons_eq_some.2 ⟨rfl, hw'⟩)
  have hd : (I.pathRound (f :: w) hpath).dim = H.k + 1 := by
    rw [hk]; exact I.dim_pathCons hw'
  have hs : (H.side α).Equiv ((I.pathRound (f :: w) hpath).boundary H.k (!α)) := by
    refine hb.trans ?_
    have e := hsp.2 (!α)
    rw [hk]
    rw [hf] at e
    cases α <;> exact e.symm
  have ht := CtxExpr.typed_paste α (u := I.pathRound (f :: w) hpath) (Set.mem_univ _) (p := p)
    hd hs
  rw [hk] at ht
  refine ⟨H.setSide α ((I.pathRound (f :: w) hpath).boundary 0 α), ht, hk, ?_,
    PdHom.side_setSide_not _ _ _⟩
  rw [PdHom.side_setSide_self]
  have e := hsp.2 α
  rw [hf] at e
  cases α <;> exact e

theorem exists_typed_besideCtx {p : Prop} {H : PdHom X} (hk : H.k = 0) {a m n b : S.Pt}
    (hm : H.v.Equiv (PastingDiagram.ofCell (I.point m)))
    (hn : H.w.Equiv (PastingDiagram.ofCell (I.point n)))
    {L R : List (Edge S.Pt S.Ed)} (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    ∃ H' : PdHom X, (I.besideCtx L R).Typed Set.univ p H H' := by
  obtain ⟨H₁, ht₁, hk₁, -, hv₁⟩ := I.exists_typed_whiskerCtx true (p := p) hk hn (c := b) hR
  have hm₁ : (H₁.side false).Equiv (PastingDiagram.ofCell (I.point m)) := by
    rw [Bool.not_true] at hv₁
    rw [hv₁]; exact hm
  obtain ⟨H₂, ht₂, -⟩ := I.exists_typed_whiskerCtx false (p := p) hk₁ hm₁ (c := a) hL
  exact ⟨H₂, .comp ht₁ ht₂⟩

end Signature.PathInterp

namespace Signature.PathInterp

variable {S : Signature.{v}} [DecidableEq S.Pt] {X : DiagSet.{u}} (I : S.PathInterp X)

noncomputable def segmentCtx (c : PastingDiagram X) (L R : List (Edge S.Pt S.Ed)) : CtxExpr X :=
  .comp (CtxExpr.paste false c 1) (I.besideCtx L R)

theorem typed_segmentCtx {c : PastingDiagram X} (hc : c.IsRound) (hdc : c.dim = 2)
    {L s s' R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hs' : S.pathEnds s' = some (m, n))
    (hL : S.walk a L = some m) (hR : S.walk n R = some b)
    (hcb : (c.boundary 1 true).Equiv
      (I.whisker false L (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil)))) :
    ∃ H' : PdHom X, (I.segmentCtx c L R).Typed Set.univ True
      ⟨1, I.path s (S.isPath_of_pathEnds hs).ne_nil, I.path s' (S.isPath_of_pathEnds hs').ne_nil⟩
      H' ∧ IsRoundCtx
      ⟨1, I.path s (S.isPath_of_pathEnds hs).ne_nil, I.path s' (S.isPath_of_pathEnds hs').ne_nil⟩
      (I.segmentCtx c L R) ∧ ∀ x, I.Spans x m n →
        ((I.segmentCtx c L R).app x).Equiv ((CtxExpr.paste false c 1).app
          (I.whisker false L (I.whisker true R x))) := by
  set H : PdHom X :=
    ⟨1, I.path s (S.isPath_of_pathEnds hs).ne_nil, I.path s' (S.isPath_of_pathEnds hs').ne_nil⟩
  have hsp := I.spans_of_hasRoundType (I.hasRoundType_path (S.isPath_of_pathEnds hs).ne_nil hs)
  have hsp' :=
    I.spans_of_hasRoundType (I.hasRoundType_path (S.isPath_of_pathEnds hs').ne_nil hs')
  have hb : ∀ β, (H.v.boundary 0 β).Equiv (H.w.boundary 0 β) := fun β =>
    (hsp.2 β).trans (hsp'.2 β).symm
  obtain ⟨H₀, hW⟩ := I.exists_typed_besideCtx (p := True) (H := H.boundary 0) rfl
    (hsp.2 false) (hsp'.2 true) hL hR
  have hv : InHom (H.boundary 0) H.v :=
    ⟨by rw [PdHom.k_boundary, I.dim_path (S.isPath_of_pathEnds hs)]; exact Nat.one_pos,
      .refl _, hb true⟩
  have hw : InHom (H.boundary 0) H.w :=
    ⟨by rw [PdHom.k_boundary, I.dim_path (S.isPath_of_pathEnds hs')]; exact Nat.one_pos,
      (hb false).symm, .refl _⟩
  have htW : (I.besideCtx L R).Typed Set.univ True H
      ⟨H.k, (I.besideCtx L R).app H.v, (I.besideCtx L R).app H.w⟩ :=
    .promote trivial rfl hv hw hW (.refl _)
  have hside : ((I.besideCtx L R).app H.v).Equiv (c.boundary 1 true) :=
    (I.besideCtx_app hsp hL hR).trans hcb.symm
  have hdc' : (⟨c, hc⟩ : RoundPastingDiagram X).dim = H.k + 1 := hdc
  have htP := CtxExpr.typed_paste false (u := ⟨c, hc⟩) (Set.mem_univ _) (p := True)
    (H := ⟨H.k, (I.besideCtx L R).app H.v, (I.besideCtx L R).app H.w⟩) hdc' hside
  have hr : IsRoundCtx H (.comp (CtxExpr.paste false c H.k) (I.besideCtx L R)) :=
    IsRoundCtx.comp_paste false htW hc hdc' hside
  have hT : (I.segmentCtx c L R).Typed Set.univ True H _ := .comp htW htP
  refine ⟨_, hT, hr, fun x hx => ?_⟩
  exact CtxExpr.app_equiv (CtxExpr.paste false c 1) (I.besideCtx_app hx hL hR)

theorem equivalent_paste_whisker {c : PastingDiagram X} (hc : c.IsRound) (hdc : c.dim = 2)
    {L s s' R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hs' : S.pathEnds s' = some (m, n))
    (hL : S.walk a L = some m) (hR : S.walk n R = some b) {u v : RoundPastingDiagram X}
    (hu : HasRoundType u.toPastingDiagram (I.pathRound s (S.isPath_of_pathEnds hs))
      (I.pathRound s' (S.isPath_of_pathEnds hs')))
    (huv : Equivalent u v)
    (hp : c.Pastable (I.whisker false L (I.whisker true R u.toPastingDiagram)) 1)
    (hp' : c.Pastable (I.whisker false L (I.whisker true R v.toPastingDiagram)) 1) :
    ∃ hr hr', Equivalent
      ⟨c.paste (I.whisker false L (I.whisker true R u.toPastingDiagram)) 1 hp, hr⟩
      ⟨c.paste (I.whisker false L (I.whisker true R v.toPastingDiagram)) 1 hp', hr'⟩ := by
  set H : PdHom X :=
    ⟨1, I.path s (S.isPath_of_pathEnds hs).ne_nil, I.path s' (S.isPath_of_pathEnds hs').ne_nil⟩
  have hd1 : (I.pathRound s (S.isPath_of_pathEnds hs)).dim = 1 :=
    I.dim_path (S.isPath_of_pathEnds hs)
  have hdu : u.dim = 2 := hu.dim_eq.trans (congrArg (· + 1) hd1)
  have hspu := (I.spans_of_hasRoundType
    (I.hasRoundType_path (S.isPath_of_pathEnds hs).ne_nil hs)).of_hasRoundType hu
  have hb₀ := hu.equiv_boundary_cond hd1
  have hcb : (c.boundary 1 true).Equiv
      (I.whisker false L (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil))) := by
    have hsp := I.spans_of_hasRoundType
      (I.hasRoundType_path (S.isPath_of_pathEnds hs).ne_nil hs)
    have hspR := hspu.whisker true (c := b) hR
    have hdR := I.dim_whisker true hspu (by omega) hR
    have hsb : I.Spans (u.boundary 1 false) m n := hsp.of_equiv (hb₀ false).symm
    have e1 := I.whisker_boundary false hspR Nat.one_pos (by omega) hL false
    have e2 := I.whisker_boundary true hspu Nat.one_pos (by omega) hR false
    have e3 := I.whisker_equiv true hsb (hb₀ false) hR
    have e4 := I.whisker_equiv false (((hsb.whisker true (c := b) hR).of_equiv e2.symm))
      (e2.trans e3) (c := a) hL
    exact hp.1.trans (e1.trans e4)
  obtain ⟨H', ht, hr, happ⟩ := I.typed_segmentCtx hc hdc hs hs' hL hR hcb
  obtain ⟨hdv, e, he, hde, hes, het⟩ := huv.data
  have huH : InHom H u.toPastingDiagram := ⟨by change 1 < u.dim; omega, hb₀ false, hb₀ true⟩
  rw [hdu] at hes het hde
  have hin : InHom H e.toPastingDiagram :=
    InHom.of_hasBdry (β := false) ⟨hde, hdu, hdv ▸ hdu, hes, het⟩ huH
  obtain ⟨hpz, hround, hz⟩ := mem_equivalences_app_paste_unit ht hr he hin hde het
  have Lw := ht.ctxLaws
  have hvH : InHom H v.toPastingDiagram :=
    (hin.boundary (Nat.lt_succ_self 1) (by omega) true).of_equiv het
  have hdTu : ((I.segmentCtx c L R).app u.toPastingDiagram).dim = 2 :=
    (Lw.dim_eq _ huH).trans hdu
  have hdTv : ((I.segmentCtx c L R).app v.toPastingDiagram).dim = 2 :=
    (Lw.dim_eq _ hvH).trans (hdv ▸ hdu)
  have hTu := hr.isRound_app ht huH hdu u.isRound
  have hTv := hr.isRound_app ht hvH (hdv ▸ hdu) v.isRound
  have hdTe : ((I.segmentCtx c L R).app e.toPastingDiagram).dim = 3 :=
    (Lw.dim_eq _ hin).trans hde
  have main : Equivalent ⟨_, hTu⟩ ⟨_, hTv⟩ := equivalent_of_mem_equivalences_cond false hz
    hdTu hdTv (by
      change ((I.segmentCtx c L R).app e.toPastingDiagram |>.paste
        ((I.segmentCtx c L R).app v.toPastingDiagram).unit (1 + 1) hpz).dim = 2 + 1
      rw [dim_paste, dim_unit, hdTe, hdTv]; rfl)
    ((equiv_boundary_paste hpz false).trans ((Lw.boundary _ hin (Nat.lt_succ_self 1)
      (by omega) false).trans (CtxExpr.app_equiv _ hes)))
    ((equiv_boundary_paste hpz true).trans (boundary_unit hdTv true))
  have E : ∀ {x : RoundPastingDiagram X} (hx : I.Spans x.toPastingDiagram m n)
      (hpx : c.Pastable (I.whisker false L (I.whisker true R x.toPastingDiagram)) 1),
      ((I.segmentCtx c L R).app x.toPastingDiagram).Equiv
        (c.paste (I.whisker false L (I.whisker true R x.toPastingDiagram)) 1 hpx) :=
    fun hx hpx => (happ _ hx).trans (CtxExpr.paste_app false hpx)
  have hspv : I.Spans v.toPastingDiagram m n :=
    ⟨by rw [← hdv, hdu]; omega, fun β =>
      (huv.equiv_boundary (by omega) β).symm.trans (hspu.2 β)⟩
  exact ⟨(E hspu hp).isRound_iff.1 hTu, (E hspv hp').isRound_iff.1 hTv,
    equivalent_trans (equivalent_of_equiv (E hspu hp).symm)
      (equivalent_trans main (equivalent_of_equiv (E hspv hp')))⟩

theorem pastable_whisker {c : PastingDiagram X} (hdc : c.dim = 2)
    {L s s' R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hs' : S.pathEnds s' = some (m, n))
    (hL : S.walk a L = some m) (hR : S.walk n R = some b) {u : PastingDiagram X}
    (hu : HasRoundType u (I.pathRound s (S.isPath_of_pathEnds hs))
      (I.pathRound s' (S.isPath_of_pathEnds hs')))
    (hcb : (c.boundary 1 true).Equiv (I.path (L ++ s ++ R)
      (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
        (S.isPath_of_pathEnds hs).ne_nil) _))) :
    c.Pastable (I.whisker false L (I.whisker true R u)) 1 := by
  have h₁ := I.hasRoundType_whisker true hs hs' hu (c := b) hR
  have h₂ := I.hasRoundType_whisker false (S.pathEnds_whisker true hs (c := b) hR)
    (S.pathEnds_whisker true hs' (c := b) hR) h₁ (c := a) hL
  have hd1 := I.dim_path (S.isPath_of_pathEnds (S.pathEnds_whisker false
    (S.pathEnds_whisker true hs (c := b) hR) (c := a) hL))
  refine ⟨hcb.trans ((PastingDiagram.equiv_of_eq (I.path_congr (by simp) _ _)).trans
    (h₂.equiv_boundary_cond hd1 false).symm), ?_⟩
  have hdw : (I.whisker false L (I.whisker true R u)).dim = 2 := h₂.dim_eq.trans
    (congrArg (· + 1) hd1)
  rw [hdw, hdc]
  omega

theorem equivalent_paste_whisker_unit {c : PastingDiagram X} (hc : c.IsRound) (hdc : c.dim = 2)
    {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt} (hs : S.pathEnds s = some (m, n))
    (hL : S.walk a L = some m) (hR : S.walk n R = some b)
    (hp : c.Pastable
      (I.whisker false L (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit)) 1) :
    ∃ hr, Equivalent ⟨c.paste
      (I.whisker false L (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit)) 1
        hp, hr⟩ ⟨c, hc⟩ := by
  have hpath := S.isPath_of_pathEnds hs
  have hd1 : (I.path s hpath.ne_nil).dim = 1 := I.dim_path hpath
  have hspy := I.spans_of_hasRoundType (I.hasRoundType_path hpath.ne_nil hs)
  have hspu := hspy.of_hasRoundType (hasRoundType_unit (I.pathRound s hpath))
  obtain ⟨H₀', hP⟩ := I.exists_typed_besideCtx (p := True)
    (H := ⟨0, PastingDiagram.ofCell (I.point m), PastingDiagram.ofCell (I.point n)⟩) rfl
    (.refl _) (.refl _) hL hR
  have hyu : InHom ⟨0, PastingDiagram.ofCell (I.point m), PastingDiagram.ofCell (I.point n)⟩
      (I.path s hpath.ne_nil).unit := ⟨hspu.1, hspu.2 false, hspu.2 true⟩
  obtain ⟨ω, Fr, hω⟩ := hP.exists_argLoc _ hyu
  have Ex := I.besideCtx_app hspu hL hR
  have hdx : ((I.besideCtx L R).app (I.path s hpath.ne_nil).unit).dim = 2 := by
    rw [hP.ctxLaws.dim_eq _ hyu, dim_unit, hd1]
  have hιy : (I.path s hpath.ne_nil).Equiv (argOccurrenceDiagram ω hω) :=
    (boundary_unit hd1 false).symm.trans (equiv_argOccurrence ω hω)
  have hdz : (((I.besideCtx L R).app (I.path s hpath.ne_nil).unit).boundary 1 false).dim = 1 :=
    dim_boundary _ (by omega) false
  have hι : (((I.besideCtx L R).app (I.path s hpath.ne_nil).unit).boundary 1 false).shape.ogp
      |>.IsRewritableSubmolecule (argOccurrence ω hω).image ⊤ :=
    (argOccurrence ω hω).isRewritableSubmolecule_image_iff.2
      ⟨isSubmoleculeOf_image_occurrence _ _ _ _, hιy.isRound_iff.1 (I.isRound_path hpath),
        (dim_eq_of_equiv hιy).symm.trans (hd1.trans hdz.symm)⟩
  have hu : ((argOccurrenceDiagram ω hω).unit.boundary 1 (!true)).Equiv
      (argOccurrenceDiagram ω hω) :=
    boundary_unit ((dim_eq_of_equiv hιy).symm.trans hd1) false
  let d : CylSpec X := ⟨1, true, _, some ⟨_, argOccurrence ω hω, hι⟩⟩
  have hf : d.Fits c := ⟨hc, by change 1 < c.dim; omega,
    hp.1.trans (Ex.boundary 1 false).symm⟩
  obtain ⟨hr', he, hdf⟩ := hf.fam_spec
  have hdc' : c.dim = 1 + 1 := hdc
  have E1 := (hf.atEnd_self (β := true) (Or.inl rfl)).equiv_boundary hdc'
  have E2 := (hf.atEnd_sidePaste_unit (ι := ⟨_, argOccurrence ω hω, hι⟩) rfl hu).equiv_boundary
    hdc'
  have hp₁ : c.Pastable ((I.besideCtx L R).app (I.path s hpath.ne_nil).unit) 1 :=
    hp.of_equiv (.refl _) Ex.symm
  have E3 := equiv_sidePaste_argOccurrence ω hω (Equiv.unit hιy.symm) hu hp₁
  have E4 : (c.paste ((I.besideCtx L R).app (I.path s hpath.ne_nil).unit) 1 hp₁).Equiv
      (c.paste (I.whisker false L (I.whisker true R (I.path s hpath.ne_nil).unit)) 1 hp) :=
    Equiv.paste (.refl _) Ex hp₁ hp
  have E := E2.symm.trans (E3.trans E4)
  have hdb : (((d.fam c).boundary (1 + 1) false)).dim = 2 :=
    dim_boundary _ (by omega) false
  refine ⟨E.isRound_iff.1 (isRound_boundary_of_isRound hr' _ _), ?_⟩
  exact equivalent_of_mem_equivalences_cond false (z := ⟨d.fam c, hr'⟩) he (k := 2)
    ((dim_eq_of_equiv E).symm.trans hdb) hdc (hdf.trans (by rw [hdc])) E E1.symm
end Signature.PathInterp

namespace Signature.Interp

variable {S : Signature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] {X : DiagSet.{u}}
  (I : S.Interp X) (hS : S.WellFormed)

theorem exists_equivalent_roundDiagram_append {src p₂ q : List (Edge S.Pt S.Ed)}
    (hsrc : src ≠ []) {P C : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (htP : S.target ⟨src, P⟩ = some p₂) (htd : S.target ⟨src, P ++ C⟩ = some q)
    (hp₂ : p₂ ≠ []) (hC : S.targetFrom p₂ C = some q) :
    ∃ hp hr, Equivalent (I.roundDiagram hS htd hsrc)
      ⟨(I.roundDiagram hS htP hsrc).toPastingDiagram.paste
        (I.diagram (Diagram.mk p₂ (C ++ [(Cell.unit q, 0)])) hp₂) 1 hp, hr⟩ := by
  have hpath := S.isPath_source_of_target htP
  have hq := S.isPath_target hS htd
  have hpath₂ := S.isPath_target hS htP
  have hqu : S.target ⟨q, [(Cell.unit q, 0)]⟩ = some q :=
    S.target_singleton (l := (.unit q, 0)) hq (S.applyLayer_unit_self hq.ne_nil)
  have hd' : S.target ⟨p₂, C ++ [(Cell.unit q, 0)]⟩ = some q := by
    rw [target, if_pos hpath₂, S.targetFrom_append, hC, Option.bind_some]
    rw [target, if_pos hq] at hqu
    exact hqu
  set x := I.roundDiagram hS htd hsrc
  have hdx : x.dim = 1 + 1 := I.dim_diagram hS ((S.target_unitFirst _).trans htd) hsrc
  have hxb : (x.boundary 1 true).Equiv (I.path q hq.ne_nil) :=
    (I.hasRoundType_roundDiagram hS htd hsrc).equiv_boundary_cond
      (I.dim_path (S.isPath_source_of_target htd)) true
  obtain ⟨h₁, e₁⟩ := I.equiv_diagram_append hS (d := (Diagram.mk src (P ++ C)).unitFirst)
    (d' := ⟨q, [(.unit q, 0)]⟩) ((S.target_unitFirst _).trans htd) rfl hsrc hq.ne_nil
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (by rw [hqu]; rfl)
  have eu := PastingDiagram.equiv_of_eq (I.diagram_unit_singleton hq.ne_nil)
  have hpx : (cond true x.toPastingDiagram (x.toPastingDiagram.boundary 1 true).unit).Pastable
      (cond true (x.toPastingDiagram.boundary 1 true).unit x.toPastingDiagram) 1 :=
    h₁.of_equiv (.refl _) (eu.trans hxb.unit.symm)
  obtain ⟨h₂, e₂⟩ := I.equiv_diagram_append hS (d := (Diagram.mk src P).unitFirst)
    (d' := ⟨p₂, C ++ [(.unit q, 0)]⟩) ((S.target_unitFirst _).trans htP) rfl hsrc hp₂
    (List.cons_ne_nil _ _) (by simp) (by rw [hd']; rfl)
  have hlist : (Diagram.mk src (P ++ C)).unitFirst ++ ⟨q, [(.unit q, 0)]⟩ =
      (Diagram.mk src P).unitFirst ++ ⟨p₂, C ++ [(.unit q, 0)]⟩ :=
    congrArg (Diagram.mk src) (by simp)
  have E : ((cond true x.toPastingDiagram (x.toPastingDiagram.boundary 1 true).unit).paste
      (cond true (x.toPastingDiagram.boundary 1 true).unit x.toPastingDiagram) 1 hpx).Equiv
      ((I.roundDiagram hS htP hsrc).toPastingDiagram.paste
        (I.diagram (Diagram.mk p₂ (C ++ [(Cell.unit q, 0)])) hp₂) 1 h₂) :=
    (Equiv.paste (.refl _) (hxb.unit.trans eu.symm) hpx h₁).trans (e₁.symm.trans
      ((PastingDiagram.equiv_of_eq (I.diagram_congr hlist _ _)).trans e₂))
  have hr := isRound_paste_of_round false hpx (u := x.toPastingDiagram) x.isRound hdx
    (by rw [dim_unit, dim_boundary x.toPastingDiagram (k := 1) (by omega) true])
  exact ⟨h₂, E.isRound_iff.1 hr, equivalent_trans
    (equivalent_paste_unit_cond true x hdx hpx hr) (equivalent_of_equiv E)⟩

private theorem targetFrom_of_target_append {src p₂ q : List (Edge S.Pt S.Ed)}
    {P C : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    (htP : S.target ⟨src, P⟩ = some p₂) (htd : S.target ⟨src, P ++ C⟩ = some q) :
    S.targetFrom p₂ C = some q := by
  have hpath := S.isPath_source_of_target htP
  rw [target, if_pos hpath] at htP htd
  rw [S.targetFrom_append, htP, Option.bind_some] at htd
  exact htd

theorem equivalent_roundDiagram_append {src p₂ q : List (Edge S.Pt S.Ed)} (hsrc : src ≠ [])
    {P P' C : List (Cell S.Pt S.Ed S.Ce × ℕ)} (htP : S.target ⟨src, P⟩ = some p₂)
    (htP' : S.target ⟨src, P'⟩ = some p₂) (htd : S.target ⟨src, P ++ C⟩ = some q)
    (htd' : S.target ⟨src, P' ++ C⟩ = some q)
    (h : Equivalent (I.roundDiagram hS htP hsrc) (I.roundDiagram hS htP' hsrc)) :
    Equivalent (I.roundDiagram hS htd hsrc) (I.roundDiagram hS htd' hsrc) := by
  have hp₂ := (S.isPath_target hS htP).ne_nil
  have hC := targetFrom_of_target_append htP htd
  obtain ⟨hp, hr, e⟩ := I.exists_equivalent_roundDiagram_append hS hsrc htP htd hp₂ hC
  obtain ⟨hp', hr', e'⟩ := I.exists_equivalent_roundDiagram_append hS hsrc htP' htd' hp₂ hC
  have hd' : S.target ⟨p₂, C ++ [(Cell.unit q, 0)]⟩ = some q := by
    have hq := S.isPath_target hS htd
    rw [target, if_pos (S.isPath_target hS htP), S.targetFrom_append, hC, Option.bind_some,
      targetFrom, S.applyLayer_unit_self hq.ne_nil, Option.bind_some]
    rfl
  have hy := I.isRound_diagram_of_last hS hd' hp₂ (l := (.unit q, 0)) rfl rfl
  have hdy : (I.diagram ⟨p₂, C ++ [(Cell.unit q, 0)]⟩ hp₂).dim =
      (I.roundDiagram hS htP hsrc).dim :=
    (I.dim_diagram hS hd' hp₂).trans (I.dim_diagram hS ((S.target_unitFirst _).trans htP) hsrc).symm
  exact equivalent_trans e (equivalent_trans
    (equivalent_paste_cond false (c := ⟨_, hy⟩) h rfl hdy hp hp' hr hr') (equivalent_symm e'))

theorem equivalent_roundDiagram_swap {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hsw : S.swap d h = some d') {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ []) :
    Equivalent (I.roundDiagram hS hq hsrc) (I.roundDiagram hS hq' hsrc') :=
  equivalent_of_equiv (I.equiv_diagram_swap hS (S.swap_unitFirst hsw)
    ((S.target_unitFirst d).trans hq) hsrc hsrc')

theorem equivalent_roundDiagram_congr {d d' : Diagram S.Pt S.Ed S.Ce}
    {q q' : List (Edge S.Pt S.Ed)} (h : d = d') (hd : S.target d = some q)
    (hd' : S.target d' = some q') (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) :
    Equivalent (I.roundDiagram hS hd hsrc) (I.roundDiagram hS hd' hsrc') := by
  subst h
  obtain rfl : q = q' := Option.some.inj (hd.symm.trans hd')
  exact equivalent_refl _

omit [DecidableEq S.Ed] in
private theorem cellDiagram_unit (x : PastingDiagram X) {s : List (Edge S.Pt S.Ed)}
    (hs : s ≠ []) : I.cellDiagram x (.unit s) = (I.path s hs).unit := by
  obtain _ | ⟨e, s⟩ := s
  · exact absurd rfl hs
  · rfl

theorem equivalent_roundDiagram_append_unit {src p : List (Edge S.Pt S.Ed)} (hsrc : src ≠ [])
    {A : List (Cell S.Pt S.Ed S.Ce × ℕ)} {s : List (Edge S.Pt S.Ed)} {o : ℕ}
    (htA : S.target ⟨src, A⟩ = some p) (htA' : S.target ⟨src, A ++ [(.unit s, o)]⟩ = some p)
    (ha : S.applyLayer p (.unit s) o = some p) :
    Equivalent (I.roundDiagram hS htA' hsrc) (I.roundDiagram hS htA hsrc) := by
  have hpath := S.isPath_target hS htA
  obtain ⟨hne, L, R, hpLR, hL, -⟩ := S.applyLayer_eq_some_iff.1 ha
  simp only [cellType] at hne hpLR
  obtain ⟨a, b, hab⟩ := S.exists_pathEnds_of_isPath hpath
  rw [hpLR] at hab
  obtain ⟨m, n, hLw, hs, hRw⟩ := S.exists_walk_of_split hab hne
  set c := I.roundDiagram hS htA hsrc
  have hdc : c.dim = 2 := I.dim_diagram hS ((S.target_unitFirst _).trans htA) hsrc
  obtain ⟨h₁, e₁⟩ := I.equiv_diagram_append hS (d := (Diagram.mk src A).unitFirst)
    (d' := ⟨p, [(.unit s, o)]⟩) ((S.target_unitFirst _).trans htA) rfl hsrc hpath.ne_nil
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
    (by rw [S.target_singleton (l := (.unit s, o)) hpath ha]; rfl)
  have e₂ : I.diagram ⟨p, [(.unit s, o)]⟩ hpath.ne_nil =
      I.whisker false L (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit) := by
    rw [I.diagram_singleton (l := (.unit s, o)) hpath.ne_nil (by simpa [cellType] using hpLR) hL
      (by simpa [cellType] using hne) (I.path s hne).unit, cellDiagram_unit]
  have hp : c.Pastable (I.whisker false L
      (I.whisker true R (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit)) 1 :=
    h₁.of_equiv (.refl _) (PastingDiagram.equiv_of_eq e₂)
  obtain ⟨hr, E⟩ := I.toPathInterp.equivalent_paste_whisker_unit c.isRound hdc hs hLw hRw hp
  refine equivalent_trans (equivalent_of_equiv ?_) E
  exact (PastingDiagram.equiv_of_eq (I.diagram_congr rfl _ _)).trans
    (e₁.trans (Equiv.paste (.refl _) (PastingDiagram.equiv_of_eq e₂) h₁ hp))

theorem equivalent_roundDiagram_insertUnit {d d' : Diagram S.Pt S.Ed S.Ce} {h o : ℕ}
    {s : List (Edge S.Pt S.Ed)}
    (hd' : d' = ⟨d.source, d.layers.take h ++ (.unit s, o) :: d.layers.drop h⟩)
    {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hq' : S.target d' = some q')
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) :
    Equivalent (I.roundDiagram hS hq' hsrc') (I.roundDiagram hS hq hsrc) := by
  subst hd'
  obtain ⟨src, ls⟩ := d
  dsimp only at hq hq' hsrc hsrc' ⊢
  have hpath := S.isPath_source_of_target hq
  have hq₀ := hq'
  rw [target, if_pos hpath, S.targetFrom_append] at hq₀
  obtain ⟨p, hA, hrest⟩ := Option.bind_eq_some_iff.1 hq₀
  obtain ⟨p₁, ha, -⟩ := Option.bind_eq_some_iff.1 hrest
  obtain ⟨-, -, rfl⟩ := S.eq_of_applyLayer_eq_some ha
  have hseg := (S.eq_of_applyLayer_eq_some ha).2.1
  simp only [cellType] at hseg ha
  rw [hseg] at ha
  have htA := S.target_mk_of_targetFrom hpath hA
  have htA' : S.target ⟨src, ls.take h ++ [(.unit s, o)]⟩ = some p := by
    refine S.target_mk_of_targetFrom hpath ?_
    rw [S.targetFrom_append, hA, Option.bind_some, targetFrom, ha, Option.bind_some]
    rfl
  have hls : ls.take h ++ (Cell.unit s, o) :: ls.drop h =
      (ls.take h ++ [(.unit s, o)]) ++ ls.drop h := by simp
  have hq'' : S.target ⟨src, (ls.take h ++ [(.unit s, o)]) ++ ls.drop h⟩ = some q' := by
    rw [← hls]; exact hq'
  have hq''' : S.target ⟨src, ls.take h ++ ls.drop h⟩ = some q := by
    rw [List.take_append_drop]; exact hq
  have hC : S.targetFrom p (ls.drop h) = some q := targetFrom_of_target_append htA hq'''
  rw [targetFrom, ha, Option.bind_some, hC] at hrest
  obtain rfl : q' = q := (Option.some.inj hrest).symm
  exact equivalent_trans (I.equivalent_roundDiagram_congr hS (congrArg (Diagram.mk src) hls)
    hq' hq'' hsrc' hsrc') (equivalent_trans (I.equivalent_roundDiagram_append hS hsrc htA' htA
      hq'' hq''' (I.equivalent_roundDiagram_append_unit hS hsrc htA htA' ha))
    (I.equivalent_roundDiagram_congr hS (congrArg (Diagram.mk src) (List.take_append_drop h ls))
      hq''' hq hsrc hsrc))

end Signature.Interp

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

omit [DecidableEq S.Ce] in
theorem targetFrom_side (hS : S.WellFormed) {r : S.Rel} {L R q : List (Edge S.Pt S.Ed)}
    {o : ℕ} (hL : L.length = o) (hq : S.target (S.relSource r) = some q) (β : Bool) :
    S.targetFrom (L ++ (S.relSource r).source ++ R)
      ((S.side r β).layers.map (fun l => (l.1, l.2 + o))) = some (L ++ q ++ R) := by
  have hside : S.targetFrom (S.relSource r).source (S.side r β).layers = some q := by
    have := (target_side hS r β).trans hq
    rw [Signature.target, if_pos (by rw [source_side hS]; exact isPath_source_side hS r),
      source_side hS] at this
    exact this
  have := S.targetFrom_whisker false L (S.targetFrom_whisker true R hside)
  subst hL
  simpa [Diagram.whisker] using this

namespace Interp

variable {hS : S.WellFormed} {X : DiagSet.{u}} (I : S.Interp hS X)

omit [DecidableEq S.Ce] in
private theorem exists_equivalent_roundDiagram_side {src L R q : List (Edge S.Pt S.Ed)}
    (hsrc : src ≠ []) {A : List (Cell S.Pt S.Ed S.Ce × ℕ)} {r : S.Rel} {o : ℕ}
    (hL : L.length = o) (hq : S.target (S.relSource r) = some q)
    (htA : S.target ⟨src, A⟩ = some (L ++ (S.relSource r).source ++ R)) (β : Bool)
    (htβ : S.target ⟨src, A ++ (S.side r β).layers.map (fun l => (l.1, l.2 + o))⟩ =
      some (L ++ q ++ R)) :
    ∃ m n a b : S.Pt, S.pathEnds (S.relSource r).source = some (m, n) ∧
      S.pathEnds q = some (m, n) ∧ S.walk a L = some m ∧ S.walk n R = some b ∧
      ∃ (hp : (I.toInterp.roundDiagram hS.1 htA hsrc).Pastable
        (I.whisker false L (I.whisker true R (sideRound I.toInterp hS r β).toPastingDiagram)) 1)
      (hr : ((I.toInterp.roundDiagram hS.1 htA hsrc).paste
        (I.whisker false L (I.whisker true R (sideRound I.toInterp hS r β).toPastingDiagram)) 1
          hp).IsRound),
      Equivalent (I.toInterp.roundDiagram hS.1 htβ hsrc) ⟨_, hr⟩ := by
  set J := I.toInterp
  have hpsrc := isPath_source_side hS r
  have hpath := S.isPath_target hS.1 htA
  obtain ⟨a, b, hab⟩ := S.exists_pathEnds_of_isPath hpath
  obtain ⟨m, n, hLw, hs, hRw⟩ := S.exists_walk_of_split hab hpsrc.ne_nil
  have hq' : S.pathEnds q = some (m, n) := S.pathEnds_target hS.1 hq hs
  set c := J.roundDiagram hS.1 htA hsrc
  have hdc : c.dim = 2 := J.dim_diagram hS.1 ((S.target_unitFirst _).trans htA) hsrc
  have hu := hasRoundType_side J hS r hq β
  have hcb : (c.boundary 1 true).Equiv (J.path (L ++ (S.relSource r).source ++ R)
      hpath.ne_nil) :=
    (J.hasRoundType_roundDiagram hS.1 htA hsrc).equiv_boundary_cond
      (J.dim_path (S.isPath_source_of_target htA)) true
  have hp := J.toPathInterp.pastable_whisker hdc hs hq' hLw hRw hu hcb
  have heta : S.side r β = ⟨(S.relSource r).source, (S.side r β).layers⟩ := by
    have e : S.side r β = ⟨(S.side r β).source, (S.side r β).layers⟩ := rfl
    rw [source_side hS] at e
    exact e
  by_cases hl : (S.side r β).layers = []
  · have hside : (sideRound J hS r β).toPastingDiagram = (J.path _ hpsrc.ne_nil).unit := by
      exact (J.diagram_congr (d' := ⟨(S.relSource r).source, []⟩) (heta.trans (by rw [hl])) _
        hpsrc.ne_nil).trans (J.diagram_nil hpsrc.ne_nil)
    have ew : (J.whisker false L (J.whisker true R (J.path _ hpsrc.ne_nil).unit)).Equiv
        (J.whisker false L (J.whisker true R (sideRound J hS r β).toPastingDiagram)) :=
      PastingDiagram.equiv_of_eq (by rw [hside])
    have hp' := hp.of_equiv (.refl _) ew.symm
    obtain ⟨hr, E⟩ := J.toPathInterp.equivalent_paste_whisker_unit c.isRound hdc hs hLw hRw hp'
    have E' := Equiv.paste (.refl c.toPastingDiagram) ew hp' hp
    refine ⟨m, n, a, b, hs, hq', hLw, hRw, hp, E'.isRound_iff.1 hr, ?_⟩
    have hA : A ++ (S.side r β).layers.map (fun l => (l.1, l.2 + o)) = A := by simp [hl]
    exact equivalent_trans (I.toInterp.equivalent_roundDiagram_congr hS.1
      (congrArg (Diagram.mk src) hA) htβ htA hsrc hsrc)
      (equivalent_trans (equivalent_symm E) (equivalent_of_equiv E'))
  · have hside : S.targetFrom (S.relSource r).source (S.side r β).layers = some q := by
      have := (target_side hS r β).trans hq
      rw [Signature.target, if_pos (by rw [source_side hS]; exact hpsrc), source_side hS] at this
      exact this
    have hd' := S.target_mk_of_targetFrom hpath (targetFrom_side hS hL hq β (R := R))
    obtain ⟨h₁, e₁⟩ := J.equiv_diagram_append hS.1 (d := (Diagram.mk src A).unitFirst)
      (d' := ⟨L ++ (S.relSource r).source ++ R, (S.side r β).layers.map
        (fun l => (l.1, l.2 + o))⟩) ((S.target_unitFirst _).trans htA) rfl hsrc hpath.ne_nil
      (List.cons_ne_nil _ _) (by simpa using hl) (by rw [hd']; rfl)
    have hw : (⟨L ++ (S.relSource r).source ++ R, (S.side r β).layers.map
        (fun l => (l.1, l.2 + o))⟩ : Diagram S.Pt S.Ed S.Ce) = Diagram.whisker false L
          (Diagram.whisker true R ⟨(S.relSource r).source, (S.side r β).layers⟩) := by
      subst hL
      simp [Diagram.whisker]
    have hne : (Diagram.whisker false L (Diagram.whisker true R
        ⟨(S.relSource r).source, (S.side r β).layers⟩)).source ≠ [] := by
      rw [← hw]; exact hpath.ne_nil
    have e₂ := J.equiv_diagram_whisker_whisker hS.1 hs hLw hRw hl hside hne
    have Ew : (J.diagram ⟨L ++ (S.relSource r).source ++ R, (S.side r β).layers.map
        (fun l => (l.1, l.2 + o))⟩ hpath.ne_nil).Equiv
        (J.whisker false L (J.whisker true R (sideRound J hS r β).toPastingDiagram)) :=
      (PastingDiagram.equiv_of_eq (J.diagram_congr hw _ hne)).trans (e₂.trans
        (PastingDiagram.equiv_of_eq (congrArg (fun z => J.whisker false L (J.whisker true R z))
          (J.diagram_congr heta.symm _ _))))
    have E : (J.roundDiagram hS.1 htβ hsrc).toPastingDiagram.Equiv
        (c.toPastingDiagram.paste
          (J.whisker false L (J.whisker true R (sideRound J hS r β).toPastingDiagram)) 1 hp) :=
      (PastingDiagram.equiv_of_eq (J.diagram_congr rfl _ _)).trans
        (e₁.trans (Equiv.paste (.refl _) Ew h₁ hp))
    exact ⟨m, n, a, b, hs, hq', hLw, hRw, hp,
      E.isRound_iff.1 (J.roundDiagram hS.1 htβ hsrc).isRound, equivalent_of_equiv E⟩

theorem equivalent_roundDiagram_relation {r : S.Rel} (hρ : IsEquivalence X (I.rel r).2)
    {d d' : Diagram S.Pt S.Ed S.Ce} {h o : ℕ} (hd : S.relationApply d r h o = some d')
    {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq' : S.target d' = some q') (hsrc' : d'.source ≠ []) :
    Equivalent (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') := by
  set J := I.toInterp
  obtain ⟨L, R, hA, hL, hcd⟩ := exists_eq_of_relationApply_eq_some hS hd
  obtain ⟨qr, hqr⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  have hpath := S.isPath_source_of_target hq
  set C := d.layers.drop (h + (S.relSource r).layers.length)
  set P : Bool → List (Cell S.Pt S.Ed S.Ce × ℕ) := fun β =>
    d.layers.take h ++ (S.side r β).layers.map (fun l => (l.1, l.2 + o))
  have htA := S.target_mk_of_targetFrom hpath hA
  have htP : ∀ β, S.target ⟨d.source, P β⟩ = some (L ++ qr ++ R) := fun β =>
    S.target_mk_of_targetFrom hpath (by
      rw [S.targetFrom_append, hA, Option.bind_some]
      exact targetFrom_side hS hL hqr β)
  have hd₀ : d = ⟨d.source, P false ++ C⟩ := hcd false
  have hd₁ : d' = ⟨d.source, P true ++ C⟩ := hcd true
  have htd : S.target ⟨d.source, P false ++ C⟩ = some q := by rw [← hd₀]; exact hq
  have htd' : S.target ⟨d.source, P true ++ C⟩ = some q' := by rw [← hd₁]; exact hq'
  obtain ⟨m, n, a, b, hs, hs', hLw, hRw, hp, hr, E₀⟩ :=
    I.exists_equivalent_roundDiagram_side hsrc hL hqr htA false (htP false)
  obtain ⟨-, -, -, -, -, -, -, -, hp', hr', E₁⟩ :=
    I.exists_equivalent_roundDiagram_side hsrc hL hqr htA true (htP true)
  have hρt := I.hasRoundType_rel r
  have huv : Equivalent (sideRound J hS r false) (sideRound J hS r true) :=
    EquivalenceData.equivalent ⟨hρt.dim_eq_dim, cellRound (I.rel r).2, hρ, hρt.dim_eq,
      hρt.source, hρt.target⟩
  have hdc : (J.roundDiagram hS.1 htA hsrc).dim = 2 :=
    J.dim_diagram hS.1 ((S.target_unitFirst _).trans htA) hsrc
  have hu : HasRoundType (sideRound J hS r false).toPastingDiagram
      (J.pathRound (S.relSource r).source (S.isPath_of_pathEnds hs))
      (J.pathRound qr (S.isPath_of_pathEnds hs')) := hasRoundType_side J hS r hqr false
  obtain ⟨hr₀, hr₁, T⟩ := J.toPathInterp.equivalent_paste_whisker
    (c := (J.roundDiagram hS.1 htA hsrc).toPastingDiagram) (L := L) (R := R)
    (u := sideRound J hS r false) (v := sideRound J hS r true)
    (J.roundDiagram hS.1 htA hsrc).isRound hdc hs hs' hLw hRw hu huv hp hp'
  have hPP : Equivalent (J.roundDiagram hS.1 (htP false) hsrc)
      (J.roundDiagram hS.1 (htP true) hsrc) :=
    equivalent_trans E₀ (equivalent_trans T (equivalent_symm E₁))
  have hq'' : q' = q := by
    have h₀ := Signature.Interp.targetFrom_of_target_append (htP false) htd
    have h₁ := Signature.Interp.targetFrom_of_target_append (htP true) htd'
    exact Option.some.inj (h₁.symm.trans h₀)
  subst hq''
  exact equivalent_trans (J.equivalent_roundDiagram_congr hS.1 hd₀ hq htd hsrc hsrc)
    (equivalent_trans (J.equivalent_roundDiagram_append hS.1 hsrc (htP false) (htP true) htd htd'
      hPP) (J.equivalent_roundDiagram_congr hS.1 hd₁.symm htd' hq' hsrc hsrc'))

theorem equivalent_roundDiagram_relationBackward {r : S.Rel}
    (hρ : IsEquivalence X (I.rel r).2) {d d' : Diagram S.Pt S.Ed S.Ce} {h o : ℕ}
    (hd : S.relationApply d' r h o = some d) {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) :
    Equivalent (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') :=
  equivalent_symm (I.equivalent_roundDiagram_relation hρ hd hq' hsrc' hq hsrc)

omit [DecidableEq S.Ce] in
theorem isEquivalence_rel_of_isInftyCategory {n : ℕ∞} (hX : IsInftyCategory n X) (hn : n ≤ 2)
    (r : S.Rel) : IsEquivalence X (I.rel r).2 := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  have hd : (I.rel r).1.dimension = 3 :=
    (I.hasRoundType_rel r).dim_eq.trans (congrArg (· + 1)
      (((hasRoundType_side I.toInterp hS r hq false).dim_eq).trans
        (congrArg (· + 1) (I.dim_path (isPath_source_side hS r)))))
  refine hX.2 _ _ (lt_of_le_of_lt hn ?_)
  rw [hd]
  decide

end Interp

end RelSignature

end Atoms.Diagrammatic.Layered
