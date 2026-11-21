import Atoms.Diagrammatic.Context.Rounded
import Atoms.Diagrammatic.Localization.CellularExtension

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

theorem isRoundCtx_of_isRound_app {A : Set (RoundPastingDiagram X)} {p : Prop} {H H' : PdHom X}
    {t : CtxExpr X} (ht : t.Typed A p H H') {a : PastingDiagram (⊤_ DiagSet.{u})}
    (ha : IsRoundIn (H.mapTo (terminal.from X)) a)
    (h : ((t.mapTo (terminal.from X)).app a).IsRound) : IsRoundCtx H t := by
  intro c hc hdc hrc
  have ht' := ht.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial
  have L := ht'.ctxLaws
  obtain ⟨e, hine, hde, -⟩ := exists_formalCell (RoundHom.ofIsRoundIn ha ⟨hc, hdc, hrc⟩)
  replace hde : e.dim = H.k + 1 + 1 := hde
  have hein := InHom.of_inHom_succ hine ha.inHom hc
  have hk2 : H.k + 1 < e.dim := by rw [hde]; omega
  have h₁ : (((t.mapTo (terminal.from X)).app e).boundary (H.k + 1) false).Equiv
      ((t.mapTo (terminal.from X)).app a) :=
    (L.boundary e hein (Nat.lt_succ_self H.k) hk2 false).trans
      (CtxExpr.app_equiv _ hine.source)
  have h₂ : (((t.mapTo (terminal.from X)).app e).boundary (H.k + 1) true).Equiv
      ((t.mapTo (terminal.from X)).app c) :=
    (L.boundary e hein (Nat.lt_succ_self H.k) hk2 true).trans
      (CtxExpr.app_equiv _ hine.target)
  exact h₂.isRound_iff.1 (PastingDiagram.isRound_boundary_true_of_false _
    ((L.dim_eq e hein).trans hde) (h₁.isRound_iff.2 h))

namespace CtxExpr

noncomputable def frameOf (α : Bool) (ℓ : PastingDiagram X) (k : ℕ) : CtxExpr X :=
  if h : ℓ.dim = k + 1 then ℓ.frameCtx α h else .id

theorem frameOf_of_eq (α : Bool) {ℓ : PastingDiagram X} {k : ℕ} (h : ℓ.dim = k + 1) :
    frameOf α ℓ k = ℓ.frameCtx α h :=
  dif_pos h

theorem frameOf_of_not (α : Bool) {ℓ : PastingDiagram X} {k : ℕ} (hdl : ¬ ℓ.dim = k + 1) :
    frameOf α ℓ k = .id :=
  dif_neg hdl

noncomputable def frame (ℓ r : PastingDiagram X) (k : ℕ) : CtxExpr X :=
  .comp (frameOf true r k) (frameOf false ℓ k)

theorem mapTo_frameOf (g : X ⟶ Y) (α : Bool) (ℓ : PastingDiagram X) (k : ℕ) :
    (frameOf α ℓ k).mapTo g = frameOf α (ℓ.mapTo g) k := by
  by_cases h : ℓ.dim = k + 1
  · rw [frameOf_of_eq α h, frameOf_of_eq α (show (ℓ.mapTo g).dim = k + 1 from h)]
    classical
    exact frame_mapTo g _ (krullDim_top_shape h) α _
  · rw [frameOf_of_not α h, frameOf_of_not α (show ¬ (ℓ.mapTo g).dim = k + 1 from h)]
    rfl

theorem mapTo_frame (g : X ⟶ Y) (ℓ r : PastingDiagram X) (k : ℕ) :
    (frame ℓ r k).mapTo g = frame (ℓ.mapTo g) (r.mapTo g) k := by
  change CtxExpr.comp ((frameOf true r k).mapTo g) ((frameOf false ℓ k).mapTo g) = _
  rw [mapTo_frameOf, mapTo_frameOf]
  rfl

theorem typed_frameOf (α : Bool) {ℓ : PastingDiagram X} {H : PdHom X} (hd : ℓ.dim ≤ H.k + 1)
    (hs : (H.side α).Equiv (ℓ.boundary H.k (!α))) :
    (frameOf α ℓ H.k).Typed (ℓ.topCells H.k) False H (H.setSide α (ℓ.boundary H.k α)) := by
  by_cases h : ℓ.dim = H.k + 1
  · rw [frameOf_of_eq α h]
    exact ℓ.typed_frameCtx α h hs
  · rw [frameOf_of_not α h]
    have hle : ℓ.dim ≤ H.k := by omega
    exact .id (PdHom.equiv_setSide H (hs.trans
      ((equiv_boundary_dim ℓ hle (!α)).trans (equiv_boundary_dim ℓ hle α).symm)))

theorem typed_frame {ℓ r : PastingDiagram X} {H : PdHom X} (hdℓ : ℓ.dim ≤ H.k + 1)
    (hdr : r.dim ≤ H.k + 1) (hv : H.v.Equiv (ℓ.boundary H.k true))
    (hw : H.w.Equiv (r.boundary H.k false)) :
    (frame ℓ r H.k).Typed Set.univ False H ⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩ :=
  .comp ((typed_frameOf false hdℓ hv).mono (Set.subset_univ _) fun h => h)
    ((typed_frameOf true (H := H.setSide false (ℓ.boundary H.k false)) hdr hw).mono
      (Set.subset_univ _) fun h => h)

end CtxExpr

namespace Pastes

variable {k : ℕ}

theorem frameOf (α : Bool) {ℓ x c : PastingDiagram X} (h : Pastes (cond α x ℓ) (cond α ℓ x) k c)
    (hd : ℓ.dim ≤ k + 1) (hdx : k < x.dim) :
    ((CtxExpr.frameOf α ℓ k).app x).Equiv c ∧ (ℓ.boundary k (!α)).Equiv (x.boundary k α) := by
  rcases h with ⟨hp, hc⟩ | ⟨γ, hd', hu, hc⟩
  · have hdl : ℓ.dim = k + 1 := by
      have h2 := lt_min_iff.1 hp.2
      cases α <;> simp only [cond_true, cond_false] at h2 <;> omega
    rw [CtxExpr.frameOf_of_eq α hdl]
    exact ⟨(ℓ.frameCtx_app α hdl x hp).trans hc.symm, hp.side.symm⟩
  cases α <;> cases γ <;> simp only [cond_true, cond_false] at hd' hu hc
  all_goals first
    | omega
    | (rw [CtxExpr.frameOf_of_not _ (by omega)]
       exact ⟨hc.symm, (equiv_boundary_dim ℓ hd' _).trans hu⟩)

end Pastes

theorem pastes_frameOf (α : Bool) {ℓ x : PastingDiagram X} {k : ℕ} (hd : ℓ.dim ≤ k + 1)
    (hdx : k < x.dim) (he : (ℓ.boundary k (!α)).Equiv (x.boundary k α)) :
    Pastes (cond α x ℓ) (cond α ℓ x) k ((CtxExpr.frameOf α ℓ k).app x) := by
  by_cases hdl : ℓ.dim = k + 1
  · rw [CtxExpr.frameOf_of_eq α hdl]
    have hp := PastingDiagram.Pastable.of_side α he.symm hdx (by omega)
    exact Or.inl ⟨hp, ℓ.frameCtx_app α hdl x hp⟩
  · rw [CtxExpr.frameOf_of_not α hdl]
    have hle : ℓ.dim ≤ k := by omega
    refine Or.inr ⟨α, ?_⟩
    cases α <;> exact ⟨hle, (equiv_boundary_dim ℓ hle _).symm.trans he, .refl _⟩

noncomputable def CtxExpr.ofFramesRev : ContextFrames X → CtxExpr X
  | [] => .id
  | (ℓ, r) :: fs => .comp (frame ℓ r fs.length) (ofFramesRev fs)

def RoundHom.pred (H : RoundHom X) (n : ℕ) (hn : H.k = n + 1) : RoundHom X :=
  ⟨H.boundary n, isRound_boundary_of_isRound H.isRound_v n false,
    isRound_boundary_of_isRound H.isRound_w n true,
    dim_boundary H.v (by rw [H.dim_v, hn]; omega) false,
    (parallel_boundary H.isRound_v (H.dim_v.trans hn) false true).of_equiv_right
      ((H.parallel.equiv_boundary_pred (H.dim_v.trans hn) true).symm)⟩

theorem RoundHom.isRoundIn_v (H : RoundHom X) {n : ℕ} (hn : H.k = n + 1) :
    IsRoundIn (H.boundary n) H.v :=
  H.isRoundIn_side hn false

theorem RoundHom.isRoundIn_w (H : RoundHom X) {n : ℕ} (hn : H.k = n + 1) :
    IsRoundIn (H.boundary n) H.w :=
  H.isRoundIn_side hn true

def FramesOn : ContextFrames X → PdHom X → Prop
  | [], _ => True
  | (ℓ, r) :: fs, H => ℓ.dim ≤ H.k + 1 ∧ r.dim ≤ H.k + 1 ∧
      ((CtxExpr.ofFramesRev fs).app H.v).Equiv (ℓ.boundary H.k true) ∧
      ((CtxExpr.ofFramesRev fs).app H.w).Equiv (r.boundary H.k false) ∧
      FramesOn fs (H.boundary (H.k - 1))

theorem typed_ofFramesRev : ∀ (ℓ r : PastingDiagram X) (fs : ContextFrames X) {H : RoundHom X},
    H.k = fs.length → FramesOn ((ℓ, r) :: fs) H →
      (CtxExpr.ofFramesRev ((ℓ, r) :: fs)).Typed Set.univ True H
        ⟨H.k, ℓ.boundary H.k false, r.boundary H.k true⟩
  | ℓ, r, fs, H, hk, ⟨hdℓ, hdr, hv, hw, hf⟩ => by
    have hG : (CtxExpr.ofFramesRev fs).Typed Set.univ True H
        ⟨H.k, (CtxExpr.ofFramesRev fs).app H.v, (CtxExpr.ofFramesRev fs).app H.w⟩ := by
      match fs, hk, hf with
      | [], _, _ => exact .id (.refl _)
      | (ℓ', r') :: fs', hk, hf =>
        rw [hk] at hf
        exact .promote trivial hk (H.isRoundIn_v hk).inHom (H.isRoundIn_w hk).inHom
          (typed_ofFramesRev ℓ' r' fs' (H := H.pred fs'.length hk) rfl hf) (.refl _)
    rw [hk] at hdℓ hdr hv hw ⊢
    exact .comp (hG.congr_codomain (H'' := ⟨fs.length, _, _⟩) ⟨hk, .refl _, .refl _⟩)
      ((CtxExpr.typed_frame (H := ⟨fs.length, (CtxExpr.ofFramesRev fs).app H.v,
        (CtxExpr.ofFramesRev fs).app H.w⟩) hdℓ hdr hv hw).mono (Set.subset_univ _)
        fun h => h.elim)

theorem typed_inner {fs : ContextFrames X} {H : RoundHom X} (hk : H.k = fs.length)
    (hf : FramesOn fs (H.boundary (H.k - 1))) :
    (CtxExpr.ofFramesRev fs).Typed Set.univ True H
      ⟨H.k, (CtxExpr.ofFramesRev fs).app H.v, (CtxExpr.ofFramesRev fs).app H.w⟩ := by
  match fs, hk, hf with
  | [], _, _ => exact .id (.refl _)
  | (ℓ', r') :: fs', hk, hf =>
    rw [hk] at hf
    exact .promote trivial hk (H.isRoundIn_v hk).inHom (H.isRoundIn_w hk).inHom
      (typed_ofFramesRev ℓ' r' fs' (H := H.pred fs'.length hk) rfl hf) (.refl _)

theorem evalFrames_ofFramesRev : ∀ (ℓ r : PastingDiagram X) (fs : ContextFrames X)
    {H : RoundHom X}, H.k = fs.length → FramesOn ((ℓ, r) :: fs) H →
      ∀ a, InHom H a →
        EvalFrames ((ℓ, r) :: fs).reverse 0 a ((CtxExpr.ofFramesRev ((ℓ, r) :: fs)).app a)
  | ℓ, r, fs, H, hk, ⟨hdℓ, hdr, hv, hw, hf⟩, a, ha => by
    have hGa := (typed_inner hk hf).mapsInto a ha
    rw [hk] at hdℓ hdr hv hw hGa
    have hc := (CtxExpr.typed_frameOf false (H := ⟨fs.length, (CtxExpr.ofFramesRev fs).app H.v,
      (CtxExpr.ofFramesRev fs).app H.w⟩) hdℓ hv).mapsInto _ hGa
    rw [List.reverse_cons, EvalFrames.append_singleton, List.length_reverse, Nat.zero_add]
    refine ⟨(CtxExpr.ofFramesRev fs).app a, ?_, _, _,
      pastes_frameOf false hdℓ hGa.lt_dim (PastingDiagram.Equiv.symm
        (hGa.source.trans hv)),
      pastes_frameOf true hdr hc.lt_dim (hc.target.trans hw).symm,
      .refl _⟩
    match fs, hk, hf, ha with
    | [], _, _, _ => exact .refl _
    | (ℓ', r') :: fs', hk, hf, ha =>
      rw [hk] at hf
      exact evalFrames_ofFramesRev ℓ' r' fs' (H := H.pred fs'.length hk) rfl hf a
        (ha.promote (by rw [hk]; exact Nat.lt_succ_self _))

def BoundedRev : ContextFrames X → Prop
  | [] => True
  | (ℓ, r) :: fs => ℓ.dim ≤ fs.length + 1 ∧ r.dim ≤ fs.length + 1 ∧ BoundedRev fs

theorem boundedRev_of_boundedFrames : ∀ fs : ContextFrames X,
    BoundedFrames fs.reverse → BoundedRev fs
  | [] => fun _ => trivial
  | (ℓ, r) :: fs => fun h => by
    rw [List.reverse_cons] at h
    have h₁ := h ⟨fs.reverse.length, by simp⟩
    simp only [List.get_eq_getElem, List.getElem_concat_length, List.length_reverse] at h₁
    refine ⟨h₁.1, h₁.2, boundedRev_of_boundedFrames fs fun i => ?_⟩
    have hi := i.isLt
    have h₂ := h ⟨i.val, by
      simp only [List.length_append, List.length_singleton] at hi ⊢; omega⟩
    simp only [List.get_eq_getElem] at h₂ ⊢
    rwa [List.getElem_append_left hi] at h₂

theorem framesOn_of_evalFrames {Y : DiagSet.{u}} (f : X ⟶ Y) [Mono f] :
    ∀ (ℓ r : PastingDiagram X) (fs : ContextFrames X) {H : RoundHom X}, H.k = fs.length →
      BoundedRev ((ℓ, r) :: fs) → ∀ {a c : PastingDiagram Y}, InHom (H.mapTo f) a →
        EvalFrames (((ℓ, r) :: fs).reverse.map fun p => (p.1.mapTo f, p.2.mapTo f)) 0 a c →
          FramesOn ((ℓ, r) :: fs) H ∧
            (((CtxExpr.ofFramesRev ((ℓ, r) :: fs)).mapTo f).app a).Equiv c
  | ℓ, r, fs, H, hk, ⟨hdℓ, hdr, hb⟩, a, c, ha, he => by
    rw [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      EvalFrames.append_singleton] at he
    obtain ⟨d, hin, htop⟩ := he
    rw [List.length_map, List.length_reverse, Nat.zero_add] at htop
    obtain ⟨hf, hGd⟩ : FramesOn fs (H.boundary (H.k - 1)) ∧
        (((CtxExpr.ofFramesRev fs).mapTo f).app a).Equiv d := by
      match fs, hk, hb, hin with
      | [], _, _, hin => exact ⟨trivial, hin⟩
      | (ℓ', r') :: fs', hk, hb, hin =>
        rw [hk]
        exact framesOn_of_evalFrames f ℓ' r' fs' (H := H.pred fs'.length hk) rfl hb
          (InHom.of_inHom_succ
            (ha.congr (H' := ⟨fs'.length + 1, H.v.mapTo f, H.w.mapTo f⟩) ⟨hk, .refl _, .refl _⟩)
            ((H.isRoundIn_v hk).inHom.mapTo f) ((H.isRoundIn_w hk).inHom.mapTo f)) hin
    have hGa := (((typed_inner hk hf).mapTo f (B := Set.univ) fun _ _ => trivial).mapsInto a
      ha).of_equiv hGd
    rw [hk] at hGa
    obtain ⟨c₁, c₂, h₁, h₂, h₃⟩ := htop
    obtain ⟨hcL, hbL⟩ := h₁.frameOf false (ℓ := ℓ.mapTo f) (x := d) hdℓ hGa.lt_dim
    rw [boundary_mapTo] at hbL
    have hv : ((CtxExpr.ofFramesRev fs).app H.v).Equiv (ℓ.boundary fs.length true) :=
      PastingDiagram.Equiv.of_mapTo f (PastingDiagram.Equiv.symm
        (hbL.trans hGa.source))
    have hc₁ := ((CtxExpr.typed_frameOf false (ℓ := ℓ.mapTo f)
      (H := ⟨fs.length, ((CtxExpr.ofFramesRev fs).app H.v).mapTo f,
        ((CtxExpr.ofFramesRev fs).app H.w).mapTo f⟩) hdℓ
      (by rw [boundary_mapTo]; exact hv.mapTo f)).mapsInto d hGa).of_equiv hcL
    obtain ⟨hcR, hbR⟩ := h₂.frameOf true (ℓ := r.mapTo f) (x := c₁) hdr hc₁.lt_dim
    rw [boundary_mapTo] at hbR
    have hw : ((CtxExpr.ofFramesRev fs).app H.w).Equiv (r.boundary fs.length false) :=
      PastingDiagram.Equiv.of_mapTo f (PastingDiagram.Equiv.trans
        (hc₁.target.symm) hbR.symm)
    rw [← hk] at hdℓ hdr hv hw
    refine ⟨⟨hdℓ, hdr, hv, hw, hf⟩, ?_⟩
    change ((CtxExpr.frame ℓ r fs.length).mapTo f).app (((CtxExpr.ofFramesRev fs).mapTo f).app a)
      |>.Equiv c
    rw [CtxExpr.mapTo_frame]
    exact PastingDiagram.Equiv.trans
      (CtxExpr.app_equiv (CtxExpr.frame (ℓ.mapTo f) (r.mapTo f) fs.length) hGd)
      (PastingDiagram.Equiv.trans
        (CtxExpr.app_equiv (CtxExpr.frameOf true (r.mapTo f) fs.length) hcL)
        (hcR.trans h₃))

theorem PastingDiagram.isRound_boundary_true_of_false_of_le (d : PastingDiagram X) {k : ℕ}
    (hd : d.dim ≤ k + 1) (h : (d.boundary k false).IsRound) : (d.boundary k true).IsRound := by
  by_cases hd' : d.dim = k + 1
  · exact d.isRound_boundary_true_of_false hd' h
  · have hle : d.dim ≤ k := by omega
    exact ((equiv_boundary_dim d hle true).trans
      ((equiv_boundary_dim d hle false).symm)).isRound_iff.2 h

theorem isRoundCtx_ofFramesRev_of_hole {Y : DiagSet.{u}} (f : X ⟶ Y) (ℓ r : PastingDiagram X)
    (fs : ContextFrames X) {H : RoundHom X} (hk : H.k = fs.length)
    (hf : FramesOn ((ℓ, r) :: fs) H) {a c : PastingDiagram Y} (ha : IsRoundIn (H.mapTo f) a)
    (hc : (((CtxExpr.ofFramesRev ((ℓ, r) :: fs)).mapTo f).app a).Equiv c) (hrc : c.IsRound) :
    IsRoundCtx H (CtxExpr.ofFramesRev ((ℓ, r) :: fs)) := by
  have hE := typed_ofFramesRev ℓ r fs hk hf
  have e : f ≫ terminal.from Y = terminal.from X := Subsingleton.elim _ _
  have hv : (H.v.mapTo f).mapTo (terminal.from Y) = H.v.mapTo (terminal.from X) := by
    rw [← e]; rfl
  have hw : (H.w.mapTo f).mapTo (terminal.from Y) = H.w.mapTo (terminal.from X) := by
    rw [← e]; rfl
  have ha' := ha.inHom.mapTo (terminal.from Y)
  change InHom ⟨H.k, (H.v.mapTo f).mapTo (terminal.from Y), (H.w.mapTo f).mapTo (terminal.from Y)⟩
    _ at ha'
  rw [hv, hw] at ha'
  refine isRoundCtx_of_isRound_app hE ⟨ha', ha.dim_eq, ha.isRound⟩ ?_
  rw [← e, ← CtxExpr.mapTo_mapTo]
  exact (CtxExpr.Typed.app_mapTo (terminal.from Y) (hE.mapTo f (B := Set.univ) fun _ _ => trivial) a
    ha.inHom).isRound_iff.2
      (show ((CtxExpr.ofFramesRev ((ℓ, r) :: fs)).mapTo f |>.app a).IsRound from
        hc.isRound_iff.2 hrc)

theorem isRoundCtx_inner (ℓ r ℓ' r' : PastingDiagram X) (fs : ContextFrames X)
    {H : RoundHom X} (hk : H.k = fs.length + 1)
    (hf : FramesOn ((ℓ, r) :: (ℓ', r') :: fs) H)
    (hr : IsRoundCtx H (CtxExpr.ofFramesRev ((ℓ, r) :: (ℓ', r') :: fs))) :
    IsRoundCtx (H.boundary fs.length) (CtxExpr.ofFramesRev ((ℓ', r') :: fs)) := by
  obtain ⟨hdℓ, hdr, hvℓ, hwr, hf'⟩ := hf
  set G := CtxExpr.ofFramesRev ((ℓ', r') :: fs)
  have hGn := typed_inner (fs := (ℓ', r') :: fs) hk hf'
  rw [hk] at hdℓ hdr hvℓ hwr hf'
  have hGm : G.Typed Set.univ True (H.boundary fs.length)
      ⟨fs.length, ℓ'.boundary fs.length false, r'.boundary fs.length true⟩ :=
    typed_ofFramesRev ℓ' r' fs (H := H.pred fs.length hk) rfl hf'
  obtain ⟨e, hine, hde, her⟩ := exists_formalCell (H.mapTo (terminal.from X))
  have hEr := hr e hine hde her
  have hGe := (hGn.mapTo (terminal.from X) (B := Set.univ) fun _ _ => trivial).mapsInto e hine
  rw [hk] at hGe
  have hFr := (CtxExpr.typed_frame (ℓ := ℓ.mapTo (terminal.from X))
    (r := r.mapTo (terminal.from X)) (H := ⟨fs.length + 1, (G.app H.v).mapTo (terminal.from X),
      (G.app H.w).mapTo (terminal.from X)⟩) hdℓ hdr
    (by rw [boundary_mapTo]; exact hvℓ.mapTo _)
    (by rw [boundary_mapTo]; exact hwr.mapTo _)).mapsInto _ hGe
  have hval : ((CtxExpr.ofFramesRev ((ℓ, r) :: (ℓ', r') :: fs)).mapTo (terminal.from X)).app e =
      (CtxExpr.frame (ℓ.mapTo (terminal.from X)) (r.mapTo (terminal.from X)) (fs.length + 1)).app
        ((G.mapTo (terminal.from X)).app e) := by
    change ((CtxExpr.frame ℓ r (fs.length + 1)).mapTo (terminal.from X)).app _ = _
    rw [CtxExpr.mapTo_frame]
  rw [hval] at hEr
  have hℓ₀ : ((ℓ.mapTo (terminal.from X)).boundary (fs.length + 1) false).IsRound :=
    hFr.source.isRound_iff.1 (isRound_boundary_of_isRound hEr _ false)
  have hℓ₁ := (ℓ.mapTo (terminal.from X)).isRound_boundary_true_of_false_of_le hdℓ hℓ₀
  rw [boundary_mapTo] at hℓ₁
  have hvIn := H.isRoundIn_v hk
  have hGv : ((G.mapTo (terminal.from X)).app (H.v.mapTo (terminal.from X))).IsRound :=
    (CtxExpr.Typed.app_mapTo (terminal.from X) hGm H.v hvIn.inHom).isRound_iff.2
      ((hvℓ.mapTo (terminal.from X)).isRound_iff.2 hℓ₁)
  exact isRoundCtx_of_isRound_app hGm
    ⟨hvIn.inHom.mapTo (terminal.from X), hvIn.dim_eq, hvIn.isRound⟩ hGv

theorem exists_cell_extension (v w : RoundPastingDiagram X)
    (h : Parallel v w) :
    ∃ (Y : DiagSet.{u}) (f : X ⟶ Y), Mono f ∧
      ∃ (U : Atom) (a : diagram Y U),
        HasRoundType (PastingDiagram.ofCell a) ⟨v.toPastingDiagram.mapTo f, v.isRound⟩
          ⟨w.toPastingDiagram.mapTo f, w.isRound⟩ :=
  let c : CellularExtensionData X := ⟨PUnit, fun _ => v, fun _ => w, fun _ => h⟩
  ⟨c.extension, c.incl, inferInstance, c.shape .unit, c.cell .unit, c.hasRoundType_cell .unit⟩

end Atoms.Diagrammatic
