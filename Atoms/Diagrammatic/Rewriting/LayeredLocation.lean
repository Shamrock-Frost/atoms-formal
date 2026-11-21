import Atoms.Diagrammatic.Rewriting.InftyCategory
import Atoms.Diagrammatic.Equivalence.UnitSolution

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic

theorem mem_equivalences_app_paste {X : DiagSet.{u}} {A : Set (RoundPastingDiagram X)} {p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H') (hr : IsRoundCtx H t)
    {e : RoundPastingDiagram X} (he : e ∈ equivalences X) (hin : InHom H e.toPastingDiagram)
    (hde : e.dim = H.k + 1 + 1) {w : RoundPastingDiagram X} (hdw : w.dim = H.k + 1 + 1)
    (hw : (t.app (e.boundary (H.k + 1) true)).Equiv (w.boundary (H.k + 1) false)) :
    ∃ (hp : (t.app e.toPastingDiagram).Pastable w.toPastingDiagram (H.k + 1))
      (hround : ((t.app e.toPastingDiagram).paste w.toPastingDiagram (H.k + 1) hp).IsRound),
      ((⟨_, hround⟩ : RoundPastingDiagram X) ∈ equivalences X ↔ w ∈ equivalences X) := by
  set k := H.k
  have L := ht.ctxLaws
  have hk1 : k < k + 1 := Nat.lt_succ_self k
  have hk2 : k + 1 < e.dim := by omega
  have hp₀ := hin.boundary hk1 hk2 false
  have hdp₀ : (e.boundary (k + 1) false).dim = k + 1 := dim_boundary _ (by omega) false
  have hHp : (t.app (e.boundary (k + 1) false)).IsRound :=
    hr.isRound_app ht hp₀ hdp₀ (isRound_boundary_of_isRound e.isRound _ _)
  have hdHp : (t.app (e.boundary (k + 1) false)).dim = k + 1 := (L.dim_eq _ hp₀).trans hdp₀
  have hdHe : (t.app e.toPastingDiagram).dim = k + 1 + 1 := (L.dim_eq _ hin).trans hde
  have hbe₀ := L.boundary _ hin hk1 hk2 false
  have hdu₀ : (t.app (e.boundary (k + 1) false)).unit.dim = k + 1 + 1 := by rw [dim_unit, hdHp]
  have hp₁ : (t.app (e.boundary (k + 1) false)).unit.Pastable (t.app e.toPastingDiagram)
      (k + 1) :=
    ⟨(boundary_unit hdHp true).trans hbe₀.symm, by rw [hdu₀, hdHe]; omega⟩
  have hp : (t.app e.toPastingDiagram).Pastable w.toPastingDiagram (k + 1) :=
    ⟨(L.boundary _ hin hk1 hk2 true).trans hw, by rw [hdHe, hdw]; omega⟩
  set m := (t.app (e.boundary (k + 1) false)).unit.paste (t.app e.toPastingDiagram) (k + 1) hp₁
  let wU := Within.pasteInl _ _ (k + 1) hp₁
  let wH := Within.pasteInr _ _ (k + 1) hp₁
  have hpm : m.shape.ogp.IsPastingIn (k + 1) wU.image wH.image ⊤ :=
    Within.isPastingIn_paste _ _ (k + 1) hp₁
  obtain ⟨ω, Fr, hω⟩ := ht.exists_argLoc e.toPastingDiagram hin
  let wE := ω.trans wH
  have hc : m.shape.ogp.IsPastingAtIn (k + 1) true wE.image wU.image ⊤ :=
    hω.isPastingAtIn_trans wU wH hpm
  have hV := hc.isSubmoleculeOf_inf
  have hh' : (e.toPastingDiagram.boundary (k + 1) (!true)).Equiv
      (occurrenceDiagram wU (k + 1) true hV) :=
    equiv_boundary_occurrence wU (k + 1) true hV wE hc.inf_eq.symm
  have hpaste := equiv_pasteAtBoundary_of_within wE wU hc (occurrence wU (k + 1) true hV)
    (isSubmoleculeOf_image_occurrence _ _ _ _) (image_occurrence wU (k + 1) true hV) hh'
  have hdsub : (occurrenceDiagram wU (k + 1) true hV).dim =
      ((t.app (e.boundary (k + 1) false)).unit.boundary (k + 1) true).dim := by
    rw [← dim_eq_of_equiv hh', dim_boundary _ (by omega), dim_boundary _ (by omega)]
  let d : PasteAtData true (k + 1) e hHp.unit :=
    ⟨hde, hdu₀, _, occurrence wU (k + 1) true hV,
      (occurrence wU (k + 1) true hV).isRewritableSubmolecule_image_iff.2
        ⟨isSubmoleculeOf_image_occurrence _ _ _ _,
          hh'.isRound_iff.1 (isRound_boundary_of_isRound e.isRound _ _), hdsub⟩, hh'⟩
  have hdm : d.round ∈ equivalences X :=
    (pasteAt_mem_equivalences_iff d he).2 (unit_mem_equivalences ⟨_, hHp⟩)
  have hmE : d.pasting.Equiv m := hpaste.trans (equiv_restrictTo_univ m)
  have hmR : m.IsRound := hmE.isRound_iff.1 d.isRound_pasting
  have hmem : (⟨m, hmR⟩ : RoundPastingDiagram X) ∈ equivalences X :=
    mem_equivalences_of_equiv hmE hdm
  have hR := isRound_paste_of_round true hp w.isRound hdw (by rw [hdHe])
  refine ⟨hp, hR, ?_⟩
  have hdm' : m.dim = k + 1 + 1 := by rw [dim_paste, hdu₀, hdHe, max_self]
  have h₂ : m.Pastable w.toPastingDiagram (k + 1) :=
    ⟨(equiv_boundary_paste hp₁ true).trans hp.1, by rw [hdm', hdw]; omega⟩
  obtain ⟨h₃, h₄, ea⟩ := equiv_paste_assoc hp₁ h₂
  have hdR : ((t.app e.toPastingDiagram).paste w.toPastingDiagram (k + 1) hp).dim = k + 1 + 1 := by
    rw [dim_paste, hdHe, hdw, max_self]
  have hmz := paste_mem_equivalences_iff_right (v := w) hmem hdm' hdw h₂
  have hxR := paste_mem_equivalences_iff_right (u := hHp.unit) (v := ⟨_, hR⟩)
    (unit_mem_equivalences ⟨_, hHp⟩) hdu₀ hdR h₄
  have hr₂ := isRound_paste_of_dim ⟨m, hmR⟩ w hdm' hdw h₂
  have hr₄ := isRound_paste_of_dim hHp.unit ⟨_, hR⟩ hdu₀ hdR h₄
  exact hxR.symm.trans (Iff.trans
    ⟨fun h => mem_equivalences_of_equiv (e := ⟨_, hr₄⟩) (e' := ⟨_, hr₂⟩) ea.symm h,
      fun h => mem_equivalences_of_equiv (e := ⟨_, hr₂⟩) (e' := ⟨_, hr₄⟩) ea h⟩ hmz)

def IsPiece {X : DiagSet.{u}} (k : ℕ) (p : Prop) (P a b : PastingDiagram X) : Prop :=
  HasBdry false (k + 1) P a b ∧ ∀ (w : RoundPastingDiagram X)
    (hp : P.Pastable w.toPastingDiagram (k + 1)), w.dim = k + 1 + 1 →
    ∃ hr : (P.paste w.toPastingDiagram (k + 1) hp).IsRound,
      (p → ((⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ↔ w ∈ equivalences X))

theorem isPiece_app {X : DiagSet.{u}} {A : Set (RoundPastingDiagram X)} {p' p : Prop}
    {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p' H H') (hr : IsRoundCtx H t)
    {e : RoundPastingDiagram X} (he : p → e ∈ equivalences X) (hin : InHom H e.toPastingDiagram)
    (hde : e.dim = H.k + 1 + 1) :
    IsPiece H.k p (t.app e.toPastingDiagram) (t.app (e.boundary (H.k + 1) false))
      (t.app (e.boundary (H.k + 1) true)) := by
  have L := ht.ctxLaws
  have hk1 : H.k < H.k + 1 := Nat.lt_succ_self _
  have hk2 : H.k + 1 < e.dim := by omega
  refine ⟨⟨(L.dim_eq _ hin).trans hde,
    (L.dim_eq _ (hin.boundary hk1 hk2 false)).trans (dim_boundary _ hk2.le false),
    (L.dim_eq _ (hin.boundary hk1 hk2 true)).trans (dim_boundary _ hk2.le true),
    L.boundary _ hin hk1 hk2 false, L.boundary _ hin hk1 hk2 true⟩, fun w hpw hdw => ?_⟩
  have hw := (L.boundary _ hin hk1 hk2 true).symm.trans hpw.1
  have hR := isRound_paste_of_round true hpw w.isRound hdw (by rw [(L.dim_eq _ hin).trans hde])
  refine ⟨hR, fun hp => ?_⟩
  obtain ⟨_, _, hiff⟩ := mem_equivalences_app_paste ht hr (he hp) hin hde hdw hw
  exact hiff

theorem IsPiece.of_equiv {X : DiagSet.{u}} {k : ℕ} {p : Prop}
    {P a b a' b' : PastingDiagram X}
    (h : IsPiece k p P a b) (ea : a.Equiv a') (eb : b.Equiv b') : IsPiece k p P a' b' :=
  ⟨(h.1.of_equiv_side ea).of_equiv_other eb, h.2⟩

theorem IsPiece.pasteOr {X : DiagSet.{u}} {k : ℕ} {p : Prop}
    {P Q a b b' c : PastingDiagram X} (hP : IsPiece k p P a b) (hQ : IsPiece k p Q b' c)
    (e : b.Equiv b') : IsPiece k p (P.pasteOr Q (k + 1)) a c := by
  have hpq := hP.1.pastable hQ.1 e
  refine ⟨hP.1.pasteOr hQ.1 e, ?_⟩
  rw [PastingDiagram.pasteOr_of hpq]
  intro w hpw hdw
  obtain ⟨h₃, h₄, ea⟩ := equiv_paste_assoc hpq hpw
  obtain ⟨hr₃, hi₃⟩ := hQ.2 w h₃ hdw
  obtain ⟨hr₄, hi₄⟩ := hP.2 ⟨_, hr₃⟩ h₄ (by rw [dim_paste, hQ.1.dim_h, hdw, max_self])
  refine ⟨ea.isRound_iff.2 hr₄, fun hp => Iff.trans ⟨fun h => ?_, fun h => ?_⟩
    ((hi₄ hp).trans (hi₃ hp))⟩
  · exact mem_equivalences_of_equiv (e' := ⟨_, hr₄⟩) ea h
  · exact mem_equivalences_of_equiv (e := ⟨_, hr₄⟩) ea.symm h

end Atoms.Diagrammatic

namespace Atoms.Diagrammatic.Layered

namespace Signature.PathInterp

variable {S : Signature.{v}} [DecidableEq S.Pt] {X : DiagSet.{u}} (I : S.PathInterp X)

noncomputable def withinWhisker {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) : (α : Bool) → (w : List (Edge S.Pt S.Ed)) →
    S.walk (cond α b c) w = some (cond α c a) → Within x (I.whisker α w x)
  | _, [], _ => Within.refl x
  | true, f :: w, hw =>
    Eq.mpr (congrArg (Within x) (I.whisker_cons_of (hx.pastable_whisker true hw)))
      (Within.pasteInl x (I.pathCons f w) 0 (hx.pastable_whisker true hw))
  | false, f :: w, hw =>
      Eq.mpr (congrArg (Within x) (I.whisker_cons_of (hx.pastable_whisker false hw)))
        (Within.pasteInr (I.pathCons f w) x 0 (hx.pastable_whisker false hw))

omit [DecidableEq S.Pt] in
theorem exists_argLoc_mpr {k : ℕ} {x A B : PastingDiagram X} (E : A = B) (ω : Within x B)
    (h : ∃ Fr, ArgLoc k ω Fr) : ∃ Fr, ArgLoc k (Eq.mpr (congrArg (Within x) E) ω) Fr := by
  subst E
  exact h

theorem exists_argLoc_withinWhisker {x : PastingDiagram X} {a b c : S.Pt}
    (hx : I.Spans x a b) : ∀ (α : Bool) (w : List (Edge S.Pt S.Ed))
    (hw : S.walk (cond α b c) w = some (cond α c a)), ∃ Fr, ArgLoc 0 (I.withinWhisker hx α w hw) Fr
  | _, [], _ => ⟨⊥, ArgLoc.refl 0 x⟩
  | true, f :: w, hw => by
    obtain ⟨-, hw'⟩ := S.walk_cons_eq_some.1 hw
    have hp := hx.pastable_whisker true hw
    have hpst := Within.isPastingIn_paste x (I.pathCons f w) 0 hp
    have hd : (I.pathCons f w).dim = 0 + 1 := I.dim_pathCons hw'
    refine exists_argLoc_mpr (I.whisker_cons_of hp) _ ⟨_, ArgLoc.of_isPastingAtIn (α := true) _
      ⟨(Within.pasteInr x (I.pathCons f w) 0 hp).isMoleculeIn_image,
        (Within.pasteInl x (I.pathCons f w) 0 hp).isMoleculeIn_image,
        by rw [sup_comm]; exact hpst.sup_eq.symm, by rw [inf_comm]; exact hpst.inf_eq_input, ?_⟩
      (by rw [Within.krullDim_image]; exact_mod_cast hd)⟩
    rw [inf_comm, hpst.inf_eq_output]
    exact Molecule.OGP.IsSubmoleculeOf.refl
      ((Within.pasteInl x (I.pathCons f w) 0 hp).isMoleculeIn_image.boundary 0 true)
  | false, f :: w, hw => by
    obtain ⟨-, hw'⟩ := S.walk_cons_eq_some.1 hw
    have hp := hx.pastable_whisker false hw
    have hpst := Within.isPastingIn_paste (I.pathCons f w) x 0 hp
    have hd : (I.pathCons f w).dim = 0 + 1 := I.dim_pathCons hw'
    refine exists_argLoc_mpr (I.whisker_cons_of hp) _ ⟨_, ArgLoc.of_isPastingAtIn (α := false) _
      ⟨(Within.pasteInl (I.pathCons f w) x 0 hp).isMoleculeIn_image,
        (Within.pasteInr (I.pathCons f w) x 0 hp).isMoleculeIn_image, hpst.sup_eq.symm,
        hpst.inf_eq_output, ?_⟩ (by rw [Within.krullDim_image]; exact_mod_cast hd)⟩
    rw [hpst.inf_eq_input]
    exact Molecule.OGP.IsSubmoleculeOf.refl
      ((Within.pasteInr (I.pathCons f w) x 0 hp).isMoleculeIn_image.boundary 0 false)

noncomputable abbrev unitWhisker (L R : List (Edge S.Pt S.Ed)) {s : List (Edge S.Pt S.Ed)}
    (hs : s ≠ []) : PastingDiagram X :=
  I.whisker false L (I.whisker true R (I.path s hs).unit)

theorem spans_unit_path {s : List (Edge S.Pt S.Ed)} {m n : S.Pt}
    (hs : S.pathEnds s = some (m, n)) :
    I.Spans (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit m n :=
  (I.spans_of_hasRoundType (I.hasRoundType_path _ hs)).of_hasRoundType
    (hasRoundType_unit (I.pathRound s (S.isPath_of_pathEnds hs)))

noncomputable def segmentOcc {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    Within (I.path s (S.isPath_of_pathEnds hs).ne_nil).unit
      (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil) :=
  (I.withinWhisker (I.spans_unit_path hs) true R hR).trans
    (I.withinWhisker ((I.spans_unit_path hs).whisker true (c := b) hR) false L hL)

theorem exists_argLoc_segmentOcc {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    ∃ Fr, ArgLoc 0 (I.segmentOcc hs hL hR) Fr := by
  obtain ⟨Fr₁, h₁⟩ := I.exists_argLoc_withinWhisker (I.spans_unit_path hs) true R hR
  obtain ⟨Fr₂, h₂⟩ := I.exists_argLoc_withinWhisker
    ((I.spans_unit_path hs).whisker true (c := b) hR) false L hL
  exact ⟨_, h₁.trans h₂⟩

theorem isSubmoleculeOf_segmentOcc {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil).shape.ogp.IsSubmoleculeOf
      ((I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil).shape.ogp.boundary
        (I.segmentOcc hs hL hR).image (0 + 1) false)
      ((I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil).shape.ogp.boundary
        (Within.refl (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil)).image (0 + 1)
          false) := by
  obtain ⟨Fr, hω⟩ := I.exists_argLoc_segmentOcc hs hL hR
  rw [Within.image_refl]
  exact hω.isSubmoleculeOf (n := 0 + 1) (Nat.lt_succ_self 0) false

noncomputable def segmentBdryOcc {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m) (hR : S.walk n R = some b) :=
  occurrence (Within.refl (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil)) (0 + 1) false
    (I.isSubmoleculeOf_segmentOcc hs hL hR)

theorem isRewritableSubmolecule_segmentBdryOcc {L s R : List (Edge S.Pt S.Ed)}
    {a m n b : S.Pt} (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m)
    (hR : S.walk n R = some b) :
    ((I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil).boundary (0 + 1) false).shape.ogp
      |>.IsRewritableSubmolecule (I.segmentBdryOcc hs hL hR).image ⊤ := by
  obtain ⟨Fr, hω⟩ := I.exists_argLoc_segmentOcc hs hL hR
  have hpath := S.isPath_of_pathEnds hs
  have hd1 : (I.path s hpath.ne_nil).dim = 1 := I.dim_path hpath
  have hspu := I.spans_unit_path hs
  have hdx : (I.unitWhisker L R hpath.ne_nil).dim = 2 := by
    have h₁ := I.dim_whisker true hspu (by rw [dim_unit, hd1]; omega) (c := b) hR
    rw [I.dim_whisker false (hspu.whisker true (c := b) hR) (by rw [h₁, dim_unit, hd1]; omega)
      (c := a) hL, h₁, dim_unit, hd1]
  have hιy : (I.path s hpath.ne_nil).Equiv (argOccurrenceDiagram _ hω) :=
    (boundary_unit hd1 false).symm.trans (equiv_argOccurrence _ hω)
  have hdz : ((I.unitWhisker L R hpath.ne_nil).boundary 1 false).dim = 1 :=
    dim_boundary _ (by omega) false
  exact (argOccurrence _ hω).isRewritableSubmolecule_image_iff.2
    ⟨isSubmoleculeOf_image_occurrence _ _ _ _, hιy.isRound_iff.1 (I.isRound_path hpath),
      (dim_eq_of_equiv hιy).symm.trans (hd1.trans hdz.symm)⟩

noncomputable def segmentSpec {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt}
    (hs : S.pathEnds s = some (m, n)) (hL : S.walk a L = some m) (hR : S.walk n R = some b) :
    CylSpec X :=
  ⟨0 + 1, true, (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil).boundary (0 + 1) false,
    some ⟨_, I.segmentBdryOcc hs hL hR, I.isRewritableSubmolecule_segmentBdryOcc hs hL hR⟩⟩

theorem segmentUnitor_spec {c : PastingDiagram X} (hc : c.IsRound) (hdc : c.dim = 2)
    {L s R : List (Edge S.Pt S.Ed)} {a m n b : S.Pt} (hs : S.pathEnds s = some (m, n))
    (hL : S.walk a L = some m) (hR : S.walk n R = some b)
    (hp : c.Pastable (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil) 1) :
    ∃ hr : ((I.segmentSpec hs hL hR).fam c).IsRound,
      (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
      ((I.segmentSpec hs hL hR).fam c).IsDegenerate ∧
      HasBdry false 2 ((I.segmentSpec hs hL hR).fam c)
        (c.paste (I.unitWhisker L R (S.isPath_of_pathEnds hs).ne_nil) 1 hp) c := by
  obtain ⟨Fr, hω⟩ := I.exists_argLoc_segmentOcc hs hL hR
  have hpath := S.isPath_of_pathEnds hs
  have hd1 : (I.path s hpath.ne_nil).dim = 1 := I.dim_path hpath
  have hιy : (I.path s hpath.ne_nil).Equiv (argOccurrenceDiagram _ hω) :=
    (boundary_unit hd1 false).symm.trans (equiv_argOccurrence _ hω)
  have hu : ((argOccurrenceDiagram _ hω).unit.boundary 1 (!true)).Equiv
      (argOccurrenceDiagram _ hω) :=
    boundary_unit ((dim_eq_of_equiv hιy).symm.trans hd1) false
  have hf : (I.segmentSpec hs hL hR).Fits c :=
    ⟨hc, lt_of_lt_of_eq (Nat.lt_succ_self 1) hdc.symm, hp.1⟩
  obtain ⟨hr', he, hdf⟩ := hf.fam_spec
  have hdc' : c.dim = 1 + 1 := hdc
  have E1 := (hf.atEnd_self (β := true) (Or.inl rfl)).equiv_boundary hdc'
  have E2 := (hf.atEnd_sidePaste_unit (ι := ⟨_, argOccurrence _ hω,
    I.isRewritableSubmolecule_segmentBdryOcc hs hL hR⟩) rfl hu).equiv_boundary hdc'
  have E3 := equiv_sidePaste_argOccurrence _ hω (Equiv.unit hιy.symm) hu hp
  have hdx : ((I.segmentSpec hs hL hR).fam c).dim = 2 + 1 := hdf.trans (by rw [hdc])
  exact ⟨hr', he, isDegenerate_cylDiagram c _ hf.K_le_bdryFull,
    ⟨hdx, (dim_eq_of_equiv (E2.symm.trans E3)).symm.trans
      (dim_boundary _ (by rw [hdx]; exact Nat.le_succ 2) false), hdc,
      E2.symm.trans E3, E1.symm⟩⟩

end Signature.PathInterp

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

omit [DecidableEq S.Ce] in
theorem getD_target_relSource_ne_nil (hS : S.WellFormed) (r : S.Rel) :
    (S.target (S.relSource r)).getD [] ≠ [] := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  rw [hq, Option.getD_some]
  exact (S.isPath_target hS.1 hq).ne_nil

def pathAt (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ) : List (Edge S.Pt S.Ed) :=
  (S.targetFrom d.source (d.layers.take h)).getD []

def pathBefore (d : Diagram S.Pt S.Ed S.Ce) (h o : ℕ) : List (Edge S.Pt S.Ed) :=
  (pathAt d h).take o

def pathAfter (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (h o : ℕ) :
    List (Edge S.Pt S.Ed) :=
  (pathAt d h).drop (o + (S.relSource r).source.length)

theorem relationApply_occurrence (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce}
    {r : S.Rel} {h o : ℕ} (hd : S.relationApply d r h o = some d') :
    S.targetFrom d.source (d.layers.take h) =
      some (pathBefore d h o ++ (S.relSource r).source ++ pathAfter d r h o) ∧
      (pathBefore d h o).length = o ∧
      ∀ β, cond β d' d = ⟨d.source, d.layers.take h ++
        (S.side r β).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ := by
  obtain ⟨L, R, hA, hL, hcd⟩ := exists_eq_of_relationApply_eq_some hS hd
  simp only [pathBefore, pathAfter, pathAt, hA, Option.getD_some]
  subst hL
  simp [List.drop_append, List.drop_eq_nil_of_le, hcd]

def sideLayers (r : S.Rel) (o : ℕ) (β : Bool) : List (Cell S.Pt S.Ed S.Ce × ℕ) :=
  if (S.side r β).layers = [] then [(.unit (S.side r β).source, o)]
  else (S.side r β).layers.map (fun l => (l.1, l.2 + o))

omit [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce] in
theorem sideLayers_ne_nil (r : S.Rel) (o : ℕ) (β : Bool) : sideLayers r o β ≠ [] := by
  unfold sideLayers
  split_ifs with hl
  · exact List.cons_ne_nil _ _
  · simpa using hl

omit [DecidableEq S.Ce] in
theorem targetFrom_sideLayers (hS : S.WellFormed) {r : S.Rel} {o : ℕ}
    {L R t : List (Edge S.Pt S.Ed)} (hL : L.length = o) (ht : S.target (S.relSource r) = some t)
    (β : Bool) :
    S.targetFrom (L ++ (S.relSource r).source ++ R) (sideLayers r o β) = some (L ++ t ++ R) := by
  have hside := targetFrom_side hS hL ht β (R := R)
  unfold sideLayers
  split_ifs with hl
  · rw [hl, List.map_nil] at hside
    rw [source_side hS, ← hside]
    have hap : S.applyLayer (L ++ (S.relSource r).source ++ R) (.unit (S.relSource r).source) o =
        some (L ++ (S.relSource r).source ++ R) :=
      S.applyLayer_eq_some_iff.2 ⟨(isPath_source_side hS r).ne_nil, L, R, rfl, hL, rfl⟩
    simp only [Signature.targetFrom, hap, Option.bind_some]
  · exact hside

theorem targetFrom_above (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') {q t : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (ht : S.target (S.relSource r) = some t) :
    S.targetFrom (pathBefore d h o ++ t ++ pathAfter d r h o)
      (d.layers.drop (h + (S.relSource r).layers.length)) = some q := by
  obtain ⟨hA, hL, hcd⟩ := relationApply_occurrence hS hd
  have h₀ := (congrArg S.target (hcd false)).symm.trans hq
  rw [Signature.target, if_pos (S.isPath_source_of_target hq), S.targetFrom_append,
    S.targetFrom_append, hA, Option.bind_some, targetFrom_side hS hL ht false,
    Option.bind_some] at h₀
  exact h₀

theorem target_ends (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (β : Bool) :
    S.target (cond β d' d) = some q ∧
      S.target ⟨d.source, d.layers.take h ++ sideLayers r o β ++
        d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩ = some q := by
  obtain ⟨hA, hL, hcd⟩ := relationApply_occurrence hS hd
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  have hpath := S.isPath_source_of_target hq
  have hC := targetFrom_above hS hd hq ht
  refine ⟨?_, S.target_mk_of_targetFrom hpath ?_⟩
  · rw [hcd β]
    refine S.target_mk_of_targetFrom hpath ?_
    rw [S.targetFrom_append, S.targetFrom_append, hA, Option.bind_some,
      targetFrom_side hS hL ht β, Option.bind_some, hC]
  · rw [S.targetFrom_append, S.targetFrom_append, S.targetFrom_append, hA, Option.bind_some,
      targetFrom_sideLayers hS hL ht β, Option.bind_some, hC, Option.bind_some,
      Signature.targetFrom, S.applyLayer_unit_self (S.isPath_target hS.1 hq).ne_nil,
      Option.bind_some]
    rfl

theorem walk_beside (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') (h₁ : S.IsPath d.source) :
    S.walk ((S.pathEnds d.source).get h₁).1 (pathBefore d h o) =
        some ((S.pathEnds (S.relSource r).source).get (isPath_source_side hS r)).1 ∧
      S.walk ((S.pathEnds (S.relSource r).source).get (isPath_source_side hS r)).2
        (pathAfter d r h o) = some ((S.pathEnds d.source).get h₁).2 := by
  obtain ⟨hA, -, -⟩ := relationApply_occurrence hS hd
  obtain ⟨m, n, hLw, hs, hRw⟩ := S.exists_walk_of_split
    (S.pathEnds_targetFrom hS.1 hA (Option.some_get h₁).symm) (isPath_source_side hS r).ne_nil
  simp only [hs, Option.get_some]
  exact ⟨hLw, hRw⟩

omit [DecidableEq S.Ce] in
theorem target_eq_of_layers_eq_nil (hS : S.WellFormed) {r : S.Rel} {β : Bool}
    (hl : (S.side r β).layers = []) {t : List (Edge S.Pt S.Ed)}
    (ht : S.target (S.relSource r) = some t) : t = (S.relSource r).source := by
  have h := (target_side hS r β).trans ht
  rw [Signature.target, if_pos (by rw [source_side hS]; exact isPath_source_side hS r), hl,
    source_side hS] at h
  exact (Option.some.inj h).symm

omit [DecidableEq S.Ce] in
theorem target_append_unit (hS : S.WellFormed) {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) :
    S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q := by
  have hpath := S.isPath_source_of_target hq
  have hq' := hq
  rw [Signature.target, if_pos hpath] at hq'
  refine S.target_mk_of_targetFrom hpath ?_
  rw [S.targetFrom_append, hq', Option.bind_some, Signature.targetFrom,
    S.applyLayer_unit_self (S.isPath_target hS.1 hq).ne_nil, Option.bind_some]
  rfl

omit [DecidableEq S.Ce] in
theorem swap_append_unit (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hsw : S.swap d h = some d') {q : List (Edge S.Pt S.Ed)} (hq : S.target d' = some q) :
    S.swap ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ h =
      some ⟨d'.source, d'.layers ++ [(.unit q, 0)]⟩ := by
  obtain ⟨l₁, l₂, rest, n, hdrop, hn, rfl⟩ := S.eq_of_swap_eq_some hsw
  have hle : h ≤ d.layers.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_cons] at this
    omega
  have ht := target_append_unit hS hq
  simp only [List.append_assoc] at ht
  simp only [Signature.swap, List.drop_append_of_le_length hle, hdrop, List.cons_append, hn,
    Option.bind_some, List.take_append_of_le_length hle, List.append_assoc, ht,
    Option.isSome_some, ↓reduceIte]

def RewriteChain.append {d d' d'' : Diagram S.Pt S.Ed S.Ce} :
    S.RewriteChain d d' → S.RewriteChain d' d'' → S.RewriteChain d d''
  | .refl _, c' => c'
  | .cons l c, c' => .cons l (c.append c')

def RewriteChain.IsLayered : {d d' : Diagram S.Pt S.Ed S.Ce} → S.RewriteChain d d' → Prop
  | _, _, .refl _ => True
  | _, _, .cons (.relation ..) c => c.IsLayered
  | _, _, .cons (.identification ..) c => c.IsLayered
  | _, _, .cons _ _ => False

theorem RewriteChain.IsLayered.append {d d' d'' : Diagram S.Pt S.Ed S.Ce}
    {c : S.RewriteChain d d'} {c' : S.RewriteChain d' d''} (hc : c.IsLayered)
    (hc' : c'.IsLayered) : (c.append c').IsLayered := by
  induction c with
  | refl => exact hc'
  | cons l c ih =>
    cases l
    · exact ih hc hc'
    · exact hc.elim
    · exact ih hc hc'
    · exact hc.elim

theorem RewriteChain.isSome_target_and_source (hS : S.toSignature.WellFormed) :
    ∀ {d d' : Diagram S.Pt S.Ed S.Ce} (_ : S.RewriteChain d d'), (S.target d).isSome →
      (S.target d').isSome ∧ d'.source = d.source
  | _, _, .refl _, h => ⟨h, rfl⟩
  | _, _, .cons l c, h =>
    ⟨(RewriteChain.isSome_target_and_source hS c (l.isSome_target_of_isSome hS h)).1,
      (RewriteChain.isSome_target_and_source hS c (l.isSome_target_of_isSome hS h)).2.trans
        l.source_eq⟩

end RelSignature

end Atoms.Diagrammatic.Layered
