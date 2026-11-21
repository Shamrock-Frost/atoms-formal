import Atoms.Diagrammatic.Context.NaturalSim

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

section ArgOccurrence

variable {k : ℕ} {x tx : PastingDiagram X} (ω : Within x tx) {Fr : LowerSet tx.shape.ogp}
  (hω : ArgLoc k ω Fr)

abbrev argOccurrenceDiagram : PastingDiagram X :=
  occurrenceDiagram (Within.refl tx) (k + 1) false
    (by rw [Within.image_refl]; exact hω.isSubmoleculeOf (n := k + 1) (Nat.lt_succ_self k) false)

def argOccurrence : Within (argOccurrenceDiagram ω hω) (tx.boundary (k + 1) false) :=
  occurrence (Within.refl tx) (k + 1) false
    (by rw [Within.image_refl]; exact hω.isSubmoleculeOf (n := k + 1) (Nat.lt_succ_self k) false)

theorem image_argOccurrence {m : PastingDiagram X} (w : Within tx m) :
    ((argOccurrence ω hω).trans
        ((Within.boundary tx (k + 1) false).trans w)).image =
      OGP.map w.emb (tx.shape.ogp.boundary ω.image (k + 1) false) := by
  have h := image_occurrence (Within.refl tx) (k + 1) false
    (by rw [Within.image_refl]; exact hω.isSubmoleculeOf (n := k + 1) (Nat.lt_succ_self k) false)
  rw [Within.image_trans] at h
  rw [Within.image_trans, ← h, ← map_comp]
  rfl

theorem equiv_argOccurrence : (x.boundary (k + 1) false).Equiv (argOccurrenceDiagram ω hω) :=
  equiv_occurrence_of_image_eq (Within.refl tx) (k + 1) false _
    ((Within.boundary x (k + 1) false).trans ω) (Within.image_boundary_trans ω (k + 1) false)

theorem equiv_sidePaste_argOccurrence {u y : PastingDiagram X} (e : u.Equiv x)
    (h : (u.boundary (k + 1) (!true)).Equiv (argOccurrenceDiagram ω hω))
    (hp : y.Pastable tx (k + 1)) :
    (sidePaste true u (k + 1) (argOccurrence ω hω) (isSubmoleculeOf_image_occurrence _ _ _ _) h
      y).Equiv (y.paste tx (k + 1) hp) := by
  have hs : (y.boundary (k + 1) true).Equiv (tx.boundary (k + 1) false) := hp.1
  let wQ := Within.pasteInl y tx (k + 1) hp
  let wP := Within.pasteInr y tx (k + 1) hp
  let wU := (Within.ofEquiv e).trans (ω.trans wP)
  have hpst := Within.isPastingIn_paste y tx (k + 1) hp
  have hcX := hω.isPastingAtIn_trans wQ wP hpst
  have hwU : wU.image = (ω.trans wP).image := Within.image_ofEquiv_trans e _
  have hc : (y.paste tx (k + 1) hp).shape.ogp.IsPastingAtIn (k + 1) true wU.image wQ.image ⊤ := by
    rw [hwU]
    exact hcX
  have hside : sideWithin wQ (k + 1) true hs = (Within.boundary tx (k + 1) false).trans wP :=
    Within.ext_of_image_eq _ _ (by
      rw [image_sideWithin, Within.image_boundary_trans, ← hpst.inf_eq_output,
        hpst.inf_eq_input])
  have hocc : ((argOccurrence ω hω).trans
      (sideWithin wQ (k + 1) true hs)).image = wU.image ⊓ wQ.image := by
    rw [hside, image_argOccurrence ω hω wP, hwU, hcX.inf_eq, Bool.not_true, Within.image_trans,
      map_boundary]
  exact PastingDiagram.Equiv.trans
    (sidePaste_equiv_restrictTo (hι := isSubmoleculeOf_image_occurrence _ _ _ _) (h := h) wU wQ hs
      hc hocc (y.paste tx (k + 1) hp).shape.isMolecule)
    (equiv_restrictTo_univ _)

end ArgOccurrence

theorem InHom.of_paste {H : PdHom X} {n : ℕ} {y z : PastingDiagram X} (γ : Bool)
    (hy : InHom H (cond γ z y)) (hkn : H.k < n) (hp : y.Pastable z n) :
    InHom H (y.paste z n hp) :=
  ⟨lt_of_lt_of_le hy.lt_dim (by
      rw [dim_paste]; cases γ; exacts [le_max_left _ _, le_max_right _ _]),
    (equiv_boundary_paste_of_lt hp γ hkn false).symm.trans hy.source,
    (equiv_boundary_paste_of_lt hp γ hkn true).symm.trans hy.target⟩

theorem InHom.unit {H : PdHom X} {y : PastingDiagram X} (hy : InHom H y)
    (hdy : y.dim = H.k + 1) : InHom H y.unit :=
  InHom.of_hasBdry (hasType_unit hdy) hy

namespace CtxTriple

variable {A : Set (CtxTriple X)}

theorem Sim.unit (α : Bool) (hU : cylTriples X ⊆ A) (D D' : RoundHom X) {T : CtxExpr X}
    (hT : IsRoundCtxOn D D' T) :
    Sim (Closure A) D D'
      (cond α (fun c => (cond α (T.app c) (D'.side α).unit).pasteOr
        (cond α (D'.side α).unit (T.app c)) D'.k) T.app)
      (cond α T.app (fun c => (cond α (T.app c) (D'.side α).unit).pasteOr
        (cond α (D'.side α).unit (T.app c)) D'.k)) := by
  have hdz : (D'.side α).dim = D'.k :=
    Bool.cond_rec_prop (p := fun x : PastingDiagram X => x.dim = D'.k) α D'.dim_w D'.dim_v
  have hι : (D'.side α).shape.ogp.IsRewritableSubmolecule (Within.refl (D'.side α)).image ⊤ :=
    (Within.refl _).isRewritableSubmolecule_image_iff.2
      ⟨Within.isSubmoleculeOf_image_refl _, Bool.cond_rec_prop α D'.isRound_w D'.isRound_v, rfl⟩
  have hu : ((D'.side α).unit.boundary D'.k (!α)).Equiv (D'.side α) := boundary_unit hdz (!α)
  have e : ∀ c, InHom D' (T.app c) →
      ((CtxExpr.side α (D'.side α).unit D'.k (Within.refl _) hι.isSubmoleculeOf hu).app
        (T.app c)).Equiv ((cond α (T.app c) (D'.side α).unit).pasteOr
          (cond α (D'.side α).unit (T.app c)) D'.k) := fun c hTc => by
    have hp := Pastable.of_side α ((hTc.side α).trans hu.symm) hTc.lt_dim
      (by rw [dim_unit, hdz]; omega)
    rw [PastingDiagram.pasteOr_of hp]
    exact CtxExpr.sidePaste_equiv_paste α (Within.image_refl _) hu (hTc.side α) hp
  refine ((Sim.of_mem (A := A) (hU ⟨_, isCylTriple_unitor α D' (Within.refl _) hι hu⟩)).right
    D hT).of_equiv (fun c hc => ?_) (fun c hc => ?_) <;> cases α
  exacts [.refl _, e c (hT.typed.mapsInto c hc), e c (hT.typed.mapsInto c hc), .refl _]

theorem Sim.paste_app_unit (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) (D D' : RoundHom X)
    {H H₁ : PdHom X} {P : CtxExpr X} (hP : P.Typed Set.univ True H H₁) {y : PastingDiagram X}
    (hy : IsRoundIn H y) (hD : D'.k = H.k + 1) (hw : D'.w.Equiv (P.app y)) {T : CtxExpr X}
    (hT : IsRoundCtxOn D D' T) :
    Sim (Closure A) D D' T.app (fun c => (T.app c).pasteOr (P.app y.unit) D'.k) := by
  obtain ⟨⟨k', x₀, w'⟩, hx₀, hw', hdx₀, hp₀⟩ := D'
  dsimp only at hD hw hT hdx₀ ⊢
  subst hD
  have hyu : InHom H y.unit := hy.inHom.unit hy.dim_eq
  obtain ⟨ω, Fr, hω⟩ := hP.exists_argLoc y.unit hyu
  have L := hP.ctxLaws
  have hz : ((P.app y.unit).boundary (H.k + 1) false).Equiv (P.app y) :=
    PastingDiagram.Equiv.trans
      (L.boundary _ hyu (Nat.lt_succ_self H.k) (by rw [dim_unit, hy.dim_eq]; omega) false)
      (CtxExpr.app_equiv P (boundary_unit hy.dim_eq false))
  have hιy : y.Equiv (argOccurrenceDiagram ω hω) :=
    (boundary_unit hy.dim_eq false).symm.trans (equiv_argOccurrence ω hω)
  have hdz : ((P.app y.unit).boundary (H.k + 1) false).dim = H.k + 1 :=
    dim_boundary _ (by rw [L.dim_eq _ hyu, dim_unit, hy.dim_eq]; omega) false
  have hι : ((P.app y.unit).boundary (H.k + 1) false).shape.ogp.IsRewritableSubmolecule
      (argOccurrence ω hω).image ⊤ :=
    (argOccurrence ω hω).isRewritableSubmolecule_image_iff.2
      ⟨isSubmoleculeOf_image_occurrence _ _ _ _, hιy.isRound_iff.1 hy.isRound,
        (dim_eq_of_equiv hιy).symm.trans (hy.dim_eq.trans hdz.symm)⟩
  have hu : ((argOccurrenceDiagram ω hω).unit.boundary (H.k + 1) false).Equiv
      (argOccurrenceDiagram ω hω) :=
    boundary_unit ((dim_eq_of_equiv hιy).symm.trans hy.dim_eq) false
  have hzw : ((P.app y.unit).boundary (H.k + 1) false).Equiv w' := hz.trans hw.symm
  have hzr : ((P.app y.unit).boundary (H.k + 1) false).IsRound := hzw.isRound_iff.2 hw'
  have S := ((Sim.of_mem (A := A) (hU ⟨_, isCylTriple_rightUnitor
    ⟨⟨H.k + 1, x₀, (P.app y.unit).boundary (H.k + 1) false⟩, hx₀, hzr, hdx₀,
      hp₀.of_equiv_right hzw⟩
    (argOccurrence ω hω) hι hu⟩)).symm hA).right D (hT.congr (.refl _) ⟨rfl, .refl _, hzw.symm⟩)
  refine (S.congr (H₁' := ⟨H.k + 1, x₀, w'⟩) (.refl _) ⟨rfl, .refl _, hzw⟩).of_equiv
    (fun _ _ => .refl _) (fun c hc => ?_)
  have hTc := hT.typed.mapsInto c hc
  have hp : (T.app c).Pastable (P.app y.unit) (H.k + 1) :=
    ⟨hTc.target.trans hzw.symm,
      lt_min hTc.lt_dim (by rw [L.dim_eq _ hyu, dim_unit, hy.dim_eq]; omega)⟩
  rw [PastingDiagram.pasteOr_of hp]
  exact equiv_sidePaste_argOccurrence ω hω (Equiv.unit hιy.symm) hu hp

theorem Sim.round_right (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) {H₀ H H₁ : PdHom X}
    {K P Q : CtxExpr X} (hK : IsRoundCtxOn H₀ H K) (hP : IsRoundCtxOn H H₁ P)
    (hQ : IsRoundCtxOn H H₁ Q) {a b : PastingDiagram X} (ha : IsRoundIn H₀ a)
    (hb : IsRoundIn H₀ b) {θ θ' : PastingDiagram X} (hθ : θ.IsRound) (hθ' : θ'.IsRound)
    (htθ : HasBdry false (H₀.k + 1) θ (P.app (K.app b)) (Q.app (K.app b)))
    (htθ' : HasBdry false (H₀.k + 1) θ' (P.app (K.app a)) (Q.app (K.app a)))
    (h : Sim (Closure A) ⟨H₀.k + 1, K.app a, K.app b⟩
      ⟨H₀.k + 1, P.app (K.app a), Q.app (K.app b)⟩
      (fun c => (CtxExpr.paste true θ (H₀.k + 1)).app (P.app c))
      (fun c => (CtxExpr.paste false θ' (H₀.k + 1)).app (Q.app c))) :
    Sim (Closure A) ⟨H₀.k + 1, a, b⟩ ⟨H₀.k + 1, P.app (K.app a), Q.app (K.app b)⟩
      (fun c => (CtxExpr.paste true θ (H₀.k + 1)).app (P.app (K.app c)))
      (fun c => (CtxExpr.paste false θ' (H₀.k + 1)).app (Q.app (K.app c))) := by
  obtain ⟨k, v₀, w₀⟩ := H₀
  obtain ⟨k', v, w⟩ := H
  obtain ⟨k'', v₁, w₁⟩ := H₁
  have e₁ : k = k' := hK.typed.k_eq.symm
  subst e₁
  have e₂ : k = k'' := hP.typed.k_eq.symm
  subst e₂
  dsimp only at htθ htθ' h ⊢
  have ha' := hK.isRoundIn ha
  have hb' := hK.isRoundIn hb
  have hPa := hP.isRoundIn ha'
  have hPb := hP.isRoundIn hb'
  have hQb := hQ.isRoundIn hb'
  have hdb' : (K.app b).dim = k + 1 := hb'.dim_eq
  have hθs : (P.app (K.app b)).Equiv (θ.boundary (k + 1) false) :=
    htθ.side.symm
  have hθt' : (Q.app (K.app a)).Equiv (θ'.boundary (k + 1) true) :=
    htθ'.other.symm
  have hKp := hK.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hRb : (K.app b).Equiv ((K.app b).unit.boundary (k + 1) false) :=
    (boundary_unit hdb' false).symm
  have hdu : (K.app b).unit.dim = k + 1 + 1 := by rw [dim_unit, hdb']
  have hR : IsRoundCtxOn ⟨k + 1, a, b⟩ ⟨k + 1, K.app a, K.app b⟩
      (.comp (CtxExpr.paste true (K.app b).unit (k + 1)) K) :=
    (isRoundCtxOn_comp_paste true hKp (isRound_unit hb'.isRound) hdu hRb).congr (.refl _)
      ⟨rfl, .refl _, boundary_unit hdb' true⟩
  have S1 := h.right (RoundHom.ofIsRoundIn ha hb) hR
  have hPKp : (CtxExpr.comp P K).Typed Set.univ True ⟨k + 1, a, b⟩
      ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩ :=
    (hK.typed.comp hP.typed).promote_of_inHom trivial ha.inHom hb.inHom
  have hQKp : (CtxExpr.comp Q K).Typed Set.univ True ⟨k + 1, a, b⟩
      ⟨k + 1, Q.app (K.app a), Q.app (K.app b)⟩ :=
    (hK.typed.comp hQ.typed).promote_of_inHom trivial ha.inHom hb.inHom
  have hPRp : (CtxExpr.comp P (.comp (CtxExpr.paste true (K.app b).unit (k + 1)) K)).Typed
      Set.univ True ⟨k + 1, a, b⟩ ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩ :=
    hR.typed.comp (hP.typed.promote_of_inHom trivial ha'.inHom hb'.inHom)
  have hθR : ∀ {q : Prop}, (CtxExpr.paste true θ (k + 1)).Typed Set.univ q
      ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩ ⟨k + 1, P.app (K.app a), Q.app (K.app b)⟩ :=
    fun {_} =>
    (CtxExpr.typed_paste true (u := ⟨θ, hθ⟩) (H := ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩)
      (Set.mem_univ _) htθ.dim_h hθs).congr_codomain ⟨rfl, .refl _, htθ.other⟩
  have hT1 : IsRoundCtxOn ⟨k + 1, a, b⟩ ⟨k + 1, P.app (K.app a), Q.app (K.app b)⟩
      (.comp (CtxExpr.paste true θ (k + 1)) (.comp P K)) :=
    (isRoundCtxOn_comp_paste true hPKp hθ htθ.dim_h hθs).congr (.refl _) ⟨rfl, .refl _, htθ.other⟩
  have hT2 : IsRoundCtxOn ⟨k + 1, a, b⟩ ⟨k + 1, P.app (K.app a), Q.app (K.app b)⟩
      (.comp (CtxExpr.paste true θ (k + 1))
        (.comp P (.comp (CtxExpr.paste true (K.app b).unit (k + 1)) K))) :=
    (isRoundCtxOn_comp_paste true hPRp hθ htθ.dim_h hθs).congr (.refl _) ⟨rfl, .refl _, htθ.other⟩
  have hx₀u : (P.app (K.app a)).Equiv ((P.app (K.app a)).unit.boundary (k + 1) true) :=
    (boundary_unit hPa.dim_eq true).symm
  have hdx₀u : (P.app (K.app a)).unit.dim = k + 1 + 1 := by rw [dim_unit, hPa.dim_eq]
  have hY : IsRoundCtxOn ⟨k + 1, a, b⟩ ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩
      (.comp (CtxExpr.paste false (P.app (K.app a)).unit (k + 1)) (.comp P K)) :=
    (isRoundCtxOn_comp_paste false hPKp (isRound_unit hPa.isRound) hdx₀u hx₀u).congr (.refl _)
      ⟨rfl, boundary_unit hPa.dim_eq false, .refl _⟩
  have hU1 : IsRoundCtxOn ⟨k + 1, a, b⟩ ⟨k + 1, P.app (K.app a), Q.app (K.app b)⟩
      (.comp (CtxExpr.paste false θ' (k + 1)) (.comp Q K)) :=
    (isRoundCtxOn_comp_paste false hQKp hθ' htθ'.dim_h hθt').congr (.refl _)
      ⟨rfl, htθ'.side, .refl _⟩
  have L1 := Sim.unit false (A := A) hU (RoundHom.ofIsRoundIn ha hb)
    (RoundHom.ofIsRoundIn hPa hQb) hT1
  have L2 := (Sim.paste_app_unit hA hU (RoundHom.ofIsRoundIn ha hb)
    (RoundHom.ofIsRoundIn hPa hPb) hP.typed hb' rfl (.refl _) hY).left
      (⟨hθR, isRoundCtx_of_trim hθR⟩ : IsRoundCtxOn ⟨k + 1, P.app (K.app a), P.app (K.app b)⟩
        ⟨k + 1, P.app (K.app a), Q.app (K.app b)⟩ (CtxExpr.paste true θ (k + 1)))
  have L3 := (Sim.unit false (A := A) hU (RoundHom.ofIsRoundIn ha hb)
    (RoundHom.ofIsRoundIn hPa hQb) hT2).symm hA
  have Rt := (Sim.paste_app_unit hA hU (RoundHom.ofIsRoundIn ha hb)
    (RoundHom.ofIsRoundIn hPa hQb) hQ.typed hb' rfl (.refl _) hU1).symm hA
  have hεb := hb'.inHom.unit hdb'
  have pst : ∀ {x y : PastingDiagram X}, (x.boundary (k + 1) true).Equiv
      (y.boundary (k + 1) false) → k + 1 < x.dim → k + 1 < y.dim → x.Pastable y (k + 1) :=
    fun h hx hy => ⟨h, lt_min hx hy⟩
  have dP : ∀ c, InHom ⟨k + 1, a, b⟩ c → k + 1 < (P.app (K.app c)).dim := fun c hc =>
    (hPKp.mapsInto c hc).lt_dim
  have dQ : ∀ c, InHom ⟨k + 1, a, b⟩ c → k + 1 < (Q.app (K.app c)).dim := fun c hc =>
    (hQKp.mapsInto c hc).lt_dim
  have hdPu : k + 1 < (P.app (K.app b).unit).dim := by
    rw [hP.typed.ctxLaws.dim_eq _ hεb, hdu]; omega
  have hdQu : k + 1 < (Q.app (K.app b).unit).dim := by
    rw [hQ.typed.ctxLaws.dim_eq _ hεb, hdu]; omega
  have hdθ : k + 1 < θ.dim := by rw [htθ.dim_h]; omega
  have hdθ' : k + 1 < θ'.dim := by rw [htθ'.dim_h]; omega
  have hdx : k + 1 < (P.app (K.app a)).unit.dim := by rw [hdx₀u]; omega
  have hlt : ∀ {x y : PastingDiagram X} (hp : x.Pastable y (k + 1)), k + 1 < x.dim →
      k + 1 < (x.paste y (k + 1) hp).dim := fun hp hx => by
    rw [dim_paste]; exact lt_of_lt_of_le hx (le_max_left _ _)
  have sPR : ∀ {t : CtxExpr X} {v₂ w₂ : PastingDiagram X}, t.Typed Set.univ True ⟨k, v, w⟩ ⟨k, v₂,
      w₂⟩ →
      ∀ c, InHom ⟨k + 1, a, b⟩ c → ∃ q : (t.app (K.app c)).Pastable (t.app (K.app b).unit) (k + 1),
        (t.app ((CtxExpr.paste true (K.app b).unit (k + 1)).app (K.app c))).Equiv
          ((t.app (K.app c)).paste (t.app (K.app b).unit) (k + 1) q) := by
    intro t v₂ w₂ ht c hc
    have hKc := hKp.mapsInto c hc
    have q1 : (K.app c).Pastable (K.app b).unit (k + 1) :=
      pst (hKc.target.trans hRb) hKc.lt_dim (by omega)
    obtain ⟨q2, e2⟩ := ht.ctxLaws.paste (K.app c) (K.app b).unit q1
      ((hK.typed.mapsInto c (hc.of_inHom_succ ha.inHom hb.inHom)).of_paste false
        (Nat.lt_succ_self k) q1) (Nat.lt_succ_self k)
    exact ⟨q2, (CtxExpr.app_equiv t (CtxExpr.paste_app true q1)).trans e2⟩
  have E1 : ∀ c, InHom ⟨k + 1, a, b⟩ c →
      ((CtxExpr.paste true θ (k + 1)).app ((CtxExpr.comp (CtxExpr.paste false
        (P.app (K.app a)).unit (k + 1)) (.comp P K)).app c)).Equiv
      ((P.app (K.app a)).unit.pasteOr ((CtxExpr.comp (CtxExpr.paste true θ (k + 1))
        (.comp P K)).app c) (k + 1)) := by
    intro c hc
    have hPKc := hPKp.mapsInto c hc
    have p3 : (P.app (K.app a)).unit.Pastable (P.app (K.app c)) (k + 1) :=
      pst ((boundary_unit hPa.dim_eq true).trans
        (hPKc.source.symm)) hdx (dP c hc)
    have p4 : ((P.app (K.app a)).unit.paste (P.app (K.app c)) (k + 1) p3).Pastable θ (k + 1) :=
      pst ((equiv_boundary_paste p3 true).trans
        (hPKc.target.trans hθs)) (hlt p3 hdx) hdθ
    obtain ⟨h₃, h₄, hassoc⟩ := equiv_paste_assoc p3 p4
    have p5 := Pastable.of_equiv p4 ((CtxExpr.paste_app false p3).symm)
      (.refl θ)
    have p2 := Pastable.of_equiv h₄ (.refl _)
      ((CtxExpr.paste_app true h₃).symm)
    change ((CtxExpr.paste true θ (k + 1)).app ((CtxExpr.paste false (P.app (K.app a)).unit
      (k + 1)).app (P.app (K.app c)))).Equiv ((P.app (K.app a)).unit.pasteOr
        ((CtxExpr.paste true θ (k + 1)).app (P.app (K.app c))) (k + 1))
    rw [PastingDiagram.pasteOr_of p2]
    exact (CtxExpr.paste_app true p5).trans
      ((Equiv.paste (CtxExpr.paste_app false p3) (.refl _) p5 p4).trans (hassoc.trans
          (Equiv.paste (.refl _) ((CtxExpr.paste_app true h₃).symm) h₄ p2)))
  have E2 : ∀ c, InHom ⟨k + 1, a, b⟩ c →
      ((CtxExpr.paste true θ (k + 1)).app (((CtxExpr.comp (CtxExpr.paste false
        (P.app (K.app a)).unit (k + 1)) (.comp P K)).app c).pasteOr
          (P.app (K.app b).unit) (k + 1))).Equiv
      ((P.app (K.app a)).unit.pasteOr ((CtxExpr.comp (CtxExpr.paste true θ (k + 1))
        (.comp P (.comp (CtxExpr.paste true (K.app b).unit (k + 1)) K))).app c) (k + 1)) := by
    intro c hc
    have hPKc := hPKp.mapsInto c hc
    obtain ⟨q2, e2⟩ := sPR hP.typed c hc
    have p3 : (P.app (K.app a)).unit.Pastable (P.app (K.app c)) (k + 1) :=
      pst ((boundary_unit hPa.dim_eq true).trans
        (hPKc.source.symm)) hdx (dP c hc)
    have q6 : ((P.app (K.app a)).unit.paste (P.app (K.app c)) (k + 1) p3).Pastable
        (P.app (K.app b).unit) (k + 1) :=
      pst ((equiv_boundary_paste p3 true).trans q2.1) (hlt p3 hdx) hdPu
    obtain ⟨h₅, h₆, hassoc2⟩ := equiv_paste_assoc p3 q6
    have p6 := Pastable.of_equiv q6
      ((CtxExpr.paste_app false (u := (P.app (K.app a)).unit) p3).symm) (.refl _)
    let PR := P.app ((CtxExpr.paste true (K.app b).unit (k + 1)).app (K.app c))
    have ePR : PR.Equiv ((P.app (K.app c)).paste (P.app (K.app b).unit) (k + 1) q2) := e2
    have p8 := Pastable.of_equiv h₆ (.refl _) (ePR.symm)
    have hdPR : k + 1 < PR.dim := by rw [dim_eq_of_equiv ePR]; exact hlt q2 (dP c hc)
    have hPu : ((P.app (K.app b).unit).boundary (k + 1) true).Equiv (P.app (K.app b)) :=
      (hP.typed.ctxLaws.boundary _ hεb (Nat.lt_succ_self k)
        (by rw [dim_unit]; omega) true).trans
        (CtxExpr.app_equiv P (boundary_unit hdb' true))
    have hPRt : (PR.boundary (k + 1) true).Equiv (θ.boundary (k + 1) false) :=
      (ePR.boundary _ _).trans (PastingDiagram.Equiv.trans
        (equiv_boundary_paste q2 true) (hPu.trans hθs))
    have p9 : ((P.app (K.app a)).unit.paste PR (k + 1) p8).Pastable θ (k + 1) :=
      pst ((equiv_boundary_paste p8 true).trans hPRt) (hlt p8 hdx) hdθ
    obtain ⟨h₇, h₈, hassoc3⟩ := equiv_paste_assoc p8 p9
    have p10 := Pastable.of_equiv h₈ (.refl _)
      ((CtxExpr.paste_app true h₇).symm)
    have ea : PastingDiagram.Equiv (((CtxExpr.paste false (P.app (K.app a)).unit (k + 1)).app
        (P.app (K.app c))).pasteOr (P.app (K.app b).unit) (k + 1))
        ((P.app (K.app a)).unit.paste PR (k + 1) p8) := by
      rw [PastingDiagram.pasteOr_of p6]
      exact (Equiv.paste (CtxExpr.paste_app false p3) (.refl _) p6 q6).trans (hassoc2.trans
          (Equiv.paste (.refl _) (ePR.symm) h₆ p8))
    change ((CtxExpr.paste true θ (k + 1)).app (((CtxExpr.paste false (P.app (K.app a)).unit
      (k + 1)).app (P.app (K.app c))).pasteOr (P.app (K.app b).unit) (k + 1))).Equiv
      ((P.app (K.app a)).unit.pasteOr ((CtxExpr.paste true θ (k + 1)).app PR) (k + 1))
    rw [PastingDiagram.pasteOr_of p10]
    exact (CtxExpr.app_equiv _ ea).trans (PastingDiagram.Equiv.trans
      (CtxExpr.paste_app true p9) (hassoc3.trans
        (Equiv.paste (.refl _) ((CtxExpr.paste_app true h₇).symm) h₈ p10)))
  have E3 : ∀ c, InHom ⟨k + 1, a, b⟩ c →
      (((CtxExpr.comp (CtxExpr.paste false θ' (k + 1)) (.comp Q K)).app c).pasteOr
        (Q.app (K.app b).unit) (k + 1)).Equiv
      ((CtxExpr.paste false θ' (k + 1)).app
        (Q.app ((CtxExpr.paste true (K.app b).unit (k + 1)).app (K.app c)))) := by
    intro c hc
    have hQKc := hQKp.mapsInto c hc
    obtain ⟨q2, e2⟩ := sPR hQ.typed c hc
    have r1 : θ'.Pastable (Q.app (K.app c)) (k + 1) :=
      pst (htθ'.other.trans (hQKc.source.symm)) hdθ'
        (dQ c hc)
    have r3 : (θ'.paste (Q.app (K.app c)) (k + 1) r1).Pastable (Q.app (K.app b).unit) (k + 1) :=
      pst ((equiv_boundary_paste r1 true).trans q2.1) (hlt r1 hdθ') hdQu
    obtain ⟨h₉, h₁₀, hassoc4⟩ := equiv_paste_assoc r1 r3
    have r2 := Pastable.of_equiv r3 ((CtxExpr.paste_app false r1).symm)
      (.refl _)
    have r4 := Pastable.of_equiv h₁₀ (.refl _) (e2.symm)
    change (((CtxExpr.paste false θ' (k + 1)).app (Q.app (K.app c))).pasteOr
      (Q.app (K.app b).unit) (k + 1)).Equiv _
    rw [PastingDiagram.pasteOr_of r2]
    exact (Equiv.paste (CtxExpr.paste_app false r1) (.refl _) r2 r3).trans
      (hassoc4.trans (PastingDiagram.Equiv.trans
        (Equiv.paste (.refl _) (e2.symm) h₁₀ r4)
        ((CtxExpr.paste_app false r4).symm)))
  exact ((L1.trans ((L2.of_equiv E1 E2).trans L3)).trans S1).trans
    (Rt.of_equiv E3 (fun _ _ => .refl _))

end CtxTriple

end Atoms.Diagrammatic
