import Atoms.Diagrammatic.Context.Pushforward

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

def pfwTriples (X : DiagSet.{u}) : Set (CtxTriple X) :=
  {τ | ∃ (α : Bool) (H : RoundHom X) (x x' h : PastingDiagram X), PfwSpec H.k x x' h ∧
    (x.boundary H.k (!α)).Equiv (H.side α) ∧ τ = ctxPfw α H x x' h}

theorem valid_of_mem_pfwTriples {τ : CtxTriple X} (h : τ ∈ pfwTriples X) : τ.Valid := by
  obtain ⟨α, H, x, x', h, hs, hx, rfl⟩ := h
  exact hs.valid α hx

theorem valid_of_mem_cylTriples {τ : CtxTriple X} (h : τ ∈ cylTriples X) : τ.Valid :=
  h.choose_spec.valid

theorem subset_natOp_closure {A : Set (CtxTriple X)} (hA : ∀ τ ∈ A, τ.Valid)
    (hU : cylTriples X ⊆ A) :
    cylTriples X ∪ pfwTriples X ⊆ CtxTriple.natOp (CtxTriple.Closure A) := by
  rintro τ (hτ | hτ)
  · exact CtxTriple.natOp_mono (fun σ hσ => CtxTriple.Closure.base (hU hσ))
      (cylTriples_subset_natOp hτ)
  · obtain ⟨α, H, x, x', h, hs, hx, rfl⟩ := hτ
    exact hs.mem_natOp α hA hU hx

namespace CtxExpr

theorem paste_app_pasteOr (α : Bool) {u x : PastingDiagram X} {n : ℕ}
    (hp : (cond α x u).Pastable (cond α u x) n) :
    ((paste α u n).app x).Equiv ((cond α x u).pasteOr (cond α u x) n) := by
  rw [PastingDiagram.pasteOr_of hp]
  exact paste_app α hp

theorem paste_app_paste (α : Bool) {n : ℕ} {x u v : PastingDiagram X}
    (hxu : (cond α x u).Pastable (cond α u x) n) (huv : (cond α u v).Pastable (cond α v u) n) :
    ((paste α v n).app ((paste α u n).app x)).Equiv
      ((paste α ((cond α u v).pasteOr (cond α v u) n) n).app x) := by
  cases α <;> simp only [cond_false, cond_true] at hxu huv ⊢
  · have h₂ := Pastable.paste_left huv hxu
    obtain ⟨h₃, h₄, e⟩ := equiv_paste_assoc huv h₂
    rw [PastingDiagram.pasteOr_of huv]
    exact (app_equiv _ (paste_app false hxu)).trans
      ((paste_app false h₄).trans (e.symm.trans ((paste_app false h₂).symm)))
  · have h₂ := Pastable.paste_left hxu huv
    obtain ⟨h₃, h₄, e⟩ := equiv_paste_assoc hxu h₂
    rw [PastingDiagram.pasteOr_of h₃]
    exact (app_equiv _ (paste_app true hxu)).trans
      ((paste_app true h₂).trans (e.trans ((paste_app true h₄).symm)))

theorem pasteRight_app_pasteLeft {n : ℕ} {x u v : PastingDiagram X} (hvx : v.Pastable x n)
    (hxu : x.Pastable u n) :
    ((paste true u n).app ((paste false v n).app x)).Equiv
      ((paste false v n).app ((paste true u n).app x)) := by
  have h₂ := Pastable.paste_left hvx hxu
  obtain ⟨h₃, h₄, e⟩ := equiv_paste_assoc hvx h₂
  exact (app_equiv _ (paste_app false hvx)).trans
    ((paste_app true h₂).trans
      (e.trans (PastingDiagram.Equiv.trans
        ((paste_app false h₄).symm)
        (app_equiv _ ((paste_app true hxu).symm)))))

variable {A : Set (RoundPastingDiagram X)} {p : Prop}

theorem Typed.app_paste (α : Bool) {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H')
    {y u : PastingDiagram X} (hy : InHom H y)
    (hp : (cond α y u).Pastable (cond α u y) (H.k + 1)) :
    (t.app ((paste α u (H.k + 1)).app y)).Equiv
      ((paste α (t.app u) (H.k + 1)).app (t.app y)) := by
  cases α
  · obtain ⟨hp', e⟩ := ht.ctxLaws.paste u y hp
      (InHom.of_paste true hy (Nat.lt_succ_self H.k) hp) (Nat.lt_succ_self H.k)
    exact (app_equiv t (paste_app false hp)).trans (e.trans ((paste_app false hp').symm))
  · obtain ⟨hp', e⟩ := ht.ctxLaws.paste y u hp
      (InHom.of_paste false hy (Nat.lt_succ_self H.k) hp) (Nat.lt_succ_self H.k)
    exact (app_equiv t (paste_app true hp)).trans (e.trans ((paste_app true hp').symm))

theorem Typed.hasType_app {H H' : PdHom X} {t : CtxExpr X} (ht : t.Typed A p H H')
    {θ x y : PastingDiagram X} (hθ : HasBdry false (H.k + 1) θ x y) (hx : InHom H x)
    (hy : InHom H y) : HasBdry false (H.k + 1) (t.app θ) (t.app x) (t.app y) := by
  have L := ht.ctxLaws
  have hin := InHom.of_hasBdry hθ hx
  exact ⟨(L.dim_eq _ hin).trans hθ.dim_h, (L.dim_eq _ hx).trans hθ.dim_a,
    (L.dim_eq _ hy).trans hθ.dim_b,
    (L.boundary _ hin (Nat.lt_succ_self H.k) (by rw [hθ.dim_h]; omega)
      false).trans (app_equiv t hθ.side),
    (L.boundary _ hin (Nat.lt_succ_self H.k) (by rw [hθ.dim_h]; omega)
      true).trans (app_equiv t hθ.other)⟩

end CtxExpr

theorem isRoundCtxOn_paste (α : Bool) (H : PdHom X) {u : PastingDiagram X} (hu : u.IsRound)
    (hdu : u.dim = H.k + 1) (hb : (H.side α).Equiv (u.boundary H.k (!α))) :
    IsRoundCtxOn H (H.setSide α (u.boundary H.k α)) (CtxExpr.paste α u H.k) :=
  ⟨CtxExpr.typed_paste α (u := ⟨u, hu⟩) (Set.mem_univ _) hdu hb,
    isRoundCtx_of_trim (CtxExpr.typed_paste α (A := Set.univ) (p := False) (u := ⟨u, hu⟩)
      (Set.mem_univ _) hdu hb)⟩

namespace CtxTriple

variable {A : Set (CtxTriple X)}

theorem Sim.unit_nat (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) {H H' : PdHom X}
    {K : CtxExpr X} (hK : IsRoundCtxOn H H' K) {a b : PastingDiagram X} (ha : IsRoundIn H a)
    (hb : IsRoundIn H b) :
    Sim (Closure A) ⟨H.k + 1, a, b⟩ ⟨H.k + 1, K.app a, K.app b⟩
      (fun c => (CtxExpr.paste true (K.app b).unit (H.k + 1)).app (K.app c))
      (fun c => (CtxExpr.paste false (K.app a).unit (H.k + 1)).app (K.app c)) := by
  obtain ⟨k, v, w⟩ := H
  obtain ⟨k', v', w'⟩ := H'
  have e : k = k' := hK.typed.k_eq.symm
  subst e
  have hKa := hK.isRoundIn ha
  have hKb := hK.isRoundIn hb
  have hσ := Sim.of_mem (A := A) (hU ⟨_, (isCylTriple_unit hKa.roundHom).next hKa hKb⟩)
  exact Sim.round_right hA hU hK isRoundCtxOn_id isRoundCtxOn_id ha hb (isRound_unit hKb.isRound)
    (isRound_unit hKa.isRound) (hasType_unit hKb.dim_eq)
    (hasType_unit hKa.dim_eq) hσ

theorem natOp_comp {τ₁ τ₂ : CtxTriple X} (h₁ : τ₁ ∈ natOp (Closure A))
    (h₂ : τ₂ ∈ natOp (Closure A)) (hm : τ₂.Realizes τ₁.dom τ₁.cod τ₁.G.app τ₂.G.app) :
    (⟨τ₁.dom, τ₁.cod, τ₁.F, τ₂.G, fun a => (τ₁.ϑ a).pasteOr (τ₂.ϑ a) (τ₁.dom.k + 1)⟩ :
      CtxTriple X) ∈ natOp (Closure A) := by
  refine ⟨Closure.valid (A := {σ | σ.Valid}) (fun _ h => h) (.comp (.base h₁.1) (.base h₂.1) hm),
    fun a b ha hb => ?_⟩
  obtain ⟨D, C, F, G, ϑ⟩ := τ₁
  obtain ⟨⟨⟨k₂, v₂, w₂⟩, hv₂r, hw₂r, hdv₂, hp₂⟩, C₂, G₂, H, ψ⟩ := τ₂
  obtain rfl : k₂ = D.k := hm.equiv_dom.k_eq
  obtain ⟨hv₁, N₁⟩ := h₁
  obtain ⟨hv₂, N₂⟩ := h₂
  change IsRoundIn D a at ha
  change IsRoundIn D b at hb
  have ha₂ : IsRoundIn ⟨D.k, v₂, w₂⟩ a := ha.congr hm.equiv_dom.symm
  have hb₂ : IsRoundIn ⟨D.k, v₂, w₂⟩ b := hb.congr hm.equiv_dom.symm
  obtain ⟨hrϑa, -, tϑa⟩ := hv₁.comp a ha
  obtain ⟨-, -, tϑb⟩ := hv₁.comp b hb
  obtain ⟨-, -, tψa⟩ := hv₂.comp a ha₂
  obtain ⟨hrψb, -, tψb⟩ := hv₂.comp b hb₂
  have eGa : (G₂.app a).Equiv (G.app a) := hm.equiv_F a ha.inHom
  have eGb : (G₂.app b).Equiv (G.app b) := hm.equiv_F b hb.inHom
  have hFp := hv₁.ctxF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGp := hv₁.ctxG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hHp := hv₂.ctxG.typed.promote_of_inHom trivial ha₂.inHom hb₂.inHom
  have hK₁ : IsRoundCtxOn ⟨D.k + 1, F.app a, G.app b⟩ ⟨D.k + 1, F.app a, H.app b⟩
      (CtxExpr.paste true (ψ b) (D.k + 1)) :=
    (isRoundCtxOn_paste true ⟨D.k + 1, F.app a, G.app b⟩ hrψb tψb.dim_h
      (eGb.symm.trans tψb.side.symm)).congr (.refl _)
      ⟨rfl, .refl _, tψb.other⟩
  have hK₂ : IsRoundCtxOn ⟨D.k + 1, G₂.app a, H.app b⟩ ⟨D.k + 1, F.app a, H.app b⟩
      (CtxExpr.paste false (ϑ a) (D.k + 1)) :=
    (isRoundCtxOn_paste false ⟨D.k + 1, G₂.app a, H.app b⟩ hrϑa tϑa.dim_h
      (eGa.trans tϑa.other.symm)).congr (.refl _)
      ⟨rfl, tϑa.side, .refl _⟩
  refine ((Sim.left (N₁ a b ha hb) hK₁).trans_of_equiv (Sim.left (N₂ a b ha₂ hb₂) hK₂)
    (fun c hc => ?_)).of_equiv (fun c hc => ?_) (fun c hc => ?_)
  · have hGc := hGp.mapsInto c hc
    exact (CtxExpr.pasteRight_app_pasteLeft
      (tϑa.pastable_inHom hGc (.refl _))
      (hGc.pastable_hasType tψb (eGb.symm))).trans
      (CtxExpr.app_equiv (CtxExpr.paste false (ϑ a) (D.k + 1))
        (CtxExpr.app_equiv (CtxExpr.paste true (ψ b) (D.k + 1)) (PastingDiagram.Equiv.symm
          (hm.equiv_F c (InHom.of_inHom_succ hc ha.inHom hb.inHom)))))
  · exact CtxExpr.paste_app_paste true
      ((hFp.mapsInto c hc).pastable_hasType tϑb (.refl _))
      (tϑb.pastable tψb (eGb.symm))
  · exact CtxExpr.paste_app_paste false
      (tψa.pastable_inHom (hHp.mapsInto c hc) (.refl _))
      (tϑa.pastable tψa (eGa.symm))

theorem natOp_left (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) {τ : CtxTriple X}
    (h : τ ∈ natOp (Closure A)) {H : CtxExpr X} {C : PdHom X} (hH : IsRoundCtxOn τ.cod C H) :
    (⟨τ.dom, C, .comp H τ.F, .comp H τ.G,
      fun a => (H.app (τ.ϑ a)).pasteOr (H.app (τ.G.app a)).unit (τ.dom.k + 1)⟩ : CtxTriple X) ∈
      natOp (Closure A) := by
  refine ⟨Closure.valid (A := {σ | σ.Valid}) (fun _ h => h) (.left (.base h.1) hH),
    fun a b ha hb => ?_⟩
  obtain ⟨D, ⟨k', v', w'⟩, F, G, ϑ⟩ := τ
  obtain ⟨k'', v'', w''⟩ := C
  obtain ⟨hv, N⟩ := h
  obtain rfl : k' = D.k := hv.ctxF.typed.k_eq
  obtain rfl : k'' = D.k := hH.typed.k_eq
  change IsRoundIn D a at ha
  change IsRoundIn D b at hb
  have hFa := hv.ctxF.isRoundIn ha
  have hFb := hv.ctxF.isRoundIn hb
  have hGa := hv.ctxG.isRoundIn ha
  have hGb := hv.ctxG.isRoundIn hb
  have hHF : IsRoundCtxOn D ⟨D.k, v'', w''⟩ (.comp H F) := hv.ctxF.comp hH
  have hHG : IsRoundCtxOn D ⟨D.k, v'', w''⟩ (.comp H G) := hv.ctxG.comp hH
  have hHGa := hHG.isRoundIn ha
  have hHGb := hHG.isRoundIn hb
  obtain ⟨-, -, tϑa⟩ := hv.comp a ha
  obtain ⟨-, -, tϑb⟩ := hv.comp b hb
  have tHϑa := hH.typed.hasType_app tϑa hFa.inHom hGa.inHom
  have tHϑb := hH.typed.hasType_app tϑb hFb.inHom hGb.inHom
  have uGa := hasType_unit hHGa.dim_eq
  have uGb := hasType_unit hHGb.dim_eq
  have hFp := hv.ctxF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGp := hv.ctxG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hHFp := hHF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hHGp := hHG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hHp := hH.typed.promote_of_inHom trivial hFa.inHom hGb.inHom
  have hK₁ : IsRoundCtxOn ⟨D.k + 1, F.app a, G.app b⟩ ⟨D.k + 1, H.app (F.app a), H.app
      (G.app b)⟩ (.comp (CtxExpr.paste true (H.app (G.app b)).unit (D.k + 1)) H) :=
    (isRoundCtxOn_comp_paste true hHp (isRound_unit hHGb.isRound) uGb.dim_h
      (uGb.side.symm)).congr (.refl _) ⟨rfl, .refl _, uGb.other⟩
  set t := (H.app (ϑ a)).frameCtx false tHϑa.dim_h
  have happ := (H.app (ϑ a)).frameCtx_app false tHϑa.dim_h
  have htt := (H.app (ϑ a)).typed_frameCtx false
    (H := ⟨D.k + 1, H.app (G.app a), H.app (G.app b)⟩) tHϑa.dim_h (tHϑa.other.symm)
  have hT : IsRoundCtxOn ⟨D.k + 1, H.app (G.app a), H.app (G.app b)⟩ ⟨D.k + 1, H.app (F.app
      a), H.app (G.app b)⟩ t :=
    ⟨(htt.mono (Set.subset_univ _) (fun _ => trivial)).congr_codomain ⟨rfl, tHϑa.side, .refl _⟩,
        isRoundCtx_of_trim htt⟩
  have hframe : ∀ y (hq : (H.app (ϑ a)).Pastable y (D.k + 1)),
      ((CtxExpr.paste false (H.app (ϑ a)) (D.k + 1)).app y).Equiv (t.app y) := fun y hq =>
    (CtxExpr.paste_app false hq).trans ((happ y hq).symm)
  refine ((Sim.left (N a b ha hb) hK₁).trans_of_equiv ((Sim.unit_nat hA hU hHG ha hb).left hT)
    (fun c hc => ?_)).of_equiv (fun c hc => ?_) (fun c hc => ?_)
  · have hGc := hGp.mapsInto c hc
    have hHGc := hHGp.mapsInto c hc
    have p₁ : (H.app (ϑ a)).Pastable (H.app (G.app c)) (D.k + 1) :=
      tHϑa.pastable_inHom hHGc (.refl _)
    have p₂ : (H.app (G.app c)).Pastable (H.app (G.app b)).unit (D.k + 1) :=
      hHGc.pastable_hasType uGb (.refl _)
    exact (CtxExpr.app_equiv
      (CtxExpr.paste true (H.app (G.app b)).unit (D.k + 1)) (hH.typed.app_paste false
      (InHom.of_inHom_succ hGc hGa.inHom hGb.inHom)
      (tϑa.pastable_inHom hGc (.refl _)))).trans
      ((CtxExpr.pasteRight_app_pasteLeft p₁ p₂).trans
        (hframe _ (Pastable.of_equiv (Pastable.paste_right p₁ p₂) (.refl _)
          ((CtxExpr.paste_app true p₂).symm))))
  · have hFc := hFp.mapsInto c hc
    exact (CtxExpr.app_equiv
      (CtxExpr.paste true (H.app (G.app b)).unit (D.k + 1)) (hH.typed.app_paste true
      (InHom.of_inHom_succ hFc hFa.inHom hFb.inHom)
      (hFc.pastable_hasType tϑb (.refl _)))).trans
      (CtxExpr.paste_app_paste true
        ((hHFp.mapsInto c hc).pastable_hasType tHϑb (.refl _))
        (tHϑb.pastable uGb (.refl _)))
  · have hHGc := hHGp.mapsInto c hc
    have r₁ : (H.app (ϑ a)).Pastable (H.app (G.app a)).unit (D.k + 1) :=
      tHϑa.pastable uGa (.refl _)
    have r₂ : (H.app (G.app a)).unit.Pastable (H.app (G.app c)) (D.k + 1) :=
      uGa.pastable_inHom hHGc (.refl _)
    exact ((hframe _
      (Pastable.of_equiv (Pastable.paste_right r₁ r₂) (.refl _)
        ((CtxExpr.paste_app false r₂).symm))).symm).trans
      (CtxExpr.paste_app_paste false r₂ r₁)

theorem natOp_right (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) {τ : CtxTriple X}
    (h : τ ∈ natOp (Closure A)) {K : CtxExpr X} {D : RoundHom X} (hK : IsRoundCtxOn D τ.dom K) :
    (⟨D, τ.cod, .comp τ.F K, .comp τ.G K, fun a => τ.ϑ (K.app a)⟩ : CtxTriple X) ∈
      natOp (Closure A) := by
  refine ⟨Closure.valid (A := {σ | σ.Valid}) (fun _ h => h) (.right (.base h.1) hK),
    fun a b ha hb => ?_⟩
  obtain ⟨⟨k, v₀, w₀⟩, hv₀, hw₀, hdv, hpar⟩ := D
  obtain rfl : τ.dom.k = k := hK.typed.k_eq
  obtain ⟨hv, N⟩ := h
  change IsRoundIn ⟨τ.dom.k, v₀, w₀⟩ a at ha
  change IsRoundIn ⟨τ.dom.k, v₀, w₀⟩ b at hb
  have hKa := hK.isRoundIn ha
  have hKb := hK.isRoundIn hb
  obtain ⟨hrb, -, tb⟩ := hv.comp _ hKb
  obtain ⟨hra, -, ta⟩ := hv.comp _ hKa
  exact Sim.round_right hA hU hK hv.ctxF hv.ctxG ha hb hrb hra tb ta (N _ _ hKa hKb)

theorem natOp_inv (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A) (hP : pfwTriples X ⊆ A)
    {τ : CtxTriple X} (h : τ ∈ natOp (Closure A)) {ϑ' : PastingDiagram X → PastingDiagram X}
    (hϑ' : ∀ a, IsRoundIn τ.dom a → IsWeakInverse (τ.ϑ a) (ϑ' a)) :
    (⟨τ.dom, τ.cod, τ.G, τ.F, ϑ'⟩ : CtxTriple X) ∈ natOp (Closure A) := by
  refine ⟨Closure.valid (A := {σ | σ.Valid}) (fun _ h => h) (.inv (.base h.1) hϑ'),
    fun a b ha hb => ?_⟩
  obtain ⟨D, ⟨k', v', w'⟩, F, G, ϑ⟩ := τ
  obtain ⟨hv, N⟩ := h
  obtain rfl : k' = D.k := hv.ctxF.typed.k_eq
  change IsRoundIn D a at ha
  change IsRoundIn D b at hb
  have hFa := hv.ctxF.isRoundIn ha
  have hFb := hv.ctxF.isRoundIn hb
  have hGa := hv.ctxG.isRoundIn ha
  have hGb := hv.ctxG.isRoundIn hb
  obtain ⟨hra, -, tϑa⟩ := hv.comp a ha
  obtain ⟨hrb, -, tϑb⟩ := hv.comp b hb
  obtain ⟨hr'a, tϑ'a, -, ⟨ha', hha', hma', tha'⟩⟩ := (hϑ' a ha).spec tϑa
  obtain ⟨hr'b, tϑ'b, ⟨zb, hzb, hmzb, tzb⟩, -⟩ := (hϑ' b hb).spec tϑb
  have uGa := hasType_unit hGa.dim_eq
  have uFb := hasType_unit hFb.dim_eq
  have hFp := hv.ctxF.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hGp := hv.ctxG.typed.promote_of_inHom trivial ha.inHom hb.inHom
  have hR₁ : IsRoundCtxOn ⟨D.k + 1, a, b⟩ ⟨D.k + 1, G.app a, F.app b⟩ (.comp (CtxExpr.paste
      true (ϑ' b) (D.k + 1)) G) :=
    (isRoundCtxOn_comp_paste true hGp hr'b tϑ'b.dim_h (tϑ'b.side.symm)).congr (.refl _) ⟨rfl, .refl
        _, tϑ'b.other⟩
  have hR₄ : IsRoundCtxOn ⟨D.k + 1, a, b⟩ ⟨D.k + 1, G.app a, F.app b⟩ (.comp (CtxExpr.paste
      false (ϑ' a) (D.k + 1)) F) :=
    (isRoundCtxOn_comp_paste false hFp hr'a tϑ'a.dim_h (tϑ'a.other.symm)).congr (.refl _) ⟨rfl,
        tϑ'a.side, .refl _⟩
  have hK₃ : IsRoundCtxOn ⟨D.k + 1, F.app a, G.app b⟩ ⟨D.k + 1, G.app a, F.app b⟩ (.comp
      (CtxExpr.paste false (ϑ' a) (D.k + 1)) (CtxExpr.paste true (ϑ' b) (D.k + 1))) :=
    (isRoundCtxOn_comp_paste false (CtxExpr.typed_paste true (u := ⟨ϑ' b, hr'b⟩)
      (H := ⟨D.k + 1, F.app a, G.app b⟩) (Set.mem_univ _)
      tϑ'b.dim_h (tϑ'b.side.symm)) hr'a tϑ'a.dim_h
      (tϑ'a.other.symm)).congr (.refl _) ⟨rfl, tϑ'a.side, tϑ'b.other⟩
  have tx' := tϑ'a.pasteOr tϑa (.refl _)
  have tx := tϑb.pasteOr tϑ'b (.refl _)
  have hrx' := tϑ'a.isRound_pasteOr tϑa (.refl _) hr'a hra
  have hrx := tϑb.isRound_pasteOr tϑ'b (.refl _) hrb hr'b
  have hσ₂ : ctxPfw false (RoundHom.ofIsRoundIn hGa hFb) (G.app a).unit
      ((ϑ' a).pasteOr (ϑ a) (D.k + 1)) ha' ∈ pfwTriples X :=
    ⟨false, RoundHom.ofIsRoundIn hGa hFb, _, _, _, ⟨hha', hma', tha'⟩, uGa.other, rfl⟩
  have hσ₄ : ctxPfw true (RoundHom.ofIsRoundIn hGa hFb) ((ϑ b).pasteOr (ϑ' b) (D.k + 1))
      (F.app b).unit zb ∈ pfwTriples X :=
    ⟨true, RoundHom.ofIsRoundIn hGa hFb, _, _, _, ⟨hzb, hmzb, tzb⟩, tx.side, rfl⟩
  have S₂ := ((Sim.of_mem (A := A) (hP hσ₂)).right (RoundHom.ofIsRoundIn ha hb) hR₁).congr
    (H₁' := ⟨D.k + 1, G.app a, F.app b⟩) (.refl _) ⟨rfl, uGa.side, .refl _⟩
  have S₄ := ((Sim.of_mem (A := A) (hP hσ₄)).right (RoundHom.ofIsRoundIn ha hb) hR₄).congr
    (H₁' := ⟨D.k + 1, G.app a, F.app b⟩) (.refl _) ⟨rfl, .refl _, tx.other⟩
  refine (((((Sim.unit false hU (RoundHom.ofIsRoundIn ha hb) (RoundHom.ofIsRoundIn hGa hFb)
    hR₁).trans_of_equiv S₂ (fun c hc => ?_)).trans_of_equiv ((Sim.left (N a b ha hb) hK₃).symm hA)
      (fun c hc => ?_)).trans_of_equiv S₄ (fun c hc => ?_)).trans_of_equiv
    (Sim.unit true hU (RoundHom.ofIsRoundIn ha hb) (RoundHom.ofIsRoundIn hGa hFb) hR₄)
      (fun c hc => ?_))
  · exact (CtxExpr.paste_app_pasteOr false
      (uGa.pastable_inHom (hR₁.typed.mapsInto c hc) (.refl _))).symm
  · have hGc := hGp.mapsInto c hc
    exact ((CtxExpr.paste_app_paste false
      (tϑa.pastable_inHom (hR₁.typed.mapsInto c hc) (.refl _))
      (tϑ'a.pastable tϑa (.refl _))).symm).trans
      (CtxExpr.app_equiv (CtxExpr.paste false (ϑ' a) (D.k + 1))
        ((CtxExpr.pasteRight_app_pasteLeft
        (tϑa.pastable_inHom hGc (.refl _))
        (hGc.pastable_hasType tϑ'b (.refl _))).symm))
  · have hFc := hFp.mapsInto c hc
    exact (CtxExpr.app_equiv (CtxExpr.paste false (ϑ' a) (D.k + 1))
      (CtxExpr.paste_app_paste true
      (hFc.pastable_hasType tϑb (.refl _))
      (tϑb.pastable tϑ'b (.refl _)))).trans
      ((CtxExpr.pasteRight_app_pasteLeft
        (tϑ'a.pastable_inHom hFc (.refl _))
        (hFc.pastable_hasType tx (.refl _))).symm)
  · exact CtxExpr.paste_app_pasteOr true
      ((hR₄.typed.mapsInto c hc).pastable_hasType uFb (.refl _))

theorem closure_subset_natOp (hA : ∀ τ ∈ A, τ.Valid) (hU : cylTriples X ⊆ A)
    (hP : pfwTriples X ⊆ A) (hN : A ⊆ natOp (Closure A)) {τ : CtxTriple X} (h : Closure A τ) :
    τ ∈ natOp (Closure A) := by
  induction h with
  | base hτ => exact hN hτ
  | comp _ _ hm ih₁ ih₂ => exact natOp_comp ih₁ ih₂ hm
  | left _ hH ih => exact natOp_left hA hU ih hH
  | right _ hH ih => exact natOp_right hA hU ih hH
  | inv _ hϑ' ih => exact natOp_inv hA hU hP ih hϑ'

end CtxTriple

theorem closure_subset_natEqv {A : Set (CtxTriple X)} (hA : ∀ τ ∈ A, τ.Valid)
    (hU : cylTriples X ⊆ A) (hP : pfwTriples X ⊆ A) (hN : A ⊆ CtxTriple.natOp (CtxTriple.Closure A))
    {τ : CtxTriple X} (h : CtxTriple.Closure A τ) : τ ∈ natEqv X :=
  subset_natEqv (A := CtxTriple.Closure A)
    (fun _ hσ => CtxTriple.closure_subset_natOp hA hU hP hN hσ) h

theorem mem_natEqv_of_closure_union {τ : CtxTriple X}
    (h : CtxTriple.Closure (natEqv X ∪ cylTriples X ∪ pfwTriples X) τ) : τ ∈ natEqv X := by
  have hA : ∀ σ ∈ natEqv X ∪ cylTriples X ∪ pfwTriples X, σ.Valid := by
    rintro σ ((hσ | hσ) | hσ)
    · exact valid_of_mem_natEqv hσ
    · exact valid_of_mem_cylTriples hσ
    · exact valid_of_mem_pfwTriples hσ
  have hU : cylTriples X ⊆ natEqv X ∪ cylTriples X ∪ pfwTriples X :=
    fun _ hσ => Or.inl (Or.inr hσ)
  refine closure_subset_natEqv hA hU (fun _ hσ => Or.inr hσ) (fun σ hσ => ?_) h
  rcases hσ with (hσ | hσ) | hσ
  · rw [← natOp_natEqv] at hσ
    exact CtxTriple.natOp_mono (fun ρ hρ => CtxTriple.Closure.base (Or.inl (Or.inl hρ))) hσ
  · exact subset_natOp_closure hA hU (Or.inl hσ)
  · exact subset_natOp_closure hA hU (Or.inr hσ)

theorem cylTriples_union_pfwTriples_subset_natEqv : cylTriples X ∪ pfwTriples X ⊆ natEqv X := by
  rintro τ (hτ | hτ)
  · exact mem_natEqv_of_closure_union (.base (Or.inl (Or.inr hτ)))
  · exact mem_natEqv_of_closure_union (.base (Or.inr hτ))

theorem closure_natEqv : {τ | CtxTriple.Closure (natEqv X) τ} = natEqv X :=
  Set.ext fun _ => ⟨fun h => mem_natEqv_of_closure_union
    (CtxTriple.Closure.mono (fun _ hσ => Or.inl (Or.inl hσ)) h), fun h => .base h⟩

def CtxEquivalent (H : RoundHom X) (H' : PdHom X) (F G : CtxExpr X) : Prop :=
  ∃ ϑ : PastingDiagram X → PastingDiagram X, (⟨H, H', F, G, ϑ⟩ : CtxTriple X) ∈ natEqv X

theorem mem_natEqv_of_realizes {σ : CtxTriple X} (hσ : σ ∈ natEqv X) {H : RoundHom X}
    {H' : PdHom X} {F G : CtxExpr X} (hr : σ.Realizes H H' F.app G.app)
    (hF : IsRoundCtxOn H H' F) (hG : IsRoundCtxOn H H' G) :
    (⟨H, H', F, G, σ.ϑ⟩ : CtxTriple X) ∈ natEqv X := by
  obtain ⟨⟨k, v, w⟩, hv, hw, hdv, hpar⟩ := H
  obtain rfl : σ.dom.k = k := hr.equiv_dom.k_eq
  rw [← natOp_natEqv] at hσ ⊢
  obtain ⟨hvσ, N⟩ := hσ
  have hin : ∀ {a : PastingDiagram X}, IsRoundIn ⟨σ.dom.k, v, w⟩ a → IsRoundIn σ.dom a :=
    fun ha => ha.congr hr.equiv_dom.symm
  refine ⟨⟨hF, hG, fun a ha => ?_⟩, fun a b ha hb => ?_⟩
  · obtain ⟨hra, hea, ta⟩ := hvσ.comp a (hin ha)
    exact ⟨hra, hea, (ta.of_equiv_side (hr.equiv_F a ha.inHom)).of_equiv_other
      (hr.equiv_G a ha.inHom)⟩
  · change IsRoundIn ⟨σ.dom.k, v, w⟩ a at ha
    change IsRoundIn ⟨σ.dom.k, v, w⟩ b at hb
    exact (CtxTriple.Sim.of_equiv (N a b (hin ha) (hin hb))
      (fun c hc => CtxExpr.app_equiv (CtxExpr.paste true (σ.ϑ b) (σ.dom.k + 1))
        (hr.equiv_F c (InHom.of_inHom_succ hc ha.inHom hb.inHom)))
      (fun c hc => CtxExpr.app_equiv (CtxExpr.paste false (σ.ϑ a) (σ.dom.k + 1))
        (hr.equiv_G c (InHom.of_inHom_succ hc ha.inHom hb.inHom)))).congr
      (H₁' := ⟨σ.dom.k + 1, F.app a, G.app b⟩) (.refl _)
      ⟨rfl, hr.equiv_F a ha.inHom, hr.equiv_G b hb.inHom⟩

theorem Equivalent.spec {k : ℕ} {x y : PastingDiagram X} {hx : x.IsRound} {hy : y.IsRound}
    (hdx : x.dim = k + 1) (hxy : Equivalent ⟨x, hx⟩ ⟨y, hy⟩) :
    Parallel ⟨x, hx⟩ ⟨y, hy⟩ ∧ ∃ e : RoundPastingDiagram X, e ∈ equivalences X ∧
      HasBdry false (k + 1) e.toPastingDiagram x y := by
  obtain ⟨-, e, he, hde, hes, het⟩ := hxy.data
  have hd : (⟨x, hx⟩ : RoundPastingDiagram X).dim = k + 1 := hdx
  rw [hd] at hde hes het
  have hpxy : Parallel ⟨x, hx⟩ ⟨y, hy⟩ :=
    ((parallel_boundary e.isRound hde false true).of_equiv_left
      (hes.symm)).of_equiv_right (het.symm)
  exact ⟨hpxy, e, he, hde, hdx, hpxy.1.symm.trans hdx, hes, het⟩

abbrev NatSim (X : DiagSet.{u}) (H H' : PdHom X) (F G : PastingDiagram X → PastingDiagram X) :
    Prop :=
  CtxTriple.Sim (CtxTriple.Closure (natEqv X)) H H' F G

theorem pfwTriples_subset_natEqv : pfwTriples X ⊆ natEqv X :=
  fun _ h => cylTriples_union_pfwTriples_subset_natEqv (Or.inr h)

namespace NatSim

variable {H H' H'' : PdHom X} {F G I : PastingDiagram X → PastingDiagram X}

theorem symm (h : NatSim X H H' F G) : NatSim X H H' G F :=
  CtxTriple.Sim.symm (fun _ => valid_of_mem_natEqv) h

theorem refl (D : RoundHom X) {K : CtxExpr X} (hK : IsRoundCtxOn D H' K) :
    NatSim X D H' K.app K.app :=
  CtxTriple.Sim.refl cylTriples_subset_natEqv D hK

theorem unit (α : Bool) (D D' : RoundHom X) {T : CtxExpr X} (hT : IsRoundCtxOn D D' T) :
    NatSim X D D'
      (cond α (fun c => (cond α (T.app c) (D'.side α).unit).pasteOr
        (cond α (D'.side α).unit (T.app c)) D'.k) T.app)
      (cond α T.app (fun c => (cond α (T.app c) (D'.side α).unit).pasteOr
        (cond α (D'.side α).unit (T.app c)) D'.k)) :=
  CtxTriple.Sim.unit α cylTriples_subset_natEqv D D' hT

theorem unit_left (D D' : RoundHom X) {T : CtxExpr X} (hT : IsRoundCtxOn D D' T) :
    NatSim X D D' T.app (fun c => D'.v.unit.pasteOr (T.app c) D'.k) :=
  unit false D D' hT

theorem unit_right (D D' : RoundHom X) {T : CtxExpr X} (hT : IsRoundCtxOn D D' T) :
    NatSim X D D' (fun c => (T.app c).pasteOr D'.w.unit D'.k) T.app :=
  unit true D D' hT

theorem equivalent_app (h : NatSim X H H' F G) {b : PastingDiagram X} (hb : IsRoundIn H b)
    (hFb : (F b).IsRound) (hGb : (G b).IsRound) : Equivalent ⟨F b, hFb⟩ ⟨G b, hGb⟩ := by
  obtain ⟨σ, hσ, r⟩ := h
  have hv := CtxTriple.Closure.valid (fun _ => valid_of_mem_natEqv) hσ
  obtain ⟨hr, he, ht⟩ := hv.comp b (hb.congr r.equiv_dom.symm)
  have hF := r.equiv_F b hb.inHom
  have hG := r.equiv_G b hb.inHom
  have hk : (F b).dim = σ.dom.k + 1 := (dim_eq_of_equiv hF).symm.trans ht.dim_a
  refine EquivalenceData.equivalent
    ⟨(dim_eq_of_equiv hF).symm.trans (ht.dim_a.trans (ht.dim_b.symm.trans
      (dim_eq_of_equiv hG))), ⟨σ.ϑ b, hr⟩, he, ?_, ?_, ?_⟩
  · change (σ.ϑ b).dim = (F b).dim + 1
    rw [ht.dim_h, hk]
  · change ((σ.ϑ b).boundary (F b).dim false).Equiv (F b)
    rw [hk]
    exact ht.side.trans hF
  · change ((σ.ϑ b).boundary (F b).dim true).Equiv (G b)
    rw [hk]
    exact ht.other.trans hG

theorem paste (α : Bool) (D D' : RoundHom X) {x y : PastingDiagram X} (hx : x.IsRound)
    (hy : y.IsRound) (hdx : x.dim = D'.k + 1) (hxy : Equivalent ⟨x, hx⟩ ⟨y, hy⟩)
    (hxv : (x.boundary D'.k (!α)).Equiv (D'.side α)) {F G : CtxExpr X}
    (hF : IsRoundCtxOn D D' F) (h : NatSim X D D' F.app G.app) :
    NatSim X D (D'.setSide α (x.boundary D'.k α))
      (CtxExpr.comp (CtxExpr.paste α x D'.k) F).app
      (CtxExpr.comp (CtxExpr.paste α y D'.k) G).app := by
  obtain ⟨hpxy, e, he, te⟩ := Equivalent.spec hdx hxy
  have hdy : y.dim = D'.k + 1 := hpxy.1.symm.trans hdx
  have hσ : ctxPfw α D' x y e.toPastingDiagram ∈ natEqv X :=
    cylTriples_union_pfwTriples_subset_natEqv
      (Or.inr ⟨α, D', x, y, e.toPastingDiagram, ⟨e.isRound, he, te⟩, hxv, rfl⟩)
  have hyv : (y.boundary D'.k (!α)).Equiv (D'.side α) :=
    (hpxy.equiv_boundary_pred hdx (!α)).symm.trans hxv
  have hyx : (y.boundary D'.k α).Equiv (x.boundary D'.k α) :=
    (hpxy.equiv_boundary_pred hdx α).symm
  have hL := (isRoundCtxOn_paste α D' hy hdy hyv.symm).congr (.refl _)
    ((PdHom.Equiv.refl D'.toPdHom).setSide α hyx)
  have S := (CtxTriple.Sim.of_mem (A := natEqv X) hσ).right D hF
  exact S.trans (h.left hL)

end NatSim

theorem ctxEquivalent_iff_natSim (H : RoundHom X) {H' : PdHom X} {F G : CtxExpr X}
    (hF : IsRoundCtxOn H H' F) (hG : IsRoundCtxOn H H' G) :
    CtxEquivalent H H' F G ↔ NatSim X H H' F.app G.app :=
  ⟨fun ⟨_, h⟩ => ⟨_, .base h, CtxTriple.realizes_self _⟩, fun ⟨_, hσ, hr⟩ =>
    ⟨_, mem_natEqv_of_realizes (mem_natEqv_of_closure_union
      (CtxTriple.Closure.mono (fun _ h => Or.inl (Or.inl h)) hσ)) hr hF hG⟩⟩

end Atoms.Diagrammatic
