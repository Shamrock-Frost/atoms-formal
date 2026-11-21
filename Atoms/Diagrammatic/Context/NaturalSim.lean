import Atoms.Diagrammatic.Context.NaturalUnitor

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

variable {X : DiagSet.{u}}

namespace CtxTriple

theorem Realizes.of_equiv {σ : CtxTriple X} {H H' : PdHom X}
    {F G F' G' : PastingDiagram X → PastingDiagram X} (h : σ.Realizes H H' F G)
    (hF : ∀ c, InHom H c → (F c).Equiv (F' c)) (hG : ∀ c, InHom H c → (G c).Equiv (G' c)) :
    σ.Realizes H H' F' G' :=
  ⟨h.equiv_dom, h.equiv_cod, fun c hc => (h.equiv_F c hc).trans (hF c hc),
    fun c hc => (h.equiv_G c hc).trans (hG c hc)⟩

theorem Realizes.congr {σ : CtxTriple X} {H H' H₁ H₁' : PdHom X}
    {F G : PastingDiagram X → PastingDiagram X} (h : σ.Realizes H H' F G) (e : H.Equiv H₁)
    (e' : H'.Equiv H₁') : σ.Realizes H₁ H₁' F G :=
  ⟨h.equiv_dom.trans e, h.equiv_cod.trans e', fun c hc => h.equiv_F c (hc.congr e.symm),
    fun c hc => h.equiv_G c (hc.congr e.symm)⟩

def Sim (B : Set (CtxTriple X)) (H H' : PdHom X) (F G : PastingDiagram X → PastingDiagram X) :
    Prop :=
  ∃ σ ∈ B, σ.Realizes H H' F G

variable {A B : Set (CtxTriple X)} {H H' : PdHom X} {F G I : PastingDiagram X → PastingDiagram X}

theorem Sim.mono (hAB : A ⊆ B) (h : Sim A H H' F G) : Sim B H H' F G :=
  h.imp fun _ ⟨hσ, hr⟩ => ⟨hAB hσ, hr⟩

theorem Sim.of_equiv {F' G' : PastingDiagram X → PastingDiagram X} (h : Sim B H H' F G)
    (hF : ∀ c, InHom H c → (F c).Equiv (F' c)) (hG : ∀ c, InHom H c → (G c).Equiv (G' c)) :
    Sim B H H' F' G' :=
  h.imp fun _ ⟨hσ, hr⟩ => ⟨hσ, hr.of_equiv hF hG⟩

theorem Sim.congr {H₁ H₁' : PdHom X} (h : Sim B H H' F G) (e : H.Equiv H₁) (e' : H'.Equiv H₁') :
    Sim B H₁ H₁' F G :=
  h.imp fun _ ⟨hσ, hr⟩ => ⟨hσ, hr.congr e e'⟩

theorem Sim.of_mem {σ : CtxTriple X} (hσ : σ ∈ A) : Sim (Closure A) σ.dom σ.cod σ.F.app σ.G.app :=
  ⟨σ, .base hσ, σ.realizes_self⟩

theorem Sim.trans (h₁ : Sim (Closure A) H H' F G) (h₂ : Sim (Closure A) H H' G I) :
    Sim (Closure A) H H' F I := by
  obtain ⟨σ₁, hσ₁, r₁⟩ := h₁
  obtain ⟨σ₂, hσ₂, r₂⟩ := h₂
  have hin : ∀ c, InHom σ₁.dom c → InHom H c := fun c hc => hc.congr r₁.equiv_dom
  have hm : σ₂.Realizes σ₁.dom σ₁.cod σ₁.G.app σ₂.G.app :=
    ⟨r₂.equiv_dom.trans r₁.equiv_dom.symm, r₂.equiv_cod.trans r₁.equiv_cod.symm,
      fun c hc => (r₂.equiv_F c (hin c hc)).trans (r₁.equiv_G c (hin c hc)).symm,
      fun _ _ => .refl _⟩
  exact ⟨_, .comp hσ₁ hσ₂ hm, ⟨r₁.equiv_dom, r₁.equiv_cod, r₁.equiv_F, r₂.equiv_G⟩⟩

theorem Sim.trans_of_equiv {G' : PastingDiagram X → PastingDiagram X}
    (h₁ : Sim (Closure A) H H' F G) (h₂ : Sim (Closure A) H H' G' I)
    (e : ∀ c, InHom H c → (G c).Equiv (G' c)) : Sim (Closure A) H H' F I :=
  h₁.trans (h₂.of_equiv (fun c hc => (e c hc).symm) (fun _ _ => .refl _))

theorem Sim.symm (hA : ∀ τ ∈ A, τ.Valid) (h : Sim (Closure A) H H' F G) :
    Sim (Closure A) H H' G F := by
  obtain ⟨σ, hσ, r⟩ := h
  have hv := Closure.valid hA hσ
  have hex : ∀ a, IsRoundIn σ.dom a → ∃ e', IsWeakInverse (σ.ϑ a) e' := fun a ha => by
    obtain ⟨hr, he, -⟩ := hv.comp a ha
    obtain ⟨e', he'⟩ := exists_isWeakInverse he
    exact ⟨_, he'⟩
  choose! ϑ' hϑ' using hex
  exact ⟨_, .inv hσ hϑ', ⟨r.equiv_dom, r.equiv_cod, r.equiv_G, r.equiv_F⟩⟩

theorem Sim.left (h : Sim (Closure A) H H' F G) {K : CtxExpr X} {H'' : PdHom X}
    (hK : IsRoundCtxOn H' H'' K) :
    Sim (Closure A) H H'' (fun c => K.app (F c)) (fun c => K.app (G c)) := by
  obtain ⟨σ, hσ, r⟩ := h
  exact ⟨_, .left hσ (hK.congr r.equiv_cod.symm (.refl _)), ⟨r.equiv_dom, .refl _,
    fun c hc => CtxExpr.app_equiv K (r.equiv_F c hc),
    fun c hc => CtxExpr.app_equiv K (r.equiv_G c hc)⟩⟩

theorem Sim.right {H'' : PdHom X} (h : Sim (Closure A) H' H'' F G) {K : CtxExpr X}
    (D : RoundHom X) (hK : IsRoundCtxOn D H' K) :
    Sim (Closure A) D H'' (fun c => F (K.app c)) (fun c => G (K.app c)) := by
  obtain ⟨σ, hσ, r⟩ := h
  exact ⟨_, .right hσ (hK.congr (.refl _) r.equiv_dom.symm), ⟨.refl _, r.equiv_cod,
    fun c hc => r.equiv_F _ (hK.typed.mapsInto c hc),
    fun c hc => r.equiv_G _ (hK.typed.mapsInto c hc)⟩⟩

theorem Sim.refl (hU : cylTriples X ⊆ A) (D : RoundHom X) {K : CtxExpr X}
    (hK : IsRoundCtxOn D H' K) : Sim (Closure A) D H' K.app K.app :=
  (Sim.of_mem (A := A) (hU ⟨_, isCylTriple_unit D⟩)).left hK

end CtxTriple

end Atoms.Diagrammatic
