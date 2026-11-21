import Atoms.Diagrammatic.Marked.Cylinder
import Atoms.Diagrammatic.Marked.Horn

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u

namespace Atoms.Diagrammatic

noncomputable def markedIsoMk {X Y : MarkedDiagSet.{u}} (e : X.underlying ≅ Y.underlying)
    (h : ∀ (V : Atom) (x : X.underlying.obj (op V)),
      x ∈ X.marked V ↔ e.hom.app (op V) x ∈ Y.marked V) : X ≅ Y where
  hom := MarkedPresheaf.homMk e.hom fun V x hx => (h V x).1 hx
  inv := MarkedPresheaf.homMk e.inv fun V y hy => (h V _).2 (by
    rw [Iso.inv_hom_id_app_apply]
    exact hy)
  hom_inv_id := MarkedPresheaf.hom_ext e.hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext e.inv_hom_id

def HornLike {P Q : MarkedDiagSet.{u}} (g : P ⟶ Q) : Prop :=
  ∃ (m : MarkedHornData) (s : m.source ⟶ P) (t : m.target ≅ Q), Epi s ∧
    markedHornInclusion m ≫ t.hom = s ≫ g

theorem hornLike_markedHornInclusion (m : MarkedHornData) : HornLike.{u} (markedHornInclusion m) :=
  ⟨m, 𝟙 _, Iso.refl _, inferInstance, (Category.comp_id _).trans (Category.id_comp _).symm⟩

theorem HornLike.hasLiftingProperty {P Q : MarkedDiagSet.{u}} {g : P ⟶ Q} (hg : HornLike g)
    {X Y : MarkedDiagSet.{u}} {p : X ⟶ Y} (hp : markedHorns.rlp p) :
    HasLiftingProperty g p := by
  obtain ⟨m, s, t, hs, hst⟩ := hg
  refine ⟨fun {u v} sq => ?_⟩
  have := hp _ (MorphismProperty.ofHoms.mk m)
  have sq' : CommSq (s ≫ u) (markedHornInclusion m) p (t.hom ≫ v) :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc, ← hst, Category.assoc]⟩
  refine ⟨⟨⟨t.inv ≫ sq'.lift, ?_, ?_⟩⟩⟩
  · rw [← cancel_epi s, ← Category.assoc, ← hst, Category.assoc, t.hom_inv_id_assoc, sq'.fac_left]
  · rw [Category.assoc, sq'.fac_right, t.inv_hom_id_assoc]

theorem HornLike.of_arrow {P Q P' Q' : MarkedDiagSet.{u}} {g : P ⟶ Q} {g' : P' ⟶ Q'}
    (hg : HornLike g) (a : P ⟶ P') (ha : Epi a) (b : Q ≅ Q') (w : g ≫ b.hom = a ≫ g') :
    HornLike g' := by
  obtain ⟨m, s, t, hs, hst⟩ := hg
  refine ⟨m, s ≫ a, t ≪≫ b, epi_comp _ _, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, hst, Category.assoc, w, Category.assoc]

theorem epi_leibnizSourceMap_endpointsNatTrans {K X K' X' : MarkedDiagSet.{u}} {i : K ⟶ X}
    {i' : K' ⟶ X'} (t : K ⟶ K') (s : X ⟶ X') [Epi t] [IsIso s] (w : t ≫ i' = i ≫ s) :
    Epi (NatTrans.leibnizSourceMap markedExactCylinder.endpointsNatTrans t s w) := by
  refine ⟨fun {Z} f g h => pushout.hom_ext ?_ ?_⟩
  · rw [← cancel_epi (markedExactCylinder.I.map t)]
    have e := congrArg (pushout.inl _ _ ≫ ·) h
    have hl := NatTrans.inl_leibnizSourceMap markedExactCylinder.endpointsNatTrans t s w
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hl.symm).trans
      ((Category.assoc _ _ _).trans (e.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) hl).trans (Category.assoc _ _ _))))))
  · rw [← cancel_epi (doubleFunctor.map s)]
    have e := congrArg (pushout.inr _ _ ≫ ·) h
    have hr := NatTrans.inr_leibnizSourceMap markedExactCylinder.endpointsNatTrans t s w
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) hr.symm).trans
      ((Category.assoc _ _ _).trans (e.trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ g) hr).trans (Category.assoc _ _ _))))))

theorem HornLike.bothBox {P Q : MarkedDiagSet.{u}} {g : P ⟶ Q} (hg : HornLike g)
    (hm : ∀ m : MarkedHornData,
      HornLike (markedExactCylinder.{u}.bothBox (markedHornInclusion m))) :
    HornLike (markedExactCylinder.bothBox g) := by
  obtain ⟨m, s, t, hs, hst⟩ := hg
  exact (hm m).of_arrow _ (epi_leibnizSourceMap_endpointsNatTrans s t.hom hst.symm)
    (markedExactCylinder.I.mapIso t)
    (NatTrans.leibnizSourceMap_leibnizBox markedExactCylinder.endpointsNatTrans s t.hom
      hst.symm).symm

theorem apply_top_eq_of_map_eq {V U : Atom} (c : V ⟶ U) {a : U.ogp}
    (h : Atom.map c ⊤ = LowerSet.Iic a) : c V.top = a :=
  LowerSet.Iic_inj.1 ((Atom.map_top c).symm.trans h)

theorem mem_marked_markedClosedSubset_univ_iff (U : Atom) (A : Set U.ogp)
    (hA : ∀ a ∈ A, a ∈ (⊤ : LowerSet U.ogp) ∧ 0 < grade ℕ a) {V : Atom}
    (x : (markedClosedSubset.{u} U ⊤ A hA).underlying.obj (op V)) :
    x ∈ (markedClosedSubset U ⊤ A hA).marked V ↔
      IsDegenerate (ball U) x.1 ∨ ConcreteCategory.hom x.1.down V.top ∈ A := by
  refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).trans ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with h | ⟨a, ha, him, -⟩
    · exact Or.inl (isDegenerate_app (closedSubpresheafUnivIso U).hom h)
    · exact Or.inr (apply_top_eq_of_map_eq x.1.down him ▸ ha)
  · rcases h with h | h
    · exact Or.inl (isDegenerate_app (closedSubpresheafUnivIso U).inv h)
    · rcases (grade_apply_top_le x.1.down).lt_or_eq with hlt | heq
      · exact Or.inl (isDegenerate_app (closedSubpresheafUnivIso U).inv
          (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt x.1.down hlt)))
      · exact Or.inr ⟨_, h, Atom.map_top x.1.down, heq.symm⟩

theorem hornLike_of_ball (m : MarkedHornData) {P Q : MarkedDiagSet.{u}} (g : P ⟶ Q)
    (hg : Mono (MarkedPresheaf.forget.map g)) (Φ : Q.underlying ≅ ball m.atom)
    (hQ : ∀ (V : Atom) (q : Q.underlying.obj (op V)), q ∈ Q.marked V ↔
      IsDegenerate (ball m.atom) (Φ.hom.app (op V) q) ∨
        ConcreteCategory.hom (Φ.hom.app (op V) q).down V.top ∈ m.targetMarking)
    (hrange : Subfunctor.range (MarkedPresheaf.forget.map g ≫ Φ.hom) =
      closedSubpresheaf m.atom m.hornSet)
    (hmk : ∀ (V : Atom) (c : V ⟶ m.atom) (a : m.atom.ogp), a ∈ m.marking →
      Atom.map c ⊤ = LowerSet.Iic a → V.dimension = grade ℕ a →
      ∃ p ∈ P.marked V,
        Φ.hom.app (op V) ((MarkedPresheaf.forget.map g).app (op V) p) = ULift.up c) :
    HornLike g := by
  have hΦ : Mono Φ.hom := ⟨fun a b h => by
    rw [← Category.comp_id a, ← Category.comp_id b, ← Φ.hom_inv_id, ← Category.assoc, h,
      Category.assoc]⟩
  have hmono : Mono (MarkedPresheaf.forget.map g ≫ Φ.hom) := @mono_comp _ _ _ _ _ _ hg _ hΦ
  have hinj : ∀ V : Atomᵒᵖ, Function.Injective ((MarkedPresheaf.forget.map g ≫ Φ.hom).app V) :=
    fun V => (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 hmono V)
  obtain ⟨s₀, hs₀⟩ := Subfunctor.exists_comp_eq_of_range_le
    (MarkedPresheaf.forget.map g ≫ Φ.hom)
    (closedSubpresheaf m.atom m.hornSet).ι
    (by rw [hrange, Subfunctor.range_ι])
  have hs₀x : ∀ (V : Atomᵒᵖ) (x), (MarkedPresheaf.forget.map g ≫ Φ.hom).app V (s₀.app V x) = x.1 :=
    fun V x => congrArg (fun f => f.app V x) hs₀
  let t : m.target ≅ Q := markedIsoMk (closedSubpresheafUnivIso m.atom ≪≫ Φ.symm) fun V x => by
    refine (mem_marked_markedClosedSubset_univ_iff _ _ _ x).trans ?_
    refine Iff.trans ?_ (hQ V _).symm
    have hx : Φ.hom.app _ (Φ.inv.app _ x.1) = x.1 := Iso.inv_hom_id_app_apply Φ _ _
    change _ ↔ IsDegenerate _ (Φ.hom.app _ (Φ.inv.app _ x.1)) ∨
      ConcreteCategory.hom (Φ.hom.app _ (Φ.inv.app _ x.1)).down V.top ∈ _
    rw [hx]
  let s : m.source ⟶ P := MarkedPresheaf.homMk s₀ fun V x hx => by
    rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hx with hx | ⟨a, ha, him, hd⟩
    · exact P.mem_marked_of_isDegenerate (isDegenerate_app s₀ hx)
    · obtain ⟨p, hp, hpx⟩ := hmk V x.1.down a ha him hd
      have : p = s₀.app (op V) x := hinj _ (hpx.trans (hs₀x _ x).symm)
      exact this ▸ hp
  have hepi : Epi s₀ := by
    have : ∀ V, Epi (s₀.app V) := fun V => (epi_iff_surjective _).2 fun p => by
      have hp : (MarkedPresheaf.forget.map g ≫ Φ.hom).app V p ∈
          (closedSubpresheaf m.atom m.hornSet).obj V :=
        hrange ▸ ⟨p, rfl⟩
      exact ⟨⟨_, hp⟩, hinj _ (hs₀x _ _)⟩
    exact NatTrans.epi_of_epi_app s₀
  refine ⟨m, s, t, MarkedPresheaf.forget.epi_of_epi_map hepi, MarkedPresheaf.hom_ext ?_⟩
  have e1 : (MarkedPresheaf.forget.map (markedHornInclusion m) ≫
      MarkedPresheaf.forget.map t.hom) ≫ Φ.hom =
        (closedSubpresheaf m.atom m.hornSet).ι := by
    ext V x
    exact Iso.inv_hom_id_app_apply Φ _ _
  have e2 : (MarkedPresheaf.forget.map s ≫ MarkedPresheaf.forget.map g) ≫ Φ.hom =
      (closedSubpresheaf m.atom m.hornSet).ι :=
    (Category.assoc _ _ _).trans hs₀
  rw [Functor.map_comp, Functor.map_comp]
  exact (cancel_mono Φ.hom).1 (e1.trans e2.symm)

end Atoms.Diagrammatic
