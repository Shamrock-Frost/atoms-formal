import Atoms.ForMathlib.CategoryTheory.Limits.FunctorCategory.Filtered
import Atoms.Homotopical.HomotopyColimit.ProjectiveCofibration
import Atoms.Homotopical.Localizer.AccessibleModel

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra

namespace Atoms.Homotopical

universe v

variable {A : Type v} [SmallCategory A] {I : Type v} [SmallCategory I]

section FreeImages

variable {ι : Type v} {X Y : ι → Aᵒᵖ ⥤ Type v} (f : ∀ t, X t ⟶ Y t)

theorem llp_rlp_colimMap_of_llp_rlp_ofHoms_evaluationLeftAdjoint_map
    {F G : I ⥤ Aᵒᵖ ⥤ Type v} {k : F ⟶ G}
    (hk : (MorphismProperty.ofHoms fun q : I × ι ↦
        (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) q.1).map (f q.2)).rlp.llp k) :
    (MorphismProperty.ofHoms f).rlp.llp (colimMap k) := by
  intro _ _ q hq
  exact (colimConstAdj.hasLiftingProperty_iff k q).2
    (hk _ ((rlp_ofHoms_evaluationLeftAdjoint_map_iff f _).2 fun _ ↦ hq))

end FreeImages

theorem IsAccessibleALocalizer.colimMap_mem_of_projectiveCofibrations
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsAccessibleALocalizer V]
    {F G : I ⥤ Aᵒᵖ ⥤ Type v} {α : F ⟶ G} (hα : projectiveCofibrations A I α)
    (hαV : ∀ i : I, V (α.app i)) :
    (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V) (colimMap α) := by
  obtain ⟨T, hT, hTeq⟩ := hV.exists_trivialCofibrations_eq_saturation
  obtain ⟨ι, X, Y, f, rfl⟩ := (isSmall_iff_eq_ofHoms.{v} T).1 hT
  have hW : MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V =
      (MorphismProperty.ofHoms f).rlp.llp := by
    rw [hTeq, saturation_eq_llp_rlp]
  let TI := MorphismProperty.ofHoms fun q : I × ι ↦
    (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) q.1).map (f q.2)
  have : TI.IsSmall.{v} := isSmall_ofHoms _
  let fac := factorizationData TI.rlp.llp TI.rlp α
  have hk : ∀ i, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V) (fac.i.app i) :=
    fun i ↦ hW ▸ llp_rlp_app_of_llp_rlp_ofHoms_evaluationLeftAdjoint_map f fac.hi i
  have hqV : ∀ i, V (fac.p.app i) := fun i ↦
    hV.isALocalizer.hasTwoOutOfThreeProperty.of_precomp (fac.i.app i) _ (hk i).2
      (by rw [← NatTrans.comp_app, fac.fac]; exact hαV i)
  have hq : ∀ i, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (fac.p.app i) := by
    intro i
    rw [hV.isWeakFactorizationSystem_monomorphisms.rlp]
    refine ⟨?_, hqV i⟩
    rw [hW, rlp_llp_rlp]
    exact (rlp_ofHoms_evaluationLeftAdjoint_map_iff f fac.p).1 fac.hp i
  obtain ⟨l, hl₁, hl₂⟩ := exists_lift_of_projectiveCofibrations hα hq fac.i (𝟙 G) (by simp)
  let r : RetractArrow α fac.i :=
    { i := Arrow.homMk (𝟙 F) l (by simp [hl₁])
      r := Arrow.homMk (𝟙 F) fac.p (by simp)
      retract := by ext <;> simp [hl₂] }
  have hc : (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v) ⊓ V) (colimMap fac.i) :=
    hW ▸ llp_rlp_colimMap_of_llp_rlp_ofHoms_evaluationLeftAdjoint_map f fac.hi
  exact MorphismProperty.of_retract (r.map colim) hc

theorem IsAccessibleALocalizer.colimMap_mem {V : MorphismProperty (Aᵒᵖ ⥤ Type v)}
    [hV : IsAccessibleALocalizer V] {F G : I ⥤ Aᵒᵖ ⥤ Type v}
    (hF : projectiveCofibrations A I (initial.to F))
    (hG : projectiveCofibrations A I (initial.to G)) (α : F ⟶ G)
    (hα : ∀ i : I, V (α.app i)) : V (colimMap α) := by
  let fac := (projectiveFactorization A I).factorizationData (coprod.desc α (𝟙 G))
  have hp : ∀ i, V (fac.p.app i) := fun i ↦
    hV.isALocalizer.rlp_monomorphisms_le _ ((rlp_projectiveGenerators_iff _).1 fac.hp i)
  have hc : projectiveCofibrations A I fac.i := fac.hi
  have hl : ∀ i, V ((coprod.inl ≫ fac.i).app i) := fun i ↦
    MorphismProperty.of_postcomp _ _ (fac.p.app i) (hp i) (by
      rw [← NatTrans.comp_app, Category.assoc, fac.fac, coprod.inl_desc]
      exact hα i)
  have hr : ∀ i, V ((coprod.inr ≫ fac.i).app i) := fun i ↦
    MorphismProperty.of_postcomp _ _ (fac.p.app i) (hp i) (by
      rw [← NatTrans.comp_app, Category.assoc, fac.fac, coprod.inr_desc]
      exact hV.isALocalizer.isomorphisms_le _ (isomorphisms.infer_property _))
  have hcl := (hV.colimMap_mem_of_projectiveCofibrations
    ((projectiveGenerators A I).rlp.llp.comp_mem _ _
      ((projectiveGenerators A I).rlp.llp.of_isPushout (IsPushout.of_hasBinaryCoproduct' F G)
        hG) hc)
    hl).2
  have hcr := (hV.colimMap_mem_of_projectiveCofibrations
    ((projectiveGenerators A I).rlp.llp.comp_mem _ _
      ((projectiveGenerators A I).rlp.llp.of_isPushout
        (IsPushout.of_hasBinaryCoproduct' F G).flip hF) hc)
    hr).2
  have e : ∀ {K L N : I ⥤ Aᵒᵖ ⥤ Type v} (x : K ⟶ L) (y : L ⟶ N),
      colimMap (x ≫ y) = colimMap x ≫ colimMap y := fun x y ↦ by
    simp only [colimMap_eq, Functor.map_comp]
  have hcp : V (colimMap fac.p) := by
    refine MorphismProperty.of_precomp _ _ _ hcr ?_
    rw [← e, Category.assoc, fac.fac, coprod.inr_desc, colimMap_eq, colim.map_id]
    exact hV.isALocalizer.isomorphisms_le _ (IsIso.id _)
  have hαe : α = (coprod.inl ≫ fac.i) ≫ fac.p := by
    rw [Category.assoc, fac.fac, coprod.inl_desc]
  rw [hαe, e]
  exact MorphismProperty.comp_mem _ _ _ hcl hcp

section Chain

variable {J : Type v} [LinearOrder J]

theorem map_app_map_app (P : J ⥤ Aᵒᵖ ⥤ Type v) {i i' j : J} (h : i ≤ i') (h' : i' ≤ j)
    (a : Aᵒᵖ) (z : (P.obj i).obj a) :
    (P.map (homOfLE h')).app a ((P.map (homOfLE h)).app a z) =
      (P.map (homOfLE (h.trans h'))).app a z := by
  rw [← homOfLE_comp h h', P.map_comp]
  rfl

def latching (P : J ⥤ Aᵒᵖ ⥤ Type v) (j : J) : Subfunctor (P.obj j) where
  obj a := {x | ∃ i, ∃ h : i < j, ∃ y, (P.map (homOfLE h.le)).app a y = x}
  map {a b} f := by
    rintro _ ⟨i, h, y, rfl⟩
    exact ⟨i, h, (P.obj i).map f y, NatTrans.naturality_apply _ _ _⟩

variable {F H K : J ⥤ Aᵒᵖ ⥤ Type v}

theorem exists_lift_of_latching (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h)))
    (p : H ⟶ K) (hp : ∀ j, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (p.app j))
    (g : F ⟶ K) (j : J) (l : ∀ i, F.obj i ⟶ H.obj i)
    (hl₁ : ∀ i, i < j → l i ≫ p.app i = g.app i)
    (hl₂ : ∀ i i' (h : i ≤ i'), i' < j → F.map (homOfLE h) ≫ l i' = l i ≫ H.map (homOfLE h)) :
    ∃ L : F.obj j ⟶ H.obj j, L ≫ p.app j = g.app j ∧
      ∀ i (h : i < j), F.map (homOfLE h.le) ≫ L = l i ≫ H.map (homOfLE h.le) := by
  have inj : ∀ (i i' : J) (h : i ≤ i') (a : Aᵒᵖ), Function.Injective ((F.map (homOfLE h)).app a) :=
    fun i i' h a ↦ (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1 (hF i i' h) a)
  have hl₂' : ∀ i i' (h : i ≤ i'), i' < j → ∀ a y,
      (l i').app a ((F.map (homOfLE h)).app a y) = (H.map (homOfLE h)).app a ((l i).app a y) :=
    fun i i' h h' a y ↦ ConcreteCategory.congr_hom (congr_app (hl₂ i i' h h') a) y
  have wd₀ : ∀ (a : Aᵒᵖ) (i i' : J) (hii' : i ≤ i') (h : i < j) (h' : i' < j) y y',
      (F.map (homOfLE h.le)).app a y = (F.map (homOfLE h'.le)).app a y' →
        (H.map (homOfLE h.le)).app a ((l i).app a y) =
          (H.map (homOfLE h'.le)).app a ((l i').app a y') := by
    intro a i i' hii' h h' y y' e
    rw [← map_app_map_app F hii' h'.le] at e
    rw [← inj _ _ _ _ e, hl₂' i i' hii' h' a y, map_app_map_app]
  have wd : ∀ (a : Aᵒᵖ) (i i' : J) (h : i < j) (h' : i' < j) y y',
      (F.map (homOfLE h.le)).app a y = (F.map (homOfLE h'.le)).app a y' →
        (H.map (homOfLE h.le)).app a ((l i).app a y) =
          (H.map (homOfLE h'.le)).app a ((l i').app a y') := by
    intro a i i' h h' y y' e
    rcases le_total i i' with hii' | hii'
    · exact wd₀ a i i' hii' h h' y y' e
    · exact (wd₀ a i' i hii' h' h y' y e.symm).symm
  choose sel hlt pre hpre using fun (a : Aᵒᵖ) (x : (latching F j).obj a) ↦ x.2
  have key : ∀ (a : Aᵒᵖ) (x : (latching F j).obj a) (i : J) (h : i < j) y,
      (F.map (homOfLE h.le)).app a y = x.1 →
        (H.map (homOfLE (hlt a x).le)).app a ((l (sel a x)).app a (pre a x)) =
          (H.map (homOfLE h.le)).app a ((l i).app a y) :=
    fun a x i h y e ↦ wd a (sel a x) i (hlt a x) h _ y ((hpre a x).trans e.symm)
  let E : (latching F j).toFunctor ⟶ H.obj j :=
    { app a := ↾fun x ↦ (H.map (homOfLE (hlt a x).le)).app a ((l (sel a x)).app a (pre a x))
      naturality a b f := by
        ext x
        obtain ⟨i, h, y, e⟩ := x.2
        change _ = (H.obj j).map f
          ((H.map (homOfLE (hlt a x).le)).app a ((l (sel a x)).app a (pre a x)))
        rw [key a x i h y e]
        refine (key b ((latching F j).toFunctor.map f x) i h ((F.obj i).map f y) ?_).trans ?_
        · rw [NatTrans.naturality_apply, e]
          rfl
        · rw [NatTrans.naturality_apply (l i), NatTrans.naturality_apply (H.map _)] }
  have hE : ∀ (a : Aᵒᵖ) (i : J) (h : i < j) y,
      E.app a ⟨_, ⟨i, h, y, rfl⟩⟩ = (H.map (homOfLE h.le)).app a ((l i).app a y) :=
    fun a i h y ↦ key a ⟨_, ⟨i, h, y, rfl⟩⟩ i h y rfl
  have := hp j _ (MorphismProperty.monomorphisms.infer_property (latching F j).ι)
  have sq : CommSq E (latching F j).ι (p.app j) (g.app j) := by
    constructor
    ext a x
    obtain ⟨_, ⟨i, h, y, rfl⟩⟩ := x
    change (p.app j).app a (E.app a ⟨_, ⟨i, h, y, rfl⟩⟩) = (g.app j).app a _
    have e₁ : (p.app i).app a ((l i).app a y) = (g.app i).app a y :=
      ConcreteCategory.congr_hom (congr_app (hl₁ i h) a) y
    rw [hE a i h y, natTrans_app_app_map_app, e₁]
    exact (natTrans_app_app_map_app g _ a y).symm
  refine ⟨sq.lift, sq.fac_right, fun i h ↦ ?_⟩
  ext a y
  change ((latching F j).ι ≫ sq.lift).app a ⟨_, ⟨i, h, y, rfl⟩⟩ =
    (H.map (homOfLE h.le)).app a ((l i).app a y)
  rw [sq.fac_left, hE a i h y]

variable [WellFoundedLT J]

theorem exists_lift_of_mono (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h)))
    (p : H ⟶ K) (hp : ∀ j, (MorphismProperty.monomorphisms (Aᵒᵖ ⥤ Type v)).rlp (p.app j))
    (g : F ⟶ K) : ∃ l : F ⟶ H, l ≫ p = g := by
  have h0 : ∀ j, ∃ L : F.obj j ⟶ H.obj j, L ≫ p.app j = g.app j := by
    intro j
    obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms _ (hp j)
    exact ⟨g.app j ≫ s, by rw [Category.assoc, hs, Category.comp_id]⟩
  choose l₀ hl₀ using h0
  have hext : ∀ j (l : ∀ i, F.obj i ⟶ H.obj i), ∃ L : F.obj j ⟶ H.obj j,
      L ≫ p.app j = g.app j ∧ ((∀ i, i < j → l i ≫ p.app i = g.app i) ∧
        (∀ i i' (h : i ≤ i'), i' < j → F.map (homOfLE h) ≫ l i' = l i ≫ H.map (homOfLE h)) →
      ∀ i (h : i < j), F.map (homOfLE h.le) ≫ L = l i ≫ H.map (homOfLE h.le)) := by
    intro j l
    by_cases hgood : (∀ i, i < j → l i ≫ p.app i = g.app i) ∧
        (∀ i i' (h : i ≤ i'), i' < j → F.map (homOfLE h) ≫ l i' = l i ≫ H.map (homOfLE h))
    · obtain ⟨L, h₁, h₂⟩ := exists_lift_of_latching hF p hp g j l hgood.1 hgood.2
      exact ⟨L, h₁, fun _ ↦ h₂⟩
    · exact ⟨l₀ j, hl₀ j, fun h ↦ absurd h hgood⟩
  choose step hstep₁ hstep₂ using hext
  let lift : ∀ j, F.obj j ⟶ H.obj j := wellFounded_lt.fix (C := fun j ↦ F.obj j ⟶ H.obj j)
    fun j rec ↦ step j fun i ↦ if h : i < j then rec i h else l₀ i
  have hfix : ∀ j, lift j = step j fun i ↦ if h : i < j then lift i else l₀ i :=
    fun j ↦ wellFounded_lt.fix_eq _ j
  have hlift : ∀ j, lift j ≫ p.app j = g.app j := fun j ↦ by
    rw [hfix]
    exact hstep₁ _ _
  have hcompat : ∀ j i (h : i ≤ j), F.map (homOfLE h) ≫ lift j = lift i ≫ H.map (homOfLE h) := by
    intro j
    refine (wellFounded_lt (α := J)).induction (C := fun j ↦ ∀ i (h : i ≤ j),
      F.map (homOfLE h) ≫ lift j = lift i ≫ H.map (homOfLE h)) j fun j ih ↦ ?_
    · intro i h
      rcases h.lt_or_eq with hlt | rfl
      · have := hstep₂ j (fun i ↦ if h : i < j then lift i else l₀ i)
          ⟨fun i' hi' ↦ by rw [dif_pos hi']; exact hlift i',
            fun i₁ i₂ h₁₂ h₂ ↦ by
              rw [dif_pos h₂, dif_pos (lt_of_le_of_lt h₁₂ h₂)]
              exact ih i₂ h₂ i₁ h₁₂⟩ i hlt
        rw [dif_pos hlt] at this
        rw [hfix j]
        exact this
      · change F.map (𝟙 i) ≫ lift i = lift i ≫ H.map (𝟙 i)
        rw [F.map_id, H.map_id, Category.id_comp, Category.comp_id]
  exact ⟨{ app := lift, naturality := fun i j f ↦ hcompat j i (leOfHom f) },
    NatTrans.ext (funext hlift)⟩

variable (F) in
theorem projectiveCofibrations_initial_to_of_mono
    (hF : ∀ (i j : J) (h : i ≤ j), Mono (F.map (homOfLE h))) :
    projectiveCofibrations A J (initial.to F) := by
  intro X Y q hq
  rw [rlp_projectiveGenerators_iff] at hq
  constructor
  intro f g sq
  obtain ⟨l, hl⟩ := exists_lift_of_mono hF q hq g
  exact ⟨⟨{ l := l, fac_left := initial.hom_ext _ _, fac_right := hl }⟩⟩

end Chain

theorem IsALocalizer.of_isColimit_of_projectiveCofibrations
    {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [IsALocalizer V] {X Y : I ⥤ Aᵒᵖ ⥤ Type v}
    (hX : projectiveCofibrations A I (initial.to X))
    (hY : projectiveCofibrations A I (initial.to Y)) (φ : X ⟶ Y) (hφ : ∀ i, V (φ.app i))
    {cX : Cocone X} {cY : Cocone Y} (hcX : IsColimit cX) (hcY : IsColimit cY)
    (f : cX.pt ⟶ cY.pt) (hf : ∀ i, cX.ι.app i ≫ f = φ.app i ≫ cY.ι.app i) : V f := by
  let S := MorphismProperty.ofHoms fun i ↦ φ.app i
  have : S.IsSmall.{v} := isSmall_ofHoms.{v} _
  have hS := isAccessibleALocalizer_generatedALocalizer S
  have hmem := hS.colimMap_mem hX hY φ fun i ↦
    le_generatedALocalizer S _ (MorphismProperty.ofHoms.mk i)
  refine generatedALocalizer_le (S := S) (fun _ _ _ ⟨i⟩ ↦ hφ i) _ ?_
  have hiso := hS.isALocalizer.isomorphisms_le
  let eX := (colimit.isColimit X).coconePointUniqueUpToIso hcX
  let eY := (colimit.isColimit Y).coconePointUniqueUpToIso hcY
  have hX' : ∀ i, colimit.ι X i ≫ eX.hom = cX.ι.app i :=
    fun i ↦ (colimit.isColimit X).comp_coconePointUniqueUpToIso_hom hcX i
  have hY' : ∀ i, colimit.ι Y i ≫ eY.hom = cY.ι.app i :=
    fun i ↦ (colimit.isColimit Y).comp_coconePointUniqueUpToIso_hom hcY i
  have e : f = eX.inv ≫ colimMap φ ≫ eY.hom := by
    rw [Iso.eq_inv_comp]
    refine colimit.hom_ext fun i ↦ ?_
    rw [← Category.assoc, hX', hf, ι_colimMap_assoc, hY']
  rw [e]
  exact MorphismProperty.comp_mem _ _ _ (hiso _ (isomorphisms.infer_property _))
    (MorphismProperty.comp_mem _ _ _ hmem (hiso _ (isomorphisms.infer_property _)))

theorem IsALocalizer.of_isColimit {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsALocalizer V]
    {J : Type v} [LinearOrder J] [WellFoundedLT J] {X Y : J ⥤ Aᵒᵖ ⥤ Type v}
    (hX : ∀ (i j : J) (h : i ≤ j), Mono (X.map (homOfLE h)))
    (hY : ∀ (i j : J) (h : i ≤ j), Mono (Y.map (homOfLE h)))
    (φ : X ⟶ Y) (hφ : ∀ j, V (φ.app j)) {cX : Cocone X} {cY : Cocone Y}
    (hcX : IsColimit cX) (hcY : IsColimit cY) (f : cX.pt ⟶ cY.pt)
    (hf : ∀ j, cX.ι.app j ≫ f = φ.app j ≫ cY.ι.app j) : V f :=
  hV.of_isColimit_of_projectiveCofibrations (projectiveCofibrations_initial_to_of_mono X hX)
    (projectiveCofibrations_initial_to_of_mono Y hY) φ hφ hcX hcY f hf

theorem projectiveCofibrations_initial_to_span {F₀ F₁ F₂ : Aᵒᵖ ⥤ Type v} (φ₁ : F₀ ⟶ F₁)
    (φ₂ : F₀ ⟶ F₂) [Mono φ₁] [Mono φ₂] :
    projectiveCofibrations A (AsSmall.{v} WalkingSpan)
      (initial.to (AsSmall.down ⋙ span φ₁ φ₂)) := by
  intro X Y q hq
  rw [rlp_projectiveGenerators_iff] at hq
  constructor
  intro f g sq
  let P := AsSmall.down ⋙ span φ₁ φ₂
  let z : AsSmall.{v} WalkingSpan := AsSmall.up.obj WalkingSpan.zero
  let L : AsSmall.{v} WalkingSpan := AsSmall.up.obj WalkingSpan.left
  let R : AsSmall.{v} WalkingSpan := AsSmall.up.obj WalkingSpan.right
  let fst : z ⟶ L := AsSmall.up.map WalkingSpan.Hom.fst
  let snd : z ⟶ R := AsSmall.up.map WalkingSpan.Hom.snd
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : P.obj z ⟶ X.obj z, l₀ ≫ q.app z = g.app z := by
    obtain ⟨s, hs⟩ := exists_section_of_rlp_monomorphisms _ (hq z)
    exact ⟨g.app z ≫ s, by rw [Category.assoc, hs, Category.comp_id]⟩
  have hlift : ∀ (k : AsSmall.{v} WalkingSpan) (e : z ⟶ k), Mono (P.map e) →
      ∃ l : P.obj k ⟶ X.obj k, P.map e ≫ l = l₀ ≫ X.map e ∧ l ≫ q.app k = g.app k := by
    intro k e he
    have := hq k _ (MorphismProperty.monomorphisms.infer_property (P.map e))
    have sq' : CommSq (l₀ ≫ X.map e) (P.map e) (q.app k) (g.app k) := ⟨by
      rw [Category.assoc, q.naturality, ← Category.assoc, hl₀, g.naturality]⟩
    exact ⟨sq'.lift, sq'.fac_left, sq'.fac_right⟩
  obtain ⟨l₁, hl₁, hl₁'⟩ := hlift L fst (inferInstanceAs (Mono φ₁))
  obtain ⟨l₂, hl₂, hl₂'⟩ := hlift R snd (inferInstanceAs (Mono φ₂))
  let τ : span φ₁ φ₂ ⟶ AsSmall.up ⋙ X := spanHomMk l₀ l₁ l₂ hl₁ hl₂
  let l : P ⟶ X := NatTrans.mk (fun j ↦ τ.app (ULift.down j))
    (fun _ _ e ↦ τ.naturality (ULift.down e))
  refine ⟨⟨{ l := l, fac_left := initial.hom_ext _ _, fac_right := ?_ }⟩⟩
  refine NatTrans.ext (funext fun j ↦ ?_)
  rcases j with ⟨_ | _ | _⟩
  exacts [hl₀, hl₁', hl₂']

theorem IsALocalizer.of_isPushout {V : MorphismProperty (Aᵒᵖ ⥤ Type v)} [hV : IsALocalizer V]
    {F₀ F₁ F₂ F' G₀ G₁ G₂ G' : Aᵒᵖ ⥤ Type v}
    {φ₁ : F₀ ⟶ F₁} {φ₂ : F₀ ⟶ F₂} {ε₁ : F₁ ⟶ F'} {ε₂ : F₂ ⟶ F'}
    {ψ₁ : G₀ ⟶ G₁} {ψ₂ : G₀ ⟶ G₂} {η₁ : G₁ ⟶ G'} {η₂ : G₂ ⟶ G'}
    (hF : IsPushout φ₁ φ₂ ε₁ ε₂) (hG : IsPushout ψ₁ ψ₂ η₁ η₂) [Mono φ₁] [Mono φ₂] [Mono ψ₁]
    [Mono ψ₂] (χ₀ : F₀ ⟶ G₀) (χ₁ : F₁ ⟶ G₁) (χ₂ : F₂ ⟶ G₂) (χ' : F' ⟶ G')
    (h₁ : φ₁ ≫ χ₁ = χ₀ ≫ ψ₁) (h₂ : φ₂ ≫ χ₂ = χ₀ ≫ ψ₂)
    (h₁' : ε₁ ≫ χ' = χ₁ ≫ η₁) (h₂' : ε₂ ≫ χ' = χ₂ ≫ η₂)
    (hχ₀ : V χ₀) (hχ₁ : V χ₁) (hχ₂ : V χ₂) : V χ' := by
  let χ : AsSmall.down ⋙ span φ₁ φ₂ ⟶ AsSmall.down ⋙ span ψ₁ ψ₂ :=
    Functor.whiskerLeft AsSmall.down (spanHomMk χ₀ χ₁ χ₂ h₁ h₂)
  refine hV.of_isColimit_of_projectiveCofibrations (projectiveCofibrations_initial_to_span φ₁ φ₂)
    (projectiveCofibrations_initial_to_span ψ₁ ψ₂) χ ?_
    (hF.isColimit.whiskerEquivalence AsSmall.equiv.symm)
    (hG.isColimit.whiskerEquivalence AsSmall.equiv.symm) χ' ?_
  · rintro ⟨_ | _ | _⟩
    exacts [hχ₀, hχ₁, hχ₂]
  · rintro ⟨_ | _ | _⟩
    · change (φ₁ ≫ ε₁) ≫ χ' = χ₀ ≫ ψ₁ ≫ η₁
      rw [Category.assoc, h₁', ← Category.assoc, h₁, Category.assoc]
    · exact h₁'
    · exact h₂'

end Atoms.Homotopical
