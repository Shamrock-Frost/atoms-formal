import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Mathlib.AlgebraicTopology.ModelCategory.Homotopy
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace HomotopicalAlgebra

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]

theorem weakEquivalence_of_hasLiftingProperty {A B : C} (u : A ⟶ B)
    (h : ∀ ⦃X Y : C⦄ (p : X ⟶ Y), IsFibrant X → IsFibrant Y → Fibration p →
      HasLiftingProperty u p) :
    WeakEquivalence u := by
  let ψ := factorizationData (trivialCofibrations C) (fibrations C) (terminal.from B)
  have : IsFibrant ψ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from ψ.Z) ψ.p]
    infer_instance
  let φ := factorizationData (trivialCofibrations C) (fibrations C) (u ≫ ψ.i)
  have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have := h φ.p inferInstance inferInstance inferInstance
  have hu : WeakEquivalence (u ≫ ψ.i) := by
    rw [weakEquivalence_iff]
    exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty φ.fac) φ.hi.2
  exact weakEquivalence_of_postcomp u ψ.i

theorem weakEquivalence_of_rightHomotopyRel {X Y : C} [IsCofibrant X] [IsFibrant X]
    [IsCofibrant Y] [IsFibrant Y] (f : X ⟶ Y) (g : Y ⟶ X)
    (hfg : RightHomotopyRel (f ≫ g) (𝟙 X)) (hgf : RightHomotopyRel (g ≫ f) (𝟙 Y)) :
    WeakEquivalence f := by
  let φ := factorizationData (trivialCofibrations C) (fibrations C) f
  have : Cofibration φ.i := (cofibration_iff _).2 φ.hi.1
  have : WeakEquivalence φ.i := (weakEquivalence_iff _).2 φ.hi.2
  have : Fibration φ.p := (fibration_iff _).2 φ.hp
  have : IsCofibrant φ.Z := isCofibrant_of_cofibration φ.i
  have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have sqr : CommSq (𝟙 X) φ.i (terminal.from X) (terminal.from φ.Z) := ⟨terminal.hom_ext _ _⟩
  let r := sqr.lift
  have hir : φ.i ≫ r = 𝟙 X := sqr.fac_left
  have hri : RightHomotopyRel (r ≫ φ.i) (𝟙 φ.Z) := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_cofibration_of_weakEquivalence φ.Z φ.i).1
    simp only [RightHomotopyClass.precomp_mk, reassoc_of% hir, Category.comp_id]
  have hp : RightHomotopyRel φ.p (r ≫ f) := by
    have h := (hri.postcomp φ.p).symm
    rwa [Category.id_comp, Category.assoc, φ.fac] at h
  have hgf' : LeftHomotopyRel ((g ≫ φ.i) ≫ φ.p) (𝟙 Y) := by
    rw [Category.assoc, φ.fac, leftHomotopyRel_iff_rightHomotopyRel]
    exact hgf
  obtain ⟨P, _, ⟨h⟩⟩ := hgf'.exists_good_cylinder
  obtain ⟨s, h', hh'⟩ := h.covering_homotopy φ.p (g ≫ φ.i)
  have hs : s ≫ φ.p = 𝟙 Y := by
    rw [← h'.h₁, Category.assoc, hh', h.h₁]
  have hsg : RightHomotopyRel s (g ≫ φ.i) := by
    rw [← leftHomotopyRel_iff_rightHomotopyRel]
    exact h'.leftHomotopyRel.symm
  have hps : RightHomotopyRel (φ.p ≫ s) (𝟙 φ.Z) := by
    refine (hsg.precomp φ.p).trans ?_
    refine ((hp.postcomp (g ≫ φ.i)).trans ?_).trans hri
    have h₁ := (hfg.postcomp φ.i).precomp r
    simp only [Category.assoc, Category.id_comp] at h₁ ⊢
    exact h₁
  obtain ⟨Q, ⟨hQ⟩⟩ := hps
  have : WeakEquivalence (φ.p ≫ s) := hQ.weakEquivalence_iff.2 inferInstance
  have hret : RetractArrow φ.p (φ.p ≫ s) :=
    { i := Arrow.homMk (𝟙 _) s
      r := Arrow.homMk (𝟙 _) φ.p (by simp [hs])
      retract := by ext <;> simp [hs] }
  have : WeakEquivalence φ.p := by
    rw [weakEquivalence_iff] at this ⊢
    exact MorphismProperty.of_retract hret this
  rw [← φ.fac]
  infer_instance

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} {G : D ⥤ C}

section

variable [CategoryWithCofibrations C] [CategoryWithWeakEquivalences C]
  [CategoryWithCofibrations D] [CategoryWithWeakEquivalences D]

structure IsQuillen (adj : F ⊣ G) : Prop where
  cofibrations_le : cofibrations C ≤ (cofibrations D).inverseImage F
  trivialCofibrations_le : trivialCofibrations C ≤ (trivialCofibrations D).inverseImage F

end

variable [ModelCategory C] [ModelCategory D]

theorem isQuillen_of_fibrations_between_fibrant (adj : F ⊣ G)
    (hF : cofibrations C ≤ (cofibrations D).inverseImage F)
    (hG : ∀ ⦃X Y : D⦄ (p : X ⟶ Y), IsFibrant X → IsFibrant Y → Fibration p →
      Fibration (G.map p)) :
    adj.IsQuillen where
  cofibrations_le := hF
  trivialCofibrations_le A B u hu := by
    rw [mem_trivialCofibrations_iff] at hu
    obtain ⟨_, _⟩ := hu
    rw [inverseImage_iff, mem_trivialCofibrations_iff, cofibration_iff]
    refine ⟨hF u (mem_cofibrations u), weakEquivalence_of_hasLiftingProperty _
      fun X Y p hX hY hp ↦ ?_⟩
    have := hG p hX hY hp
    exact (adj.hasLiftingProperty_iff u p).2 inferInstance

theorem isQuillen_of_fibrations_of_trivialFibrations (adj : F ⊣ G)
    (h₁ : fibrations D ≤ (fibrations C).inverseImage G)
    (h₂ : trivialFibrations D ≤ (trivialFibrations C).inverseImage G) :
    adj.IsQuillen where
  cofibrations_le _ _ i hi := by
    rw [inverseImage_iff, ← trivialFibrations_llp]
    rw [← trivialFibrations_llp] at hi
    exact fun _ _ p hp ↦ (adj.hasLiftingProperty_iff i p).2 (hi _ (h₂ p hp))
  trivialCofibrations_le _ _ i hi := by
    rw [inverseImage_iff, ← fibrations_llp]
    rw [← fibrations_llp] at hi
    exact fun _ _ p hp ↦ (adj.hasLiftingProperty_iff i p).2 (hi _ (h₁ p hp))

variable {adj : F ⊣ G}

theorem IsQuillen.weakEquivalence_map (h : adj.IsQuillen) {A B : C} [IsCofibrant A]
    [IsCofibrant B] (f : A ⟶ B) [WeakEquivalence f] : WeakEquivalence (F.map f) := by
  let φ := factorizationData (cofibrations C) (trivialFibrations C) (coprod.desc f (𝟙 B))
  have hA : WeakEquivalence (coprod.inl ≫ φ.i) :=
    weakEquivalence_of_postcomp_of_fac (g := φ.p)
      (by rw [Category.assoc, φ.fac, coprod.inl_desc])
  have hB : WeakEquivalence (coprod.inr ≫ φ.i) :=
    weakEquivalence_of_postcomp_of_fac (g := φ.p)
      (by rw [Category.assoc, φ.fac, coprod.inr_desc])
  have hFA := ((mem_trivialCofibrations_iff _).1
    (h.trivialCofibrations_le _ (mem_trivialCofibrations (coprod.inl ≫ φ.i)))).2
  have hFB := ((mem_trivialCofibrations_iff _).1
    (h.trivialCofibrations_le _ (mem_trivialCofibrations (coprod.inr ≫ φ.i)))).2
  have hp : WeakEquivalence (F.map φ.p) :=
    weakEquivalence_of_precomp_of_fac (f := F.map (coprod.inr ≫ φ.i))
      (by rw [← F.map_comp, Category.assoc, φ.fac, coprod.inr_desc, F.map_id])
  rw [show f = (coprod.inl ≫ φ.i) ≫ φ.p by rw [Category.assoc, φ.fac, coprod.inl_desc],
    F.map_comp]
  infer_instance

structure IsQuillenEquivalence (adj : F ⊣ G) : Prop extends adj.IsQuillen where
  weakEquivalence_iff {A : C} {X : D} [IsCofibrant A] [IsFibrant X] (f : F.obj A ⟶ X) :
    WeakEquivalence f ↔ WeakEquivalence (adj.homEquiv A X f)

theorem IsQuillen.isQuillenEquivalence_iff (h : adj.IsQuillen) :
    adj.IsQuillenEquivalence ↔
      (∀ {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B),
        WeakEquivalence (F.map f) → WeakEquivalence f) ∧
      ∀ (X : D) [IsFibrant X] (B : C) [IsCofibrant B] (q : B ⟶ G.obj X) [Fibration q]
        [WeakEquivalence q], WeakEquivalence (F.map q ≫ adj.counit.app X) := by
  constructor
  · intro hQ
    refine ⟨fun {A B} _ _ f hf ↦ ?_, fun X _ B _ q _ _ ↦ ?_⟩
    · let ψ := factorizationData (trivialCofibrations D) (fibrations D) (terminal.from (F.obj B))
      have : IsFibrant ψ.Z := by
        rw [isFibrant_iff, Subsingleton.elim (terminal.from ψ.Z) ψ.p]
        infer_instance
      have hj := (hQ.weakEquivalence_iff ψ.i).1 inferInstance
      have hfj := (hQ.weakEquivalence_iff (F.map f ≫ ψ.i)).1 inferInstance
      rw [adj.homEquiv_naturality_left] at hfj
      exact weakEquivalence_of_postcomp f (adj.homEquiv B ψ.Z ψ.i)
    · have key : adj.homEquiv B X (F.map q ≫ adj.counit.app X) = q :=
        (congrArg (adj.homEquiv B X) (adj.homEquiv_symm_apply B X q).symm).trans
          ((adj.homEquiv B X).apply_symm_apply q)
      exact (hQ.weakEquivalence_iff (X := X) (F.map q ≫ adj.counit.app X)).2
        (by rw [key]; infer_instance)
  · rintro ⟨hF, hε⟩
    refine ⟨h, fun {A X} _ _ f ↦ ?_⟩
    let φ := factorizationData (cofibrations C) (trivialFibrations C) (initial.to (G.obj X))
    have : IsCofibrant φ.Z := by
      rw [isCofibrant_iff, Subsingleton.elim (initial.to φ.Z) φ.i]
      infer_instance
    have sq : CommSq (initial.to φ.Z) (initial.to A) φ.p (adj.homEquiv A X f) :=
      ⟨initial.hom_ext _ _⟩
    let g := sq.lift
    have hg : g ≫ φ.p = adj.homEquiv A X f := sq.fac_right
    have := hε X φ.Z φ.p
    have key : F.map g ≫ F.map φ.p ≫ adj.counit.app X = f := by
      rw [← Category.assoc, ← F.map_comp, hg]
      exact (adj.homEquiv_symm_apply _ _ _).symm.trans ((adj.homEquiv A X).symm_apply_apply f)
    rw [← hg]
    conv_lhs => rw [← key]
    rw [weakEquivalence_postcomp_iff, weakEquivalence_postcomp_iff]
    exact ⟨hF _, fun _ ↦ h.weakEquivalence_map _⟩

theorem IsQuillen.weakEquivalence_map_of_isFibrant (h : adj.IsQuillen) {X Y : D} [IsFibrant X]
    [IsFibrant Y] (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence (G.map f) := by
  obtain ⟨b⟩ := (inferInstance : Nonempty (FibrantBrownFactorization f))
  have htf {Z W : D} (p : Z ⟶ W) [Fibration p] [WeakEquivalence p] :
      WeakEquivalence (G.map p) := by
    have hp : trivialFibrations D p := mem_trivialFibrations p
    rw [← cofibrations_rlp] at hp
    have : trivialFibrations C (G.map p) := by
      rw [← cofibrations_rlp]
      intro A B i hi
      exact (adj.hasLiftingProperty_iff i p).1 (hp _ (h.cofibrations_le i hi))
    exact ((mem_trivialFibrations_iff _).1 this).2
  have := htf b.p
  have := htf b.r
  have : WeakEquivalence (G.map b.i) :=
    weakEquivalence_of_postcomp_of_fac (g := G.map b.r) (by rw [← G.map_comp, b.i_r, G.map_id])
  rw [← b.fac, G.map_comp]
  infer_instance

theorem IsQuillen.isQuillenEquivalence_iff_of_isCofibrant (h : adj.IsQuillen)
    [∀ X : C, IsCofibrant X] :
    adj.IsQuillenEquivalence ↔
      (∀ {A B : C} (f : A ⟶ B), WeakEquivalence (F.map f) → WeakEquivalence f) ∧
        ∀ (X : D) [IsFibrant X], WeakEquivalence (adj.counit.app X) := by
  rw [h.isQuillenEquivalence_iff]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨fun f hf ↦ h₁ f hf, fun X _ ↦ ?_⟩,
    fun ⟨h₁, h₂⟩ ↦ ⟨fun f hf ↦ h₁ f hf, fun X _ B _ q _ _ ↦ ?_⟩⟩
  · simpa only [F.map_id, Category.id_comp] using h₂ X (G.obj X) (𝟙 _)
  · have := h.weakEquivalence_map q
    infer_instance

theorem IsQuillen.fibration_map (h : adj.IsQuillen) {X Y : D} (p : X ⟶ Y) [Fibration p] :
    Fibration (G.map p) := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro A B i hi
  rw [← adj.hasLiftingProperty_iff]
  have hp : fibrations D p := mem_fibrations p
  rw [← trivialCofibrations_rlp] at hp
  exact hp _ (h.trivialCofibrations_le i hi)

theorem IsQuillen.isFibrant_obj (h : adj.IsQuillen) (X : D) [IsFibrant X] :
    IsFibrant (G.obj X) := by
  have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
  have := h.fibration_map (terminal.from X)
  exact (isFibrant_iff_of_isTerminal (G.map (terminal.from X))
    (terminalIsTerminal.isTerminalObj G _)).2 this

theorem IsQuillen.isCofibrant_obj (h : adj.IsQuillen) (A : C) [IsCofibrant A] :
    IsCofibrant (F.obj A) := by
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have := h.cofibrations_le (initial.to A) (mem_cofibrations _)
  exact (isCofibrant_iff_of_isInitial (F.map (initial.to A))
    (initialIsInitial.isInitialObj F _)).2 ((cofibration_iff _).2 this)

theorem IsQuillen.of_iso {F' : C ⥤ D} {G' : D ⥤ C} (h : adj.IsQuillen) (adj' : F' ⊣ G')
    (e : F ≅ F') : adj'.IsQuillen where
  cofibrations_le _ _ f hf :=
    ((cofibrations D).arrow_mk_iso_iff (Arrow.isoOfNatIso e f)).1 (h.cofibrations_le f hf)
  trivialCofibrations_le _ _ f hf :=
    ((trivialCofibrations D).arrow_mk_iso_iff (Arrow.isoOfNatIso e f)).1
      (h.trivialCofibrations_le f hf)

theorem IsQuillenEquivalence.of_iso {F' : C ⥤ D} {G' : D ⥤ C} (h : adj.IsQuillenEquivalence)
    (adj' : F' ⊣ G') (e : F ≅ F') : adj'.IsQuillenEquivalence := by
  refine ⟨h.toIsQuillen.of_iso adj' e, fun {A X} _ _ f ↦ ?_⟩
  let β := conjugateIsoEquiv adj adj' e.symm
  have key : adj'.homEquiv A X f = adj.homEquiv A X (e.hom.app A ≫ f) ≫ β.hom.app X := by
    rw [homEquiv_unit, homEquiv_unit, Category.assoc, β.hom.naturality, ← Category.assoc]
    change _ = (adj.unit.app A ≫ (conjugateEquiv adj adj' e.inv).app (F.obj A)) ≫ _
    rw [unit_conjugateEquiv, Category.assoc, ← G'.map_comp, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  rw [key, weakEquivalence_postcomp_iff, ← h.weakEquivalence_iff, weakEquivalence_precomp_iff]

section comp

variable {E : Type u₃} [Category.{v₃} E] [ModelCategory E] {F₂ : D ⥤ E} {G₂ : E ⥤ D}
  {adj₂ : F₂ ⊣ G₂}

theorem IsQuillen.comp (h : adj.IsQuillen) (h₂ : adj₂.IsQuillen) : (adj.comp adj₂).IsQuillen where
  cofibrations_le _ _ f hf := h₂.cofibrations_le _ (h.cofibrations_le f hf)
  trivialCofibrations_le _ _ f hf := h₂.trivialCofibrations_le _ (h.trivialCofibrations_le f hf)

theorem IsQuillen.isQuillenEquivalence_of_comp (h₂ : adj₂.IsQuillen)
    (h₁ : adj.IsQuillenEquivalence) (h : (adj.comp adj₂).IsQuillenEquivalence) :
    adj₂.IsQuillenEquivalence := by
  refine ⟨h₂, fun {A X} _ _ f ↦ ?_⟩
  let ψ := factorizationData (trivialCofibrations D) (fibrations D) (terminal.from A)
  have : IsFibrant ψ.Z := by
    rw [isFibrant_iff, Subsingleton.elim (terminal.from ψ.Z) ψ.p]
    infer_instance
  have : IsCofibrant ψ.Z := isCofibrant_of_cofibration ψ.i
  have hj : trivialCofibrations E (F₂.map ψ.i) := h₂.trivialCofibrations_le _ ψ.hi
  have : Cofibration (F₂.map ψ.i) := (cofibration_iff _).2 hj.1
  have : WeakEquivalence (F₂.map ψ.i) := (weakEquivalence_iff _).2 hj.2
  have sq : CommSq f (F₂.map ψ.i) (terminal.from X) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  let f' := sq.lift
  have hf' : F₂.map ψ.i ≫ f' = f := sq.fac_left
  let φ := factorizationData (cofibrations C) (trivialFibrations C) (initial.to (G.obj ψ.Z))
  have : IsCofibrant φ.Z := by
    rw [isCofibrant_iff, Subsingleton.elim (initial.to φ.Z) φ.i]
    infer_instance
  let a := (adj.homEquiv φ.Z ψ.Z).symm φ.p
  have : WeakEquivalence a := by
    rw [h₁.weakEquivalence_iff, Equiv.apply_symm_apply]
    infer_instance
  have : IsCofibrant (F.obj φ.Z) := h₁.toIsQuillen.isCofibrant_obj φ.Z
  have : WeakEquivalence (F₂.map a) := h₂.weakEquivalence_map a
  have : IsFibrant (G₂.obj X) := h₂.isFibrant_obj X
  have e₁ : WeakEquivalence f ↔ WeakEquivalence f' := by
    rw [← hf', weakEquivalence_precomp_iff]
  have e₂ : WeakEquivalence (adj₂.homEquiv A X f) ↔
      WeakEquivalence (adj₂.homEquiv ψ.Z X f') := by
    rw [← hf', adj₂.homEquiv_naturality_left, weakEquivalence_precomp_iff]
  have e₃ : WeakEquivalence (F₂.map a ≫ f') ↔ WeakEquivalence (adj₂.homEquiv ψ.Z X f') := by
    rw [h.weakEquivalence_iff (A := φ.Z) (X := X) (F₂.map a ≫ f'), comp_homEquiv]
    dsimp only [Equiv.trans_apply]
    rw [adj₂.homEquiv_naturality_left, ← h₁.weakEquivalence_iff, weakEquivalence_precomp_iff]
  rw [e₁, e₂, ← e₃, weakEquivalence_precomp_iff]

end comp

section naturalWeakEquivalence

private noncomputable def IsQuillen.pathObjectMap (h : adj.IsQuillen) {X : D} [IsFibrant X]
    (P : PathObject X) [P.IsGood] : PathObject (G.obj X) where
  P := G.obj P.P
  p₀ := G.map P.p₀
  p₁ := G.map P.p₁
  ι := G.map P.ι
  ι_p₀ := by rw [← G.map_comp, P.ι_p₀, G.map_id]
  ι_p₁ := by rw [← G.map_comp, P.ι_p₁, G.map_id]
  weakEquivalence_ι := h.weakEquivalence_map_of_isFibrant P.ι

theorem IsQuillen.rightHomotopyRel_map (h : adj.IsQuillen) {A X : D} [IsFibrant X]
    {f g : A ⟶ X} (hfg : RightHomotopyRel f g) : RightHomotopyRel (G.map f) (G.map g) := by
  obtain ⟨P, _, ⟨k⟩⟩ := hfg.exists_good_pathObject
  let k' : (h.pathObjectMap P).RightHomotopy (G.map f) (G.map g) :=
    { h := G.map k.h
      h₀ := by
        change G.map k.h ≫ G.map P.p₀ = _
        rw [← G.map_comp, k.h₀]
      h₁ := by
        change G.map k.h ≫ G.map P.p₁ = _
        rw [← G.map_comp, k.h₁] }
  exact ⟨_, ⟨k'⟩⟩

theorem IsQuillen.rightHomotopyRel_homEquiv (h : adj.IsQuillen) {A : C} {X : D} [IsFibrant X]
    {f g : F.obj A ⟶ X} (hfg : RightHomotopyRel f g) :
    RightHomotopyRel (adj.homEquiv A X f) (adj.homEquiv A X g) := by
  obtain ⟨P, _, ⟨k⟩⟩ := hfg.exists_good_pathObject
  let k' : (h.pathObjectMap P).RightHomotopy (adj.homEquiv A X f) (adj.homEquiv A X g) :=
    { h := adj.homEquiv _ _ k.h
      h₀ := by
        change adj.homEquiv _ _ k.h ≫ G.map P.p₀ = _
        rw [← homEquiv_naturality_right, k.h₀]
      h₁ := by
        change adj.homEquiv _ _ k.h ≫ G.map P.p₁ = _
        rw [← homEquiv_naturality_right, k.h₁] }
  exact ⟨_, ⟨k'⟩⟩

variable {F' : C ⥤ D} {G' : D ⥤ C}

omit [ModelCategory C] [ModelCategory D] in
private theorem homEquiv_comp_conjugateEquiv (adj : F ⊣ G) (adj' : F' ⊣ G') (α : F' ⟶ F)
    {A : C} {X : D} (f : F.obj A ⟶ X) :
    adj'.homEquiv A X (α.app A ≫ f) =
      adj.homEquiv A X f ≫ (conjugateEquiv adj adj' α).app X := by
  rw [homEquiv_unit, homEquiv_unit, Category.assoc, (conjugateEquiv adj adj' α).naturality,
    ← Category.assoc, unit_conjugateEquiv, Category.assoc, G'.map_comp]

theorem IsQuillenEquivalence.of_natTrans_weakEquivalence (h : adj.IsQuillenEquivalence)
    {adj' : F' ⊣ G'} (h' : adj'.IsQuillen) (α : F' ⟶ F)
    (hα : ∀ (A : C) [IsCofibrant A], WeakEquivalence (α.app A)) :
    adj'.IsQuillenEquivalence := by
  have hQ := h.toIsQuillen
  refine h'.isQuillenEquivalence_iff.2 ⟨fun {A B} _ _ f hf => ?_, fun X _ B _ q _ _ => ?_⟩
  · have := hα A
    have := hα B
    have : WeakEquivalence (α.app A ≫ F.map f) := by
      rw [← α.naturality f]
      infer_instance
    have : WeakEquivalence (F.map f) := weakEquivalence_of_precomp (α.app A) _
    exact (hQ.isQuillenEquivalence_iff.1 h).1 f this
  · let β := conjugateEquiv adj adj' α
    have : IsFibrant (G.obj X) := hQ.isFibrant_obj X
    have : IsFibrant (G'.obj X) := h'.isFibrant_obj X
    have : IsFibrant B := isFibrant_of_fibration q
    have : IsCofibrant (F'.obj B) := h'.isCofibrant_obj B
    have : IsCofibrant (F.obj B) := hQ.isCofibrant_obj B
    have := hα B
    let φ := factorizationData (cofibrations C) (trivialFibrations C) (initial.to (G.obj X))
    have : IsCofibrant φ.Z := by
      rw [isCofibrant_iff, Subsingleton.elim (initial.to φ.Z) φ.i]
      infer_instance
    have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
    have : IsCofibrant (F'.obj φ.Z) := h'.isCofibrant_obj φ.Z
    have : IsCofibrant (F.obj φ.Z) := hQ.isCofibrant_obj φ.Z
    have := hα φ.Z
    let c := (adj'.homEquiv B X).symm q
    let d := (adj.homEquiv φ.Z X).symm φ.p
    have : WeakEquivalence d := by
      rw [h.weakEquivalence_iff, Equiv.apply_symm_apply]
      infer_instance
    have sqs : CommSq (initial.to B) (initial.to φ.Z) q (φ.p ≫ β.app X) := ⟨initial.hom_ext _ _⟩
    let s := sqs.lift
    have hs : s ≫ q = φ.p ≫ β.app X := sqs.fac_right
    have hsc : F'.map s ≫ c = α.app φ.Z ≫ d := by
      apply (adj'.homEquiv _ _).injective
      rw [adj'.homEquiv_naturality_left, Equiv.apply_symm_apply, hs,
        homEquiv_comp_conjugateEquiv adj adj' α, Equiv.apply_symm_apply]
    obtain ⟨E, hE⟩ :=
      (RightHomotopyClass.precomp_bijective_of_weakEquivalence X (α.app B)).2 (.mk c)
    obtain ⟨e, rfl⟩ := E.mk_surjective
    have he : RightHomotopyRel (α.app B ≫ e) c := by
      rw [← RightHomotopyClass.mk_eq_mk_iff]
      simpa using hE
    have sqt : CommSq (initial.to φ.Z) (initial.to B) φ.p (adj.homEquiv B X e) :=
      ⟨initial.hom_ext _ _⟩
    let t := sqt.lift
    have ht : t ≫ φ.p = adj.homEquiv B X e := sqt.fac_right
    have hts : RightHomotopyRel (t ≫ s) (𝟙 B) := by
      have h1 : RightHomotopyRel ((t ≫ s) ≫ q) (𝟙 B ≫ q) := by
        have h2 := h'.rightHomotopyRel_homEquiv he
        rw [homEquiv_comp_conjugateEquiv adj adj' α, Equiv.apply_symm_apply] at h2
        rwa [Category.assoc, hs, ← Category.assoc, ht, Category.id_comp]
      rw [← leftHomotopyRel_iff_rightHomotopyRel, ← LeftHomotopyClass.mk_eq_mk_iff] at h1 ⊢
      apply (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence B q).1
      simpa only [LeftHomotopyClass.postcomp_mk] using h1
    have hst : RightHomotopyRel (s ≫ t) (𝟙 φ.Z) := by
      have h2 : RightHomotopyRel (F.map s ≫ e) d := by
        rw [← RightHomotopyClass.mk_eq_mk_iff]
        apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence X (α.app φ.Z)).1
        simp only [RightHomotopyClass.precomp_mk]
        rw [RightHomotopyClass.mk_eq_mk_iff, ← Category.assoc, ← α.naturality, Category.assoc,
          ← hsc]
        exact he.precomp _
      have h1 : RightHomotopyRel ((s ≫ t) ≫ φ.p) (𝟙 φ.Z ≫ φ.p) := by
        have h3 := hQ.rightHomotopyRel_homEquiv h2
        rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] at h3
        rwa [Category.assoc, ht, Category.id_comp]
      rw [← leftHomotopyRel_iff_rightHomotopyRel, ← LeftHomotopyClass.mk_eq_mk_iff] at h1 ⊢
      apply (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence φ.Z φ.p).1
      simpa only [LeftHomotopyClass.postcomp_mk] using h1
    have := weakEquivalence_of_rightHomotopyRel s t hst hts
    have := h'.weakEquivalence_map s
    have : WeakEquivalence (F'.map s ≫ c) := by
      rw [hsc]
      infer_instance
    have hc : c = F'.map q ≫ adj'.counit.app X := adj'.homEquiv_counit _ _ _
    rw [← hc]
    exact weakEquivalence_of_precomp (F'.map s) c

theorem IsQuillen.weakEquivalence_conjugateEquiv_app (h : adj.IsQuillen) {adj' : F' ⊣ G'}
    (h' : adj'.IsQuillen) (α : F' ⟶ F)
    (hα : ∀ (A : C) [IsCofibrant A], WeakEquivalence (α.app A)) (X : D) [IsFibrant X]
    [IsCofibrant (G.obj X)] [IsCofibrant (G'.obj X)] :
    WeakEquivalence ((conjugateEquiv adj adj' α).app X) := by
  let β := conjugateEquiv adj adj' α
  have : IsFibrant (G.obj X) := h.isFibrant_obj X
  have : IsFibrant (G'.obj X) := h'.isFibrant_obj X
  have : IsCofibrant (F'.obj (G'.obj X)) := h'.isCofibrant_obj _
  have : IsCofibrant (F.obj (G'.obj X)) := h.isCofibrant_obj _
  have : IsCofibrant (F'.obj (G.obj X)) := h'.isCofibrant_obj _
  have : IsCofibrant (F.obj (G.obj X)) := h.isCofibrant_obj _
  have := hα (G'.obj X)
  have := hα (G.obj X)
  let c' := (adj'.homEquiv _ X).symm (𝟙 (G'.obj X))
  let c := (adj.homEquiv _ X).symm (𝟙 (G.obj X))
  obtain ⟨E, hE⟩ :=
    (RightHomotopyClass.precomp_bijective_of_weakEquivalence X (α.app (G'.obj X))).2 (.mk c')
  obtain ⟨e, rfl⟩ := E.mk_surjective
  have he : RightHomotopyRel (α.app _ ≫ e) c' := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    simpa using hE
  let g := adj.homEquiv _ X e
  have hgβ : RightHomotopyRel (g ≫ β.app X) (𝟙 _) := by
    have h₁ := h'.rightHomotopyRel_homEquiv he
    rwa [homEquiv_comp_conjugateEquiv adj adj' α, Equiv.apply_symm_apply] at h₁
  have key : α.app (G.obj X) ≫ c = F'.map (β.app X) ≫ c' := by
    apply (adj'.homEquiv _ _).injective
    rw [homEquiv_comp_conjugateEquiv adj adj' α, adj'.homEquiv_naturality_left,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply, Category.id_comp, Category.comp_id]
  have h₂ : RightHomotopyRel (F.map (β.app X) ≫ e) c := by
    rw [← RightHomotopyClass.mk_eq_mk_iff]
    apply (RightHomotopyClass.precomp_bijective_of_weakEquivalence X (α.app (G.obj X))).1
    simp only [RightHomotopyClass.precomp_mk]
    rw [RightHomotopyClass.mk_eq_mk_iff, ← Category.assoc, ← α.naturality, Category.assoc, key]
    exact he.precomp _
  have hβg : RightHomotopyRel (β.app X ≫ g) (𝟙 _) := by
    have h₃ := h.rightHomotopyRel_homEquiv h₂
    rwa [adj.homEquiv_naturality_left, Equiv.apply_symm_apply] at h₃
  exact weakEquivalence_of_rightHomotopyRel (β.app X) g hβg hgβ

end naturalWeakEquivalence

section isLocalization

variable (D) [HasFunctorialFactorization (trivialCofibrations D) (fibrations D)]

private noncomputable def toTerminalArrow : D ⥤ Arrow D where
  obj Y := Arrow.mk (terminal.from Y)
  map f := Arrow.homMk f (𝟙 _) (terminal.hom_ext _ _)

private noncomputable def fibrantReplacement : D ⥤ D :=
  toTerminalArrow D ⋙ (functorialFactorizationData (trivialCofibrations D) (fibrations D)).Z

private noncomputable def toFibrantReplacement : 𝟭 D ⟶ fibrantReplacement D where
  app Y := (functorialFactorizationData _ _).i.app ((toTerminalArrow D).obj Y)
  naturality _ _ f := (functorialFactorizationData _ _).i.naturality ((toTerminalArrow D).map f)

variable {D}

private theorem weakEquivalence_toFibrantReplacement_app (Y : D) :
    WeakEquivalence ((toFibrantReplacement D).app Y) :=
  (HomotopicalAlgebra.weakEquivalence_iff _).2
    ((functorialFactorizationData (trivialCofibrations D) (fibrations D)).hi
      ((toTerminalArrow D).obj Y)).2

private theorem isFibrant_fibrantReplacement_obj (Y : D) :
    IsFibrant ((fibrantReplacement D).obj Y) := by
  rw [isFibrant_iff, Subsingleton.elim (terminal.from ((fibrantReplacement D).obj Y))
    ((functorialFactorizationData _ _).p.app ((toTerminalArrow D).obj Y))]
  exact (fibration_iff _).2 ((functorialFactorizationData _ _).hp _)

private theorem weakEquivalence_fibrantReplacement_map {Y Y' : D} (f : Y ⟶ Y')
    [WeakEquivalence f] : WeakEquivalence ((fibrantReplacement D).map f) := by
  have := weakEquivalence_toFibrantReplacement_app Y
  have := weakEquivalence_toFibrantReplacement_app Y'
  have hfac : (toFibrantReplacement D).app Y ≫ (fibrantReplacement D).map f =
      f ≫ (toFibrantReplacement D).app Y' := ((toFibrantReplacement D).naturality f).symm
  exact weakEquivalence_of_precomp_of_fac hfac

variable [∀ X : C, IsCofibrant X]

private def IsQuillen.localizerMorphism (h : adj.IsQuillen) :
    LocalizerMorphism (weakEquivalences C) (weakEquivalences D) where
  functor := F
  map _ _ f hf := by
    have : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).2 hf
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1 (h.weakEquivalence_map f)

private noncomputable def IsQuillen.localizerMorphismFibrantReplacement (h : adj.IsQuillen) :
    LocalizerMorphism (weakEquivalences D) (weakEquivalences C) where
  functor := fibrantReplacement D ⋙ G
  map Y Y' f hf := by
    have : WeakEquivalence f := (HomotopicalAlgebra.weakEquivalence_iff f).2 hf
    have := weakEquivalence_fibrantReplacement_map f
    have := isFibrant_fibrantReplacement_obj Y
    have := isFibrant_fibrantReplacement_obj Y'
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1
      (h.weakEquivalence_map_of_isFibrant ((fibrantReplacement D).map f))

private noncomputable def derivedUnit (adj : F ⊣ G) : 𝟭 C ⟶ F ⋙ fibrantReplacement D ⋙ G where
  app X := adj.unit.app X ≫ G.map ((toFibrantReplacement D).app (F.obj X))
  naturality X X' f := by
    change f ≫ adj.unit.app X' ≫ G.map ((toFibrantReplacement D).app (F.obj X')) =
      (adj.unit.app X ≫ G.map ((toFibrantReplacement D).app (F.obj X))) ≫
        G.map ((fibrantReplacement D).map (F.map f))
    rw [Category.assoc, ← G.map_comp, ← (toFibrantReplacement D).naturality (F.map f)]
    simp

private noncomputable def counitFibrantReplacement (adj : F ⊣ G) :
    (fibrantReplacement D ⋙ G) ⋙ F ⟶ fibrantReplacement D where
  app Y := adj.counit.app ((fibrantReplacement D).obj Y)
  naturality _ _ f := adj.counit.naturality ((fibrantReplacement D).map f)

theorem IsQuillenEquivalence.isLocalization (h : adj.IsQuillenEquivalence) :
    (F ⋙ (weakEquivalences D).Q).IsLocalization (weakEquivalences C) := by
  let Φ := h.toIsQuillen.localizerMorphism
  let Ψ := h.toIsQuillen.localizerMorphismFibrantReplacement
  have hθ (X : C) : weakEquivalences C ((derivedUnit adj).app X) := by
    have := isFibrant_fibrantReplacement_obj (F.obj X)
    have := weakEquivalence_toFibrantReplacement_app (F.obj X)
    have h' := (h.weakEquivalence_iff ((toFibrantReplacement D).app (F.obj X))).1 inferInstance
    rw [adj.homEquiv_unit] at h'
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1 h'
  have hκ (Y : D) : weakEquivalences D ((counitFibrantReplacement adj).app Y) := by
    have : IsFibrant ((𝟭 D).obj ((fibrantReplacement D).obj Y)) :=
      isFibrant_fibrantReplacement_obj Y
    have h' := (h.weakEquivalence_iff (A := G.obj ((fibrantReplacement D).obj Y))
      (adj.counit.app ((fibrantReplacement D).obj Y))).2 (by
        rw [adj.homEquiv_unit, adj.right_triangle_components]
        infer_instance)
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1 h'
  have : IsIso (Functor.whiskerRight (derivedUnit adj) (weakEquivalences C).Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun X ↦ Localization.inverts (weakEquivalences C).Q (weakEquivalences C) _ (hθ X)
  have hκiso :
      IsIso (Functor.whiskerRight (counitFibrantReplacement adj) (weakEquivalences D).Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun Y ↦ Localization.inverts (weakEquivalences D).Q (weakEquivalences D) _ (hκ Y)
  have : IsIso (Functor.whiskerRight (toFibrantReplacement D) (weakEquivalences D).Q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun Y ↦ Localization.inverts (weakEquivalences D).Q (weakEquivalences D) _
      ((HomotopicalAlgebra.weakEquivalence_iff _).1 (weakEquivalence_toFibrantReplacement_app Y))
  let E := Localization.equivalence (weakEquivalences C).Q (weakEquivalences C)
    (weakEquivalences D).Q (weakEquivalences D) (Φ.functor ⋙ (weakEquivalences D).Q)
    (Φ.localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q)
    (Ψ.functor ⋙ (weakEquivalences C).Q)
    (Ψ.localizedFunctor (weakEquivalences D).Q (weakEquivalences C).Q)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso Ψ.functor (weakEquivalences D).Q
        (weakEquivalences C).Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      (asIso (Functor.whiskerRight (derivedUnit adj) (weakEquivalences C).Q)).symm ≪≫
      Functor.leftUnitor _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (CatCommSq.iso Φ.functor (weakEquivalences C).Q
        (weakEquivalences D).Q _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      @asIso _ _ _ _ (Functor.whiskerRight (counitFibrantReplacement adj) (weakEquivalences D).Q)
        hκiso ≪≫
      (asIso (Functor.whiskerRight (toFibrantReplacement D) (weakEquivalences D).Q)).symm ≪≫
      Functor.leftUnitor _)
  have : (Φ.localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q).IsEquivalence :=
    E.isEquivalence_functor
  have : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.mk' Φ (weakEquivalences C).Q (weakEquivalences D).Q
      (Φ.localizedFunctor (weakEquivalences C).Q (weakEquivalences D).Q)
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ (weakEquivalences D).Q

end isLocalization

end CategoryTheory.Adjunction
