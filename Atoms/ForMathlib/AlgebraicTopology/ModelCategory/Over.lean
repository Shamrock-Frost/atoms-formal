import Atoms.ForMathlib.CategoryTheory.LiftingProperties.Over
import Mathlib.AlgebraicTopology.ModelCategory.Over
import Atoms.ForMathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Atoms.ForMathlib.CategoryTheory.Limits.Over
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen

universe v u v₂ u₂

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] (S : C)

namespace HomotopicalAlgebra

section

variable [CategoryWithCofibrations C]

instance categoryWithCofibrationsUnder : CategoryWithCofibrations (Under S) where
  cofibrations := (cofibrations C).under

lemma cofibrations_under_def :
    cofibrations (Under S) = (cofibrations C).under := rfl

lemma cofibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Cofibration f ↔ Cofibration f.right := by
  simp only [cofibration_iff, cofibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Cofibration f] : Cofibration f.right := by
  rwa [← cofibrations_under_iff]

instance [(cofibrations C).IsStableUnderRetracts] :
    (cofibrations (Under S)).IsStableUnderRetracts := by
  rw [cofibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithFibrations C]

instance categoryWithFibrationsUnder : CategoryWithFibrations (Under S) where
  fibrations := (fibrations C).under

lemma fibrations_under_def :
    fibrations (Under S) = (fibrations C).under := rfl

lemma fibrations_under_iff {X Y : Under S} (f : X ⟶ Y) :
    Fibration f ↔ Fibration f.right := by
  simp only [fibration_iff, fibrations_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [Fibration f] : Fibration f.right := by
  rwa [← fibrations_under_iff]

instance [(fibrations C).IsStableUnderRetracts] :
    (fibrations (Under S)).IsStableUnderRetracts := by
  rw [fibrations_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

section

variable [CategoryWithWeakEquivalences C]

instance categoryWithWeakEquivalencesUnder : CategoryWithWeakEquivalences (Under S) where
  weakEquivalences := (weakEquivalences C).under

lemma weakEquivalences_under_def :
    weakEquivalences (Under S) = (weakEquivalences C).under := rfl

lemma weakEquivalences_under_iff {X Y : Under S} (f : X ⟶ Y) :
    WeakEquivalence f ↔ WeakEquivalence f.right := by
  simp only [weakEquivalence_iff, weakEquivalences_under_def, MorphismProperty.under_iff]

instance {X Y : Under S} (f : X ⟶ Y) [WeakEquivalence f] : WeakEquivalence f.right := by
  rwa [← weakEquivalences_under_iff]

instance [(weakEquivalences C).IsStableUnderRetracts] :
    (weakEquivalences (Under S)).IsStableUnderRetracts := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

instance [(weakEquivalences C).HasTwoOutOfThreeProperty] :
    (weakEquivalences (Under S)).HasTwoOutOfThreeProperty := by
  rw [weakEquivalences_under_def, MorphismProperty.under_eq_inverseImage]
  infer_instance

end

lemma trivialCofibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C] :
    trivialCofibrations (Under S) = (trivialCofibrations C).under := rfl

lemma trivialFibrations_under_eq
    [CategoryWithWeakEquivalences C] [CategoryWithFibrations C] :
    trivialFibrations (Under S) = (trivialFibrations C).under := rfl

section

variable [CategoryWithWeakEquivalences C] [CategoryWithCofibrations C]
  [CategoryWithFibrations C]

instance [(trivialCofibrations C).HasFactorization (fibrations C)] :
    (trivialCofibrations (Under S)).HasFactorization (fibrations (Under S)) := by
  rw [fibrations_under_def, trivialCofibrations_under_eq]
  infer_instance

instance [(cofibrations C).HasFactorization (trivialFibrations C)] :
    (cofibrations (Under S)).HasFactorization (trivialFibrations (Under S)) := by
  rw [cofibrations_under_def, trivialFibrations_under_eq]
  infer_instance

end

instance ModelCategory.under [ModelCategory C] : ModelCategory (Under S) where
  cm4a _ _ _ _ _ := .under _ _
  cm4b _ _ _ _ _ := .under _ _

lemma isFibrant_under_iff [ModelCategory C] (Y : Under S) : IsFibrant Y ↔ IsFibrant Y.right := by
  rw [isFibrant_iff_of_isTerminal (terminal.from Y) terminalIsTerminal,
    isFibrant_iff_of_isTerminal (terminal.from Y).right
      (terminalIsTerminal.isTerminalObj (Under.forget S) _), fibrations_under_iff]

lemma isCofibrant_under_mk_iff [ModelCategory C] {X : C} (i : S ⟶ X) :
    IsCofibrant (Under.mk i) ↔ Cofibration i := by
  rw [isCofibrant_iff_of_isInitial (Under.homMk i : Under.mk (𝟙 S) ⟶ Under.mk i)
    Under.mkIdInitial, cofibrations_under_iff]
  rfl

section Over

variable [ModelCategory C] {B B' : C}

lemma isFibrant_over_mk {E : C} (p : E ⟶ B) [Fibration p] : IsFibrant (Over.mk p) := by
  rw [isFibrant_iff_of_isTerminal (Over.homMk p : Over.mk p ⟶ Over.mk (𝟙 B)) Over.mkIdTerminal,
    fibrations_over_iff]
  exact ‹_›

theorem isQuillen_mapPullbackAdj (g : B' ⟶ B) : (Over.mapPullbackAdj g).IsQuillen where
  cofibrations_le _ _ f hf := by
    simp only [MorphismProperty.inverseImage_iff, ← cofibration_iff, cofibrations_over_iff] at hf ⊢
    exact hf
  trivialCofibrations_le _ _ f hf := by
    simp only [MorphismProperty.inverseImage_iff, cofibrations_over_iff,
      mem_trivialCofibrations_iff, weakEquivalences_over_iff] at hf ⊢
    exact hf

theorem weakEquivalence_pullback_map_of_fibration {E E' : C} (g : B' ⟶ B) (p : E ⟶ B)
    (p' : E' ⟶ B) [Fibration p] [Fibration p'] (w : E ⟶ E') (hw : w ≫ p' = p)
    [WeakEquivalence w] :
    WeakEquivalence (pullback.map p g p' g w (𝟙 _) (𝟙 _) (by simp [hw]) (by simp)) := by
  have := isFibrant_over_mk p
  have := isFibrant_over_mk p'
  let w' : Over.mk p ⟶ Over.mk p' := Over.homMk w hw
  have : WeakEquivalence w' := by rwa [weakEquivalences_over_iff]
  have h := (isQuillen_mapPullbackAdj g).weakEquivalence_map_of_isFibrant w'
  rw [weakEquivalences_over_iff] at h
  have e : pullback.map p g p' g w (𝟙 _) (𝟙 _) (by simp [hw]) (by simp) =
      ((Over.pullback g).map w').left :=
    pullback.hom_ext (by simp [w', pullback.map]) (by simp [w', pullback.map])
  rwa [e]

private lemma trivialFibrations_pullback_fst_comp_p₁ {D D' : C} [IsFibrant D] [IsFibrant D']
    (P : PathObject D) [P.IsGood] (q : D' ⟶ D) [WeakEquivalence q] :
    trivialFibrations C (pullback.fst P.p₀ q ≫ P.p₁) := by
  rw [mem_trivialFibrations_iff]
  constructor
  · let ψ : pullback P.p₀ q ⟶ D' ⨯ D := prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ P.p₁)
    have sq : IsPullback (pullback.fst P.p₀ q) ψ P.p (prod.map q (𝟙 D)) := by
      refine IsPullback.of_bot ?_ ?_ (IsPullback.of_prod_fst_with_id q D).flip
      · rw [prod.lift_fst, PrepathObject.p_fst]
        exact IsPullback.of_hasPullback P.p₀ q
      · apply prod.hom_ext
        · rw [Category.assoc, PrepathObject.p_fst, Category.assoc, prod.map_fst,
            prod.lift_fst_assoc, pullback.condition]
        · rw [Category.assoc, PrepathObject.p_snd, Category.assoc, prod.map_snd,
            Category.comp_id, prod.lift_snd]
    have : Fibration ψ := by
      rw [fibration_iff]
      exact (fibrations C).of_isPullback sq (by rw [← fibration_iff]; infer_instance)
    rw [← prod.lift_snd (pullback.snd P.p₀ q) (pullback.fst P.p₀ q ≫ P.p₁)]
    infer_instance
  · let s : D' ⟶ pullback P.p₀ q := pullback.lift (q ≫ P.ι) (𝟙 D') (by simp)
    have : WeakEquivalence s := weakEquivalence_of_postcomp_of_fac (pullback.lift_snd _ _ _)
    exact weakEquivalence_of_precomp_of_fac (f := s) (fg := q) (by
      rw [pullback.lift_fst_assoc, Category.assoc, PrepathObject.ι_p₁, Category.comp_id])

theorem weakEquivalence_pullback_fst_of_fibration {E D D' : C} [IsFibrant D] [IsFibrant D']
    (p : E ⟶ D) [Fibration p] (q : D' ⟶ D) [WeakEquivalence q] :
    WeakEquivalence (pullback.fst p q) := by
  obtain ⟨P, _⟩ := PathObject.exists_very_good D
  let π := pullback.snd p P.p₁ ≫ P.p₀
  let σ : E ⟶ pullback p P.p₁ := pullback.lift (𝟙 E) (p ≫ P.ι) (by simp)
  have hσ : σ ≫ π = p := by
    rw [pullback.lift_snd_assoc, Category.assoc, PrepathObject.ι_p₀, Category.comp_id]
  have : WeakEquivalence σ := weakEquivalence_of_postcomp_of_fac (pullback.lift_fst _ _ _)
  have := weakEquivalence_pullback_map_of_fibration q p π σ hσ
  let k : pullback π q ⟶ pullback P.p₀ q :=
    pullback.lift (pullback.fst π q ≫ pullback.snd p P.p₁) (pullback.snd π q)
      (by rw [Category.assoc, pullback.condition])
  have sq : IsPullback k (pullback.fst π q ≫ pullback.fst p P.p₁)
      (pullback.fst P.p₀ q ≫ P.p₁) p :=
    (IsPullback.of_right (by rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback π q).flip)
      (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback P.p₀ q).flip).paste_vert
        (IsPullback.of_hasPullback p P.p₁).flip
  have : WeakEquivalence (pullback.fst π q ≫ pullback.fst p P.p₁) :=
    ((mem_trivialFibrations_iff _).1 ((trivialFibrations C).of_isPullback sq
      (trivialFibrations_pullback_fst_comp_p₁ P q))).2
  have e : pullback.fst p q = pullback.map p q π q σ (𝟙 _) (𝟙 _) (by simp [hσ]) (by simp) ≫
      pullback.fst π q ≫ pullback.fst p P.p₁ := by
    rw [pullback.lift_fst_assoc, Category.assoc, pullback.lift_fst, Category.comp_id]
  rw [e]
  infer_instance

theorem _root_.CategoryTheory.IsPullback.weakEquivalence_of_fibration {E D D' E' : C}
    [IsFibrant D] [IsFibrant D'] {p : E ⟶ D} {q : D' ⟶ D} {q' : E' ⟶ E} {p' : E' ⟶ D'}
    (h : IsPullback q' p' p q) [Fibration p] [WeakEquivalence q] : WeakEquivalence q' := by
  have := weakEquivalence_pullback_fst_of_fibration p q
  rw [← h.isoPullback_hom_fst]
  infer_instance

theorem _root_.CategoryTheory.IsPullback.weakEquivalence_map_of_fibration
    {P E A B P' E' A' B' : C} {fst : P ⟶ E} {snd : P ⟶ A} {p : E ⟶ B} {b : A ⟶ B}
    {fst' : P' ⟶ E'} {snd' : P' ⟶ A'} {p' : E' ⟶ B'} {b' : A' ⟶ B'}
    (h : IsPullback fst snd p b) (h' : IsPullback fst' snd' p' b') [Fibration p] [Fibration p']
    [IsFibrant A] [IsFibrant A'] [IsFibrant B] [IsFibrant B'] (wE : E ⟶ E') (wB : B ⟶ B')
    (wA : A ⟶ A') (wP : P ⟶ P') (hE : p ≫ wB = wE ≫ p') (hA : b ≫ wB = wA ≫ b')
    (hfst : wP ≫ fst' = fst ≫ wE) (hsnd : wP ≫ snd' = snd ≫ wA) [WeakEquivalence wE]
    [WeakEquivalence wB] [WeakEquivalence wA] : WeakEquivalence wP := by
  let π := pullback.snd p' wB
  let σ : E ⟶ pullback p' wB := pullback.lift wE p hE.symm
  have hσ : σ ≫ π = p := pullback.lift_snd _ _ _
  have := weakEquivalence_pullback_fst_of_fibration p' wB
  have : WeakEquivalence σ := weakEquivalence_of_postcomp_of_fac (pullback.lift_fst _ _ _)
  have := weakEquivalence_pullback_map_of_fibration b p π σ hσ
  let k : pullback π b ⟶ P' := h'.lift (pullback.fst π b ≫ pullback.fst p' wB)
    (pullback.snd π b ≫ wA) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, hA, Category.assoc])
  have hk : IsPullback k (pullback.snd π b) snd' wA := by
    refine IsPullback.of_right ?_ (h'.lift_snd _ _ _) h'
    rw [h'.lift_fst, ← hA]
    exact (IsPullback.of_hasPullback π b).paste_horiz (IsPullback.of_hasPullback p' wB)
  have : Fibration snd' := by
    rw [fibration_iff]
    exact (fibrations C).of_isPullback h' (by rw [← fibration_iff]; infer_instance)
  have := hk.weakEquivalence_of_fibration
  have e : wP = h.isoPullback.hom ≫
      pullback.map p b π b σ (𝟙 _) (𝟙 _) (by simp [hσ]) (by simp) ≫ k := by
    refine h'.hom_ext ?_ ?_
    · rw [hfst, Category.assoc, Category.assoc, h'.lift_fst, pullback.lift_fst_assoc,
        Category.assoc, pullback.lift_fst, h.isoPullback_hom_fst_assoc]
    · rw [hsnd, Category.assoc, Category.assoc, h'.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id, h.isoPullback_hom_snd_assoc]
  rw [e]
  infer_instance

end Over

section Span

variable [ModelCategory C] {A B A' B' Z : C}

structure ArrowSpanComparison (a : A ⟶ B) (a' : A' ⟶ B') (l : Z ⟶ B) (r : Z ⟶ B') where
  total : C
  left : total ⟶ A
  right : total ⟶ A'
  base : total ⟶ Z
  left_fac : left ≫ a = base ≫ l
  right_fac : right ≫ a' = base ≫ r
  weakEquivalence_left : WeakEquivalence left
  weakEquivalence_right : WeakEquivalence right
  trivialFibration_base : trivialFibrations C base

noncomputable def arrowSpanComparisonOfTrivialFibrations [HasPullbacks C]
    (a : A ⟶ B) (a' : A' ⟶ B') (l : Z ⟶ B) (r : Z ⟶ B')
    [Fibration a] [WeakEquivalence a] [Fibration a'] [WeakEquivalence a']
    [WeakEquivalence l] [WeakEquivalence r] : ArrowSpanComparison a a' l r := by
  let q := pullback.snd a l
  have hq : trivialFibrations C q := (trivialFibrations C).of_isPullback
    (IsPullback.of_hasPullback a l) (mem_trivialFibrations a)
  have : Fibration q := ((mem_trivialFibrations_iff _).1 hq).1
  have : WeakEquivalence q := ((mem_trivialFibrations_iff _).1 hq).2
  have he : pullback.fst a l ≫ a = q ≫ l := pullback.condition
  have : WeakEquivalence (pullback.fst a l) := weakEquivalence_of_postcomp_of_fac he
  let t := pullback.snd a' (q ≫ r)
  have ht : trivialFibrations C t := (trivialFibrations C).of_isPullback
    (IsPullback.of_hasPullback a' (q ≫ r)) (mem_trivialFibrations a')
  have : Fibration t := ((mem_trivialFibrations_iff _).1 ht).1
  have : WeakEquivalence t := ((mem_trivialFibrations_iff _).1 ht).2
  have he' : pullback.fst a' (q ≫ r) ≫ a' = t ≫ q ≫ r := pullback.condition
  have : WeakEquivalence (pullback.fst a' (q ≫ r)) :=
    weakEquivalence_of_postcomp_of_fac he'
  exact {
    total := pullback a' (q ≫ r)
    left := t ≫ pullback.fst a l
    right := pullback.fst a' (q ≫ r)
    base := t ≫ q
    left_fac := by rw [Category.assoc, he, ← Category.assoc]
    right_fac := he'.trans (Category.assoc _ _ _).symm
    weakEquivalence_left := inferInstance
    weakEquivalence_right := inferInstance
    trivialFibration_base := mem_trivialFibrations _ }

end Span

section Under

variable [ModelCategory C] {A B : C}

theorem isQuillen_mapPushoutAdj (g : A ⟶ B) : (Under.mapPushoutAdj g).IsQuillen :=
  (Under.mapPushoutAdj g).isQuillen_of_fibrations_of_trivialFibrations
    (fun _ _ _ hf ↦ hf) (fun _ _ _ hf ↦ hf)

theorem weakEquivalence_pushout_map_of_cofibration {X X' : C} (g : A ⟶ B) (i : A ⟶ X)
    (i' : A ⟶ X') [Cofibration i] [Cofibration i'] (w : X ⟶ X') (hw : i ≫ w = i')
    [WeakEquivalence w] :
    WeakEquivalence (pushout.map i g i' g w (𝟙 _) (𝟙 _) (by simp [hw]) (by simp)) := by
  have := (isCofibrant_under_mk_iff A i).2 ‹_›
  have := (isCofibrant_under_mk_iff A i').2 ‹_›
  let w' : Under.mk i ⟶ Under.mk i' := Under.homMk w hw
  have : WeakEquivalence w' := by rwa [weakEquivalences_under_iff]
  have h := (isQuillen_mapPushoutAdj g).weakEquivalence_map w'
  rw [weakEquivalences_under_iff] at h
  have e : pushout.map i g i' g w (𝟙 _) (𝟙 _) (by simp [hw]) (by simp) =
      ((Under.pushout g).map w').right :=
    pushout.hom_ext (by simp [w', pushout.map]) (by simp [w', pushout.map])
  rwa [e]

theorem isQuillen_postAdjunctionLeft {D : Type u₂} [Category.{v₂} D] [ModelCategory D]
    {F : C ⥤ D} {G : D ⥤ C} {adj : F ⊣ G} (h : adj.IsQuillen) (X : C) :
    (Under.postAdjunctionLeft (X := X) adj).IsQuillen where
  cofibrations_le _ _ f hf := h.cofibrations_le f.right hf
  trivialCofibrations_le _ _ f hf := h.trivialCofibrations_le f.right hf

theorem isQuillenEquivalence_postAdjunctionLeft {D : Type u₂} [Category.{v₂} D]
    [ModelCategory D] {F : C ⥤ D} {G : D ⥤ C} {adj : F ⊣ G} (h : adj.IsQuillenEquivalence)
    (X : C) [IsCofibrant X] :
    (Under.postAdjunctionLeft (X := X) adj).IsQuillenEquivalence where
  toIsQuillen := isQuillen_postAdjunctionLeft h.toIsQuillen X
  weakEquivalence_iff {Y Z} _ _ f := by
    have : Cofibration Y.hom := (isCofibrant_under_mk_iff X Y.hom).1 ‹_›
    have : IsCofibrant ((𝟭 C).obj X) := ‹IsCofibrant X›
    have : IsCofibrant Y.right := isCofibrant_of_cofibration Y.hom
    have : IsFibrant Z.right := (isFibrant_under_iff _ Z).1 ‹_›
    have e : ((Under.postAdjunctionLeft adj).homEquiv Y Z f).right =
        adj.homEquiv Y.right Z.right f.right := by
      simp only [Adjunction.homEquiv_unit]
      rfl
    rw [weakEquivalences_under_iff, weakEquivalences_under_iff, e]
    exact h.weakEquivalence_iff f.right

end Under

end HomotopicalAlgebra
