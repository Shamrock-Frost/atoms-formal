import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CommaCone

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory Simplicial
  MorphismProperty HomotopicalAlgebra

universe u

namespace SSet

section FiberMap

noncomputable abbrev fiberMap {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F)
    (hφ : φ ≫ q = p) (b : B _⦋0⦌) :
    pullback p (yonedaEquiv.symm b) ⟶ pullback q (yonedaEquiv.symm b) :=
  pullback.map p (yonedaEquiv.symm b) q (yonedaEquiv.symm b) φ (𝟙 _) (𝟙 _)
    (by simp [hφ]) (by simp)

theorem fiberMap_comp {E F G B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} {r : G ⟶ B}
    (φ : E ⟶ F) (ψ : F ⟶ G) (hφ : φ ≫ q = p) (hψ : ψ ≫ r = q) (b : B _⦋0⦌) :
    fiberMap (φ ≫ ψ) (by rw [Category.assoc, hψ, hφ]) b = fiberMap φ hφ b ≫ fiberMap ψ hψ b := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
  · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]

theorem fiberMap_id {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    fiberMap (𝟙 E) (Category.id_comp p) b = 𝟙 _ :=
  pullback.map_id

theorem isPullback_fiberMap {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F)
    (hφ : φ ≫ q = p) (b : B _⦋0⦌) :
    IsPullback (pullback.fst p (yonedaEquiv.symm b)) (fiberMap φ hφ b) φ
      (pullback.fst q (yonedaEquiv.symm b)) := by
  have h : fiberMap φ hφ b ≫ pullback.snd q (yonedaEquiv.symm b) = pullback.snd _ _ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
    (IsPullback.of_hasPullback q (yonedaEquiv.symm b))
  rw [h, hφ]
  exact IsPullback.of_hasPullback _ _

theorem trivialFibration_fiberMap {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F)
    (hφ : φ ≫ q = p) (h : modelCategoryQuillen.I.rlp φ) (b : B _⦋0⦌) :
    modelCategoryQuillen.I.rlp (fiberMap φ hφ b) :=
  MorphismProperty.of_isPullback (isPullback_fiberMap φ hφ b) h

theorem rightFibrations_fiberMap {E F B : SSet.{u}} {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F)
    (hφ : φ ≫ q = p) (h : rightFibrations φ) (b : B _⦋0⦌) : rightFibrations (fiberMap φ hφ b) :=
  MorphismProperty.of_isPullback (P := rightHornInclusions.rlp) (isPullback_fiberMap φ hφ b) h

theorem isPullback_fiberMap_of_isPullback {E A A' B : SSet.{u}} {a : E ⟶ A} {a' : E ⟶ A'}
    {f : A ⟶ B} {f' : A' ⟶ B} (h : IsPullback a a' f f') {p : E ⟶ B} (ha : a ≫ f = p)
    (ha' : a' ≫ f' = p) (b : B _⦋0⦌) :
    IsPullback (fiberMap a ha b) (fiberMap a' ha' b) (pullback.snd f (yonedaEquiv.symm b))
      (pullback.snd f' (yonedaEquiv.symm b)) := by
  have h₁ := (isPullback_fiberMap a' ha' b).paste_horiz h
  rw [pullback.condition, (isPullback_fiberMap a ha b).w] at h₁
  exact IsPullback.of_right h₁ (stdSimplex.isTerminalObj₀.hom_ext _ _)
    (IsPullback.of_hasPullback f (yonedaEquiv.symm b))

noncomputable def fiberVertex {X S : SSet.{u}} (p : X ⟶ S) (x : X _⦋0⦌) {b : S _⦋0⦌}
    (hx : p.app _ x = b) : (pullback p (yonedaEquiv.symm b)) _⦋0⦌ :=
  yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (𝟙 Δ[0]) (by
    rw [yonedaEquiv_symm_comp, hx, Category.id_comp]))

@[reassoc]
theorem yonedaEquiv_symm_fiberVertex_fst {X S : SSet.{u}} (p : X ⟶ S) (x : X _⦋0⦌)
    {b : S _⦋0⦌} (hx : p.app _ x = b) :
    yonedaEquiv.symm (fiberVertex p x hx) ≫ pullback.fst _ _ = yonedaEquiv.symm x := by
  rw [fiberVertex, Equiv.symm_apply_apply, pullback.lift_fst]

theorem isPullback_fiber_fiberMap {P G B : SSet.{u}} (π : P ⟶ G) (pG : G ⟶ B) {g : G _⦋0⦌}
    {b : B _⦋0⦌} (hg : pG.app _ g = b) :
    IsPullback (pullback.lift (pullback.fst π (yonedaEquiv.symm g)) (pullback.snd _ _) (by
        rw [pullback.condition_assoc, yonedaEquiv_symm_comp, hg]) :
        pullback π (yonedaEquiv.symm g) ⟶ pullback (π ≫ pG) (yonedaEquiv.symm b))
      (pullback.snd π (yonedaEquiv.symm g)) (fiberMap (p := π ≫ pG) π rfl b)
      (yonedaEquiv.symm (fiberVertex pG g hg)) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst _ _) (h₂₂ := pullback.fst _ _) ?_ ?_
    (isPullback_fiberMap π rfl b)
  · rw [pullback.lift_fst, yonedaEquiv_symm_fiberVertex_fst]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        yonedaEquiv_symm_fiberVertex_fst, pullback.condition]
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
      exact stdSimplex.isTerminalObj₀.hom_ext _ _

end FiberMap

section Evaluation

@[simp]
theorem uncurry_constDiagram (K X : SSet.{u}) : uncurry (constDiagram K X) = snd K X := by
  rw [constDiagram, uncurry_curry]

@[reassoc (attr := simp)]
theorem constDiagram_comp_evalVertex {A : SSet.{u}} (a : A _⦋0⦌) (X : SSet.{u}) :
    constDiagram A X ≫ evalVertex a X = 𝟙 X := by
  rw [comp_evalVertex, uncurry_constDiagram, lift_snd]

instance isIso_constDiagram_stdSimplex_zero (X : SSet.{u}) : IsIso (constDiagram Δ[0] X) :=
  inferInstanceAs (IsIso (ihomStdSimplexZeroIso X).inv)

theorem ihomStdSimplexZeroIso_hom_eq_evalVertex (X : SSet.{u}) :
    (ihomStdSimplexZeroIso X).hom = evalVertex (yonedaEquiv (𝟙 Δ[0])) X :=
  (cancel_epi (constDiagram Δ[0] X)).1
    ((ihomStdSimplexZeroIso X).inv_hom_id.trans (constDiagram_comp_evalVertex _ _).symm)

instance isIso_evalVertex_stdSimplex_zero (X : SSet.{u}) :
    IsIso (evalVertex (yonedaEquiv (𝟙 Δ[0])) X) :=
  IsIso.of_isIso_fac_left (constDiagram_comp_evalVertex _ X)

@[reassoc]
theorem whiskerRight_comp_uncurry {A X Z : SSet.{u}} (a : A _⦋0⦌) (g : Z ⟶ (ihom A).obj X) :
    yonedaEquiv.symm a ▷ Z ≫ uncurry g = snd _ _ ≫ g ≫ evalVertex a X := by
  have h : yonedaEquiv.symm a ▷ Z =
      snd _ _ ≫ lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm a) (𝟙 Z) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ (by simp)
    rw [whiskerRight_fst, Category.assoc, lift_fst, ← Category.assoc]
    exact congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)
  rw [h, Category.assoc, comp_evalVertex]

theorem yonedaEquiv_symm_obj₀Equiv_symm (ε : Fin 2) :
    (yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm ε) : Δ[0] ⟶ (Δ[1] : SSet.{u})) =
      stdSimplex.δ ε.rev := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply stdSimplex.obj₀Equiv.injective
  rw [Equiv.apply_symm_apply]
  fin_cases ε <;> rfl

private lemma horn_one_one_ι :
    (horn.{u} 1 1).ι =
      stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 1) := by
  rw [yonedaEquiv_symm_obj₀Equiv_symm]
  refine horn.hom_ext' fun j hj ↦ ?_
  obtain rfl : j = 0 := by
    fin_cases j
    · rfl
    · exact (hj rfl).elim
  rw [horn.ι_ι, ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext
    (horn.ι 1 0 hj ≫ stdSimplex.isTerminalObj₀.from _) (𝟙 _), Category.id_comp]
  rfl

private lemma horn_one_one_whiskerRight_comp_uncurry {X Z : SSet.{u}}
    (g : Z ⟶ (ihom Δ[1]).obj X) :
    (horn.{u} 1 1).ι ▷ Z ≫ uncurry g =
      snd _ _ ≫ g ≫ evalVertex (stdSimplex.obj₀Equiv.symm 1) X := by
  rw [horn_one_one_ι, comp_whiskerRight, Category.assoc, whiskerRight_comp_uncurry,
    whiskerRight_snd_assoc]

private lemma eq_of_snd_comp {X Z : SSet.{u}} {f g : Z ⟶ X}
    (h : snd (Δ[0] : SSet.{u}) Z ≫ f = snd _ _ ≫ g) : f = g := by
  simpa using congrArg (lift (stdSimplex.isTerminalObj₀.from Z) (𝟙 Z) ≫ ·) h

end Evaluation

section FiberwisePath

variable {Z F B : SSet.{u}}

noncomputable abbrev fiberwisePath (q : F ⟶ B) : SSet.{u} :=
  pullback ((ihom Δ[1]).map q) (constDiagram Δ[1] B)

noncomputable def fiberwisePathMk {q : F ⟶ B} (H : Δ[1] ⊗ Z ⟶ F) (c : Z ⟶ B)
    (h : H ≫ q = snd _ _ ≫ c) : Z ⟶ fiberwisePath q :=
  pullback.lift (curry H) c (by
    rw [← curry_natural_right, h, curry_eq_iff, uncurry_natural_left, uncurry_constDiagram,
      whiskerLeft_snd])

@[reassoc (attr := simp)]
theorem fiberwisePathMk_fst {q : F ⟶ B} (H : Δ[1] ⊗ Z ⟶ F) (c : Z ⟶ B)
    (h : H ≫ q = snd _ _ ≫ c) : fiberwisePathMk H c h ≫ pullback.fst _ _ = curry H :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberwisePathMk_snd {q : F ⟶ B} (H : Δ[1] ⊗ Z ⟶ F) (c : Z ⟶ B)
    (h : H ≫ q = snd _ _ ≫ c) : fiberwisePathMk H c h ≫ pullback.snd _ _ = c :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem uncurry_fst_comp {q : F ⟶ B} (γ : Z ⟶ fiberwisePath q) :
    uncurry (γ ≫ pullback.fst _ _) ≫ q = snd _ _ ≫ γ ≫ pullback.snd _ _ := by
  rw [← uncurry_natural_right, Category.assoc, pullback.condition, ← Category.assoc,
    uncurry_natural_left, uncurry_constDiagram, whiskerLeft_snd]

noncomputable def fiberwisePathEval (q : F ⟶ B) (ε : Fin 2) : fiberwisePath q ⟶ F :=
  pullback.fst _ _ ≫ evalVertex (stdSimplex.obj₀Equiv.symm ε) F

@[reassoc]
theorem fiberwisePathEval_comp_eq_snd (q : F ⟶ B) (ε : Fin 2) :
    fiberwisePathEval q ε ≫ q = pullback.snd _ _ := by
  rw [fiberwisePathEval, Category.assoc, ← ihom_map_comp_evalVertex, ← Category.assoc,
    pullback.condition, Category.assoc, constDiagram_comp_evalVertex, Category.comp_id]

@[reassoc]
theorem fiberwisePathEval_comp (q : F ⟶ B) (ε ε' : Fin 2) :
    fiberwisePathEval q ε ≫ q = fiberwisePathEval q ε' ≫ q := by
  rw [fiberwisePathEval_comp_eq_snd, fiberwisePathEval_comp_eq_snd]

private lemma boundary_ι_whiskerRight_comp_uncurry {q : F ⟶ B} (γ : Z ⟶ fiberwisePath q)
    (j ε : Fin 2) (h : j.rev = ε) :
    boundary.ι j ▷ Z ≫ (∂Δ[1]).ι ▷ Z ≫ uncurry (γ ≫ pullback.fst _ _) =
      snd _ _ ≫ γ ≫ fiberwisePathEval q ε := by
  subst h
  have h := whiskerRight_comp_uncurry (stdSimplex.obj₀Equiv.symm j.rev) (γ ≫ pullback.fst _ _)
  rw [yonedaEquiv_symm_obj₀Equiv_symm, Fin.rev_rev] at h
  rw [← comp_whiskerRight_assoc, boundary.ι_ι, h, Category.assoc]
  rfl

@[reassoc]
theorem fiberwisePathMk_eval {q : F ⟶ B} (H : Δ[1] ⊗ Z ⟶ F) (c : Z ⟶ B)
    (h : H ≫ q = snd _ _ ≫ c) (ε : Fin 2) :
    fiberwisePathMk H c h ≫ fiberwisePathEval q ε =
      lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm ε))
        (𝟙 Z) ≫ H := by
  rw [fiberwisePathEval, fiberwisePathMk_fst_assoc, comp_evalVertex, uncurry_curry]

noncomputable def fiberwisePathConst (q : F ⟶ B) : F ⟶ fiberwisePath q :=
  fiberwisePathMk (snd Δ[1] F) q rfl

@[reassoc (attr := simp)]
theorem fiberwisePathConst_eval (q : F ⟶ B) (ε : Fin 2) :
    fiberwisePathConst q ≫ fiberwisePathEval q ε = 𝟙 F := by
  rw [fiberwisePathConst, fiberwisePathMk_eval, lift_snd]

theorem exists_fiberwisePath_extension {A K L : SSet.{u}} {i : A ⟶ Δ[1]} {j : K ⟶ L}
    {q : F ⟶ B} (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) [HasLiftingProperty sq.ι q]
    (γ : K ⟶ fiberwisePath q) (g : A ⊗ L ⟶ F) (c : L ⟶ B)
    (hγ : i ▷ K ≫ uncurry (γ ≫ pullback.fst _ _) = A ◁ j ≫ g) (hg : g ≫ q = snd _ _ ≫ c)
    (hc : j ≫ c = γ ≫ pullback.snd _ _) :
    ∃ γ' : L ⟶ fiberwisePath q, j ≫ γ' = γ ∧
      i ▷ L ≫ uncurry (γ' ≫ pullback.fst _ _) = g ∧ γ' ≫ pullback.snd _ _ = c := by
  let u := sq.isPushout.desc (uncurry (γ ≫ pullback.fst _ _)) g hγ
  have hu : CommSq u sq.ι q (snd _ _ ≫ c) := ⟨sq.isPushout.hom_ext
    (by
      rw [sq.isPushout.inl_desc_assoc, sq.inl_ι_assoc, uncurry_fst_comp, ← hc]
      exact (whiskerLeft_snd_assoc _ _ _).symm)
    (by
      rw [sq.isPushout.inr_desc_assoc, sq.inr_ι_assoc, hg]
      exact (whiskerRight_snd_assoc _ _ _).symm)⟩
  let M := hu.lift
  have hMl : sq.ι ≫ M = u := hu.fac_left
  have hMr : M ≫ q = snd _ _ ≫ c := hu.fac_right
  have hl : (Δ[1] : SSet.{u}) ◁ j ≫ M = uncurry (γ ≫ pullback.fst _ _) :=
    (sq.inl_ι_assoc M).symm.trans ((congrArg (sq.inl ≫ ·) hMl).trans (sq.isPushout.inl_desc _ _ _))
  have hr : i ▷ L ≫ M = g :=
    (sq.inr_ι_assoc M).symm.trans ((congrArg (sq.inr ≫ ·) hMl).trans (sq.isPushout.inr_desc _ _ _))
  refine ⟨fiberwisePathMk M c hMr, pullback.hom_ext ?_ ?_, ?_, fiberwisePathMk_snd _ _ _⟩
  · rw [Category.assoc, fiberwisePathMk_fst, ← curry_natural_left, hl, curry_uncurry]
  · rw [Category.assoc, fiberwisePathMk_snd, hc]
  · rw [fiberwisePathMk_fst, uncurry_curry, hr]

theorem trivialFibration_fiberwisePathEval_one {q : F ⟶ B} (hq : rightFibrations q) :
    modelCategoryQuillen.I.rlp (fiberwisePathEval q 1) := by
  rintro _ _ _ ⟨n⟩
  refine ⟨fun {γ f} sq ↦ ?_⟩
  let sq₁ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) Λ[1, 1].ι (∂Δ[n]).ι
  have : HasLiftingProperty sq₁.ι q := rightAnodyneExtensions_pushoutObjObjι_left sq₁
    (rightAnodyneExtensions.horn_ι (by decide : (0 : Fin 2) < 1)) q hq
  obtain ⟨γ', hγ'l, hγ'r, -⟩ := exists_fiberwisePath_extension sq₁ γ (snd _ _ ≫ f) (f ≫ q)
    (by
      rw [horn_one_one_whiskerRight_comp_uncurry, Category.assoc γ, ← fiberwisePathEval, sq.w]
      exact (whiskerLeft_snd_assoc _ _ _).symm)
    (Category.assoc _ _ _)
    (by rw [← fiberwisePathEval_comp_eq_snd q 1, sq.w_assoc])
  refine ⟨⟨⟨γ', hγ'l, ?_⟩⟩⟩
  rw [horn_one_one_whiskerRight_comp_uncurry, Category.assoc γ', ← fiberwisePathEval] at hγ'r
  simpa using congrArg (lift (stdSimplex.isTerminalObj₀.from _ ≫ horn.ι 1 0 (by decide)) (𝟙 _) ≫ ·)
    hγ'r

end FiberwisePath

section FiberwiseMappingPath

variable {E F B : SSet.{u}}

noncomputable abbrev fiberwiseMappingPath (q : F ⟶ B) (φ : E ⟶ F) : SSet.{u} :=
  pullback φ (fiberwisePathEval q 1)

noncomputable def fiberwiseMappingPathι (q : F ⟶ B) (φ : E ⟶ F) :
    E ⟶ fiberwiseMappingPath q φ :=
  pullback.lift (𝟙 E) (φ ≫ fiberwisePathConst q) (by simp)

noncomputable def fiberwiseMappingPathπ (q : F ⟶ B) (φ : E ⟶ F) :
    fiberwiseMappingPath q φ ⟶ F :=
  pullback.snd _ _ ≫ fiberwisePathEval q 0

@[reassoc (attr := simp)]
theorem fiberwiseMappingPathι_fst (q : F ⟶ B) (φ : E ⟶ F) :
    fiberwiseMappingPathι q φ ≫ pullback.fst _ _ = 𝟙 E :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fiberwiseMappingPathι_π (q : F ⟶ B) (φ : E ⟶ F) :
    fiberwiseMappingPathι q φ ≫ fiberwiseMappingPathπ q φ = φ := by
  rw [fiberwiseMappingPathι, fiberwiseMappingPathπ, pullback.lift_snd_assoc, Category.assoc,
    fiberwisePathConst_eval, Category.comp_id]

@[reassoc]
theorem fiberwiseMappingPath_fst_comp {p : E ⟶ B} {q : F ⟶ B} (φ : E ⟶ F) (hφ : φ ≫ q = p) :
    pullback.fst _ _ ≫ p = fiberwiseMappingPathπ q φ ≫ q := by
  rw [← hφ, pullback.condition_assoc, fiberwiseMappingPathπ, Category.assoc,
    fiberwisePathEval_comp q 1 0]

theorem trivialFibration_fiberwiseMappingPath_fst {q : F ⟶ B} (hq : rightFibrations q)
    (φ : E ⟶ F) : modelCategoryQuillen.I.rlp (pullback.fst φ (fiberwisePathEval q 1)) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip
    (trivialFibration_fiberwisePathEval_one hq)

theorem rightFibrations_fiberwiseMappingPathπ {p : E ⟶ B} {q : F ⟶ B}
    (hp : rightFibrations p) (hq : rightFibrations q) (φ : E ⟶ F) (hφ : φ ≫ q = p) :
    rightFibrations (fiberwiseMappingPathπ q φ) := by
  rintro _ _ _ ⟨i, h0⟩
  refine ⟨fun {a f} sq ↦ ?_⟩
  have hw : a ≫ pullback.snd _ _ ≫ fiberwisePathEval q 0 = Λ[_, i].ι ≫ f := sq.w
  have : HasLiftingProperty Λ[_, i].ι p := hp _ (.intro i h0)
  have sqe : CommSq (a ≫ pullback.fst _ _) Λ[_, i].ι p (f ≫ q) := ⟨by
    rw [Category.assoc, ← hφ, pullback.condition_assoc, fiberwisePathEval_comp q 1 0,
      reassoc_of% hw]⟩
  let e := sqe.lift
  have hel : Λ[_, i].ι ≫ e = a ≫ pullback.fst _ _ := sqe.fac_left
  have her : e ≫ p = f ≫ q := sqe.fac_right
  let sq₁ := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (∂Δ[1]).ι Λ[_, i].ι
  have : HasLiftingProperty sq₁.ι q := rightAnodyneExtensions_pushoutObjObjι sq₁
    (rightAnodyneExtensions.horn_ι h0) q hq
  obtain ⟨γ, hγl, hγr, -⟩ := exists_fiberwisePath_extension sq₁ (a ≫ pullback.snd _ _)
    (boundaryOneTensorDesc f (e ≫ φ)) (f ≫ q)
    (boundaryOneTensor_hom_ext
      (by
        rw [boundary_ι_whiskerRight_comp_uncurry _ 1 0 rfl, ← whisker_exchange_assoc,
          boundary_ι_one_whiskerRight_boundaryOneTensorDesc, Category.assoc, hw]
        exact (whiskerLeft_snd_assoc _ _ _).symm)
      (by
        rw [boundary_ι_whiskerRight_comp_uncurry _ 0 1 rfl, ← whisker_exchange_assoc,
          boundary_ι_zero_whiskerRight_boundaryOneTensorDesc, Category.assoc,
          ← pullback.condition, ← reassoc_of% hel]
        exact (whiskerLeft_snd_assoc _ _ _).symm))
    (boundaryOneTensor_hom_ext
      (by rw [boundary_ι_one_whiskerRight_boundaryOneTensorDesc_assoc, whiskerRight_snd_assoc])
      (by rw [boundary_ι_zero_whiskerRight_boundaryOneTensorDesc_assoc, whiskerRight_snd_assoc,
        Category.assoc, hφ, her]))
    (by rw [← fiberwisePathEval_comp_eq_snd q 0, Category.assoc, reassoc_of% hw])
  have hγ (j ε : Fin 2) (h : j.rev = ε) : snd _ _ ≫ γ ≫ fiberwisePathEval q ε =
      boundary.ι j ▷ _ ≫ boundaryOneTensorDesc f (e ≫ φ) := by
    rw [← hγr, boundary_ι_whiskerRight_comp_uncurry _ j ε h]
  refine ⟨⟨⟨pullback.lift e γ (eq_of_snd_comp ((hγ 0 1 rfl).trans
    (boundary_ι_zero_whiskerRight_boundaryOneTensorDesc _ _))).symm, pullback.hom_ext ?_ ?_, ?_⟩⟩⟩
  · rw [Category.assoc, pullback.lift_fst, hel]
  · rw [Category.assoc, pullback.lift_snd, hγl]
  · rw [fiberwiseMappingPathπ, pullback.lift_snd_assoc]
    exact eq_of_snd_comp ((hγ 1 0 rfl).trans
      (boundary_ι_one_whiskerRight_boundaryOneTensorDesc _ _))

end FiberwiseMappingPath

end SSet
