import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianMappingSpace

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

section Collapse

private noncomputable def joinCollapse : join Δ[0] Δ[1] ⟶ (Δ[1] : SSet.{u}) :=
  (stdSimplexJoinIso 0 1).hom ≫ stdSimplex.σ 0

@[reassoc]
private lemma joinInclRight_comp_joinCollapse :
    joinInclRight Δ[0] Δ[1] ≫ joinCollapse.{u} = 𝟙 _ := by
  rw [joinCollapse, ← Category.assoc, joinInclRight_comp_stdSimplexJoinIso_hom]
  refine (stdSimplex.map_comp _ _).symm.trans ((congrArg stdSimplex.map ?_).trans
    (stdSimplex.map_id _))
  ext i : 3
  fin_cases i <;> rfl

private lemma joinMap_δ_comp_joinCollapse (i : Fin 2) :
    joinMap (𝟙 Δ[0]) (stdSimplex.δ i) ≫ joinCollapse.{u} = (stdSimplexJoinIso 0 0).hom ≫
      stdSimplex.map (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌) (SimplexCategory.δ i) ≫
        SimplexCategory.σ 0) := by
  have h := (congrArg (fun φ ↦ joinMap φ (stdSimplex.δ i) ≫ (stdSimplexJoinIso.{u} 0 1).hom)
    (stdSimplex.map_id ⦋0⦌)).symm.trans
      (joinMap_stdSimplex_map_comp_stdSimplexJoinIso_hom (𝟙 ⦋0⦌) (SimplexCategory.δ (n := 0) i))
  rw [joinCollapse, ← Category.assoc, h, Category.assoc]
  exact congrArg _ (stdSimplex.map_comp _ _).symm

@[reassoc]
private lemma joinMap_δ_zero_comp_joinCollapse :
    joinMap (𝟙 Δ[0]) (stdSimplex.δ 0) ≫ joinCollapse.{u} = (stdSimplexJoinIso 0 0).hom := by
  refine (joinMap_δ_comp_joinCollapse 0).trans ((congrArg _ ((congrArg stdSimplex.map ?_).trans
    (stdSimplex.map_id _))).trans (Category.comp_id _))
  ext i : 3
  fin_cases i <;> rfl

@[reassoc]
private lemma joinMap_δ_one_comp_joinCollapse :
    joinMap (𝟙 Δ[0]) (stdSimplex.δ 1) ≫ joinCollapse.{u} =
      ((stdSimplexJoinIso 0 0).hom ≫ stdSimplex.σ 0) ≫ stdSimplex.δ 1 := by
  refine (joinMap_δ_comp_joinCollapse 1).trans (((congrArg _ ((congrArg stdSimplex.map ?_).trans
    (stdSimplex.map_comp _ _))).trans (Category.assoc _ _ _).symm))
  ext i : 3
  fin_cases i <;> rfl

private lemma homEquiv_symm_comp_sliceRes_right {K B B' : SSet.{u}} (g : B' ⟶ B) (t : Under B)
    (ψ : K ⟶ (slice B).obj t) :
    (((joinRightUnderAdjunction B').homEquiv _ _).symm (ψ ≫ sliceRes g t)).right =
      joinMap (𝟙 K) g ≫ (((joinRightUnderAdjunction B).homEquiv _ _).symm ψ).right := by
  have hres : sliceRes g t = (joinRightUnderAdjunction B').homEquiv _ (Under.mk (g ≫ t.hom))
      (Under.homMk (joinMap (𝟙 ((slice B).obj t)) g ≫
        (((joinRightUnderAdjunction B).homEquiv _ t).symm (𝟙 _)).right) (by
          exact (joinInclRight_comp_joinMap_assoc _ _ _).trans (congrArg (g ≫ ·)
            (Under.w (((joinRightUnderAdjunction B).homEquiv _ t).symm (𝟙 _)))))) :=
    rfl
  have h₁ : (((joinRightUnderAdjunction B).homEquiv _ _).symm ψ).right =
      joinMap ψ (𝟙 B) ≫ (((joinRightUnderAdjunction B).homEquiv _ t).symm (𝟙 _)).right := by
    conv_lhs => rw [← Category.comp_id ψ]
    rw [Adjunction.homEquiv_naturality_left_symm, Under.comp_right]
    rfl
  rw [h₁, hres, ← Adjunction.homEquiv_naturality_left, Equiv.symm_apply_apply, Under.comp_right]
  refine (joinMap_comp_joinMap_assoc ψ (𝟙 B') (𝟙 _) g _).trans ?_
  simp only [Category.comp_id, Category.id_comp]
  exact ((joinMap_comp_joinMap_assoc (𝟙 K) g ψ (𝟙 B) _).trans (congrArg (· ≫ _)
    (congrArg₂ joinMap (Category.id_comp ψ) (Category.comp_id g)))).symm

private lemma slice_map_comp_slice_map {T : SSet.{u}} {t₁ t₂ t₃ t₄ : Under T} (a : t₁ ⟶ t₂)
    (b : t₂ ⟶ t₃) (c : t₁ ⟶ t₄) (d : t₄ ⟶ t₃) (h : a.right ≫ b.right = c.right ≫ d.right) :
    (slice T).map a ≫ (slice T).map b = (slice T).map c ≫ (slice T).map d := by
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (Under.UnderMorphism.ext h)

private lemma slice_map_comp_slice_map_eq_id {T : SSet.{u}} {t₁ t₂ : Under T} (a : t₁ ⟶ t₂)
    (b : t₂ ⟶ t₁) (h : a.right ≫ b.right = 𝟙 _) : (slice T).map a ≫ (slice T).map b = 𝟙 _ := by
  rw [← Functor.map_comp, ← (slice T).map_id]
  exact congrArg _ (Under.UnderMorphism.ext h)

end Collapse

section Fiber

private lemma exists_rlp_fiber_leibnizSlice {K X S : SSet.{u}} (p : X ⟶ S) (j : Δ[0] ⟶ K)
    (f : K ⟶ X) (hψ : modelCategoryQuillen.I.rlp (leibnizSlice j p f)) {x z : X _⦋0⦌}
    {b c : S _⦋0⦌} (hx : p.app _ x = b) (hz : p.app _ z = c) (hjf : j ≫ f = yonedaEquiv.symm z)
    {Φ : SSet.{u}} {k : Φ ⟶ pullback (sliceAtπ X z) (yonedaEquiv.symm x)} {l : Φ ⟶ Δ[0]}
    {w : Δ[0] ⟶ pullback (sliceAtπ S c) (yonedaEquiv.symm b)}
    (hΦ : IsPullback k l (sliceAtFiberMap p hx hz) w)
    (σ : Δ[0] ⟶ (slice K).obj (Under.mk (f ≫ p)))
    (hσ : joinMap (𝟙 Δ[0]) j ≫ (((joinRightUnderAdjunction K).homEquiv _ _).symm σ).right =
      (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm (w ≫ pullback.fst _ _)).right) :
    ∃ a : pullback (prod.lift ((slice K).map (Under.homMk p : Under.mk f ⟶ Under.mk (f ≫ p)))
      (sliceπ (Under.mk f)) : _ ⟶ _ ⨯ X) (prod.lift σ (yonedaEquiv.symm x)) ⟶ Φ,
      modelCategoryQuillen.I.rlp a := by
  have hzp : yonedaEquiv.symm z ≫ p = yonedaEquiv.symm c :=
    (yonedaEquiv_symm_comp z p).trans (congrArg _ hz)
  let ιX := (slice Δ[0]).map (Under.homMk (𝟙 X) ((Category.comp_id _).trans hjf.symm) :
    Under.mk (yonedaEquiv.symm z) ⟶ Under.mk (j ≫ f))
  let ιX' := (slice Δ[0]).map (Under.homMk (𝟙 X) ((Category.comp_id _).trans hjf) :
    Under.mk (j ≫ f) ⟶ Under.mk (yonedaEquiv.symm z))
  let ιS := (slice Δ[0]).map (Under.homMk (𝟙 S) ((Category.comp_id _).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) hjf).trans hzp))) :
    Under.mk (j ≫ f ≫ p) ⟶ Under.mk (yonedaEquiv.symm c))
  let μ := (slice Δ[0]).map (Under.homMk p hzp :
    Under.mk (yonedaEquiv.symm z) ⟶ Under.mk (yonedaEquiv.symm c))
  have hφ : sliceAtFiberMap p hx hz ≫ pullback.fst _ _ = pullback.fst _ _ ≫ μ :=
    pullback.lift_fst _ _ _
  set ιS' := (slice Δ[0]).map (Under.homMk (𝟙 S) ((Category.comp_id _).trans
        (((congrArg yonedaEquiv.symm hz).symm.trans (yonedaEquiv_symm_comp z p).symm).trans
          ((congrArg (· ≫ p) hjf.symm).trans (Category.assoc _ _ _)))) :
      Under.mk (yonedaEquiv.symm c) ⟶ Under.mk (j ≫ f ≫ p)) with hιS'
  have hσ' : σ ≫ sliceRes j (Under.mk (f ≫ p)) = w ≫ pullback.fst _ _ ≫ ιS' := by
    apply ((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm.injective
    apply Under.UnderMorphism.ext
    rw [homEquiv_symm_comp_sliceRes_right, hσ, hιS', ← Category.assoc,
      Adjunction.homEquiv_naturality_right_symm, Under.comp_right]
    exact (Category.comp_id _).symm
  set α := (slice Δ[0]).map (Under.homMk p (by simp) :
    Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ p)) with hα
  have e₁ : ιX ≫ α = μ ≫ ιS' :=
    slice_map_comp_slice_map _ _ _ _ ((Category.id_comp p).trans (Category.comp_id p).symm)
  have e₂ : ιX' ≫ μ = α ≫ ιS :=
    slice_map_comp_slice_map _ _ _ _ ((Category.id_comp p).trans (Category.comp_id p).symm)
  have e₃ : ιX' ≫ ιX = 𝟙 _ := slice_map_comp_slice_map_eq_id _ _ (Category.comp_id _)
  have e₃' : ιX ≫ ιX' = 𝟙 _ := slice_map_comp_slice_map_eq_id _ _ (Category.comp_id _)
  have e₄ : ιS' ≫ ιS = 𝟙 _ :=
    slice_map_comp_slice_map_eq_id _ _ (Category.comp_id _)
  have e₅ : ιX ≫ sliceπ (Under.mk (j ≫ f)) = sliceAtπ X z :=
    (slice_map_sliceπ _).trans (Category.comp_id _)
  have e₆ : ιX' ≫ sliceAtπ X z = sliceπ (Under.mk (j ≫ f)) :=
    (slice_map_sliceπ _).trans (Category.comp_id _)
  have hk : k ≫ pullback.snd _ _ = l := stdSimplex.isTerminalObj₀.hom_ext _ _
  have hi : (k ≫ pullback.fst _ _ ≫ ιX) ≫ α = (l ≫ σ) ≫ sliceRes j (Under.mk (f ≫ p)) := by
    simp only [Category.assoc, e₁, ← reassoc_of% hφ, reassoc_of% hΦ.w, hσ']
  have hs (s : PullbackCone (prod.lift (pullback.snd _ _) (pullback.fst _ _ ≫ sliceπ _) :
      pullback α (sliceRes j (Under.mk (f ≫ p))) ⟶ _) (prod.lift σ (yonedaEquiv.symm x))) :
      s.fst ≫ pullback.snd _ _ = s.snd ≫ σ ∧
        s.fst ≫ pullback.fst _ _ ≫ sliceπ _ = s.snd ≫ yonedaEquiv.symm x := by
    refine ⟨?_, ?_⟩
    · simpa only [Category.assoc, prod.lift_fst] using congrArg (· ≫ prod.fst) s.condition
    · simpa only [Category.assoc, prod.lift_snd] using congrArg (· ≫ prod.snd) s.condition
  have hP : IsPullback (pullback.lift _ _ hi) l
      (prod.lift (pullback.snd α _) (pullback.fst α _ ≫ sliceπ (Under.mk (j ≫ f))) : _ ⟶ _ ⨯ X)
      (prod.lift σ (yonedaEquiv.symm x)) := by
    refine ⟨⟨prod.hom_ext ?_ ?_⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ hΦ.lift
      (pullback.lift (s.fst ≫ pullback.fst _ _ ≫ ιX') s.snd ?_) s.snd ?_) (fun s ↦ ?_)
      (fun s ↦ hΦ.lift_snd _ _ _) (fun s m hm₁ hm₂ ↦ ?_)⟩⟩
    · simp only [Category.assoc, prod.lift_fst, pullback.lift_snd]
    · simp only [Category.assoc, prod.lift_snd, pullback.lift_fst_assoc, e₅, pullback.condition,
        reassoc_of% hk]
    · rw [Category.assoc, Category.assoc, e₆]
      exact (hs s).2
    · refine pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)
      simp only [Category.assoc, hφ, pullback.lift_fst_assoc, e₂, pullback.condition_assoc,
        reassoc_of% (hs s).1, reassoc_of% hσ', e₄, Category.comp_id]
    · refine pullback.hom_ext ?_ ?_
      · simp only [Category.assoc, pullback.lift_fst, hΦ.lift_fst_assoc, pullback.lift_fst_assoc,
          e₃, Category.comp_id]
      · simp only [Category.assoc, pullback.lift_snd, hΦ.lift_snd_assoc, (hs s).1]
    · refine hΦ.hom_ext (pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _)) ?_
      · have h := congrArg (· ≫ pullback.fst _ _ ≫ ιX') hm₁
        simp only [Category.assoc, pullback.lift_fst_assoc, e₃', Category.comp_id] at h
        simp only [Category.assoc, hΦ.lift_fst_assoc, pullback.lift_fst, h]
      · exact hm₂.trans (hΦ.lift_snd _ _ _).symm
  have hγ : leibnizSlice j p f ≫ (prod.lift (pullback.snd α _)
      (pullback.fst α _ ≫ sliceπ (Under.mk (j ≫ f))) : _ ⟶ _ ⨯ X) =
        prod.lift ((slice K).map (Under.homMk p : Under.mk f ⟶ Under.mk (f ≫ p)))
          (sliceπ (Under.mk f)) :=
    prod.hom_ext (by
        rw [Category.assoc, prod.lift_fst]
        exact (leibnizSlice_snd j p f).trans (prod.lift_fst _ _).symm) (by
        rw [Category.assoc, prod.lift_snd]
        exact (leibnizSlice_fst_sliceπ j p f).trans (prod.lift_snd _ _).symm)
  refine ⟨hP.lift (pullback.fst _ _ ≫ leibnizSlice j p f) (pullback.snd _ _)
    ((Category.assoc _ _ _).trans ((congrArg _ hγ).trans pullback.condition)),
    MorphismProperty.of_isPullback (IsPullback.of_bot ?_ (hP.lift_fst _ _ _).symm hP) hψ⟩
  rw [hP.lift_snd, hγ]
  exact IsPullback.of_hasPullback _ _

private lemma exists_rlp_of_isCartesianEdge {X S X₀ : SSet.{u}} (p : X ⟶ S) [InnerFibration p]
    (f : Δ[1] ⟶ X) (hf : IsCartesianEdge p f) {x x' y : X _⦋0⦌} {b c : S _⦋0⦌}
    (hf₀ : stdSimplex.δ 0 ≫ f = yonedaEquiv.symm y)
    (hf₁ : stdSimplex.δ 1 ≫ f = yonedaEquiv.symm x') (hx : p.app _ x = b)
    (hx' : p.app _ x' = b) (hy : p.app _ y = c) {Φ : SSet.{u}}
    {k : Φ ⟶ pullback (sliceAtπ X y) (yonedaEquiv.symm x)} {l : Φ ⟶ Δ[0]}
    {w : Δ[0] ⟶ pullback (sliceAtπ S c) (yonedaEquiv.symm b)}
    (hΦ : IsPullback k l (sliceAtFiberMap p hx hy) w)
    (hw : (sliceAtFiberVerticesEquiv S b c (yonedaEquiv w)).edge = yonedaEquiv (f ≫ p))
    {q₀ : X₀ ⟶ X} {p₀ : X₀ ⟶ Δ[0]} (hX₀ : IsPullback q₀ p₀ p (yonedaEquiv.symm b))
    {v v' : X₀ _⦋0⦌} (hv : yonedaEquiv.symm v ≫ q₀ = yonedaEquiv.symm x)
    (hv' : yonedaEquiv.symm v' ≫ q₀ = yonedaEquiv.symm x') :
    ∃ (F : SSet.{u}) (a : F ⟶ Φ) (b : F ⟶ pullback (sliceAtπ X₀ v') (yonedaEquiv.symm v)),
      modelCategoryQuillen.I.rlp a ∧ modelCategoryQuillen.I.rlp b := by
  obtain rfl : x = q₀.app _ v :=
    yonedaEquiv.symm.injective (hv.symm.trans (yonedaEquiv_symm_comp _ _))
  obtain rfl : x' = q₀.app _ v' :=
    yonedaEquiv.symm.injective (hv'.symm.trans (yonedaEquiv_symm_comp _ _))
  obtain ⟨σ, hσ⟩ : ∃ σ : Δ[0] ⟶ (slice Δ[1]).obj (Under.mk (f ≫ p)),
      (((joinRightUnderAdjunction Δ[1]).homEquiv _ _).symm σ).right = joinCollapse ≫ f ≫ p :=
    ⟨(joinRightUnderAdjunction Δ[1]).homEquiv _ _ (Under.homMk (joinCollapse ≫ f ≫ p)
      (joinInclRight_comp_joinCollapse_assoc _)), by rw [Equiv.symm_apply_apply]; rfl⟩
  rw [sliceAtFiberVerticesEquiv_edge, Equiv.symm_apply_apply] at hw
  obtain ⟨a, ha⟩ := exists_rlp_fiber_leibnizSlice p (stdSimplex.δ 0) f hf hx hy hf₀ hΦ σ (by
    rw [hσ, joinMap_δ_zero_comp_joinCollapse_assoc]
    exact ((Iso.inv_comp_eq _).1 (yonedaEquiv.injective hw)).symm)
  have hpt (t : (Δ[0] : SSet.{u}) _⦋0⦌) : (yonedaEquiv.symm b).app _ t = b := by
    rw [← yonedaEquiv.apply_symm_apply t, ← yonedaEquiv_comp,
      stdSimplex.isTerminalObj₀.hom_ext (yonedaEquiv.symm t) (𝟙 _), Category.id_comp,
      Equiv.apply_symm_apply]
  have hT : IsTerminal (sliceAt Δ[0] (p₀.app _ v')) := by
    have := (joinRightUnderAdjunction (Δ[0] : SSet.{u})).rightAdjoint_preservesLimits
    exact IsTerminal.isTerminalObj (slice Δ[0]) _ (IsTerminal.ofUniqueHom
      (fun _ ↦ Under.homMk (stdSimplex.isTerminalObj₀.from _)
        (stdSimplex.isTerminalObj₀.hom_ext _ _))
      fun s m ↦ Under.UnderMorphism.ext (stdSimplex.isTerminalObj₀.hom_ext _ _))
  have : IsIso (sliceAtπ Δ[0] (p₀.app _ v')) := isIso_of_isTerminal hT stdSimplex.isTerminalObj₀ _
  let e := pullback.snd (sliceAtπ Δ[0] (p₀.app _ v')) (yonedaEquiv.symm (p₀.app _ v))
  have hΦ₀ : IsPullback (sliceAtFiberMap q₀ rfl rfl) (sliceAtFiberMap p₀ rfl rfl ≫ e)
      (sliceAtFiberMap p hx hx') (inv e ≫ sliceAtFiberMap (yonedaEquiv.symm b) (hpt _) (hpt _)) :=
    (isPullback_sliceAtFiberMap hX₀ v v' (hpt _) (hpt _) hx hx').of_iso (Iso.refl _) (Iso.refl _)
      (asIso e) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  obtain ⟨b', hb'⟩ := exists_rlp_fiber_leibnizSlice p (stdSimplex.δ 1) f
    (trivialFibration_leibnizSlice leftAnodyneExtensions_stdSimplex_δ_one p f) hx hx' hf₁ hΦ₀ σ (by
      have h₁ : stdSimplex.δ 1 ≫ f ≫ p = yonedaEquiv.symm b :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ p) hf₁).trans
          ((yonedaEquiv_symm_comp _ _).trans (congrArg _ hx')))
      rw [hσ, joinMap_δ_one_comp_joinCollapse_assoc, h₁, Category.assoc, sliceAtFiberMap,
        pullback.lift_fst]
      conv_rhs => rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
      rw [Under.comp_right]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _)))
  exact ⟨_, a, b', ha, hb'⟩

private lemma exists_isPullback_sliceAtFiberMap_of_eq {X S : SSet.{u}} (p : X ⟶ S)
    {x₁ x₂ y₁ y₂ : X _⦋0⦌} {b c : S _⦋0⦌} (hx₁ : p.app _ x₁ = b) (hy₁ : p.app _ y₁ = c)
    (hx₂ : p.app _ x₂ = b) (hy₂ : p.app _ y₂ = c) (hx : x₁ = x₂) (hy : y₁ = y₂)
    {w w' : Δ[0] ⟶ pullback (sliceAtπ S c) (yonedaEquiv.symm b)} (hw : w = w') :
    ∃ k : pullback (sliceAtFiberMap p hx₁ hy₁) w ⟶ pullback (sliceAtπ X y₂) (yonedaEquiv.symm x₂),
      IsPullback k (pullback.snd _ _) (sliceAtFiberMap p hx₂ hy₂) w' := by
  subst hx hy hw
  exact ⟨_, IsPullback.of_hasPullback _ _⟩

end Fiber

section Cartesian

theorem exists_trivialFibrations_fiber_sliceAtFiberMap_of_isCartesianEdge {X S : SSet.{u}}
    (p : X ⟶ S) [InnerFibration p] {x x' y : X _⦋0⦌} (e : Edge x' y)
    (he : IsCartesianEdge p (yonedaEquiv.symm e.edge)) (hx : p.app _ x = p.app _ x') :
    ∃ (F : SSet.{u})
      (a : F ⟶ pullback (sliceAtFiberMap p hx rfl)
        (yonedaEquiv.symm ((sliceAtFiberVerticesEquiv S _ _).symm (e.map p))))
      (b : F ⟶ pullback (sliceAtπ (pullback p (yonedaEquiv.symm (p.app _ x')))
        (fiberVertex p x' rfl)) (yonedaEquiv.symm (fiberVertex p x hx))),
      modelCategoryQuillen.I.rlp a ∧ modelCategoryQuillen.I.rlp b :=
  exists_rlp_of_isCartesianEdge p _ he
    ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.tgt_eq))
    ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.src_eq)) hx rfl rfl
    (IsPullback.of_hasPullback _ _) (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, Edge.map_edge, yonedaEquiv_comp,
        Equiv.apply_symm_apply]) (IsPullback.of_hasPullback _ _)
    (yonedaEquiv_symm_fiberVertex_fst p x hx) (yonedaEquiv_symm_fiberVertex_fst p x' rfl)

theorem exists_trivialFibrations_fiber_sliceAtFiberMap {X S : SSet.{u}} (p : X ⟶ S)
    [InnerFibration p] {x x' y : X _⦋0⦌} (e : Edge x' y)
    (he : IsLocallyCartesianEdge p (yonedaEquiv.symm e.edge)) (hx : p.app _ x = p.app _ x') :
    ∃ (F : SSet.{u})
      (a : F ⟶ pullback (sliceAtFiberMap p hx rfl)
        (yonedaEquiv.symm ((sliceAtFiberVerticesEquiv S _ _).symm (e.map p))))
      (b : F ⟶ pullback (sliceAtπ (pullback p (yonedaEquiv.symm (p.app _ x')))
        (fiberVertex p x' rfl)) (yonedaEquiv.symm (fiberVertex p x hx))),
      modelCategoryQuillen.I.rlp a ∧ modelCategoryQuillen.I.rlp b := by
  set f := yonedaEquiv.symm e.edge with hf
  have hf₀ : stdSimplex.δ 0 ≫ f = yonedaEquiv.symm y :=
    (stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.tgt_eq)
  have hf₁ : stdSimplex.δ 1 ≫ f = yonedaEquiv.symm x' :=
    (stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.src_eq)
  have hb : stdSimplex.δ 1 ≫ f ≫ p = yonedaEquiv.symm (p.app _ x') :=
    ((reassoc_of% hf₁) p).trans (yonedaEquiv_symm_comp _ _)
  set f' : Δ[1] ⟶ pullback p (f ≫ p) := pullback.lift f (𝟙 Δ[1]) (Category.id_comp _).symm
  have hf'₁ : f' ≫ pullback.fst _ _ = f := pullback.lift_fst _ _ _
  have hf'₂ : f' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  let q₀ : pullback p (yonedaEquiv.symm (p.app _ x')) ⟶ pullback p (f ≫ p) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ stdSimplex.δ 1)
      (by rw [pullback.condition, Category.assoc, hb])
  have hq₀₁ : q₀ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hX₀ : IsPullback q₀ (pullback.snd _ _) (pullback.snd p (f ≫ p)) (stdSimplex.δ 1) :=
    IsPullback.of_right (by rw [hq₀₁, hb]; exact IsPullback.of_hasPullback _ _)
      (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  have hq (t : (pullback p (yonedaEquiv.symm (p.app _ x'))) _⦋0⦌) :
      yonedaEquiv.symm ((pullback.snd p (f ≫ p)).app _ (q₀.app _ t)) = stdSimplex.δ 1 := by
    rw [← yonedaEquiv_symm_comp, ← yonedaEquiv_symm_comp, Category.assoc, hX₀.w,
      ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
  let v := fiberVertex p x hx
  let v' := fiberVertex p x' rfl
  let y₁ : (pullback p (f ≫ p)) _⦋0⦌ := yonedaEquiv (stdSimplex.δ 0 ≫ f')
  have hx₁ : (pullback.fst p (f ≫ p)).app _ (q₀.app _ v) = x := yonedaEquiv.symm.injective (by
    rw [← yonedaEquiv_symm_comp, ← yonedaEquiv_symm_comp, Category.assoc, hq₀₁,
      yonedaEquiv_symm_fiberVertex_fst])
  have hy₁ : (pullback.fst p (f ≫ p)).app _ y₁ = y := yonedaEquiv.symm.injective (by
    rw [← yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.assoc, hf'₁, hf₀])
  have hb₁ : (f ≫ p).app _ ((pullback.snd p (f ≫ p)).app _ (q₀.app _ v)) = p.app _ x' :=
    yonedaEquiv.symm.injective (by rw [← yonedaEquiv_symm_comp, hq, hb])
  have hc₁ : (f ≫ p).app _ ((pullback.snd p (f ≫ p)).app _ y₁) = p.app _ y :=
    yonedaEquiv.symm.injective (by
      simp only [y₁, ← yonedaEquiv_symm_comp, Equiv.symm_apply_apply, Category.assoc,
        reassoc_of% hf'₂, reassoc_of% hf₀])
  let w₁ := yonedaEquiv.symm ((sliceAtFiberVerticesEquiv Δ[1] _ _).symm
    (Edge.mk (yonedaEquiv (f' ≫ pullback.snd _ _))
      (x₀ := (pullback.snd p (f ≫ p)).app _ (q₀.app _ v)) (x₁ := (pullback.snd p (f ≫ p)).app _ y₁)
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, hf'₂, Category.comp_id,
          hq]))
      (yonedaEquiv.symm.injective (by
        rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, ← yonedaEquiv_symm_comp,
          Equiv.symm_apply_apply, Category.assoc]))))
  have hw₁ : (sliceAtFiberVerticesEquiv Δ[1] _ _ (yonedaEquiv w₁)).edge =
      yonedaEquiv (f' ≫ pullback.snd _ _) := by
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  have hw : w₁ ≫ sliceAtFiberMap (f ≫ p) hb₁ hc₁ =
      yonedaEquiv.symm ((sliceAtFiberVerticesEquiv S _ _).symm (e.map p)) := by
    refine yonedaEquiv.injective ((sliceAtFiberVerticesEquiv S _ _).injective (Edge.ext ?_))
    rw [yonedaEquiv_comp, sliceAtFiberVerticesEquiv_sliceAtFiberMap, hw₁, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Edge.map_edge, ← yonedaEquiv_comp, hf'₂, Category.id_comp,
      yonedaEquiv_comp, hf, Equiv.apply_symm_apply]
  have hBC := isPullback_sliceAtFiberMap (IsPullback.of_hasPullback p (f ≫ p)) (q₀.app _ v) y₁
    hb₁ hc₁ ((congrArg _ hx₁).trans hx) (congrArg _ hy₁)
  obtain ⟨k, hk⟩ := exists_isPullback_sliceAtFiberMap_of_eq p hx rfl
    ((congrArg _ hx₁).trans hx) (congrArg _ hy₁) hx₁.symm hy₁.symm hw.symm
  exact exists_rlp_of_isCartesianEdge (pullback.snd p (f ≫ p)) f' he
    (Equiv.symm_apply_apply _ _).symm (by
      rw [← yonedaEquiv_symm_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hf'₁, hf₁, Category.assoc, hq₀₁, yonedaEquiv_symm_fiberVertex_fst]
      · rw [Category.assoc, hf'₂, Category.comp_id, Category.assoc, pullback.lift_snd,
          ← Category.assoc, stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp])
    rfl (yonedaEquiv.symm.injective ((hq _).trans (hq _).symm)) rfl
    (IsPullback.of_right (h₁₁ := hBC.lift k (pullback.snd _ _ ≫ w₁)
      (by rw [hk.w, Category.assoc])) (by rw [hBC.lift_fst]; exact hk) (hBC.lift_snd _ _ _) hBC)
    hw₁ (by rw [hq]; exact hX₀) (yonedaEquiv_symm_comp _ _) (yonedaEquiv_symm_comp _ _)

end Cartesian

end SSet
