import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.InvertibleTransformation

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty Opposite
  MonoidalCategory MonoidalClosed CartesianMonoidalCategory

universe u

namespace SSet

section Points

noncomputable def ihomPointEquiv (K X : SSet.{u}) : (Δ[0] ⟶ (ihom K).obj X) ≃ (K ⟶ X) where
  toFun g := lift (𝟙 K) (stdSimplex.isTerminalObj₀.from K) ≫ uncurry g
  invFun h := curry (fst K Δ[0] ≫ h)
  left_inv g := by
    rw [curry_eq_iff, ← Category.assoc]
    conv_rhs => rw [← Category.id_comp (uncurry g)]
    congr 1
    ext1
    · simp
    · exact stdSimplex.isTerminalObj₀.hom_ext _ _
  right_inv h := by
    dsimp only
    rw [uncurry_curry, ← Category.assoc, lift_fst, Category.id_comp]

lemma ihomPointEquiv_apply (K X : SSet.{u}) (g : Δ[0] ⟶ (ihom K).obj X) :
    ihomPointEquiv K X g = lift (𝟙 K) (stdSimplex.isTerminalObj₀.from K) ≫ uncurry g := rfl

lemma ihomPointEquiv_comp_ihom_map {K X Y : SSet.{u}} (g : Δ[0] ⟶ (ihom K).obj X) (p : X ⟶ Y) :
    ihomPointEquiv K Y (g ≫ (ihom K).map p) = ihomPointEquiv K X g ≫ p := by
  rw [ihomPointEquiv_apply, ihomPointEquiv_apply, uncurry_natural_right, Category.assoc]

lemma ihomPointEquiv_comp_pre_app {K L X : SSet.{u}} (g : Δ[0] ⟶ (ihom L).obj X) (i : K ⟶ L) :
    ihomPointEquiv K X (g ≫ (pre i).app X) = i ≫ ihomPointEquiv L X g := by
  rw [ihomPointEquiv_apply, ihomPointEquiv_apply, uncurry_pre_app, ← Category.assoc,
    lift_whiskerRight, Category.id_comp, ← Category.assoc, comp_lift, Category.comp_id,
    stdSimplex.isTerminalObj₀.hom_ext (i ≫ _) (stdSimplex.isTerminalObj₀.from K)]

lemma comp_evalVertex_eq {K X : SSet.{u}} (g : Δ[0] ⟶ (ihom K).obj X) (a : K _⦋0⦌) :
    g ≫ evalVertex a X = yonedaEquiv.symm a ≫ ihomPointEquiv K X g := by
  rw [comp_evalVertex]
  refine (congrArg (· ≫ uncurry g) ?_).trans (Category.assoc _ _ _)
  ext1
  · simp only [lift_fst, Category.assoc]
    rw [stdSimplex.isTerminalObj₀.hom_ext (stdSimplex.isTerminalObj₀.from _) (𝟙 _),
      Category.id_comp, Category.comp_id]
  · simp only [lift_snd, Category.assoc]
    exact stdSimplex.isTerminalObj₀.hom_ext _ _

end Points

section Boundary

lemma ihom_boundary_one_hom_ext {X Z : SSet.{u}} {f g : Z ⟶ (ihom (∂Δ[1] : SSet.{u})).obj X}
    (h : ∀ v : (∂Δ[1] : SSet.{u}) _⦋0⦌, f ≫ evalVertex v X = g ≫ evalVertex v X) : f = g := by
  refine uncurry_injective ?_
  ext ⟨⟨k⟩⟩ ⟨σ, z⟩
  let v := (∂Δ[1] : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op σ
  have hv : (lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm v) (𝟙 Z)).app _ z =
      (σ, z) := by
    refine Prod.ext (Subtype.ext (stdSimplex.ext _ _ fun i ↦ ?_)) rfl
    obtain ⟨j, hj⟩ := (mem_boundary_iff_notMem_range σ.1).1 σ.2
    have h₀ : (σ.1 0).val ≠ j.val := fun e ↦ hj ⟨0, Fin.ext e⟩
    have h₁ : (σ.1 i).val ≠ j.val := fun e ↦ hj ⟨i, Fin.ext e⟩
    have e : σ.1 0 = σ.1 i := by
      have := (σ.1 i).isLt
      have := (σ.1 0).isLt
      have := j.isLt
      exact Fin.ext (by omega)
    exact e
  have := ConcreteCategory.congr_hom (congr_app (h v) _) z
  rw [comp_evalVertex, comp_evalVertex] at this
  have h' : (uncurry f).app _ ((lift (stdSimplex.isTerminalObj₀.from Z ≫ yonedaEquiv.symm v)
      (𝟙 Z)).app _ z) = (uncurry g).app _ ((lift (stdSimplex.isTerminalObj₀.from Z ≫
        yonedaEquiv.symm v) (𝟙 Z)).app _ z) := this
  rwa [hv] at h'

end Boundary

section MappingSpace

noncomputable def ihomStdSimplexOneEval (X : SSet.{u}) : (ihom Δ[1]).obj X ⟶ X ⊗ X :=
  lift (evalVertex (stdSimplex.obj₀Equiv.symm 0) X) (evalVertex (stdSimplex.obj₀Equiv.symm 1) X)

lemma comp_ihomStdSimplexOneEval {X Z : SSet.{u}} (a : Z ⟶ (ihom Δ[1]).obj X) :
    a ≫ ihomStdSimplexOneEval X = lift (a ≫ evalVertex (stdSimplex.obj₀Equiv.symm 0) X)
      (a ≫ evalVertex (stdSimplex.obj₀Equiv.symm 1) X) :=
  comp_lift _ _ _

noncomputable def mappingSpace (X : SSet.{u}) (x y : X _⦋0⦌) : SSet.{u} :=
  pullback (ihomStdSimplexOneEval X) (lift (yonedaEquiv.symm x) (yonedaEquiv.symm y))

private lemma nonempty_invStruct_stdSimplex_zero (e : (Δ[0] : SSet.{u}) _⦋1⦌) :
    Nonempty (Edge.mk' e).InvStruct :=
  ⟨(Edge.InvStruct.invStructId (Δ[0].δ 1 e)).ofEq (hom' := Edge.mk' e)
    (yonedaEquiv.symm.injective (stdSimplex.isTerminalObj₀.hom_ext _ _))⟩

lemma mappingSpace_fst_evalVertex_zero (X : SSet.{u}) (x y : X _⦋0⦌) :
    (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫ evalVertex (stdSimplex.obj₀Equiv.symm 0) X =
      pullback.snd _ _ ≫ yonedaEquiv.symm x := by
  have h₀ := congrArg (· ≫ CartesianMonoidalCategory.fst X X)
    (pullback.condition : (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫
      ihomStdSimplexOneEval X = pullback.snd _ _ ≫ _)
  simp only [Category.assoc, ihomStdSimplexOneEval, lift_fst] at h₀
  exact h₀

lemma mappingSpace_fst_evalVertex_one (X : SSet.{u}) (x y : X _⦋0⦌) :
    (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫ evalVertex (stdSimplex.obj₀Equiv.symm 1) X =
      pullback.snd _ _ ≫ yonedaEquiv.symm y := by
  have h₁ := congrArg (· ≫ CartesianMonoidalCategory.snd X X)
    (pullback.condition : (pullback.fst _ _ : mappingSpace X x y ⟶ _) ≫
      ihomStdSimplexOneEval X = pullback.snd _ _ ≫ _)
  simp only [Category.assoc, ihomStdSimplexOneEval, lift_snd] at h₁
  exact h₁

private lemma mappingSpace_fst_mem (X : SSet.{u}) (x y : X _⦋0⦌) {n : SimplexCategoryᵒᵖ}
    (σ : (mappingSpace X x y).obj n) :
    (pullback.fst _ _ : mappingSpace X x y ⟶ _).app n σ ∈ (objectwiseCore Δ[1] X).obj n := by
  intro a
  have h₀ := mappingSpace_fst_evalVertex_zero X x y
  have h₁ := mappingSpace_fst_evalVertex_one X x y
  have hx (z : X _⦋0⦌) : Subcomplex.range (yonedaEquiv.symm z : Δ[0] ⟶ X) ≤ X.core :=
    range_le_core _ nonempty_invStruct_stdSimplex_zero
  obtain ⟨j, rfl⟩ : ∃ j, a = stdSimplex.obj₀Equiv.symm j := ⟨_, (Equiv.symm_apply_apply _ _).symm⟩
  fin_cases j
  · exact (ConcreteCategory.congr_hom (congr_app h₀ n) σ) ▸ hx x n ⟨_, rfl⟩
  · exact (ConcreteCategory.congr_hom (congr_app h₁ n) σ) ▸ hx y n ⟨_, rfl⟩

private def boundaryOneVertex (j : Fin 2) : (∂Δ[1] : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm j, by rw [boundary_obj_eq_univ 0 1]; trivial⟩

private lemma exists_mono_comp_eq_ihomStdSimplexOneEval (X : SSet.{u}) :
    ∃ e : (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
        (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι (terminal.from X)).pt ⟶ X ⊗ X,
      (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
        (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι (terminal.from X)).π ≫ e =
          ihomStdSimplexOneEval X ∧ Mono e := by
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
    (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι (terminal.from X)
  let φ : sq₁₃.pt ⟶ (ihom (∂Δ[1] : SSet.{u})).obj X := sq₁₃.fst
  refine ⟨lift (φ ≫ evalVertex (boundaryOneVertex 0) X) (φ ≫ evalVertex (boundaryOneVertex 1) X),
    ?_, ⟨fun g h hgh ↦ ?_⟩⟩
  · have hπ : sq₁₃.π ≫ φ = (pre (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι).app X := sq₁₃.π_fst
    ext1
    · rw [Category.assoc, lift_fst, ← Category.assoc, hπ]
      exact (pre_app_comp_evalVertex (X := X) _ (boundaryOneVertex 0)).trans (lift_fst _ _).symm
    · rw [Category.assoc, lift_snd, ← Category.assoc, hπ]
      exact (pre_app_comp_evalVertex (X := X) _ (boundaryOneVertex 1)).trans (lift_snd _ _).symm
  · have h₀ := congrArg (· ≫ CartesianMonoidalCategory.fst X X) hgh
    have h₁ := congrArg (· ≫ CartesianMonoidalCategory.snd X X) hgh
    simp only [Category.assoc, lift_fst, lift_snd] at h₀ h₁
    refine sq₁₃.isPullback.hom_ext ?_ (ihom_terminal_hom_ext _ _)
    refine ihom_boundary_one_hom_ext (f := g ≫ φ) (g := h ≫ φ) fun v ↦ ?_
    obtain ⟨j, rfl⟩ : ∃ j, v = boundaryOneVertex j :=
      ⟨stdSimplex.obj₀Equiv v.1, Subtype.ext (Equiv.symm_apply_apply _ _).symm⟩
    fin_cases j
    · exact h₀
    · exact h₁

theorem kanComplex_mappingSpace (X : SSet.{u}) [X.Quasicategory] (x y : X _⦋0⦌) :
    (mappingSpace X x y).KanComplex := by
  let sq₁₃ := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
    (∂Δ[1] : (Δ[1] : SSet.{u}).Subcomplex).ι (terminal.from X)
  let π : (ihom Δ[1]).obj X ⟶ sq₁₃.pt := sq₁₃.π
  have := quasicategory_pullbackObjObj_pt (terminal.from X) _ sq₁₃
  have : Isofibration π := isofibration_pullbackObjObjπ (terminal.from X) _ sq₁₃
  obtain ⟨e, he, he'⟩ := exists_mono_comp_eq_ihomStdSimplexOneEval X
  have he₂ : π ≫ e = ihomStdSimplexOneEval X := he
  let φ₁ : mappingSpace X x y ⟶ (ihom Δ[1]).obj X := pullback.fst _ _
  let φ₂ : mappingSpace X x y ⟶ Δ[0] := pullback.snd _ _
  have hst : φ₁ ≫ ihomStdSimplexOneEval X =
      φ₂ ≫ lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) := pullback.condition
  have hfst : Subcomplex.range φ₁ ≤ ((ihom Δ[1]).obj X).core := by
    rw [← objectwiseCore_eq_core]
    rintro n _ ⟨σ, rfl⟩
    exact mappingSpace_fst_mem X x y σ
  have main {K L : SSet.{u}} (f : K ⟶ L) (hk : HasLiftingProperty f (coreMap π))
      (v₀ : Δ[0] ⟶ K) : HasLiftingProperty f (terminal.from (mappingSpace X x y)) := by
    refine ⟨fun {a _} _ ↦ ?_⟩
    let a' := Subcomplex.lift (a ≫ φ₁) (by
      rintro m _ ⟨z, rfl⟩
      exact hfst m ⟨_, rfl⟩)
    let t : L ⟶ Δ[0] := stdSimplex.isTerminalObj₀.from _
    have hsnd : a ≫ φ₂ = f ≫ t ≫ v₀ ≫ a ≫ φ₂ :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    have hπe {Z : SSet.{u}} (g : Z ⟶ (ihom Δ[1]).obj X) :
        (g ≫ π) ≫ e = g ≫ ihomStdSimplexOneEval X :=
      (Category.assoc _ _ _).trans (congrArg (g ≫ ·) he₂)
    have hcm {Z : SSet.{u}} (g : Z ⟶ ((ihom Δ[1]).obj X).core) :
        (g ≫ coreMap π) ≫ sq₁₃.pt.core.ι = (g ≫ ((ihom Δ[1]).obj X).core.ι) ≫ π :=
      (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (coreMap_ι π)).trans
        (Category.assoc _ _ _).symm)
    have ha' : a' ≫ ((ihom Δ[1]).obj X).core.ι = a ≫ φ₁ := Subcomplex.lift_ι _ _
    have key : (a ≫ φ₁) ≫ π = (f ≫ t ≫ v₀ ≫ a ≫ φ₁) ≫ π :=
      (cancel_mono e).1 ((hπe _).trans (Eq.trans (by
        simp only [Category.assoc, hst]
        exact (reassoc_of% hsnd) _) (hπe _).symm))
    have sq : CommSq a' f (coreMap π) (t ≫ v₀ ≫ a' ≫ coreMap π) := ⟨(cancel_mono
      sq₁₃.pt.core.ι).1 (calc
        (a' ≫ coreMap π) ≫ sq₁₃.pt.core.ι = (a' ≫ ((ihom Δ[1]).obj X).core.ι) ≫ π := hcm a'
        _ = (a ≫ φ₁) ≫ π := congrArg (· ≫ π) ha'
        _ = (f ≫ t ≫ v₀ ≫ a ≫ φ₁) ≫ π := key
        _ = ((f ≫ t ≫ v₀ ≫ a') ≫ ((ihom Δ[1]).obj X).core.ι) ≫ π :=
          congrArg (· ≫ π) (by simp only [Category.assoc, ha'])
        _ = ((f ≫ t ≫ v₀ ≫ a') ≫ coreMap π) ≫ sq₁₃.pt.core.ι := (hcm _).symm
        _ = (f ≫ t ≫ v₀ ≫ a' ≫ coreMap π) ≫ sq₁₃.pt.core.ι := by
          simp only [Category.assoc])⟩
    obtain ⟨l⟩ := (hk.sq_hasLift sq).exists_lift
    have hσ : (l.l ≫ ((ihom Δ[1]).obj X).core.ι) ≫ ihomStdSimplexOneEval X =
        t ≫ lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) :=
      calc (l.l ≫ ((ihom Δ[1]).obj X).core.ι) ≫ ihomStdSimplexOneEval X
          = ((l.l ≫ ((ihom Δ[1]).obj X).core.ι) ≫ π) ≫ e := (hπe _).symm
        _ = ((l.l ≫ coreMap π) ≫ sq₁₃.pt.core.ι) ≫ e := congrArg (· ≫ e) (hcm _).symm
        _ = ((t ≫ v₀ ≫ a' ≫ coreMap π) ≫ sq₁₃.pt.core.ι) ≫ e := by rw [l.fac_right]
        _ = (((t ≫ v₀ ≫ a') ≫ coreMap π) ≫ sq₁₃.pt.core.ι) ≫ e := by
          simp only [Category.assoc]
        _ = (((t ≫ v₀ ≫ a') ≫ ((ihom Δ[1]).obj X).core.ι) ≫ π) ≫ e :=
          congrArg (· ≫ e) (hcm _)
        _ = ((t ≫ v₀ ≫ a') ≫ ((ihom Δ[1]).obj X).core.ι) ≫ ihomStdSimplexOneEval X := hπe _
        _ = t ≫ lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) := by
          simp only [Category.assoc, ha', hst]
          exact congrArg (t ≫ ·) (((reassoc_of% (stdSimplex.isTerminalObj₀.hom_ext
            (v₀ ≫ a ≫ φ₂) (𝟙 _))) _))
    let σ : L ⟶ mappingSpace X x y := pullback.lift _ _ hσ
    have hσ₁ : σ ≫ φ₁ = l.l ≫ ((ihom Δ[1]).obj X).core.ι := by
      simp only [σ, φ₁]
      exact pullback.lift_fst _ _ _
    refine ⟨⟨⟨σ, pullback.hom_ext ?_ (stdSimplex.isTerminalObj₀.hom_ext _ _),
      terminal.hom_ext _ _⟩⟩⟩
    exact (Category.assoc _ _ _).trans ((congrArg (f ≫ ·) hσ₁).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) l.fac_left)).trans ha'))
  refine (modelCategoryQuillen.fibration_iff _).2 fun K L f hf ↦ ?_
  have hk : HasLiftingProperty f (coreMap π) := kanFibration_coreMap π _ hf
  simp only [modelCategoryQuillen.J, iSup_iff] at hf
  obtain ⟨n, ⟨k⟩⟩ := hf
  exact main _ hk
    (yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 0) ≫ horn.ι k _ (Fin.succAbove_ne k 0))

lemma stdSimplex_δ_one_eq : stdSimplex.δ (1 : Fin 2) =
    (yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 0) : Δ[0] ⟶ Δ[1]) := by
  rw [stdSimplex.δ_one_eq_const]
  exact yonedaEquiv.injective (by rw [Equiv.apply_symm_apply]; rfl)

lemma stdSimplex_δ_zero_eq : stdSimplex.δ (0 : Fin 2) =
    (yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm 1) : Δ[0] ⟶ Δ[1]) := by
  rw [stdSimplex.δ_zero_eq_const]
  exact yonedaEquiv.injective (by rw [Equiv.apply_symm_apply]; rfl)

private noncomputable def mappingSpaceVertexHom {X : SSet.{u}} {x y : X _⦋0⦌}
    (v : (mappingSpace X x y) _⦋0⦌) : Δ[1] ⟶ X :=
  ihomPointEquiv Δ[1] X (yonedaEquiv.symm v ≫ pullback.fst _ _)

private lemma mappingSpaceVertexHom_δ {X : SSet.{u}} {x y : X _⦋0⦌}
    (v : (mappingSpace X x y) _⦋0⦌) :
    stdSimplex.δ 1 ≫ mappingSpaceVertexHom v = yonedaEquiv.symm x ∧
      stdSimplex.δ 0 ≫ mappingSpaceVertexHom v = yonedaEquiv.symm y := by
  have h₀ := mappingSpace_fst_evalVertex_zero X x y
  have h₁ := mappingSpace_fst_evalVertex_one X x y
  have ht : yonedaEquiv.symm v ≫ (pullback.snd _ _ : mappingSpace X x y ⟶ Δ[0]) = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [stdSimplex_δ_one_eq, stdSimplex_δ_zero_eq, mappingSpaceVertexHom, ← comp_evalVertex_eq,
    ← comp_evalVertex_eq]
  have hc (z : X _⦋0⦌) : yonedaEquiv.symm v ≫
      (pullback.snd _ _ : mappingSpace X x y ⟶ Δ[0]) ≫ yonedaEquiv.symm z = yonedaEquiv.symm z :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ht).trans (Category.id_comp _))
  exact ⟨(Category.assoc _ _ _).trans ((congrArg (yonedaEquiv.symm v ≫ ·) h₀).trans (hc x)),
    (Category.assoc _ _ _).trans ((congrArg (yonedaEquiv.symm v ≫ ·) h₁).trans (hc y))⟩

noncomputable def mappingSpaceVerticesEquiv (X : SSet.{u}) (x y : X _⦋0⦌) :
    (mappingSpace X x y) _⦋0⦌ ≃ Edge x y where
  toFun v := Edge.mk (yonedaEquiv (mappingSpaceVertexHom v))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, (mappingSpaceVertexHom_δ v).1,
      Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, (mappingSpaceVertexHom_δ v).2,
      Equiv.apply_symm_apply])
  invFun e := yonedaEquiv (pullback.lift ((ihomPointEquiv Δ[1] X).symm (yonedaEquiv.symm e.edge))
    (𝟙 Δ[0]) (by
      have h (i : Fin 2) (z : X _⦋0⦌) (hz : yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm i) ≫
          yonedaEquiv.symm e.edge = yonedaEquiv.symm z) :
          (ihomPointEquiv Δ[1] X).symm (yonedaEquiv.symm e.edge) ≫
            evalVertex (stdSimplex.obj₀Equiv.symm i) X = yonedaEquiv.symm z := by
        rw [comp_evalVertex_eq, Equiv.apply_symm_apply, hz]
      ext1
      · rw [Category.assoc, ihomStdSimplexOneEval, lift_fst, Category.id_comp, lift_fst]
        exact h 0 x (by rw [← stdSimplex_δ_one_eq, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq])
      · rw [Category.assoc, ihomStdSimplexOneEval, lift_snd, Category.id_comp, lift_snd]
        exact h 1 y (by rw [← stdSimplex_δ_zero_eq, stdSimplex.δ_comp_yonedaEquiv_symm,
          e.tgt_eq])) : Δ[0] ⟶ mappingSpace X x y)
  left_inv v := by
    refine yonedaEquiv.symm.injective ((Equiv.symm_apply_apply _ _).trans ?_)
    refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans ?_)
      (stdSimplex.isTerminalObj₀.hom_ext _ _)
    exact ((congrArg (ihomPointEquiv Δ[1] X).symm (Equiv.symm_apply_apply _ _)).trans
      (Equiv.symm_apply_apply _ _))
  right_inv e := by
    refine Edge.ext ((congrArg yonedaEquiv ?_).trans (Equiv.apply_symm_apply _ _))
    refine (congrArg (ihomPointEquiv Δ[1] X) ((congrArg (· ≫ _) (Equiv.symm_apply_apply _ _)).trans
      (pullback.lift_fst _ _ _))).trans (Equiv.apply_symm_apply _ _)

lemma mappingSpaceVerticesEquiv_edge (X : SSet.{u}) (x y : X _⦋0⦌)
    (v : (mappingSpace X x y) _⦋0⦌) :
    (mappingSpaceVerticesEquiv X x y v).edge = yonedaEquiv
      (lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1]) ≫
        uncurry (yonedaEquiv.symm v ≫ pullback.fst _ _)) :=
  rfl

end MappingSpace

end SSet
