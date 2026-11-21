import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianFibration
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FibrewisePath
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

section LeibnizSlice

noncomputable abbrev leibnizSliceFiberMap {A B E S : SSet.{u}} (j : A ⟶ B) (p : E ⟶ S)
    (e : B ⟶ E) (x : E _⦋0⦌) :=
  fiberMap (p := leibnizSlice j p e ≫ pullback.fst _ _ ≫ sliceπ _) (leibnizSlice j p e) rfl x

theorem isCartesianEdge_iff_forall_leibnizSliceFiberMap {X S : SSet.{u}} (p : X ⟶ S)
    [InnerFibration p] (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f ↔
      ∀ x : X _⦋0⦌, modelCategoryQuillen.I.rlp (leibnizSliceFiberMap (stdSimplex.δ 0) p f x) := by
  refine ⟨fun h x ↦ trivialFibration_fiberMap _ rfl h x, fun h ↦ ?_⟩
  refine trivialFibration_of_rightFibrations_of_fiber
    (rightFibrations_leibnizSlice (stdSimplex.δ 0) p f) fun g ↦ ?_
  exact MorphismProperty.of_isPullback
    (isPullback_fiber_fiberMap _ (pullback.fst _ _ ≫ sliceπ _) rfl) (h _)

end LeibnizSlice

section SliceAt

noncomputable def sliceAtFiberMap {X S : SSet.{u}} (p : X ⟶ S) {x y : X _⦋0⦌}
    {b c : S _⦋0⦌} (hx : p.app _ x = b) (hy : p.app _ y = c) :
    pullback (sliceAtπ X y) (yonedaEquiv.symm x) ⟶ pullback (sliceAtπ S c) (yonedaEquiv.symm b) :=
  pullback.map _ _ _ _ ((slice Δ[0]).map (Under.homMk p
      ((yonedaEquiv_symm_comp y p).trans (congrArg yonedaEquiv.symm hy)) :
      Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm c))) (𝟙 _) p
    (slice_map_sliceπ (Under.homMk p
      ((yonedaEquiv_symm_comp y p).trans (congrArg yonedaEquiv.symm hy)) :
      Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm c))).symm
    (by rw [yonedaEquiv_symm_comp, hx, Category.id_comp])

theorem rightFibrations_sliceAtFiberMap {X S : SSet.{u}} (p : X ⟶ S) [InnerFibration p]
    {x y : X _⦋0⦌} {b c : S _⦋0⦌} (hx : p.app _ x = b) (hy : p.app _ y = c) :
    rightFibrations (sliceAtFiberMap p hx hy) := by
  let j := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  let e : Δ[0] ⟶ X := yonedaEquiv.symm y
  have : IsIso (sliceπ (Under.mk (j ≫ e))) := isIso_sliceπ_of_isEmpty _
  have : IsIso (sliceπ (Under.mk (j ≫ e ≫ p))) := isIso_sliceπ_of_isEmpty _
  have hQ : IsPullback (pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e))) (pullback.snd _ _) p
      (sliceπ (Under.mk (e ≫ p))) :=
    IsPullback.of_iso (IsPullback.of_hasPullback _ _) (Iso.refl _)
      (asIso (sliceπ (Under.mk (j ≫ e)))) (Iso.refl _) (asIso (sliceπ (Under.mk (j ≫ e ≫ p))))
      (Category.id_comp _).symm (Category.id_comp _).symm
      (slice_map_sliceπ (Under.homMk p (by simp) : Under.mk (j ≫ e) ⟶ Under.mk (j ≫ e ≫ p)))
      ((sliceRes_sliceπ _ _).trans (Category.id_comp _).symm)
  have hec : e ≫ p = yonedaEquiv.symm c := (yonedaEquiv_symm_comp y p).trans (congrArg _ hy)
  have hxb : yonedaEquiv.symm x ≫ p = yonedaEquiv.symm b :=
    (yonedaEquiv_symm_comp x p).trans (congrArg _ hx)
  let τ : Under.mk (yonedaEquiv.symm c) ⟶ Under.mk (e ≫ p) :=
    Under.homMk (𝟙 S) ((Category.comp_id _).trans hec.symm)
  have hτ : (slice Δ[0]).map τ ≫ sliceπ (Under.mk (e ≫ p)) = sliceAtπ S c :=
    (slice_map_sliceπ τ).trans (Category.comp_id _)
  let β := hQ.lift (pullback.snd (sliceAtπ S c) (yonedaEquiv.symm b) ≫ yonedaEquiv.symm x)
    (pullback.fst _ _ ≫ (slice Δ[0]).map τ)
    (by rw [Category.assoc, Category.assoc, hτ, pullback.condition, hxb])
  have hs : IsPullback (pullback.fst (sliceAtπ S c) (yonedaEquiv.symm b) ≫ (slice Δ[0]).map τ)
      (pullback.snd _ _) (sliceπ (Under.mk (e ≫ p))) (yonedaEquiv.symm x ≫ p) :=
    IsPullback.of_iso (IsPullback.of_hasPullback _ _) (Iso.refl _)
      ((slice Δ[0]).mapIso (Under.isoMk (Iso.refl S) ((Category.comp_id _).trans hec.symm)))
      (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
      ((Category.comp_id _).trans hτ.symm) (by
        rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hxb])
  have hb : IsPullback β (pullback.snd _ _) (pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e)))
      (yonedaEquiv.symm x) :=
    IsPullback.of_right (by rwa [hQ.lift_snd]) (hQ.lift_fst _ _ _) hQ.flip
  have ht : IsPullback (pullback.fst (sliceAtπ X y) (yonedaEquiv.symm x))
      (sliceAtFiberMap p hx hy) (leibnizSlice j p e) β := by
    refine IsPullback.of_bot ?_ ?_ hb
    · rw [sliceAtFiberMap, pullback.lift_snd, Category.comp_id, leibnizSlice_fst_sliceπ]
      exact IsPullback.of_hasPullback _ _
    · apply hQ.hom_ext
      · rw [Category.assoc, leibnizSlice_fst_sliceπ, Category.assoc, hQ.lift_fst,
          sliceAtFiberMap, pullback.lift_snd_assoc, Category.comp_id]
        exact pullback.condition
      · rw [Category.assoc, leibnizSlice_snd, Category.assoc, hQ.lift_snd, sliceAtFiberMap,
          pullback.lift_fst_assoc, Category.assoc, ← Functor.map_comp]
        exact congrArg (_ ≫ (slice Δ[0]).map ·) (Under.UnderMorphism.ext (Category.comp_id p).symm)
  exact MorphismProperty.of_isPullback (P := rightHornInclusions.rlp) ht
    (rightFibrations_leibnizSlice j p e)

theorem kanFibration_sliceAtFiberMap {X S : SSet.{u}} [S.Quasicategory] (p : X ⟶ S)
    [InnerFibration p] {x y : X _⦋0⦌} {b c : S _⦋0⦌} (hx : p.app _ x = b)
    (hy : p.app _ y = c) : modelCategoryQuillen.J.rlp (sliceAtFiberMap p hx hy) :=
  have := kanComplex_fiber_of_rightFibrations (rightFibrations_sliceAtπ S c) b
  kanFibration_of_rightFibrations (rightFibrations_sliceAtFiberMap p hx hy)

private lemma joinInclLeft_comp_stdSimplexJoinIso_hom_zero :
    joinInclLeft Δ[0] Δ[0] ≫ (stdSimplexJoinIso.{u} 0 0).hom = stdSimplex.δ 1 := by
  rw [joinInclLeft_comp_stdSimplexJoinIso_hom]
  refine congrArg stdSimplex.map ?_
  ext i : 3
  fin_cases i
  rfl

private lemma joinInclRight_comp_stdSimplexJoinIso_hom_zero :
    joinInclRight Δ[0] Δ[0] ≫ (stdSimplexJoinIso.{u} 0 0).hom = stdSimplex.δ 0 := by
  rw [joinInclRight_comp_stdSimplexJoinIso_hom]
  refine congrArg stdSimplex.map ?_
  ext i : 3
  fin_cases i
  rfl

private noncomputable def sliceAtFiberEdge {C : SSet.{u}} {b c : C _⦋0⦌}
    (v : (pullback (sliceAtπ C c) (yonedaEquiv.symm b)) _⦋0⦌) : Δ[1] ⟶ C :=
  (stdSimplexJoinIso 0 0).inv ≫
    (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm
      (yonedaEquiv.symm v ≫ pullback.fst _ _)).right

private lemma sliceAtFiberEdge_δ {C : SSet.{u}} {b c : C _⦋0⦌}
    (v : (pullback (sliceAtπ C c) (yonedaEquiv.symm b)) _⦋0⦌) :
    stdSimplex.δ 1 ≫ sliceAtFiberEdge v = yonedaEquiv.symm b ∧
      stdSimplex.δ 0 ≫ sliceAtFiberEdge v = yonedaEquiv.symm c := by
  have h₁ : stdSimplex.δ 1 ≫ (stdSimplexJoinIso.{u} 0 0).inv = joinInclLeft Δ[0] Δ[0] :=
    (Iso.comp_inv_eq _).2 joinInclLeft_comp_stdSimplexJoinIso_hom_zero.symm
  have h₀ : stdSimplex.δ 0 ≫ (stdSimplexJoinIso.{u} 0 0).inv = joinInclRight Δ[0] Δ[0] :=
    (Iso.comp_inv_eq _).2 joinInclRight_comp_stdSimplexJoinIso_hom_zero.symm
  refine ⟨?_, ?_⟩
  · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
      ((comp_sliceAtπ _).symm.trans ?_))
    rw [Category.assoc, pullback.condition, ← Category.assoc,
      stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]
  · refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₀).trans ?_)
    exact Under.w (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm
      (yonedaEquiv.symm v ≫ pullback.fst _ _))

private noncomputable def sliceAtVertexOfEdge {C : SSet.{u}} {b c : C _⦋0⦌} (e : Edge b c) :
    Δ[0] ⟶ sliceAt C c :=
  (joinRightUnderAdjunction Δ[0]).homEquiv _ _
    (Under.homMk ((stdSimplexJoinIso 0 0).hom ≫ yonedaEquiv.symm e.edge)
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        joinInclRight_comp_stdSimplexJoinIso_hom_zero).trans
          ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.tgt_eq)))))

private lemma sliceAtVertexOfEdge_sliceAtπ {C : SSet.{u}} {b c : C _⦋0⦌} (e : Edge b c) :
    sliceAtVertexOfEdge e ≫ sliceAtπ C c = yonedaEquiv.symm b := by
  refine (comp_sliceAtπ _).trans ?_
  rw [sliceAtVertexOfEdge, Equiv.symm_apply_apply]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    joinInclLeft_comp_stdSimplexJoinIso_hom_zero).trans
      ((stdSimplex.δ_comp_yonedaEquiv_symm _ _).trans (congrArg _ e.src_eq)))

noncomputable def sliceAtFiberVerticesEquiv (C : SSet.{u}) (b c : C _⦋0⦌) :
    (pullback (sliceAtπ C c) (yonedaEquiv.symm b)) _⦋0⦌ ≃ Edge b c where
  toFun v := Edge.mk (yonedaEquiv (sliceAtFiberEdge v))
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, (sliceAtFiberEdge_δ v).1, Equiv.apply_symm_apply])
    (by rw [← stdSimplex.yonedaEquiv_δ_comp, (sliceAtFiberEdge_δ v).2, Equiv.apply_symm_apply])
  invFun e := yonedaEquiv (pullback.lift (sliceAtVertexOfEdge e) (𝟙 Δ[0])
    ((sliceAtVertexOfEdge_sliceAtπ e).trans (Category.id_comp _).symm))
  left_inv v := by
    refine yonedaEquiv.symm.injective ((Equiv.symm_apply_apply _ _).trans ?_)
    refine pullback.hom_ext ((pullback.lift_fst _ _ _).trans ?_)
      (stdSimplex.isTerminalObj₀.hom_ext _ _)
    apply ((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm.injective
    rw [sliceAtVertexOfEdge, Equiv.symm_apply_apply]
    apply Under.UnderMorphism.ext
    exact (congrArg _ (Equiv.symm_apply_apply _ _)).trans (Iso.hom_inv_id_assoc _ _)
  right_inv e := by
    refine Edge.ext ((congrArg yonedaEquiv ?_).trans (Equiv.apply_symm_apply _ _))
    rw [sliceAtFiberEdge, Equiv.symm_apply_apply, pullback.lift_fst, sliceAtVertexOfEdge,
      Equiv.symm_apply_apply]
    exact Iso.inv_hom_id_assoc _ _

theorem sliceAtFiberVerticesEquiv_edge (C : SSet.{u}) (b c : C _⦋0⦌)
    (v : (pullback (sliceAtπ C c) (yonedaEquiv.symm b)) _⦋0⦌) :
    (sliceAtFiberVerticesEquiv C b c v).edge = yonedaEquiv ((stdSimplexJoinIso 0 0).inv ≫
      (((joinRightUnderAdjunction Δ[0]).homEquiv _ _).symm
        (yonedaEquiv.symm v ≫ pullback.fst _ _)).right) :=
  rfl

theorem sliceAtFiberVerticesEquiv_sliceAtFiberMap {X S : SSet.{u}} (p : X ⟶ S) {x y : X _⦋0⦌}
    {b c : S _⦋0⦌} (hx : p.app _ x = b) (hy : p.app _ y = c)
    (v : (pullback (sliceAtπ X y) (yonedaEquiv.symm x)) _⦋0⦌) :
    (sliceAtFiberVerticesEquiv S b c ((sliceAtFiberMap p hx hy).app _ v)).edge =
      p.app _ (sliceAtFiberVerticesEquiv X x y v).edge := by
  have h : yonedaEquiv.symm ((sliceAtFiberMap p hx hy).app _ v) ≫ pullback.fst _ _ =
      (yonedaEquiv.symm v ≫ pullback.fst _ _) ≫ (slice Δ[0]).map (Under.homMk p
        ((yonedaEquiv_symm_comp y p).trans (congrArg yonedaEquiv.symm hy)) :
        Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm c)) := by
    rw [← yonedaEquiv_symm_comp, Category.assoc, sliceAtFiberMap, pullback.lift_fst,
      Category.assoc]
  rw [sliceAtFiberVerticesEquiv_edge, sliceAtFiberVerticesEquiv_edge, ← yonedaEquiv_comp, h,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

end SliceAt

section BaseChange

theorem isPullback_sliceAtFiberMap {X' X S' S : SSet.{u}} {q : X' ⟶ X} {p' : X' ⟶ S'}
    {p : X ⟶ S} {g : S' ⟶ S} (h : IsPullback q p' p g) (x y : X' _⦋0⦌) {b c : S _⦋0⦌}
    (hb : g.app _ (p'.app _ x) = b) (hc : g.app _ (p'.app _ y) = c)
    (hx : p.app _ (q.app _ x) = b) (hy : p.app _ (q.app _ y) = c) :
    IsPullback (sliceAtFiberMap q (x := x) (y := y) rfl rfl) (sliceAtFiberMap p' rfl rfl)
      (sliceAtFiberMap p hx hy) (sliceAtFiberMap g hb hc) := by
  have hU : IsPullback
      (Under.homMk q (yonedaEquiv_symm_comp y q) :
        Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm (q.app _ y)))
      (Under.homMk p' (yonedaEquiv_symm_comp y p') :
        Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm (p'.app _ y)))
      (Under.homMk p ((yonedaEquiv_symm_comp _ p).trans
        (congrArg yonedaEquiv.symm hy)) :
        Under.mk (yonedaEquiv.symm (q.app _ y)) ⟶ Under.mk (yonedaEquiv.symm c))
      (Under.homMk g ((yonedaEquiv_symm_comp _ g).trans (congrArg yonedaEquiv.symm hc)) :
        Under.mk (yonedaEquiv.symm (p'.app _ y)) ⟶ Under.mk (yonedaEquiv.symm c)) :=
    IsPullback.of_map (Under.forget _) (Under.UnderMorphism.ext h.w) h
  have := (joinRightUnderAdjunction (Δ[0] : SSet.{u})).rightAdjoint_preservesLimits
  exact isPullback_pullback_map (hU.map (slice Δ[0])) h (slice_map_sliceπ _) (slice_map_sliceπ _)
    (slice_map_sliceπ _) (slice_map_sliceπ _) (yonedaEquiv_symm_comp x q)
    (yonedaEquiv_symm_comp x p') ((yonedaEquiv_symm_comp _ p).trans
      (congrArg yonedaEquiv.symm hx))

end BaseChange

end SSet
