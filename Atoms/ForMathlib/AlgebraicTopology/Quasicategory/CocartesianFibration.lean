import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CocartesianEdge

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet

variable {X S : SSet.{u}}

private lemma hasLiftingProperty_horn_op_iff {n : ℕ} (i : Fin (n + 1)) (p : X ⟶ S) :
    HasLiftingProperty Λ[n, i.rev].ι (opFunctor.map p) ↔ HasLiftingProperty Λ[n, i].ι p :=
  (HasLiftingProperty.iff_of_arrow_iso_left (hornArrowIsoOp n i i.rev rfl) _).trans
    (Functor.hasLiftingProperty_iff_of_isEquivalence opFunctor Λ[n, i].ι p)

private lemma innerFibration_of_opFunctor_map (p : X ⟶ S) [InnerFibration (opFunctor.map p)] :
    InnerFibration p := by
  refine ⟨fun _ _ _ ⟨i, h0, hn⟩ ↦ (hasLiftingProperty_horn_op_iff i p).1
    (mem_innerFibrations _ _ (horn_ι_mem_innerHornInclusions ?_ ?_))⟩
  · rw [Fin.lt_def] at hn ⊢
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at hn ⊢
    omega
  · rw [Fin.lt_def] at h0 ⊢
    simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at h0 ⊢
    omega

class IsCocartesianFibration (p : X ⟶ S) : Prop where
  mem_innerFibrations : innerFibrations p
  exists_isCocartesianEdge (x : X _⦋0⦌) (f : Δ[1] ⟶ S)
    (hf : stdSimplex.δ 1 ≫ f = yonedaEquiv.symm (p.app _ x)) :
    ∃ f' : Δ[1] ⟶ X, f' ≫ p = f ∧ stdSimplex.δ 1 ≫ f' = yonedaEquiv.symm x ∧
      IsCocartesianEdge p f'

theorem isCocartesianFibration_iff_op (p : X ⟶ S) :
    IsCocartesianFibration p ↔ IsCartesianFibration (opFunctor.map p) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : InnerFibration p := ⟨h.mem_innerFibrations⟩
    refine { exists_isCartesianEdge := fun y f hf ↦ ?_ }
    obtain ⟨g, rfl⟩ := edgeOp_surjective f
    obtain ⟨g', h₁, h₂, h₃⟩ := h.exists_isCocartesianEdge (opObjEquiv y) g
      ((δ_comp_edgeOp_eq_iff g 0 _).1 hf)
    exact ⟨edgeOp g', by rw [← edgeOp_comp, h₁], (δ_comp_edgeOp_eq_iff g' 0 _).2 h₂, h₃⟩
  · refine ⟨(innerFibration_of_opFunctor_map p).mem, fun x f hf ↦ ?_⟩
    obtain ⟨g', h₁, h₂, h₃⟩ := h.exists_isCartesianEdge (opObjEquiv.symm x) (edgeOp f)
      ((δ_comp_edgeOp_eq_iff f 0 _).2 hf)
    obtain ⟨g, rfl⟩ := edgeOp_surjective g'
    exact ⟨g, edgeOp_injective (by rw [edgeOp_comp, h₁]), (δ_comp_edgeOp_eq_iff g 0 x).1 h₂, h₃⟩

instance isCocartesianFibration_of_isIso (p : X ⟶ S) [IsIso p] : IsCocartesianFibration p :=
  (isCocartesianFibration_iff_op p).2 inferInstance

theorem IsCocartesianFibration.of_isPullback {X' S' : SSet.{u}} {p : X ⟶ S} {p' : X' ⟶ S'}
    {q : X' ⟶ X} {g : S' ⟶ S} (h : IsPullback q p' p g) [IsCocartesianFibration p] :
    IsCocartesianFibration p' :=
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  (isCocartesianFibration_iff_op p').2 (IsCartesianFibration.of_isPullback (h.map opFunctor))

instance isCocartesianFibration_comp {Y Z : SSet.{u}} (p : X ⟶ Y) (q : Y ⟶ Z)
    [IsCocartesianFibration p] [IsCocartesianFibration q] : IsCocartesianFibration (p ≫ q) := by
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  have := (isCocartesianFibration_iff_op q).1 inferInstance
  rw [isCocartesianFibration_iff_op, Functor.map_comp]
  infer_instance

theorem IsCocartesianFibration.isCocartesianEdge_iff (p : X ⟶ S) [IsCocartesianFibration p]
    (e : Δ[1] ⟶ X) : IsCocartesianEdge p e ↔ IsLocallyCocartesianEdge p e :=
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  IsCartesianFibration.isCartesianEdge_iff (opFunctor.map p) (edgeOp e)

theorem IsCocartesianFibration.isCocartesianEdge_id (p : X ⟶ S) [IsCocartesianFibration p]
    (x : Δ[0] ⟶ X) : IsCocartesianEdge p (stdSimplex.σ 0 ≫ x) := by
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  have h := IsCartesianFibration.isCartesianEdge_id (opFunctor.map p)
    ((stdSimplex.opIso ⦋0⦌).inv ≫ opFunctor.map x)
  have e : stdSimplex.σ 0 ≫ (stdSimplex.opIso ⦋0⦌).inv ≫ opFunctor.map x =
      edgeOp (stdSimplex.σ 0 ≫ x) :=
    yonedaEquiv.injective (by rw [stdSimplex.yonedaEquiv_σ_comp,
      stdSimplex.yonedaEquiv_opIso_inv_comp, op_σ, Equiv.apply_symm_apply, yonedaEquiv_edgeOp,
      stdSimplex.yonedaEquiv_σ_comp]; rfl)
  rwa [e] at h

theorem IsCocartesianFibration.isCocartesianEdge_δ_zero_iff_δ_one (p : X ⟶ S)
    [IsCocartesianFibration p] (σ : X _⦋2⦌)
    (hf : IsCocartesianEdge p (yonedaEquiv.symm (X.δ 2 σ))) :
    IsCocartesianEdge p (yonedaEquiv.symm (X.δ 0 σ)) ↔
      IsCocartesianEdge p (yonedaEquiv.symm (X.δ 1 σ)) := by
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  have key (i : Fin 3) : yonedaEquiv.symm (X.op.δ i (opObjEquiv.symm σ)) =
      edgeOp (yonedaEquiv.symm (X.δ i.rev σ)) := by
    rw [op_δ, Equiv.apply_symm_apply, edgeOp_yonedaEquiv_symm]
  have h := IsCartesianFibration.isCartesianEdge_δ_two_iff_δ_one (opFunctor.map p)
    (opObjEquiv.symm σ) (by rw [key]; exact hf)
  rw [key, key] at h
  exact h

theorem leftFibrations_iff_rightFibrations_op (p : X ⟶ S) :
    leftFibrations p ↔ rightFibrations (opFunctor.map p) := by
  refine ⟨fun h _ _ _ ⟨i, h0⟩ ↦ ?_, fun h _ _ _ ⟨i, hi⟩ ↦ ?_⟩
  · have := (hasLiftingProperty_horn_op_iff i.rev p).2 (h _ (.intro i.rev (by
      rw [Fin.lt_def] at h0 ⊢
      simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at h0 ⊢
      omega)))
    rwa [Fin.rev_rev] at this
  · exact (hasLiftingProperty_horn_op_iff i p).1 (h _ (.intro i.rev (by
      rw [Fin.lt_def] at hi ⊢
      simp only [Fin.val_rev, Fin.val_zero, Fin.val_last] at hi ⊢
      omega)))

theorem leftFibrations_iff_isCocartesianFibration_and_forall (p : X ⟶ S) :
    leftFibrations p ↔ IsCocartesianFibration p ∧ ∀ f : Δ[1] ⟶ X, IsCocartesianEdge p f := by
  rw [leftFibrations_iff_rightFibrations_op, rightFibrations_iff_isCartesianFibration_and_forall,
    ← isCocartesianFibration_iff_op]
  refine and_congr_right fun _ ↦ ⟨fun h f ↦ h (edgeOp f), fun h f ↦ ?_⟩
  obtain ⟨g, rfl⟩ := edgeOp_surjective f
  exact h g

instance kanComplex_op (K : SSet.{u}) [K.KanComplex] : K.op.KanComplex :=
  (kanComplex_iff_nonempty_invStruct _).2 fun e ↦ by
    obtain ⟨g, hg⟩ := edgeOp_surjective (yonedaEquiv.symm e)
    obtain ⟨I⟩ := (nonempty_invStruct_edgeOp_iff g).2 (nonempty_invStruct_of_kanComplex K _)
    exact ⟨I.ofEq (by rw [Edge.mk'_edge, Edge.mk'_edge, hg, Equiv.apply_symm_apply])⟩

open modelCategoryQuillen in
theorem leftFibrations_of_isCocartesianFibration_of_kanComplex (p : X ⟶ S)
    [IsCocartesianFibration p]
    (h : ∀ s : S _⦋0⦌, (pullback p (yonedaEquiv.symm s : Δ[0] ⟶ S)).KanComplex) :
    leftFibrations p := by
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  refine (leftFibrations_iff_rightFibrations_op p).2
    (rightFibrations_of_isCartesianFibration_of_kanComplex _ fun s ↦ ?_)
  have := h (opObjEquiv s)
  exact isFibrant_of_fibration ((isPullback_op_pullback p (yonedaEquiv.symm (opObjEquiv s))
    (stdSimplex.opIso ⦋0⦌) (yonedaEquiv.symm s) (yonedaEquiv.injective (by
      rw [stdSimplex.yonedaEquiv_opIso_inv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl))).isoPullback.inv)

def cocartesianSubcomplex (p : X ⟶ S) : X.Subcomplex where
  obj n := {σ | ∀ f : ⦋1⦌ ⟶ n.unop, IsCocartesianEdge p (yonedaEquiv.symm (X.map f.op σ))}
  map g σ hσ f := by
    simpa only [Set.mem_ofPred_eq, op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]
      using hσ (f ≫ g.unop)

theorem mem_cocartesianSubcomplex_iff (p : X ⟶ S) {n : ℕ} (σ : X _⦋n⦌) :
    σ ∈ (cocartesianSubcomplex p).obj _ ↔
      ∀ f : ⦋1⦌ ⟶ ⦋n⦌, IsCocartesianEdge p (stdSimplex.map f ≫ yonedaEquiv.symm σ) := by
  simp only [yonedaEquiv_symm_naturality_left]
  rfl

private lemma op_cocartesianSubcomplex (p : X ⟶ S) :
    (cocartesianSubcomplex p).op = cartesianSubcomplex (opFunctor.map p) := by
  refine Subfunctor.ext (funext fun d ↦ Set.ext fun σ ↦ ⟨fun h f ↦ ?_, fun h f ↦ ?_⟩)
  · have h' : IsCocartesianEdge p _ := h (SimplexCategory.rev.map f)
    rwa [IsCocartesianEdge, edgeOp_yonedaEquiv_symm] at h'
  · rw [IsCocartesianEdge, edgeOp_yonedaEquiv_symm]
    have h' := h (SimplexCategory.rev.map f)
    simp only [op_map, Quiver.Hom.unop_op, SimplexCategory.rev_map_rev_map] at h'
    exact h'

theorem leftFibrations_cocartesianSubcomplex (p : X ⟶ S) [IsCocartesianFibration p] :
    leftFibrations ((cocartesianSubcomplex p).ι ≫ p) := by
  have := (isCocartesianFibration_iff_op p).1 inferInstance
  have h := rightFibrations_cartesianSubcomplex (opFunctor.map p)
  rw [← op_cocartesianSubcomplex] at h
  rw [leftFibrations_iff_rightFibrations_op, Functor.map_comp]
  exact h

end SSet
