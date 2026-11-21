import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianMappingSpace
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty

universe u

namespace SSet.modelCategoryJoyal

theorem fibration_sliceAtFiberMap {X S : SSet.{u}} [S.Quasicategory]
    (p : X ⟶ S) [InnerFibration p] {x y : X _⦋0⦌} {b c : S _⦋0⦌} (hx : p.app _ x = b)
    (hy : p.app _ y = c) : Fibration (sliceAtFiberMap p hx hy) :=
  have := kanComplex_fiber_of_rightFibrations (rightFibrations_sliceAtπ S c) b
  fibration_of_rightFibrations (rightFibrations_sliceAtFiberMap p hx hy)

theorem isCartesianEdge_iff_forall_weakEquivalence {X S : SSet.{u}} [X.Quasicategory]
    [S.Quasicategory] (p : X ⟶ S) [InnerFibration p] (f : Δ[1] ⟶ X) :
    IsCartesianEdge p f ↔
      ∀ x : X _⦋0⦌, WeakEquivalence (leibnizSliceFiberMap (stdSimplex.δ 0) p f x) := by
  refine ⟨fun h x ↦ weakEquivalence_of_rlp_I
    ((isCartesianEdge_iff_forall_leibnizSliceFiberMap p f).1 h x), fun h ↦ ?_⟩
  have hres := rightFibrations_sliceRes (stdSimplex.δ 0) (f ≫ p)
  have hπ : rightFibrations (sliceπ (Under.mk (stdSimplex.δ 0 ≫ f))) := by
    have h : rightFibrations (sliceπ (Under.mk
        (yonedaEquiv.symm (yonedaEquiv (stdSimplex.δ 0 ≫ f))))) :=
      rightFibrations_sliceAtπ X _
    rwa [Equiv.symm_apply_apply] at h
  have hG : rightFibrations (pullback.fst ((slice Δ[0]).map (Under.homMk p (by simp) :
      Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)))
        (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p))) ≫
      sliceπ (Under.mk (stdSimplex.δ 0 ≫ f))) :=
    rightHornInclusions.rlp.comp_mem _ _
      (MorphismProperty.of_isPullback (P := rightHornInclusions.rlp)
        (IsPullback.of_hasPullback _ _).flip hres) hπ
  exact trivialFibration_of_rightFibrations_of_fiberMap hG
    (rightFibrations_leibnizSlice (stdSimplex.δ 0) p f) h

end SSet.modelCategoryJoyal

namespace SSet.modelCategoryJoyal

private theorem weakEquivalence_slice_square {K : SSet.{u}} {t t' : Under K}
    [t.right.Quasicategory] [t'.right.Quasicategory] (k : t ⟶ t')
    [WeakEquivalence k.right] : WeakEquivalence ((slice K).map k) := by
  have : WeakEquivalence k := (weakEquivalences_under_iff _ _).2 ‹_›
  have : IsFibrant t := (isFibrant_under_iff _ _).2
    ((isFibrant_iff_quasicategory _).2 inferInstance)
  have : IsFibrant t' := (isFibrant_under_iff _ _).2
    ((isFibrant_iff_quasicategory _).2 inferInstance)
  exact (isQuillen_joinRightUnderAdjunction K).weakEquivalence_map_of_isFibrant k

private theorem cartesianEdge_iff_weakEquivalence_leibnizSlice {X S : SSet.{u}}
    [X.Quasicategory] [S.Quasicategory] (p : X ⟶ S) [InnerFibration p]
    (f : Δ[1] ⟶ X) : IsCartesianEdge p f ↔
      WeakEquivalence (leibnizSlice (stdSimplex.δ 0) p f) := by
  have : ((slice Δ[0]).obj (Under.mk (stdSimplex.δ 0 ≫ f ≫ p))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs S.Quasicategory)
  have : ((slice Δ[0]).obj (Under.mk (stdSimplex.δ 0 ≫ f))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs X.Quasicategory)
  have hres := rightFibrations_sliceRes (stdSimplex.δ 0) (f ≫ p)
  have : ((slice Δ[0]).obj (Under.mk (stdSimplex.δ 0 ≫
      (Under.mk (f ≫ p)).hom))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs S.Quasicategory)
  have : Fibration (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p))) :=
    fibration_of_rightFibrations hres
  have : Fibration (pullback.fst ((slice Δ[0]).map (Under.homMk p (by simp) :
      Under.mk (stdSimplex.δ 0 ≫ f) ⟶ Under.mk (stdSimplex.δ 0 ≫ f ≫ p)))
        (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p)))) := inferInstance
  have : IsFibrant ((slice Δ[0]).obj (Under.mk (stdSimplex.δ 0 ≫ f))) :=
    (isFibrant_iff_quasicategory _).2 inferInstance
  have := isFibrant_of_fibration (pullback.fst ((slice Δ[0]).map
    (Under.homMk p rfl : Under.mk (stdSimplex.δ 0 ≫ f) ⟶
      Under.mk (stdSimplex.δ 0 ≫ f ≫ p)))
    (sliceRes (stdSimplex.δ 0) (Under.mk (f ≫ p))))
  have := (isFibrant_iff_quasicategory _).1 this
  have : Fibration (leibnizSlice (stdSimplex.δ 0) p f) :=
    fibration_of_rightFibrations (rightFibrations_leibnizSlice _ p f)
  change modelCategoryQuillen.I.rlp _ ↔ _
  rw [← rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp _ ↔ _
  rw [cofibrations_rlp, mem_trivialFibrations_iff]
  exact and_iff_right inferInstance

private theorem isFibrant_slice_obj {K Z : SSet.{u}} [Z.Quasicategory] (z : K ⟶ Z) :
    IsFibrant ((slice K).obj (Under.mk z)) :=
  (isFibrant_iff_quasicategory _).2
    (@quasicategory_slice _ _ (inferInstanceAs Z.Quasicategory))

private theorem leibnizSlice_naturality_square {A B X S X' S' : SSet.{u}}
    (j : A ⟶ B) (p : X ⟶ S) (p' : X' ⟶ S') (u : X ⟶ X') (v : S ⟶ S')
    (w : u ≫ p' = p ≫ v) (f : B ⟶ X)
    (t : pullback ((slice A).map (Under.homMk p (by simp) :
        Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ p)))
        (sliceRes j (Under.mk (f ≫ p))) ⟶
      pullback ((slice A).map (Under.homMk p' (by simp) :
        Under.mk (j ≫ (f ≫ u)) ⟶ Under.mk (j ≫ (f ≫ u) ≫ p')))
        (sliceRes j (Under.mk ((f ≫ u) ≫ p'))))
    (ht_fst : t ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      (slice A).map (Under.homMk u (by simp) :
        Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ u)))
    (ht_snd : t ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      (slice B).map (Under.homMk v (by simp [← w]) :
        Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ u) ≫ p'))) :
    leibnizSlice j p f ≫ t = (slice B).map (Under.homMk u rfl :
      Under.mk f ⟶ Under.mk (f ≫ u)) ≫ leibnizSlice j p' (f ≫ u) := by
  let a := (slice A).map (Under.homMk u (by simp) :
    Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ u))
  let d := (slice B).map (Under.homMk v (by simp [← w]) :
    Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ u) ≫ p'))
  let e := (slice B).map (Under.homMk u rfl :
    Under.mk f ⟶ Under.mk (f ≫ u))
  apply pullback.hom_ext
  · simp only [Category.assoc, ht_fst]
    calc
      _ = sliceRes j (Under.mk f) ≫ a :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ a) (leibnizSlice_fst j p f))
      _ = e ≫ sliceRes j (Under.mk (f ≫ u)) :=
        sliceRes_naturality j (Under.homMk u rfl : Under.mk f ⟶ Under.mk (f ≫ u))
      _ = _ := congrArg (e ≫ ·) (leibnizSlice_fst j p' (f ≫ u)).symm
  · simp only [Category.assoc, ht_snd]
    have hh : (slice B).map (Under.homMk p rfl : Under.mk f ⟶ Under.mk (f ≫ p)) ≫
        d = e ≫ (slice B).map
          (Under.homMk p' rfl : Under.mk (f ≫ u) ⟶ Under.mk ((f ≫ u) ≫ p')) := by
      dsimp only [d, e]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      exact Under.UnderMorphism.ext w.symm
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ d) (leibnizSlice_snd j p f)).trans
        (hh.trans (congrArg (e ≫ ·) (leibnizSlice_snd j p' (f ≫ u)).symm)))

theorem isCartesianEdge_comp_iff_of_weakEquivalence
    {X S X' S' : SSet.{u}} [X.Quasicategory] [S.Quasicategory]
    [X'.Quasicategory] [S'.Quasicategory] {p : X ⟶ S} {p' : X' ⟶ S'}
    [InnerFibration p] [InnerFibration p'] (u : X ⟶ X') (v : S ⟶ S')
    (w : u ≫ p' = p ≫ v) [WeakEquivalence u] [WeakEquivalence v]
    (f : Δ[1] ⟶ X) : IsCartesianEdge p' (f ≫ u) ↔ IsCartesianEdge p f := by
  let j : (Δ[0] : SSet.{u}) ⟶ Δ[1] := stdSimplex.δ 0
  let a := (slice Δ[0]).map (Under.homMk u (by simp) :
    Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ u))
  let b := (slice Δ[0]).map (Under.homMk v (by simp [← w]) :
    Under.mk (j ≫ f ≫ p) ⟶ Under.mk (j ≫ (f ≫ u) ≫ p'))
  let d := (slice Δ[1]).map (Under.homMk v (by simp [← w]) :
    Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ u) ≫ p'))
  let e := (slice Δ[1]).map (Under.homMk u rfl :
    Under.mk f ⟶ Under.mk (f ≫ u))
  let q := (slice Δ[0]).map (Under.homMk p (by simp) :
    Under.mk (j ≫ f) ⟶ Under.mk (j ≫ f ≫ p))
  let q' := (slice Δ[0]).map (Under.homMk p' (by simp) :
    Under.mk (j ≫ (f ≫ u)) ⟶ Under.mk (j ≫ (f ≫ u) ≫ p'))
  let r := sliceRes j (Under.mk (f ≫ p))
  let r' := sliceRes j (Under.mk ((f ≫ u) ≫ p'))
  have ha : a ≫ q' = q ≫ b := by
    dsimp only [a, q', q, b]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    exact Under.UnderMorphism.ext w
  have hd : d ≫ r' = r ≫ b :=
    (sliceRes_naturality j (Under.homMk v (by simp [← w]) :
      Under.mk (f ≫ p) ⟶ Under.mk ((f ≫ u) ≫ p'))).symm
  let t := pullback.map q r q' r' a d b ha.symm hd.symm
  have : WeakEquivalence a :=
    @weakEquivalence_slice_square _ _ _ ‹X.Quasicategory› ‹X'.Quasicategory› _ ‹_›
  have : WeakEquivalence b :=
    @weakEquivalence_slice_square _ _ _ ‹S.Quasicategory› ‹S'.Quasicategory› _ ‹_›
  have : WeakEquivalence d :=
    @weakEquivalence_slice_square _ _ _ ‹S.Quasicategory› ‹S'.Quasicategory› _ ‹_›
  have : WeakEquivalence e :=
    @weakEquivalence_slice_square _ _ _ ‹X.Quasicategory› ‹X'.Quasicategory› _ ‹_›
  have := isFibrant_slice_obj (j ≫ f)
  have := isFibrant_slice_obj (j ≫ (f ≫ u))
  have := isFibrant_slice_obj (j ≫ f ≫ p)
  have := isFibrant_slice_obj (j ≫ (f ≫ u) ≫ p')
  have := (isFibrant_iff_quasicategory _).1 (isFibrant_slice_obj (j ≫ f ≫ p))
  have := (isFibrant_iff_quasicategory _).1 (isFibrant_slice_obj (j ≫ (f ≫ u) ≫ p'))
  have : ((slice Δ[0]).obj (Under.mk (j ≫ (Under.mk (f ≫ p)).hom))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs S.Quasicategory)
  have : ((slice Δ[0]).obj
      (Under.mk (j ≫ (Under.mk ((f ≫ u) ≫ p')).hom))).Quasicategory :=
    @quasicategory_slice _ _ (inferInstanceAs S'.Quasicategory)
  have : Fibration r := fibration_of_rightFibrations (rightFibrations_sliceRes j _)
  have : Fibration r' := fibration_of_rightFibrations (rightFibrations_sliceRes j _)
  have : WeakEquivalence t := (IsPullback.of_hasPullback q r).flip
    |>.weakEquivalence_map_of_fibration (IsPullback.of_hasPullback q' r').flip
      d b a t hd.symm ha.symm (pullback.lift_snd _ _ _)
        (pullback.lift_fst _ _ _)
  have ht := leibnizSlice_naturality_square j p p' u v w f t
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  rw [cartesianEdge_iff_weakEquivalence_leibnizSlice,
    cartesianEdge_iff_weakEquivalence_leibnizSlice]
  calc
    WeakEquivalence (leibnizSlice j p' (f ≫ u)) ↔
        WeakEquivalence (e ≫ leibnizSlice j p' (f ≫ u)) :=
      (weakEquivalence_precomp_iff e _).symm
    _ ↔ WeakEquivalence (leibnizSlice j p f ≫ t) := by rw [ht]
    _ ↔ WeakEquivalence (leibnizSlice j p f) := weakEquivalence_postcomp_iff _ t

end SSet.modelCategoryJoyal
